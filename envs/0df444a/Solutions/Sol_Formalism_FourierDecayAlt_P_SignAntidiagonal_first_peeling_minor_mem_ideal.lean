-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.first_peeling_minor_mem_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:33:16.3228+00:00
-- url     : https://prove2.me/submissions/a7377ee5-f58d-40f0-a44d-323cf01274cf

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPolynomialExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstPeelingMinorMemIdeal
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_peel_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_mem_gen
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_tm_offdiag
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_last_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_expansion_last_column

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val

set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (u : ℂ) : ∀ (m i : ℕ), i ≤ m → m + 1 ≤ r →
    qminor E (fun l : Fin m => pe k r l.val) (fun l : Fin m => pe k r (if l.val < i then l.val else l.val + 1)) u -
      qminor E (fun l : Fin i => pe k r l.val) (fun l : Fin i => pe k r l.val) u ∈ Ideal.span (rgen k r z' E) := by
  intro m
  induction m with
  | zero =>
    intro i hi _
    have hi0 : i = 0 := by omega
    subst hi0
    have e : (fun l : Fin 0 => pe k r (if l.val < 0 then l.val else l.val + 1)) = fun l : Fin 0 => pe k r l.val :=
      funext fun l => l.elim0
    rw [e, sub_self]
    exact Submodule.zero_mem _
  | succ m ih =>
    intro i hi hr
    rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · have hih := ih i (by omega) (by omega)
      have hstep : qminor E (fun l : Fin (m + 1) => pe k r l.val)
            (fun l : Fin (m + 1) => pe k r (if l.val < i then l.val else l.val + 1)) u -
          qminor E (fun l : Fin m => pe k r l.val)
            (fun l : Fin m => pe k r (if l.val < i then l.val else l.val + 1)) u ∈
            Ideal.span (rgen k r z' E) := by
        have hc := peel_core (Ideal.span (rgen k r z' E)) (ι := Unit) (fun _ => (1 : ℂ))
          (fun l : Fin (m + 1) => qminor E ((fun l : Fin (m + 1) => pe k r l.val) ∘ l.succAbove)
              (fun l : Fin m => pe k r (if l.val < i then l.val else l.val + 1)) u)
          (fun l _ => Tm E (u - (m : ℂ)) (pe k r l.val) (pe k r (m + 1))) 1 ?_
        · rw [Formalism.FourierDecayAlt.P.expansion_last_column A (2 * r + k + 1) m E]
          have hm : ¬ (m < i) := by omega
          simpa [Fin.succAbove_last, Fin.val_last, hm, Function.comp_def, Fin.coe_castSucc] using hc
        · intro l
          have hl := l.isLt
          have h1 : min (l.val) (2 * r + k) = l.val := Nat.min_eq_left (by omega)
          have h2 : min (m + 1) (2 * r + k) = m + 1 := Nat.min_eq_left (by omega)
          have hne : pe k r l.val ≠ pe k r (m + 1) := by
            intro e
            have := congrArg Fin.val e
            simp only [pe_val, h1, h2] at this
            omega
          have hin : InNp k r (pe k r l.val) (pe k r (m + 1)) := by
            simp only [InNp, pe_val, h1, h2]
            omega
          have hd : dpsiP k r z' (pe k r l.val) (pe k r (m + 1)) = if l.val = m then 1 else 0 := by
            simp only [dpsiP, pe_val, h1, h2]
            rw [if_pos ⟨by omega, by omega⟩]
            split_ifs <;> first | rfl | (exfalso; omega)
          simp only [Finset.univ_unique, Finset.sum_singleton, one_smul, last_iff]
          rw [tm_offdiag _ _ hne, ← hd]
          exact mem_gen hin
      have hsum := (Ideal.span (rgen k r z' E)).add_mem hstep hih
      rwa [sub_add_sub_cancel] at hsum
    · have hi1 : i = m + 1 := by omega
      subst hi1
      have e : (fun l : Fin (m + 1) => pe k r (if l.val < m + 1 then l.val else l.val + 1)) =
          fun l : Fin (m + 1) => pe k r l.val := by
        funext l
        rw [if_pos l.isLt]
      rw [e, sub_self]
      exact Submodule.zero_mem _
end Formalism.FourierDecayAlt.P.SignAntidiagonal
