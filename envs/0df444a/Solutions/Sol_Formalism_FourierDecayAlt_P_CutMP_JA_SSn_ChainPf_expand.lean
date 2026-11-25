-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf.expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:28:55.474132+00:00
-- url     : https://prove2.me/submissions/53c5c982-08cb-4997-a4cf-9dc69a38c9f3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddSSnChain
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddSSnChainPf
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_SSn_ChainPf_hasDerivAt_list_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_SSn_ChainPf_list_sum_flatMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_SSn_ChainPf_tval_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_ev
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.SSn Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {V E' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
theorem _root_.solution {Ψ : V → E'} (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) {F : Mat k r → V}
    {U : Set (Mat k r)} (hU : IsOpen U) (hF : CkOn ⊤ (U ∩ GV k r) F) :
    ∀ w : List (Bool × Mat k r), (∀ y ∈ w, inLie k r y.2) →
      ∃ ts : List (Tm k r), ts.length ≤ (w.length + 1).factorial ∧
        (∀ t ∈ ts, t.j ≤ w.length ∧ (∑ i, (t.ws i).length) = w.length ∧ ∀ i, (t.ws i).Sublist w) ∧
        ∀ g ∈ U, g ∈ GV k r → Dw w (fun g => Ψ (F g)) g = (ts.map fun t => tval Ψ F t g).sum := by
  intro w
  induction w with
  | nil =>
    intro _
    refine ⟨[⟨0, Fin.elim0⟩], by simp, ?_, ?_⟩
    · intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      exact ⟨le_rfl, by simp, fun i => i.elim0⟩
    · intro g _ _
      simp [tval, Dw]
  | cons x w ih =>
    intro hw
    obtain ⟨ts, hlen, hts, hval⟩ := ih (fun y hy => hw y (List.mem_cons_of_mem _ hy))
    have hx : inLie k r x.2 := hw x (by simp)
    refine ⟨ts.flatMap (tnext x), ?_, ?_, ?_⟩
    · have hl : ∀ t ∈ ts, (tnext x t).length ≤ w.length + 1 := by
        intro t ht
        simp only [tnext, List.length_cons, List.length_ofFn]
        have := (hts t ht).1
        omega
      have hs : (ts.map fun t => (tnext x t).length).sum ≤ (ts.map fun _ => w.length + 1).sum :=
        List.sum_le_sum hl
      rw [List.map_const', List.sum_replicate, smul_eq_mul] at hs
      rw [List.length_flatMap, List.length_cons, Nat.factorial_succ]
      calc _ ≤ ts.length * (w.length + 1) := hs
        _ ≤ (w.length + 1).factorial * (w.length + 1 + 1) := Nat.mul_le_mul hlen (by omega)
        _ = (w.length + 1 + 1) * (w.length + 1).factorial := Nat.mul_comm _ _
    · intro t' ht'
      obtain ⟨t, ht, ht'⟩ := List.mem_flatMap.mp ht'
      obtain ⟨hj, hsum, hsub⟩ := hts t ht
      simp only [tnext, List.mem_cons, List.mem_ofFn] at ht'
      rcases ht' with rfl | ⟨i, rfl⟩
      · refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
        · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, List.length_cons, List.length_nil, hsum]
          omega
        · intro i
          refine Fin.cases ?_ (fun i => ?_) i
          · simp
          · simpa using (hsub i).cons x
      · refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
        · have e : ∀ l, (Function.update t.ws i (x :: t.ws i) l).length = (t.ws l).length + if l = i then 1 else 0 := by
            intro l
            by_cases h : l = i
            · subst h
              simp
            · simp [Function.update_apply, h]
          simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, hsum,
            List.length_cons]
        · intro l
          by_cases h : l = i
          · simpa [h] using (hsub i).cons₂ x
          · simpa [Function.update_apply, h] using (hsub l).cons x
    · intro g hgU hg
      show Dx x (Dw w (fun g => Ψ (F g))) g = _
      rw [Dx_eq]
      have hev : Filter.EventuallyEq (nhds (0 : ℝ)) (fun s : ℝ => Dw w (fun g => Ψ (F g)) (crv x g s))
          (fun s => (ts.map fun t => tval Ψ F t (crv x g s)).sum) := by
        filter_upwards [crv_ev (x := x) hU hgU] with s hs
        exact hval _ hs (crv_mem hx hg s)
      rw [hev.deriv_eq, list_sum_flatMap]
      exact (hasDerivAt_list_sum ts (fun t s => tval Ψ F t (crv x g s))
        (fun t => ((tnext x t).map fun t' => tval Ψ F t' g).sum)
        (fun t ht => tval_hasDerivAt hΨ hF hx t
          (fun i y hy => hw y (List.mem_cons_of_mem _ (((hts t ht).2.2 i).subset hy))) hgU hg)).deriv
end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
