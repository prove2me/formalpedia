-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FlagSpanVanishing.zero_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:29:32.535215+00:00
-- url     : https://prove2.me/submissions/d5496c2b-261a-4f1e-848c-6b3d712034c7

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x6_Hpk_mul_apply
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_lo


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FlagSpanVanishing
open C2x5 C2x7
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FlagSpanVanishing
theorem _root_.solution (s : B.Mat k r) (hs : s ∈ B.GV k r)
    (hcol : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → s i (eI k r a) = if i = eI k r a then 1 else 0)
    (j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) :
    ∀ n : ℕ, ∀ a : Fin r, a.val = n → s (esI k r a) j = 0 := by
  have hU : sᴴ * Hpk k r * s = Hpk k r := hs
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a ha
    have e := congrFun (congrFun hU (eI k r a)) j
    rw [Matrix.mul_assoc, Matrix.mul_apply] at e
    simp only [C2x6.Hpk_mul_apply, Matrix.conjTranspose_apply] at e
    have hH : Hpk k r (eI k r a) j = 0 := by
      rw [GBasic.Hpk_eq, if_neg]
      intro h'; have := congrArg Fin.val h'
      rw [GBasic.sig_lo _ _ _ (by simp [eI])] at this; simp [eI] at this; omega
    rw [hH, Finset.sum_eq_single (eI k r a)] at e
    · rw [hcol a _ (by simp [eI]), if_pos rfl, star_one, one_mul] at e
      have hsig : GBasic.sig k r (eI k r a) = esI k r a := by
        apply Fin.ext; rw [GBasic.sig_lo _ _ _ (by simp [eI])]; simp [eI, esI]
      have hsg : GBasic.sgn k r (eI k r a) = 1 := by
        unfold GBasic.sgn; rw [if_neg]; simp [eI]; omega
      rw [hsig, hsg, one_mul] at e
      exact e
    · intro p _ hp
      by_cases hpa : a.val ≤ p.val
      · rw [hcol a p hpa, if_neg hp, star_zero, zero_mul]
      · push_neg at hpa
        have hpr : p.val < r := by omega
        have hsig : GBasic.sig k r p = esI k r ⟨p.val, hpr⟩ := by
          apply Fin.ext; rw [GBasic.sig_lo _ _ _ hpr]; simp [esI]
        rw [hsig, ih p.val (by omega) ⟨p.val, hpr⟩ rfl, mul_zero, mul_zero]
    · simp
end Formalism.FourierDecayAlt.P.FlagSpanVanishing
