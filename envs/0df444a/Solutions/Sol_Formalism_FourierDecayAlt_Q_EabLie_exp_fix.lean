-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabLie.exp_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:02:27.333494+00:00
-- url     : https://prove2.me/submissions/d5894f34-198e-4277-9b1c-b08f3f852447

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_HasDerivAtExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabLie
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.EabLie
theorem _root_.solution (Y : Mx k r) (c : Fin (2 * r + k + 1)) (hY : ∀ x, Y x c = 0) :
    NormedSpace.exp Y *ᵥ bvec c = bvec c := by
  set P : Mx k r := Matrix.single c c 1 with hPdef
  have hYP : Y * P = 0 := by
    ext x y
    simp only [hPdef, Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    split_ifs with h
    · rw [← h.1, hY, mul_one]
    · exact mul_zero _
  have hne : NormedSpace.exp Y ≠ 0 := by
    intro h0
    have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
        NormedSpace.exp_zero]
    rw [h0, Matrix.mul_zero] at hc
    have := congrFun (congrFun hc ⟨0, by omega⟩) ⟨0, by omega⟩
    simp at this
  have hsum : Summable (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n) := by
    by_contra hns
    apply hne
    rw [congrFun (NormedSpace.exp_eq_tsum ℂ) Y]
    exact tsum_eq_zero_of_not_summable hns
  have hhas : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n) (NormedSpace.exp Y) := by
    have := hsum.hasSum
    rwa [← congrFun (NormedSpace.exp_eq_tsum ℂ) Y] at this
  have h1 := hhas.mul_right P
  have h2 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n * P) P := by
    have := hasSum_single (f := fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n * P) 0 (by
      intro m hm
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
      rw [Matrix.smul_mul, pow_succ, Matrix.mul_assoc, hYP, Matrix.mul_zero, smul_zero])
    simpa using this
  have hEP : NormedSpace.exp Y * P = P := h1.unique h2
  have hPv : P *ᵥ bvec c = bvec c := by
    ext x
    by_cases h : x = c
    · subst h; simp [hPdef, bvec, Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply]
    · simp [hPdef, bvec, Matrix.mulVec, dotProduct, Pi.single_apply, h, Ne.symm h]
  rw [← hPv, Matrix.mulVec_mulVec, hEP]
end Formalism.FourierDecayAlt.Q.EabLie
