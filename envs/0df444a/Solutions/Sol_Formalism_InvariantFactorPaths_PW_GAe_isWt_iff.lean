-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.GAe_isWt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:23:46.649342+00:00
-- url     : https://prove2.me/submissions/bab19ad9-2586-476c-aceb-1718d4ebcce9

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) (μ : Fin n → ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    (GAe p LL j e).IsWt μ x ↔ x ∈ MvPolynomial.restrictSupport ℚ_[p] {m | ∀ a, wt LL j (e a) m = μ a} := by
  classical
  rw [MvPolynomial.mem_restrictSupport_iff]
  unfold GlW.IsWt
  rw [GAe_comp]
  constructor
  · intro h m hm a
    have hm' : coeff m x ≠ 0 := mem_support_iff.mp hm
    rw [← h, coeff_weightedHomogeneousComponent] at hm'
    have hw : Finsupp.weight (fun x => (wv LL j x) ∘ e) m = μ := by
      by_contra hne; exact hm' (if_neg hne)
    rw [← weight_comp_apply, hw]
  · intro h
    ext m
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hw
    · rfl
    · by_contra hne
      apply hw
      funext a
      rw [weight_comp_apply]
      exact h (mem_support_iff.mpr (Ne.symm hne)) a
end Formalism.InvariantFactorPaths.PW
