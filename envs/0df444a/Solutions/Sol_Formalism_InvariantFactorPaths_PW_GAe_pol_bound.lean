-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.GAe_pol_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:59:36.043598+00:00
-- url     : https://prove2.me/submissions/e32954ae-2b03-4c7b-a26c-76b88a8d18fb

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_isWt_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_wt_sub_le

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
theorem _root_.solution (LL L2 : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) :
    ∀ (μ ν : Fin n → ℤ) (x y : MvPolynomial (Fin N × Fin r) ℚ_[p]), x ≠ 0 → y ≠ 0 →
      x ∈ Pol p r L2 → y ∈ Pol p r L2 → (GAe p LL j e).IsWt μ x → (GAe p LL j e).IsWt ν y →
      ∀ c, |ν c - μ c| ≤ (L2.total : ℤ) := by
  intro μ ν x y hx0 hy0 hx hy hμ hν c
  rw [GAe_isWt_iff, MvPolynomial.mem_restrictSupport_iff] at hμ hν
  obtain ⟨m, hm⟩ := (MvPolynomial.support_nonempty).mpr hx0
  obtain ⟨m', hm'⟩ := (MvPolynomial.support_nonempty).mpr hy0
  have d1 : MultiDeg L2 m := (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hx hm
  have d2 : MultiDeg L2 m' := (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hy hm'
  rw [← hμ hm c, ← hν hm' c, abs_le]
  have a1 := wt_sub_le LL L2 j (e c) d1 d2
  have a2 := wt_sub_le LL L2 j (e c) d2 d1
  constructor <;> linarith
end Formalism.InvariantFactorPaths.PW
