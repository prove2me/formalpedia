-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.exists_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:21.945173+00:00
-- url     : https://prove2.me/submissions/e5f934b0-4b2e-438e-8b0d-c9e9da2794f2

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.RF
variable {K : Type} [Field K] [StarRing K] {n : ℕ} {J : Matrix (Fin n) (Fin n) K} {W : Submodule K (Fin n → K)}
namespace CompanionTheory.D.gk.RF
theorem _root_.solution (hJ : Jᴴ = J) (hd : IsUnit J.det) {κ : Type} [Fintype κ] [DecidableEq κ] {v : κ → Fin n → K}
    (hv : LinearIndependent K v) : ∃ u : κ → Fin n → K, ∀ i j, hf J (u i) (v j) = if i = j then 1 else 0 := by
  have hk : LinearMap.ker (Fintype.linearCombination K v) = ⊥ :=
    LinearMap.ker_eq_bot'.2 fun c hc => funext (Fintype.linearIndependent_iff.1 hv c hc)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
  refine ⟨fun i => J⁻¹ *ᵥ star fun k => g (Pi.single k 1) i, fun i j => ?_⟩
  have h1 : g (v j) = Pi.single j 1 := by
    have := LinearMap.congr_fun hg (Pi.single j 1)
    simpa [Fintype.linearCombination_apply_single] using this
  have h2 : (J⁻¹)ᴴ = J⁻¹ := by rw [conjTranspose_nonsing_inv, hJ]
  unfold hf
  rw [star_mulVec, star_star, h2, dotProduct_mulVec, vecMul_vecMul, nonsing_inv_mul J hd, vecMul_one]
  have h3 : v j = ∑ k, v j k • (Pi.single k 1 : Fin n → K) := by
    ext l; simp [Finset.sum_apply, Pi.single_apply]
  have h4 := congrFun h1 i
  rw [h3, map_sum, Finset.sum_apply] at h4
  rw [Pi.single_apply] at h4
  rw [← h4]
  simp only [dotProduct, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
end CompanionTheory.D.gk.RF
