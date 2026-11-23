-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.nilpotent_lie_algebra
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:56:34.351895+00:00
-- url     : https://prove2.me/submissions/b009b714-8215-4662-9aa1-f05ce3caff22

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation
import Theorems.Thm_CompanionTheory_D_gk_RF_mat_extC
import Theorems.Thm_CompanionTheory_D_gk_RF_Lowers_triple
import Theorems.Thm_CompanionTheory_D_gk_RF_Lowers_add
import Theorems.Thm_CompanionTheory_D_gk_RF_Lowers_smul
import Theorems.Thm_CompanionTheory_D_gk_RF_Lowers_neg
import Theorems.Thm_CompanionTheory_D_gk_RF_Lowers_mul_perp
import Theorems.Thm_CompanionTheory_D_gk_RF_lowers_of_Z
import Theorems.Thm_CompanionTheory_D_gk_RF_Lowers_mul
import Theorems.Thm_CompanionTheory_D_gk_RF_second_order_exp_mul
import Theorems.Thm_CompanionTheory_D_gk_RF_star_half
import Theorems.Thm_CompanionTheory_D_gk_RF_skew_eq
import Theorems.Thm_CompanionTheory_D_gk_RF_skew_mul

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
variable [CharZero K]
namespace CompanionTheory.D.gk.RF
theorem _root_.solution : NilpAlg := by
  intro K _ _ _ n J W _ _ hW
  have inv : ∀ X, Lowers J W X → ex2 X * ex2 (-X) = 1 := fun X hX => by
    rw [second_order_exp_mul hX hX.neg]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    module
  have hneg : ∀ X, InL J W X → InL J W (-X) := fun X hX =>
    ⟨by rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hX.1, neg_zero], hX.2.neg⟩
  refine ⟨fun X hX => ⟨?_, ?_, inv X hX.2, hneg X hX⟩, fun g hg hA => ?_, fun X Y hX hY => ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩,
    fun Z hZ => ⟨⟨hZ.1, lowers_of_Z hW hZ.2.1 hZ.2.2⟩, ⟨?_, fun z hz => ?_, fun z => ?_⟩, fun X hX => ⟨?_, ?_⟩⟩⟩
  · have h1 : (ex2 X)ᴴ * J = J * ex2 (-X) := by
      simp only [ex2, conjTranspose_add, conjTranspose_one, conjTranspose_smul, star_half, add_mul, mul_add,
        smul_mul_assoc, mul_smul_comm, skew_mul hX.1 hX.1, skew_eq hX.1, Matrix.one_mul, Matrix.mul_one,
        Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    have h2 := inv _ hX.2.neg
    rw [neg_neg] at h2
    rw [h1, Matrix.mul_assoc, h2, Matrix.mul_one]
  · have : ex2 X - 1 = X + (2 : K)⁻¹ • (X * X) := by unfold ex2; abel
    rw [this]
    exact hX.2.add ((hX.2.mul hW hX.2).smul _)
  · obtain ⟨A, rfl⟩ : ∃ A, g = 1 + A := ⟨g - 1, by abel⟩
    rw [add_sub_cancel_left] at hA
    have t := hA.triple hA hA
    have h1 : (Aᴴ * J + J * (A - A * A)) * (1 + A) = 0 := by
      have e : (1 + A)ᴴ * J * (1 + A) - J = 0 := by rw [hg, sub_self]
      rw [← e]
      simp only [conjTranspose_add, conjTranspose_one, mul_add, add_mul, mul_sub, sub_mul, Matrix.mul_assoc, t,
        Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero]
      abel
    have h2 : (1 + A) * (1 - A + A * A) = 1 := by
      simp only [mul_add, add_mul, mul_sub, t, Matrix.one_mul, Matrix.mul_one]
      abel
    have h3 : Aᴴ * J = -(J * (A - A * A)) := by
      have := congrArg (· * (1 - A + A * A)) h1
      simp only [Matrix.mul_assoc _ (1 + A), h2, Matrix.mul_one, Matrix.zero_mul] at this
      exact eq_neg_of_add_eq_zero_left this
    have h4 : (A * A)ᴴ * J = J * (A * A) := by
      rw [conjTranspose_mul, Matrix.mul_assoc, h3, Matrix.mul_neg, ← Matrix.mul_assoc, h3]
      simp only [Matrix.neg_mul, neg_neg, mul_sub, sub_mul, Matrix.mul_assoc, t, Matrix.mul_zero, sub_zero,
        neg_zero]
    refine ⟨A + (-(2 : K)⁻¹) • (A * A), ⟨?_, hA.add ((hA.mul hW hA).smul _)⟩, ?_⟩
    · simp only [conjTranspose_add, conjTranspose_smul, star_neg, star_half, add_mul, mul_add, smul_mul_assoc,
        mul_smul_comm, h3, h4, mul_sub]
      module
    · simp only [ex2, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc, t, Matrix.mul_zero,
        smul_zero, add_zero]
      module
  · exact ⟨by rw [conjTranspose_add, add_mul, mul_add, skew_eq hX.1, skew_eq hY.1]; abel, hX.2.add hY.2⟩
  · simp only [conjTranspose_smul, conjTranspose_sub, star_half, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub,
      skew_mul hX.1 hY.1, skew_mul hY.1 hX.1]
    module
  · intro z hz
    rw [smul_mulVec, sub_mulVec, (hX.2.mul_perp hY.2).1 z hz, (hY.2.mul_perp hX.2).1 z hz, sub_zero, smul_zero]
  · intro z
    rw [smul_mulVec, sub_mulVec]
    exact W.smul_mem _ (W.sub_mem ((hX.2.mul_perp hY.2).2 z) ((hY.2.mul_perp hX.2).2 z))
  · have a := hX.2
    have b := hY.2
    rw [second_order_exp_mul a b]
    simp only [ex2, mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc,
      a.triple a a, a.triple a b, a.triple b a, a.triple b b, b.triple a a, b.triple a b, b.triple b a,
      b.triple b b, Matrix.mul_zero, smul_zero, sub_zero, add_zero, sub_self]
    module
  · rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hZ.1, neg_zero]
  · rw [neg_mulVec, hZ.2.1 z hz, neg_zero]
  · rw [neg_mulVec]; exact W.neg_mem (hZ.2.2 z)
  · exact mat_extC fun z => by rw [← mulVec_mulVec, hZ.2.1 _ (hX.2.2.2 z), zero_mulVec]
  · exact mat_extC fun z => by rw [← mulVec_mulVec, hX.2.1 _ (hZ.2.2 z), zero_mulVec]
end CompanionTheory.D.gk.RF
