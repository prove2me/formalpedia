-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.shift_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:44.341391+00:00
-- url     : https://prove2.me/submissions/33f71505-a07b-46aa-80c9-fece0c663046

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_card_slab
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_sdiff1
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_sdiff2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxAverageLimits
open Formalism.FourierDecayAlt.crystallineComparison
variable {Λ : Type} [AddCommGroup Λ] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.BoxAverageLimits
theorem _root_.solution (R : ℕ) (j : ι) (G : (ι → ℕ) → ℂ) (B : ℝ) (hB : ∀ m, ‖G m‖ ≤ B) :
    ‖∑ m ∈ box ι R, G (m + Pi.single j 1) - ∑ m ∈ box ι R, G m‖ ≤
      2 * B * R ^ (Fintype.card ι - 1) := by
  have hinj : Set.InjOn (fun m : ι → ℕ => m + Pi.single j 1) (box ι R) :=
    fun a _ b _ h => add_right_cancel h
  rw [← Finset.sum_image (f := G) (g := fun m => m + Pi.single j 1) hinj]
  rw [← Finset.sum_sdiff_sub_sum_sdiff]
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have e1 : ‖∑ x ∈ (box ι R).image (fun m => m + Pi.single j 1) \ box ι R, G x‖ ≤
      B * R ^ (Fintype.card ι - 1) := by
    calc _ ≤ ∑ x ∈ (box ι R).image (fun m => m + Pi.single j 1) \ box ι R, ‖G x‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ (box ι R).image (fun m => m + Pi.single j 1) \ box ι R, B :=
          Finset.sum_le_sum (fun x _ => hB x)
      _ = _ * B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (R ^ (Fintype.card ι - 1) : ℕ) * B := by
          gcongr
          rw [← card_slab R j R]
          exact Finset.card_le_card (sdiff2 R j)
      _ = _ := by push_cast; ring
  have e2 : ‖∑ x ∈ box ι R \ (box ι R).image (fun m => m + Pi.single j 1), G x‖ ≤
      B * R ^ (Fintype.card ι - 1) := by
    calc _ ≤ ∑ x ∈ box ι R \ (box ι R).image (fun m => m + Pi.single j 1), ‖G x‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ box ι R \ (box ι R).image (fun m => m + Pi.single j 1), B :=
          Finset.sum_le_sum (fun x _ => hB x)
      _ = _ * B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (R ^ (Fintype.card ι - 1) : ℕ) * B := by
          gcongr
          rw [← card_slab R j 0]
          exact Finset.card_le_card (sdiff1 R j)
      _ = _ := by push_cast; ring
  calc _ ≤ ‖∑ x ∈ (box ι R).image (fun m => m + Pi.single j 1) \ box ι R, G x‖ +
        ‖∑ x ∈ box ι R \ (box ι R).image (fun m => m + Pi.single j 1), G x‖ := norm_sub_le _ _
    _ ≤ _ := by linarith
end Formalism.FourierDecayAlt.P.BoxAverageLimits
