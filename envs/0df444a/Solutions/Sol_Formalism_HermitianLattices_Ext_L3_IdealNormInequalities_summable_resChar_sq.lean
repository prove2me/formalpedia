-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.summable_resChar_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:36.025146+00:00
-- url     : https://prove2.me/submissions/bf5024e4-8d03-4e09-96c9-1421c9c02787

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_card_filter_resChar_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
theorem _root_.solution :
    Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => ((resChar P.1 : ℝ) ^ 2)⁻¹) := by

  classical
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr (by norm_num)
  refine summable_of_sum_le (c := (finrank ℚ K : ℝ) * ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹) (fun P => by positivity)
    (fun u => ?_)
  calc ∑ P ∈ u, ((resChar P.1 : ℝ) ^ 2)⁻¹
      = ∑ n ∈ u.image (fun P => resChar P.1),
          ∑ P ∈ u.filter (fun P => resChar P.1 = n), ((resChar P.1 : ℝ) ^ 2)⁻¹ :=
        (Finset.sum_fiberwise_of_maps_to (fun P hP => Finset.mem_image_of_mem _ hP) _).symm
    _ = ∑ n ∈ u.image (fun P => resChar P.1),
          ((u.filter (fun P => resChar P.1 = n)).card : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.mp hP).2]), Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ ∑ n ∈ u.image (fun P => resChar P.1), (finrank ℚ K : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast card_filter_resChar_le u n
    _ = (finrank ℚ K : ℝ) * ∑ n ∈ u.image (fun P => resChar P.1), ((n : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ (finrank ℚ K : ℝ) * ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hs.sum_le_tsum _ (fun n _ => by positivity)
end Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
