-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVL.sum_resChar_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:39:00.447205+00:00
-- url     : https://prove2.me/submissions/b1fbc4f9-5b95-4663-b044-764148d9bd29

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVL
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_card_filter_resChar_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVL
open NumberField Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.BridgeLemVL
theorem _root_.solution (s : Finset {P : Ideal (𝓞 K) // P.IsMaximal}) :
    ∑ P ∈ s, ((resChar P.1 : ℝ) ^ 2)⁻¹ ≤ (Module.finrank ℚ K : ℝ) * Z2 := by
  classical
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr (by norm_num)
  have h1 : ∑ P ∈ s, ((resChar P.1 : ℝ) ^ 2)⁻¹ =
      ∑ n ∈ s.image (fun P => resChar P.1),
        ∑ P ∈ s.filter (fun P => resChar P.1 = n), ((resChar P.1 : ℝ) ^ 2)⁻¹ :=
    (Finset.sum_fiberwise_of_maps_to (fun P hP => Finset.mem_image_of_mem _ hP) _).symm
  rw [h1]
  calc ∑ n ∈ s.image (fun P => resChar P.1),
        ∑ P ∈ s.filter (fun P => resChar P.1 = n), ((resChar P.1 : ℝ) ^ 2)⁻¹
      ≤ ∑ n ∈ s.image (fun P => resChar P.1), (Module.finrank ℚ K : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_le_sum fun n _ => ?_
        have h2 : ∑ P ∈ s.filter (fun P => resChar P.1 = n), ((resChar P.1 : ℝ) ^ 2)⁻¹ =
            ((s.filter (fun P => resChar P.1 = n)).card : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
          rw [← nsmul_eq_mul, ← Finset.sum_const]
          refine Finset.sum_congr rfl fun P hP => ?_
          rw [(Finset.mem_filter.mp hP).2]
        rw [h2]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast card_filter_resChar_le s n
    _ = (Module.finrank ℚ K : ℝ) * ∑ n ∈ s.image (fun P => resChar P.1), ((n : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ K : ℝ) * Z2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact hs.sum_le_tsum _ (fun n _ => by positivity)
end Formalism.MainNotions.BridgeLemVL
