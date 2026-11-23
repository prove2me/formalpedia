-- Prove2me | solution 1 for Formalism.DivisionValues.StepBAux.isLocBasis_image
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:12.546988+00:00
-- url     : https://prove2.me/submissions/2432eae1-1de9-440d-b730-03c0773ab906

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Theorems.Thm_Formalism_DivisionValues_StepBAux_image_li
import Theorems.Thm_Formalism_DivisionValues_StepBAux_matLat_eq_map
import Theorems.Thm_Formalism_DivisionValues_StepBAux_locS_map
import Theorems.Thm_Formalism_DivisionValues_StepBAux_span_image

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.StepBAux
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.StepBAux
theorem _root_.solution {d : ℕ} (φ : Matrix (Fin d) (Fin d) K) (hφ : IsUnit φ.det)
    (L : Submodule (𝓞 K) (Fin d → K)) (w : HeightOneSpectrum (𝓞 K)) (e : Fin d → Fin d → K)
    (he : IsLocBasis L w e) : IsLocBasis (matLat φ L) w (fun i => φ *ᵥ e i) := by
  refine ⟨image_li φ hφ e he.1, ?_⟩
  have h2 := he.2
  unfold Formalism.HermitianLatticesTheory.loc at h2 ⊢
  rw [span_image, matLat_eq_map φ hφ, matLat_eq_map φ hφ, locS_map, locS_map, h2]
end Formalism.DivisionValues.StepBAux
