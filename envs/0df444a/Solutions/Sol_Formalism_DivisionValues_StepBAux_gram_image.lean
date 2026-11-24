-- Prove2me | solution 1 for Formalism.DivisionValues.StepBAux.gram_image
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:01.472153+00:00
-- url     : https://prove2.me/submissions/7c41ec1a-bad3-43c9-b0e1-2beffe03aa55

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
import Theorems.Thm_Formalism_DivisionValues_StepBAux_gram_change
import Theorems.Thm_Formalism_DivisionValues_StepBAux_gram_det_real
import Theorems.Thm_Formalism_DivisionValues_StepBAux_gram_re_ne
import Theorems.Thm_Formalism_DivisionValues_StepBAux_std_li
import Theorems.Thm_Formalism_DivisionValues_StepBAux_vec_expand

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
theorem _root_.solution [IsTotallyComplex K] {d : ℕ}
    (XS XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hXS : ∀ v, IsUnit (XS v).det)
    (φ : Matrix (Fin d) (Fin d) K) (e : Fin d → Fin d → K) (v : InfinitePlace K) :
    (gram XT v (fun i => φ *ᵥ e i)).det = (detRatio XS XT φ v : ℂ) * (gram XS v e).det := by
  let γ : Matrix (Fin d) (Fin d) K := Matrix.of fun k i => e i k
  have he : e = fun i => ∑ k, γ k i • (Pi.single k 1 : Fin d → K) := by
    funext i; exact vec_expand (e i)
  have hφe : (fun i => φ *ᵥ e i) = fun i => ∑ k, γ k i • (φ *ᵥ (Pi.single k 1 : Fin d → K)) := by
    funext i
    conv_lhs => rw [vec_expand (e i)]
    rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, γ, Matrix.of_apply]
  have hS := gram_re_ne XS hXS _ (std_li d) v
  rw [hφe, gram_change, he, gram_change, detRatio]
  rw [gram_det_real XT v (fun i => φ *ᵥ (Pi.single i 1 : Fin d → K)),
    gram_det_real XS v (fun i => (Pi.single i 1 : Fin d → K))]
  have hS' : (((gram XS v fun i => (Pi.single i 1 : Fin d → K)).det.re : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hS
  simp only [Complex.ofReal_re]
  rw [Complex.ofReal_div, div_mul_eq_mul_div, eq_div_iff hS']
  ring
end Formalism.DivisionValues.StepBAux
