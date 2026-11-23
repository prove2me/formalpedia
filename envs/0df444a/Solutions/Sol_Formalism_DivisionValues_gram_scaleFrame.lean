-- Prove2me | solution 1 for Formalism.DivisionValues.gram_scaleFrame
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:30.518888+00:00
-- url     : https://prove2.me/submissions/74185e47-4c8b-411b-9de6-e264814abf81

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Theorems.Thm_Formalism_DivisionValues_scaleFrame_inv
import Theorems.Thm_Formalism_DivisionValues_sqrt_mul_sqrt_complex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.DivisionValues
theorem _root_.solution [StarRing K] {d m : ℕ} (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K)
    (e : Fin m → Fin d → K) :
    gram (scaleFrame t X) v e = (t v : ℂ) • gram X v e := by
  have hs := scaleFrame_inv t ht X hX v
  have hmv : ∀ (u : Fin d → ℂ) (i : Fin d), ((((Real.sqrt (t v) : ℝ) : ℂ) • (X v)⁻¹) *ᵥ u) i =
      ((Real.sqrt (t v) : ℝ) : ℂ) * (((X v)⁻¹) *ᵥ u) i := by
    intro u i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  ext a c
  simp only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, hs, hmv, star_mul', map_mul, Complex.star_def,
    Complex.conj_ofReal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sqrt_mul_sqrt_complex (t v) (ht v)]
  ring
end Formalism.DivisionValues
