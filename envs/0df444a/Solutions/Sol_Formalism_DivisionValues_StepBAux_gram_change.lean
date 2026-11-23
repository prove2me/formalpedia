-- Prove2me | solution 1 for Formalism.DivisionValues.StepBAux.gram_change
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:30.689256+00:00
-- url     : https://prove2.me/submissions/2d8e912d-a78f-483e-bfdd-aaaf829959c2

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
import Theorems.Thm_Formalism_DivisionValues_StepBAux_gram_eq_fmat
import Theorems.Thm_Formalism_DivisionValues_StepBAux_fmat_change

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
theorem _root_.solution {d m : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v : InfinitePlace K) (e : Fin m → Fin d → K) (γ : Matrix (Fin m) (Fin m) K) :
    (gram X v (fun i => ∑ k, γ k i • e k)).det =
      star (v.embedding γ.det) * v.embedding γ.det * (gram X v e).det := by
  have hγ : (γ.map v.embedding).det = v.embedding γ.det := (RingHom.map_det _ _).symm
  rw [gram_eq_fmat, gram_eq_fmat, fmat_change, Matrix.conjTranspose_mul]
  have : (γ.map v.embedding)ᴴ * (fmat v.embedding e)ᴴ * met X v *
      (fmat v.embedding e * γ.map v.embedding) =
      (γ.map v.embedding)ᴴ * ((fmat v.embedding e)ᴴ * met X v * fmat v.embedding e) *
        γ.map v.embedding := by
    simp only [Matrix.mul_assoc]
  rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hγ]
  ring
end Formalism.DivisionValues.StepBAux
