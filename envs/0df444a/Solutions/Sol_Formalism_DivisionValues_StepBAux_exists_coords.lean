-- Prove2me | solution 1 for Formalism.DivisionValues.StepBAux.exists_coords
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:03:34.862802+00:00
-- url     : https://prove2.me/submissions/3b527152-11be-436b-a323-f7ad2aa3004d

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
theorem _root_.solution {d : ℕ} (b : Fin d → Fin d → K) (hb : LinearIndependent K b)
    (f : Fin d → Fin d → K) : ∃ γ : Matrix (Fin d) (Fin d) K, f = fun i => ∑ k, γ k i • b k := by
  have hsp : Submodule.span K (Set.range b) = ⊤ :=
    hb.span_eq_top_of_card_eq_finrank' (by simp)
  let B := Basis.mk hb (by rw [hsp])
  refine ⟨Matrix.of fun k i => B.repr (f i) k, funext fun i => ?_⟩
  have h := (B.sum_repr (f i)).symm
  simpa [B, Basis.mk_apply] using h
end Formalism.DivisionValues.StepBAux
