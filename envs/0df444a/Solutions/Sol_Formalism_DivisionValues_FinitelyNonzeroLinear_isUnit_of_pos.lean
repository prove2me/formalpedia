-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.isUnit_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:37:19.035453+00:00
-- url     : https://prove2.me/submissions/e2a4e769-7a28-41fe-8952-b7a62b1f3c81

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist

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
open Formalism.DivisionValues.FinitelyNonzeroLinear
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
theorem _root_.solution {σ : K →+* ℂ} {n : ℕ}
    {H : Matrix (Fin n) (Fin n) K} (hpos : (H.map σ).PosDef) : IsUnit H := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  have hp := hpos.det_pos
  have e : (H.map σ).det = σ H.det := (RingHom.map_det σ H).symm
  rw [e, h0, map_zero] at hp
  exact lt_irrefl _ hp
end Formalism.DivisionValues.FinitelyNonzeroLinear
