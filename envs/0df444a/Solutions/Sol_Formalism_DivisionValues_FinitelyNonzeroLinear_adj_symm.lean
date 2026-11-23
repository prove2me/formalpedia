-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.adj_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:22.013441+00:00
-- url     : https://prove2.me/submissions/12255b0d-3e57-40f3-94b2-63687017f5f0

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
variable {n : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ}
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
theorem _root_.solution (hH : Hc.PosDef) {N N' : Matrix (Fin n) (Fin n) ℂ} (hadj : Nᴴ * Hc = Hc * N') :
    N'ᴴ * Hc = Hc * N := by
  have hHh : Hcᴴ = Hc := hH.isHermitian
  have := congrArg Matrix.conjTranspose hadj
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hHh] at this
  exact this.symm
end Formalism.DivisionValues.FinitelyNonzeroLinear
