-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.map_conjTranspose_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:19:02.403256+00:00
-- url     : https://prove2.me/submissions/d7caaecf-33d1-4ab8-86a1-c3dd140691ff

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_Formalism_HN_twist


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
theorem _root_.solution {m n : ℕ} (σ : K →+* ℂ) (A : Matrix (Fin m) (Fin n) K) :
    (Aᴴ).map σ = (A.map (twist σ))ᴴ := by
  ext i k
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply, twist, RingHom.comp_apply,
    starRingEnd_apply, star_star]
end Formalism.DivisionValues.FinitelyNonzeroLinear
