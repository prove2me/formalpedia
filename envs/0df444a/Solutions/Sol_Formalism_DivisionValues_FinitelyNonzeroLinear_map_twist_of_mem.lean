-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.map_twist_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:39:40.866142+00:00
-- url     : https://prove2.me/submissions/fcb30213-01b8-420c-9673-f3e572bd3802

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
theorem _root_.solution {K0 : Subfield K} (hK0 : IsCMSub K0) (σ : K →+* ℂ) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (hA : ∀ i k, A i k ∈ K0) : A.map (twist σ) = A.map σ := by
  ext i k
  simp only [Matrix.map_apply, twist, RingHom.comp_apply, starRingEnd_apply]
  rw [hK0 σ _ (hA i k), starRingEnd_apply, star_star]
end Formalism.DivisionValues.FinitelyNonzeroLinear
