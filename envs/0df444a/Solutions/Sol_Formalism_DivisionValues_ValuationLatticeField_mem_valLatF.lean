-- Prove2me | solution 1 for Formalism.DivisionValues.ValuationLatticeField.mem_valLatF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:35:37.557078+00:00
-- url     : https://prove2.me/submissions/c8d97a77-ee70-4e93-aa11-fdf618107705

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualGeF
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily

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
open Formalism.DivisionValues.ValuationLatticeField
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.ValuationLatticeField
theorem _root_.solution {n : ℕ} {Cl V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (I : (Fin n → K) →ₗ[K] (Cl → V)) (N : Cl → Submodule (𝓞 K) V)
    (x : Fin n → K) : x ∈ valLatF I N ↔ ∀ c, I x c ∈ N c := by
  simp [valLatF, Submodule.mem_pi]
end Formalism.DivisionValues.ValuationLatticeField
