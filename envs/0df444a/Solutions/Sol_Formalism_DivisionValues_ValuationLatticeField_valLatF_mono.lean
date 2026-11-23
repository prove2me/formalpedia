-- Prove2me | solution 1 for Formalism.DivisionValues.ValuationLatticeField.valLatF_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:37.498238+00:00
-- url     : https://prove2.me/submissions/4e7d38ca-d8eb-415f-999f-fd23a65dee39

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualGeF
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Theorems.Thm_Formalism_DivisionValues_ValuationLatticeField_mem_valLatF

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
    [IsScalarTower (𝓞 K) K V] (I : (Fin n → K) →ₗ[K] (Cl → V)) {N N' : Cl → Submodule (𝓞 K) V}
    (h : ∀ c, N c ≤ N' c) : valLatF I N ≤ valLatF I N' := fun x hx =>
  (mem_valLatF I N' x).mpr fun c => h c ((mem_valLatF I N x).mp hx c)
end Formalism.DivisionValues.ValuationLatticeField
