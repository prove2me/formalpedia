-- Prove2me | solution 1 for Formalism.L2.LamCM.valuation_le_of_eq_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:43.638798+00:00
-- url     : https://prove2.me/submissions/52855d50-c585-4e4b-ba23-c6556ab538e9

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementB
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ValuationLeOfEqAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors ComplexOrder
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM
theorem _root_.solution {K' R : Type} [Field K'] [CommRing R] [Algebra R K']
    (p : HeightOneSpectrum (𝓞 K)) (f : K →+* K')
    (hval : ∀ y : K, f y ∈ Set.range (algebraMap R K') ↔ p.valuation K y ≤ 1) {k c : K} (hc : c ≠ 0) (w : R)
    (hw : f (k / c) = algebraMap R K' w) : p.valuation K k ≤ p.valuation K c := by
  have h1 : p.valuation K (k / c) ≤ 1 := (hval _).1 ⟨w, hw.symm⟩
  calc p.valuation K k = p.valuation K (k / c) * p.valuation K c := by
        rw [← map_mul, div_mul_cancel₀ k hc]
    _ ≤ 1 * p.valuation K c := by gcongr
    _ = p.valuation K c := one_mul _
end Formalism.L2.LamCM
