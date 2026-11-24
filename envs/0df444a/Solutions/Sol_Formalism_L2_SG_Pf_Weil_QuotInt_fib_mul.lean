-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Weil.QuotInt.fib_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:36.580827+00:00
-- url     : https://prove2.me/submissions/903a8cbb-f1c9-42a4-ad6a-13a590522c3b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CasimirReductionTheory_OneParameterDerivatives_WeilIndicatorMeasures_MeasurableUnitMulIndicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Set Filter
open scoped ENNReal NNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Weil
open Formalism.L2.SG.Pf.Weil.QuotInt
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] {H : Subgroup G}
namespace Formalism.L2.SG.Pf.Weil.QuotInt
theorem _root_.solution (κ : Measure H) [κ.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) (h₀ : H) :
    fib κ f (g * h₀) = fib κ f g := by
  unfold fib
  have key := lintegral_mul_left_eq_self (μ := κ) (fun h : H => f (g * (h : G))) h₀
  simpa [mul_assoc] using key
end Formalism.L2.SG.Pf.Weil.QuotInt
