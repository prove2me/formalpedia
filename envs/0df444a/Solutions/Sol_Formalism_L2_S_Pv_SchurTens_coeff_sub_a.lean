-- Prove2me | solution 1 for Formalism.L2.S.Pv.SchurTens.coeff_sub_a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:17:59.558669+00:00
-- url     : https://prove2.me/submissions/b87e0a7a-e276-43c7-84fb-404afd259ca2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_LimitMemLpAndIntegralEq
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensSpan
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.SchurTens
open Formalism.L2.SG.Pf.EnergyAbs
variable {K : Type} [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}
namespace Formalism.L2.S.Pv.SchurTens
theorem _root_.solution (a₁ a₂ b : Hs) : (fun x => coeff σs a₁ b x - coeff σs a₂ b x) = coeff σs (a₁ - a₂) b := by
  funext x
  simp only [coeff, map_sub, inner_sub_right]
end Formalism.L2.S.Pv.SchurTens
