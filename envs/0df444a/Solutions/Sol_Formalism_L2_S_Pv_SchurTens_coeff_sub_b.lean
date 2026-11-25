-- Prove2me | solution 1 for Formalism.L2.S.Pv.SchurTens.coeff_sub_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:18:37.206307+00:00
-- url     : https://prove2.me/submissions/8d1e0578-0a2c-4694-82c1-13288817cf73

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
theorem _root_.solution (a b₁ b₂ : Hs) : (fun x => coeff σs a b₁ x - coeff σs a b₂ x) = coeff σs a (b₁ - b₂) := by
  funext x
  simp only [coeff, inner_sub_left]
end Formalism.L2.S.Pv.SchurTens
