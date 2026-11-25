-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.hsA_sand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:11:40.156197+00:00
-- url     : https://prove2.me/submissions/98427aea-164b-4341-a464-419136e2a5ab

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsSchur
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_inner_sand
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_hsA_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution (σ : G → (HH →L[ℂ] HH)) (Y : V →L[ℂ] HH) (Y' : V' →L[ℂ] HH) (γ : G) :
    hsA (sand σ Y Y' γ) = ∑ j, ∑ i,
      ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2 := by
  rw [hsA_eq]
  simp only [inner_sand]
end Formalism.L2.S.Pv.EnergyAbs
