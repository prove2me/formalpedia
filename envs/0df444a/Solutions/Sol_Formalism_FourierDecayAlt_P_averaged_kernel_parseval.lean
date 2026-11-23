-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.averaged_kernel_parseval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:16.243501+00:00
-- url     : https://prove2.me/submissions/ba4561e3-dc3d-4b63-86b8-22dfdd5f2cc3

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_thxSum_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open AveragedKernelSums
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.ThxSum := by
  intro _ _ hPL hLF _ _ _ _ _ K _ _ _ R ψ hL hchar m s n₀ F Om Lc D τ cr _ _ h _ h' _
  obtain ⟨hlat, hpp, hvol⟩ := hPL K R ψ hL hchar D.L₁ D.lat₁
  exact thxSum_core hL D.le₁ D.A D.B D.repsB hpp
    (hLF K (perp ψ D.L₁) R.toAddSubgroup hlat ⟨hL.isOpen, hL.isCompact⟩) hvol m τ cr h h'
end Formalism.FourierDecayAlt.P
