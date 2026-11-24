-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallC.mem_ell
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:29.827738+00:00
-- url     : https://prove2.me/submissions/bc43a4de-96f0-46b6-91fe-a60924787d3d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VolumeNormSqLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallC
variable {M : ℕ} (a : Fin M → ℝ)
namespace Formalism.HermitianLattices.Ext.L3.BallC
theorem _root_.solution {z : Fin M → ℂ} : z ∈ ell a ↔ ∑ i, a i * Complex.normSq (z i) ≤ 1 := Iff.rfl
end Formalism.HermitianLattices.Ext.L3.BallC
