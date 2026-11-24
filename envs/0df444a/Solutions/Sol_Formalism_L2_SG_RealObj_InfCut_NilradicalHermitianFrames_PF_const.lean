-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.PF_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:42:50.442751+00:00
-- url     : https://prove2.me/submissions/57da0c0b-1013-461f-af6e-69f6d7cf0129

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_VolumeZeroFintype
import Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_NilradicalHermitianFrames_PF_mem_iff

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
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
theorem _root_.solution {ι : Type*} (a : ℂ) : (fun _ : ι → ℝ => a) ∈ PF ι :=
  PF_mem_iff.2 ⟨MvPolynomial.C a, fun y => by simp⟩
end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
