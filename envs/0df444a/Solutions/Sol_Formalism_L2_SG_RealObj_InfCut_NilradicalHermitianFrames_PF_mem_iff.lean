-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.PF_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:29:26.611943+00:00
-- url     : https://prove2.me/submissions/32be06ce-1cd9-45da-b5d1-c96461dd541a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_VolumeZeroFintype
import Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_NilradicalHermitianFrames_PF_eval

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
theorem _root_.solution {ι : Type*} {f : (ι → ℝ) → ℂ} :
    f ∈ PF ι ↔ ∃ p : MvPolynomial ι ℂ, ∀ y, f y = MvPolynomial.eval (fun i => (y i : ℂ)) p := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p, fun y => PF_eval p y⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, funext fun y => (PF_eval p y).trans (hp y).symm⟩
end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
