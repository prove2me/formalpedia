-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.PF_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:42:51.275258+00:00
-- url     : https://prove2.me/submissions/5b434631-8fc7-444d-8822-0832a0a5d45f

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
theorem _root_.solution {ι : Type*} {f : (ι → ℝ) → ℂ} (hf : f ∈ PF ι) : (fun y => conj (f y)) ∈ PF ι := by
  obtain ⟨p, hp⟩ := PF_mem_iff.1 hf
  refine PF_mem_iff.2 ⟨MvPolynomial.map (starRingEnd ℂ) p, fun y => ?_⟩
  rw [hp, MvPolynomial.eval_map]
  show starRingEnd ℂ (MvPolynomial.eval₂ (RingHom.id ℂ) _ p) = _
  rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  congr 1
  funext i
  simp
end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
