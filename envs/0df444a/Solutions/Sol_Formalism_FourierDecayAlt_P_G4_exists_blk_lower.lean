-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.exists_blk_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:23.804253+00:00
-- url     : https://prove2.me/submissions/a7964d70-d9a3-418e-ad94-3c6f7955de20

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_eta
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_lowerUni_blk_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4
namespace Formalism.FourierDecayAlt.P.G4
theorem _root_.solution {n : ℕ} {l : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hl : IsLowerUni l) :
    ∃ (l' : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ), IsLowerUni l' ∧ l = blk l' 0 a 1 := by
  have h := blk_eta l
  rw [h, lowerUni_blk_iff] at hl
  obtain ⟨h1, h2, h3⟩ := hl
  refine ⟨_, fun j => l (Fin.last n) j.castSucc, h1, ?_⟩
  rw [h2, h3] at h
  exact h
end Formalism.FourierDecayAlt.P.G4
