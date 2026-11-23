-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.exists_blk_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:00.224162+00:00
-- url     : https://prove2.me/submissions/c0f20491-8ffd-4778-a8f4-288896e69a8f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_eta
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upperUni_blk_iff

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
theorem _root_.solution {n : ℕ} {u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hu : IsUpperUni u) :
    ∃ (u' : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ), IsUpperUni u' ∧ u = blk u' b 0 1 := by
  have h := blk_eta u
  rw [h, upperUni_blk_iff] at hu
  obtain ⟨h1, h2, h3⟩ := hu
  refine ⟨_, fun i => u i.castSucc (Fin.last n), h1, ?_⟩
  rw [h2, h3] at h
  exact h
end Formalism.FourierDecayAlt.P.G4
