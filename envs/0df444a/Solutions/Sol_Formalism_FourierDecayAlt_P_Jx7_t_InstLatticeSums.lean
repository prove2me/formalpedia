-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.t_InstLatticeSums
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:02.066695+00:00
-- url     : https://prove2.me/submissions/9b0297f5-4857-442d-a50b-5f66232a4a47

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped ComplexOrder
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution : InstLatticeSums := by
  intro hLJ hIS hBox hLat hId hNorm hDeg hFP hX
  obtain ⟨C, hC1, hC⟩ := hLJ hBox
  refine ⟨C * 2 ^ ((5 : ℝ) - 5 / 2), ?_, ?_⟩
  · have : (1 : ℝ) ≤ 2 ^ ((5 : ℝ) - 5 / 2) := Real.one_le_rpow (by norm_num) (by norm_num)
    nlinarith
  intro E W _ _ _ D e G Cc de de' T T' l Θ hU hInst hg1 hg2 hCc hlen hΘ hGr
  obtain ⟨hSB, hIdl, _⟩ := hIS hLat hId hNorm hDeg hFP hX E W D e G Cc de de' T T' l Θ hU hInst hg1 hg2 hCc
    hlen (by linarith) hGr
  refine ⟨hSB, ?_⟩
  have hK : D.K = 5 := hInst.2.1
  have := hC E W D e _ _ Θ 2 hInst.2.2.1 (by omega) (by norm_num) (by linarith) hIdl
  have hK' : (D.K : ℝ) = 5 := by exact_mod_cast hK
  rw [hK'] at this ⊢
  exact this
end Formalism.FourierDecayAlt.P.Jx7
