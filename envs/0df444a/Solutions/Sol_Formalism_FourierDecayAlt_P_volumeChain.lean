-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.volumeChain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:11.228936+00:00
-- url     : https://prove2.me/submissions/92817262-07ac-4843-8f83-ce1a9fa0a4a1

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz1_vol_chain
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz1_disc_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_sumRanks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.Sz Formalism.FourierDecayAlt.P.Sz1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Sz.VolumeChain := by
  intro ι _ S hOk hM
  have hn : S.n = S.k + (2 * S.r + 1) := by unfold SizeData.n SizeData.m; omega
  have hm1 : S.m - 1 = 2 * S.r + 1 := by unfold SizeData.m; omega
  have hmR : (S.m : ℝ) - 1 = ((2 * S.r + 1 : ℕ) : ℝ) := by unfold SizeData.m; push_cast; ring
  have hsum := (sumRanks S.k S.r S.m S.n rfl rfl).1
  have h := vol_chain S hM (2 * S.r + 1) (by omega)
  rw [← hn, hsum] at h
  have hrd : 0 < S.rd := by unfold SizeData.rd; linarith [hOk.hv]
  have hdF : S.dF = S.rd ^ S.f := hOk.hdF
  have hka : S.v / Real.pi = S.ka⁻¹ := by unfold SizeData.ka; rw [inv_div]
  rw [h, hdF, disc_pow S.rd hrd, hka, inv_pow, hmR]
  simp only [mul_pow]
  ring
end Formalism.FourierDecayAlt.P
