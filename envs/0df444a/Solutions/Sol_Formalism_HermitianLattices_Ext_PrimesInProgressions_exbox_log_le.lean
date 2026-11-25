-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exbox_log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:59:44.406969+00:00
-- url     : https://prove2.me/submissions/a696f963-d81a-460d-bb02-9ee8b5e312e3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLocL
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplBox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {M : ℕ} (hM : 3 ≤ M) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b ≤ a + 1) :
    Real.log ((M : ℝ) * (b + 2)) ≤ 2 * Real.log ((M : ℝ) * (a + 2)) := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h1 : 0 < (M : ℝ) * (b + 2) := by positivity
  have hX : 6 ≤ (M : ℝ) * (a + 2) := by nlinarith
  have h3 : (M : ℝ) * (b + 2) ≤ 2 * ((M : ℝ) * (a + 2)) := by nlinarith
  have h2 : (M : ℝ) * (b + 2) ≤ ((M : ℝ) * (a + 2)) ^ 2 := by nlinarith
  calc Real.log ((M : ℝ) * (b + 2)) ≤ Real.log (((M : ℝ) * (a + 2)) ^ 2) := Real.log_le_log h1 h2
    _ = 2 * Real.log ((M : ℝ) * (a + 2)) := by rw [Real.log_pow]; norm_num
end Formalism.HermitianLattices.Ext.PrimesInProgressions
