-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exbox_log_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:56:36.100827+00:00
-- url     : https://prove2.me/submissions/725c6775-b848-4efe-8333-42b32e64bf73

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
theorem _root_.solution {M : ℕ} (hM : 3 ≤ M) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ Real.log ((M : ℝ) * (a + 2)) := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  apply Real.log_nonneg
  nlinarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
