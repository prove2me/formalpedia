-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.excI_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:59:48.12226+00:00
-- url     : https://prove2.me/submissions/1b954661-f8a7-408b-bd23-83295fe38eb5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTBAsmB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) :
    0 ≤ excI e χ := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · exact le_rfl
  · simp only [excI]; split_ifs <;> norm_num
end Formalism.HermitianLattices.Ext.PrimesInProgressions
