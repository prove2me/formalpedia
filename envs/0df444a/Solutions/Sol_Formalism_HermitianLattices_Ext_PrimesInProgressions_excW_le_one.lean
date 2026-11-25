-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.excW_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:59:06.994617+00:00
-- url     : https://prove2.me/submissions/2643c97c-b984-4175-956c-ababf787b345

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
theorem _root_.solution {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (ρ : ℂ) :
    excW e χ ρ ≤ 1 := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excW]
  · simp only [excW]; split_ifs <;> norm_num
end Formalism.HermitianLattices.Ext.PrimesInProgressions
