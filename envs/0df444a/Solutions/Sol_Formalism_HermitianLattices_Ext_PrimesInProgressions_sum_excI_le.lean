-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.sum_excI_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:33:47.567802+00:00
-- url     : https://prove2.me/submissions/0800ad2b-1e05-4ae0-befc-adf2c139b247

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
theorem _root_.solution {M : ℕ} [NeZero M] (e : Option (DirichletCharacter ℂ M × ℝ)) :
    ∑ χ : DirichletCharacter ℂ M, excI e χ ≤ 1 := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excI]
  · have h : (∑ χ : DirichletCharacter ℂ M, excI (some (χ₁, β₁)) χ) = excI (some (χ₁, β₁)) χ₁ :=
      Finset.sum_eq_single χ₁ (fun b _ hb => if_neg hb) (fun h => absurd (Finset.mem_univ _) h)
    rw [h]
    exact (if_pos rfl).le
end Formalism.HermitianLattices.Ext.PrimesInProgressions
