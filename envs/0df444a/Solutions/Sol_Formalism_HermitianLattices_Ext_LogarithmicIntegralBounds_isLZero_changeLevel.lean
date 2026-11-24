-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.isLZero_changeLevel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:33.866229+00:00
-- url     : https://prove2.me/submissions/afd9e24c-27c4-4bb9-aecb-64be55ba8ba6

import Mathlib
import Definitions.Def_Formalism_LandauZeroFreeBounds_Statement
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqPage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution {M q : ℕ} [NeZero M] [NeZero q] (h : M ∣ q) (χ : DirichletCharacter ℂ M) (hχ : χ ≠ 1)
    {s : ℂ} (hs : DirichletCharacter.LFunction χ s = 0) :
    Formalism.ZeroFreeDirichlet.IsLZero (DirichletCharacter.changeLevel h χ) s := by
  refine ⟨Or.inl ?_, ?_⟩
  · intro h1
    apply hχ
    apply DirichletCharacter.changeLevel_injective h
    rw [h1, map_one]
  · rw [DirichletCharacter.LFunction_changeLevel h χ (Or.inl hχ), hs, zero_mul]
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
