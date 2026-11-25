-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_mem_horiz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:46:03.345981+00:00
-- url     : https://prove2.me/submissions/0e9d963f-2979-471b-95c9-f7b39fce100b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRect
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectF

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
theorem _root_.solution {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) {c : ℝ} (hc : c = y₀ ∨ c = y₁) {x : ℝ}
    (h : x ∈ Set.uIcc x₀ x₁) : ((x : ℂ) + c * I) ∈ exBdry x₀ x₁ y₀ y₁ := by
  rw [Set.uIcc_of_le hx] at h
  obtain ⟨h1, h2⟩ := h
  have hc' : y₀ ≤ c ∧ c ≤ y₁ := by
    rcases hc with rfl | rfl <;> constructor <;> linarith
  refine ⟨by simpa using h1, by simpa using h2, by simpa using hc'.1, by simpa using hc'.2, ?_⟩
  right; right
  simpa using hc
end Formalism.HermitianLattices.Ext.PrimesInProgressions
