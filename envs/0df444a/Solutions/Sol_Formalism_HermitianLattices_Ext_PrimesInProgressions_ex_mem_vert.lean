-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_mem_vert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:59:39.293249+00:00
-- url     : https://prove2.me/submissions/776394ff-9640-47d1-9e6c-b6cc567c122b

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
theorem _root_.solution {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) {c : ℝ} (hc : c = x₀ ∨ c = x₁) {t : ℝ}
    (h : t ∈ Set.uIcc y₀ y₁) : ((c : ℂ) + t * I) ∈ exBdry x₀ x₁ y₀ y₁ := by
  rw [Set.uIcc_of_le hy] at h
  obtain ⟨h1, h2⟩ := h
  have hc' : x₀ ≤ c ∧ c ≤ x₁ := by
    rcases hc with rfl | rfl <;> constructor <;> linarith
  refine ⟨by simpa using hc'.1, by simpa using hc'.2, by simpa using h1, by simpa using h2, ?_⟩
  rcases hc with hc | hc
  · left
    simpa using hc
  · right; left
    simpa using hc
end Formalism.HermitianLattices.Ext.PrimesInProgressions
