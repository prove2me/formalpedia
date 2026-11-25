-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_bdry_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:55:18.625966+00:00
-- url     : https://prove2.me/submissions/b76d2809-5b74-48fb-8636-90a2c220269c

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
theorem _root_.solution {x₀ x₁ y₀ y₁ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hx₁ : 1 < x₁)
    (hy₀ : y₀ < 0) (hy₁ : 0 < y₁) {w : ℂ} (hw : w ∈ exBdry x₀ x₁ y₀ y₁) : w ≠ 0 ∧ w ≠ 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  constructor
  · rintro rfl
    simp at h1
    linarith
  · rintro rfl
    simp at h5
    rcases h5 with h | h | h | h <;> linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
