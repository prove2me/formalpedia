-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_rectInt_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:13:16.136338+00:00
-- url     : https://prove2.me/submissions/01fbdf8a-4ac9-49b8-89e5-4cf3c29805f6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRect
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectF
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_mem_horiz
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_mem_vert

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
theorem _root_.solution {f g : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (h : ∀ w ∈ exBdry x₀ x₁ y₀ y₁, f w = g w) :
    Formalism.ZF.rectInt f x₀ x₁ y₀ y₁ = Formalism.ZF.rectInt g x₀ x₁ y₀ y₁ := by
  have hh : ∀ c : ℝ, (c = y₀ ∨ c = y₁) →
      (∫ x : ℝ in x₀..x₁, f (x + c * I)) = ∫ x : ℝ in x₀..x₁, g (x + c * I) := by
    intro c hc
    exact intervalIntegral.integral_congr fun x hx' => h _ (ex_mem_horiz hx hy hc hx')
  have hv : ∀ c : ℝ, (c = x₀ ∨ c = x₁) →
      (∫ t : ℝ in y₀..y₁, f (c + t * I)) = ∫ t : ℝ in y₀..y₁, g (c + t * I) := by
    intro c hc
    exact intervalIntegral.integral_congr fun t ht => h _ (ex_mem_vert hx hy hc ht)
  unfold Formalism.ZF.rectInt
  rw [hh y₀ (Or.inl rfl), hh y₁ (Or.inr rfl), hv x₀ (Or.inl rfl), hv x₁ (Or.inr rfl)]
end Formalism.HermitianLattices.Ext.PrimesInProgressions
