-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_ii_horiz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:16:20.281902+00:00
-- url     : https://prove2.me/submissions/933379c8-0c6a-4ce0-bd4f-3b44796bf6b7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRect
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectF
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_mem_horiz

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
theorem _root_.solution {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hf : ContinuousOn f (exBdry x₀ x₁ y₀ y₁)) {c : ℝ} (hc : c = y₀ ∨ c = y₁) :
    IntervalIntegrable (fun x : ℝ => f (x + c * I)) MeasureTheory.volume x₀ x₁ := by
  apply ContinuousOn.intervalIntegrable
  exact hf.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + c * I).continuousOn
    fun x hx' => ex_mem_horiz hx hy hc hx'
end Formalism.HermitianLattices.Ext.PrimesInProgressions
