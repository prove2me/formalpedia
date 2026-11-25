-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_rectInt_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:37:46.203414+00:00
-- url     : https://prove2.me/submissions/b2683f02-d454-40fd-a6b4-f1913e601f4b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRect
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectF
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_ii_horiz
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_ii_vert

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
    (hf : ContinuousOn f (exBdry x₀ x₁ y₀ y₁)) (hg : ContinuousOn g (exBdry x₀ x₁ y₀ y₁)) :
    Formalism.ZF.rectInt (fun w => f w + g w) x₀ x₁ y₀ y₁ =
      Formalism.ZF.rectInt f x₀ x₁ y₀ y₁ + Formalism.ZF.rectInt g x₀ x₁ y₀ y₁ := by
  unfold Formalism.ZF.rectInt
  rw [intervalIntegral.integral_add (ex_ii_horiz hx hy hf (Or.inl rfl)) (ex_ii_horiz hx hy hg (Or.inl rfl)),
    intervalIntegral.integral_add (ex_ii_horiz hx hy hf (Or.inr rfl)) (ex_ii_horiz hx hy hg (Or.inr rfl)),
    intervalIntegral.integral_add (ex_ii_vert hx hy hf (Or.inr rfl)) (ex_ii_vert hx hy hg (Or.inr rfl)),
    intervalIntegral.integral_add (ex_ii_vert hx hy hf (Or.inl rfl)) (ex_ii_vert hx hy hg (Or.inl rfl))]
  ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
