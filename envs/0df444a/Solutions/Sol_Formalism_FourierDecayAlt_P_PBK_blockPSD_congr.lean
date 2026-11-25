-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.blockPSD_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:08:36.96072+00:00
-- url     : https://prove2.me/submissions/8e817f36-ef78-429a-bb8b-5a1649be3282

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockPSDCongr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {α β : Type} (Y₁ : Finset α) (Y₂ : Finset β) (a a' : α → α → ℂ) (w w' : α → β → ℂ)
    (b b' : β → β → ℂ) (ha : ∀ p ∈ Y₁, ∀ q ∈ Y₁, a p q = a' p q) (hw : ∀ p ∈ Y₁, ∀ q ∈ Y₂, w p q = w' p q)
    (hb : ∀ p ∈ Y₂, ∀ q ∈ Y₂, b p q = b' p q) (h : KB.BlockPSD Y₁ Y₂ a w b) : KB.BlockPSD Y₁ Y₂ a' w' b' := by
  unfold KB.BlockPSD TB.PSDOn at *
  convert h using 1
  ext ⟨x, hx⟩ ⟨y, hy⟩
  rcases x with p | p <;> rcases y with q | q <;>
    simp only [Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] at hx hy <;> simp [*]
end Formalism.FourierDecayAlt.P.PBK
