-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.topologicalKrullDim_lt_top_of_finite_isOpenCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:22:36.178076+00:00
-- url     : https://prove2.me/submissions/e64495dd-64ad-4159-9b67-114daa88943d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_KrullDimClosedSubset
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FiniteKrullDim
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_topologicalKrullDim_le_natCast_of_isOpenCover
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_toMarkedSequence_lastIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_toMarkedSequence_toSequenceOfBlowups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_lastIdeal
attribute [local simp] FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_toSequenceOfBlowups


section
universe u v
open TopologicalSpace AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
private theorem natCast_withBot_ne_top (n : ℕ) : ((n : ℕ) : WithBot ℕ∞) ≠ ⊤ := by
  intro hcontra
  have h2 : ((n : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
    rw [WithBot.coe_natCast]
    exact hcontra
  have h3 : (n : ℕ∞) = ⊤ := WithBot.coe_injective h2
  simp at h3
private theorem natCast_withBot_lt_top (n : ℕ) : ((n : ℕ) : WithBot ℕ∞) < ⊤ :=
  lt_top_iff_ne_top.mpr (natCast_withBot_ne_top n)
private theorem exists_le_natCast_of_lt_top {a : WithBot ℕ∞} (h : a < ⊤) :
    ∃ n : ℕ, a ≤ ((n : ℕ) : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact ⟨0, bot_le⟩
  | coe b =>
    induction b using WithTop.recTopCoe with
    | top => exact absurd h (lt_irrefl _)
    | coe n => exact ⟨n, le_rfl⟩
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u v
open TopologicalSpace AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Type u} [TopologicalSpace X]
    {ι : Type v} [Finite ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = Set.univ) (h : ∀ i, topologicalKrullDim ↥(U i) < ⊤) :
    topologicalKrullDim X < ⊤ := by
  classical
  choose N hN using fun i => exists_le_natCast_of_lt_top (h i)
  have : Fintype ι := Fintype.ofFinite ι
  have hle : topologicalKrullDim X ≤ (((Finset.univ.sup N : ℕ) : ℕ) : WithBot ℕ∞) := by
    refine topologicalKrullDim_le_natCast_of_isOpenCover U hU hcov _ ?_
    intro i
    exact le_trans (hN i) (Nat.mono_cast (Finset.le_sup (Finset.mem_univ i)))
  exact lt_of_le_of_lt hle (natCast_withBot_lt_top _)
end FunctorialResolution.EmbeddedResolution
