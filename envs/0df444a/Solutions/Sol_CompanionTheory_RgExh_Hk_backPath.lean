-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.backPath
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:21.724093+00:00
-- url     : https://prove2.me/submissions/f940cbf2-65a4-4da4-a847-43e7d56ff0a8

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_ScalarCharacters_ScalCharOfSimple
import Theorems.Thm_CompanionTheory_RgExh_Hk_nontrivial_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet)
variable {n : ℕ}
namespace CompanionTheory.RgExh.Hk
theorem _root_.solution (hC : StepChar) (hV : NonVan) (hNS : NonScal) (hB : Back) :
    ∀ (ss : List (Fin n)) (X : GMod n) (χ : Fin n → ℂ), GoodPath χ ss → HasChar X χ → Nontrivial X.V →
      ScalChar (path X χ ss) (pathEnd χ ss) → ScalChar X χ ∧ SimplePath χ ss := by
  intro ss
  induction ss with
  | nil =>
    intro X χ _ _ _ hS
    change ScalChar X χ at hS
    refine ⟨hS, ?_⟩
    change True
    trivial
  | cons s ss ih =>
    intro X χ hG hH hN hS
    change (∀ r, χ r ≠ χ s + 1) ∧ GoodPath (χ + Pi.single s 1) ss at hG
    change ScalChar (path (step X (χ s)) (χ + Pi.single s 1) ss) (pathEnd (χ + Pi.single s 1) ss) at hS
    obtain ⟨hf, hG'⟩ := hG
    have hH' := hC n X χ s hH
    have hN' := nontrivial_step hV hH hN hf
    obtain ⟨hS1, hSP⟩ := ih (step X (χ s)) (χ + Pi.single s 1) hG' hH' hN' hS
    obtain ⟨hSX, hom⟩ := hB n X χ s hH hf hS1
    refine ⟨hSX, ?_⟩
    change (∀ r, r ≠ s → χ r ≠ χ s) ∧ SimplePath (χ + Pi.single s 1) ss
    refine ⟨?_, hSP⟩
    intro r hrs heq
    obtain ⟨f, hf1, hf2⟩ := hNS n X χ s hSX hN hf ⟨r, hrs, heq⟩
    exact hf2 (hom f hf1)
end CompanionTheory.RgExh.Hk
