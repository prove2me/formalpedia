-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.fwdPath
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:16:45.25943+00:00
-- url     : https://prove2.me/submissions/1ea38455-47ce-4b03-9d9d-ced1b947e276

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_ScalarCharacters_ScalCharOfSimple
import Theorems.Thm_CompanionTheory_RgExh_Hk_scalChar_of_simple

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
theorem _root_.solution (hQ : QdetEq) (hC : StepChar) (hOS : OmScal) (hF : FwdSimple) (hR : Reflect) :
    ∀ (ss : List (Fin n)) (X : GMod n) (χ : Fin n → ℂ), GoodPath χ ss → SimplePath χ ss → IsSimple X →
      HasChar X χ → IsSimple (path X χ ss) ∧
        ∀ X' : GMod n, IsSimple X' → HasChar X' χ → Iso (path X χ ss) (path X' χ ss) → Iso X X' := by
  intro ss
  induction ss with
  | nil =>
    intro X χ _ _ hS _
    refine ⟨?_, fun X' _ _ hI => ?_⟩
    · change IsSimple X
      exact hS
    · change Iso X X' at hI
      exact hI
  | cons s ss ih =>
    intro X χ hG hSP hS hH
    change (∀ r, χ r ≠ χ s + 1) ∧ GoodPath (χ + Pi.single s 1) ss at hG
    change (∀ r, r ≠ s → χ r ≠ χ s) ∧ SimplePath (χ + Pi.single s 1) ss at hSP
    obtain ⟨hf, hG'⟩ := hG
    obtain ⟨hd, hSP'⟩ := hSP
    have hSc := scalChar_of_simple hQ hS hH
    have hS1 : IsSimple (step X (χ s)) := hF n X χ s hS hSc hf hd (hOS n X χ s hSc hd)
    have hH1 := hC n X χ s hH
    obtain ⟨hP, hRefl⟩ := ih (step X (χ s)) (χ + Pi.single s 1) hG' hSP' hS1 hH1
    refine ⟨?_, fun X' hS' hH' hI => ?_⟩
    · change IsSimple (path (step X (χ s)) (χ + Pi.single s 1) ss)
      exact hP
    · change Iso (path (step X (χ s)) (χ + Pi.single s 1) ss) (path (step X' (χ s)) (χ + Pi.single s 1) ss) at hI
      have hSc' := scalChar_of_simple hQ hS' hH'
      have hS1' : IsSimple (step X' (χ s)) := hF n X' χ s hS' hSc' hf hd (hOS n X' χ s hSc' hd)
      have hI1 := hRefl (step X' (χ s)) hS1' (hC n X' χ s hH') hI
      exact hR n X X' χ s hSc hSc' hf hd hI1
end CompanionTheory.RgExh.Hk
