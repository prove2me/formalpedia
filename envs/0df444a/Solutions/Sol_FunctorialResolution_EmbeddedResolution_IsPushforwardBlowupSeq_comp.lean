-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:31:25.585785+00:00
-- url     : https://prove2.me/submissions/9709629b-56f4-4476-b51c-19e5e136e5a2

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_StrictTransformClosedImmersion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_PushforwardComposition
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_comp
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_eq_ker
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_image_strictTransform_eq_strictTransform_image
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ker_comp_eq_imageIdealSheaf_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
namespace IsPushforwardBlowupSeq
private theorem ker_comp_eq_ker_subschemeι_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Scheme.Hom.ker (f ≫ g) = Scheme.Hom.ker ((Scheme.Hom.ker f).subschemeι ≫ g) :=
  (ker_comp_eq_imageIdealSheaf_ker f g).trans (imageIdealSheaf_eq_ker g f.ker)
end IsPushforwardBlowupSeq
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq
namespace FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq
theorem _root_.solution {Y H X : Scheme.{u}} (σ : Y ⟶ H) [IsClosedImmersion σ]
    (ρ : H ⟶ X) [IsClosedImmersion ρ]
    {s : SequenceOfBlowups Y} {t : SequenceOfBlowups H} {u : SequenceOfBlowups X}
    (hNt : ∀ i : ℕ, i ≤ t.length → AlgebraicGeometry.IsNoetherian (t.schemeAt i))
    (hNu : ∀ i : ℕ, i ≤ u.length → AlgebraicGeometry.IsNoetherian (u.schemeAt i))
    (hst : IsPushforwardBlowupSeq σ s t) (htu : IsPushforwardBlowupSeq ρ t u) :
    IsPushforwardBlowupSeq (σ ≫ ρ) s u := by
  obtain ⟨hl1, a, haci, ha0, hasq, hac, hak⟩ := hst
  obtain ⟨hl2, b, hbci, hb0, hbsq, hbc, hbk⟩ := htu
  refine ⟨hl1.trans hl2, fun i hi => a i hi ≫ b i (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hit : i ≤ t.length := by omega
    have := haci i hi
    have := hbci i hit
    show IsClosedImmersion (a i hi ≫ b i hit)
    infer_instance
  · show (a 0 (Nat.zero_le _) ≫ b 0 (Nat.zero_le _)) ≫ u.isoZero.hom
      = s.isoZero.hom ≫ (σ ≫ ρ)
    rw [Category.assoc, hb0, ← Category.assoc, ha0, Category.assoc]
  · intro i hi
    have hit : i < t.length := by omega
    show (a (i + 1) hi ≫ b (i + 1) hit) ≫ u.transitionMapSucc i
      = s.transitionMapSucc i ≫ (a i hi.le ≫ b i hit.le)
    rw [Category.assoc, hbsq i hit, ← Category.assoc, hasq i hi, Category.assoc]
  · intro i hi
    have hit : i < t.length := by omega
    have := haci i hi.le
    have := hbci i hit.le
    show u.center i = imageIdealSheaf (a i hi.le ≫ b i hit.le) (s.center i)
    rw [hbc i hit, hac i hi, imageIdealSheaf_comp]
  · intro i hi
    have hit : i < t.length := by omega
    have hiu : i < u.length := by omega
    have := hbci i hit.le
    have := hbci (i + 1) hit
    have := haci i hi.le
    have := haci (i + 1) hi
    have := hNt (i + 1) hit
    have := hNu (i + 1) hiu
    have hker : Scheme.Hom.ker (b (i + 1) hit)
        = Blowup.strictTransform (u.transitionMapSucc i)
            (Scheme.Hom.ker ((t.center i).subschemeι ≫ b i hit.le))
            (Scheme.Hom.ker (b i hit.le)) := by
      rw [hbk i hit, hbc i hit, imageIdealSheaf_eq_ker]
    have key := image_strictTransform_eq_strictTransform_image (b i hit.le) (t.center i)
      (Scheme.Hom.ker (a i hi.le)) (t.transitionMapSucc i) (u.transitionMapSucc i) (b (i + 1) hit)
      (hbsq i hit) hker
    have hL : Scheme.Hom.ker (a (i + 1) hi ≫ b (i + 1) hit)
        = Scheme.Hom.ker ((Blowup.strictTransform (t.transitionMapSucc i) (t.center i)
            (Scheme.Hom.ker (a i hi.le))).subschemeι ≫ b (i + 1) hit) := by
      rw [ker_comp_eq_ker_subschemeι_comp, hak i hi]
    have hD : Scheme.Hom.ker (a i hi.le ≫ b i hit.le)
        = Scheme.Hom.ker ((Scheme.Hom.ker (a i hi.le)).subschemeι ≫ b i hit.le) :=
      ker_comp_eq_ker_subschemeι_comp _ _
    have hC : u.center i = Scheme.Hom.ker ((t.center i).subschemeι ≫ b i hit.le) := by
      rw [hbc i hit, imageIdealSheaf_eq_ker]
    show Scheme.Hom.ker (a (i + 1) hi ≫ b (i + 1) hit)
      = Blowup.strictTransform (u.transitionMapSucc i) (u.center i)
          (Scheme.Hom.ker (a i hi.le ≫ b i hit.le))
    rw [hL, key, hC, hD]
end FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq
