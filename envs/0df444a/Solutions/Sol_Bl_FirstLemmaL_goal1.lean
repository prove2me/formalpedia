-- Prove2me | solution 1 for Bl.FirstLemmaL.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:34:39.366284+00:00
-- url     : https://prove2.me/submissions/344c3e3a-e22f-41ba-8039-4f328ff85b6d

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.FirstLemmaL
namespace Bl.FirstLemmaL
theorem _root_.solution :
  ∀ {G : Type} [inst : Group.{0} G] [inst_1 : TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G]
  [LocallyCompactSpace.{0} G] [SecondCountableTopology.{0} G] [T2Space.{0} G] [inst_6 : MeasurableSpace.{0} G]
  [BorelSpace.{0} G] {μ : MeasureTheory.Measure.{0} G} [MeasureTheory.Measure.IsHaarMeasure.{0} μ] {φ : G → Complex},
  MeasureTheory.Integrable.{0, 0} φ μ →
    (∀ (w : G),
        Eq.{1}
          (MeasureTheory.integral.{0, 0} μ fun (y : G) ↦
            HMul.hMul.{0, 0, 0} (φ y) (φ (HMul.hMul.{0, 0, 0} (Inv.inv.{0} y) w)))
          (φ w)) →
      ∀ {F : G → Complex},
        Continuous.{0, 0} F →
          ∀ {M : Real},
            (∀ (y : G), LE.le.{0} (Norm.norm.{0} (F y)) M) →
              Eq.{1}
                (MeasureTheory.integral.{0, 0} μ fun (y : G) ↦
                  HMul.hMul.{0, 0, 0} (φ y)
                    (MeasureTheory.integral.{0, 0} μ fun (z : G) ↦
                      HMul.hMul.{0, 0, 0} (φ z) (F (HMul.hMul.{0, 0, 0} y z))))
                (MeasureTheory.integral.{0, 0} μ fun (w : G) ↦ HMul.hMul.{0, 0, 0} (φ w) (F w)) := by
  intro G _ _ _ _ _ _ _ _ μ _ φ hφ hid F hF M hM
  have hT : MeasureTheory.MeasurePreserving (MeasurableEquiv.shearMulRight G) (μ.prod μ) (μ.prod μ) :=
    MeasureTheory.measurePreserving_prod_mul μ μ
  have hcomp : ((fun p : G × G => φ p.1 * φ (p.1⁻¹ * p.2) * F p.2) ∘ (MeasurableEquiv.shearMulRight G))
      = fun p : G × G => φ p.1 * (φ p.2 * F (p.1 * p.2)) := by
    funext p
    simp [MeasurableEquiv.shearMulRight, mul_assoc]
  have hGi : MeasureTheory.Integrable (fun p : G × G => φ p.1 * (φ p.2 * F (p.1 * p.2))) (μ.prod μ) := by
    have h1 : MeasureTheory.Integrable (fun p : G × G => φ p.1 * φ p.2) (μ.prod μ) := hφ.mul_prod hφ
    have h2 := h1.mul_bdd (c := M) (g := fun p : G × G => F (p.1 * p.2))
      ((hF.comp continuous_mul).aestronglyMeasurable) (Filter.Eventually.of_forall fun p => hM _)
    refine h2.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [mul_assoc]
  have hHi : MeasureTheory.Integrable (fun p : G × G => φ p.1 * φ (p.1⁻¹ * p.2) * F p.2) (μ.prod μ) := by
    rw [← hT.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _), hcomp]
    exact hGi
  calc ∫ y, φ y * ∫ z, φ z * F (y * z) ∂μ ∂μ
      = ∫ p, (fun p : G × G => φ p.1 * (φ p.2 * F (p.1 * p.2))) p ∂(μ.prod μ) := by
        rw [MeasureTheory.integral_prod _ hGi]
        congr 1
        funext y
        dsimp only
        exact (MeasureTheory.integral_const_mul _ _).symm
    _ = ∫ p, ((fun p : G × G => φ p.1 * φ (p.1⁻¹ * p.2) * F p.2) ∘ (MeasurableEquiv.shearMulRight G)) p ∂(μ.prod μ) := by
        rw [hcomp]
    _ = ∫ p, (fun p : G × G => φ p.1 * φ (p.1⁻¹ * p.2) * F p.2) p ∂(μ.prod μ) :=
        hT.integral_comp' (fun p : G × G => φ p.1 * φ (p.1⁻¹ * p.2) * F p.2)
    _ = ∫ w, ∫ y, φ y * φ (y⁻¹ * w) * F w ∂μ ∂μ := MeasureTheory.integral_prod_symm _ hHi
    _ = ∫ w, φ w * F w ∂μ := by
        congr 1
        funext w
        rw [MeasureTheory.integral_mul_const, hid]
end Bl.FirstLemmaL
