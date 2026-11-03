-- Prove2me | solution 2 for AvramDividend.Classical.avram_wave6_05_generic_bv_stieltjes_Ioc_fubini_exchange
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:51:31.518572+00:00
-- url     : https://prove2.me/submissions/5cb1d557-de39-42a2-91f4-e5eb46e13f96

import Mathlib
import Mathlib.MeasureTheory.VectorMeasure.Prod
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section
theorem solution (f g : ℝ≥0 → ℝ)
    (hf : BoundedVariationOn f Set.univ) (hg : BoundedVariationOn g Set.univ)
    (a b : ℝ≥0) (hab : a ≤ b) :
    (∫ᵛ t in Ioc a b, (Function.rightLim g t - Function.rightLim g a) ∂• hf.vectorMeasure) =
    (∫ᵛ t in Ioc a b, (Function.rightLim f b - Function.leftLim f t) ∂• hg.vectorMeasure) := by
  let μ : VectorMeasure ℝ≥0 ℝ := hf.vectorMeasure
  let ν : VectorMeasure ℝ≥0 ℝ := hg.vectorMeasure
  let B : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hfinite (η : VectorMeasure ℝ≥0 ℝ) : IsFiniteMeasure η.variation := by rw [← SignedMeasure.totalVariation_eq_variation]; infer_instance
  letI : IsFiniteMeasure μ.variation := hfinite μ
  letI : IsFiniteMeasure ν.variation := hfinite ν
  let T : Set (ℝ≥0 × ℝ≥0) := {p | p.1 ∈ Ioc a b ∧ p.2 ∈ Ioc a p.1}
  have hT : MeasurableSet T := by
    change MeasurableSet {p : ℝ≥0 × ℝ≥0 |
      (a < p.1 ∧ p.1 ≤ b) ∧ (a < p.2 ∧ p.2 ≤ p.1)}
    measurability
  have hTs : MeasurableSet (Prod.swap ⁻¹' T) := hT.preimage (by fun_prop)
  have hLeftFiber (x : ℝ≥0) :
      ν (Prod.mk x ⁻¹' T) = (Ioc a b).indicator (fun z => ν (Ioc a z)) x := by
    by_cases hx : x ∈ Ioc a b
    · have hs : Prod.mk x ⁻¹' T = Ioc a x := by ext y; change (x ∈ Ioc a b ∧ y ∈ Ioc a x) ↔ y ∈ Ioc a x; simp [hx]
      simp [hs, Set.indicator_of_mem hx]
    · have hs : Prod.mk x ⁻¹' T = ∅ := by ext y; change (x ∈ Ioc a b ∧ y ∈ Ioc a x) ↔ False; simp [hx]
      simp [hs, Set.indicator_of_notMem hx]
  have hRightFiber (y : ℝ≥0) :
      μ (Prod.mk y ⁻¹' (Prod.swap ⁻¹' T)) =
      (Ioc a b).indicator (fun z => μ (Icc z b)) y := by
    by_cases hy : y ∈ Ioc a b
    · have hs : Prod.mk y ⁻¹' (Prod.swap ⁻¹' T) = Icc y b := by
        ext x
        simp only [mem_preimage, mem_setOf_eq, mem_Ioc, mem_Icc] at *
        constructor
        · rintro ⟨⟨_, hxb⟩, ⟨_, hyx⟩⟩; exact ⟨hyx, hxb⟩
        · intro hx; exact ⟨⟨lt_of_lt_of_le hy.1 hx.1, hx.2⟩, ⟨hy.1, hx.1⟩⟩
      simp [hs, Set.indicator_of_mem hy]
    · have hs : Prod.mk y ⁻¹' (Prod.swap ⁻¹' T) = ∅ := by
        ext x
        constructor
        · intro hx
          exfalso; apply hy
          change x ∈ Ioc a b ∧ y ∈ Ioc a x at hx
          exact ⟨hx.2.1, le_trans hx.2.2 hx.1.2⟩
        · simp
      simp [hs, Set.indicator_of_notMem hy]
  have hProdL : μ.prod ν B T =
      ∫ᵛ t in Ioc a b, (Function.rightLim g t - Function.rightLim g a) ∂[B.flip; μ] := by
    rw [VectorMeasure.prod_apply_eq_integral hT]; simp_rw [hLeftFiber]
    rw [VectorMeasure.integral_indicator measurableSet_Ioc]
    apply VectorMeasure.setIntegral_congr_fun
    intro t ht; exact hg.vectorMeasure_Ioc (le_of_lt ht.1)
  have hProdR : ν.prod μ B.flip (Prod.swap ⁻¹' T) =
      ∫ᵛ t in Ioc a b, (Function.rightLim f b - Function.leftLim f t) ∂[B; ν] := by
    rw [VectorMeasure.prod_apply_eq_integral hTs]
    simp only [ContinuousLinearMap.flip_flip]; simp_rw [hRightFiber]
    rw [VectorMeasure.integral_indicator measurableSet_Ioc]
    apply VectorMeasure.setIntegral_congr_fun
    intro t ht; exact hf.vectorMeasure_Icc ht.2
  have hProdSwap : μ.prod ν B = (ν.prod μ B.flip).map Prod.swap := by
    apply VectorMeasure.prod_eq_of_forall_apply_prod
    intro s t hs ht
    rw [VectorMeasure.map_apply _ (by fun_prop) (hs.prod ht)]
    have hpre : Prod.swap ⁻¹' (s ×ˢ t) = t ×ˢ s := by ext p; simp
    rw [hpre]
    simp only [VectorMeasure.prod_apply, ContinuousLinearMap.flip_apply]
  have hProd : μ.prod ν B T = ν.prod μ B.flip (Prod.swap ⁻¹' T) := by rw [hProdSwap, VectorMeasure.map_apply _ (by fun_prop) hT]
  have hB : B.flip = B := by ext x y <;> simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply] <;> exact mul_comm y x
  calc
    (∫ᵛ t in Ioc a b, (Function.rightLim g t - Function.rightLim g a) ∂• hf.vectorMeasure)
        = (∫ᵛ t in Ioc a b, (Function.rightLim g t - Function.rightLim g a) ∂[B.flip; μ]) := by rw [hB]
    _ = μ.prod ν B T := hProdL.symm
    _ = ν.prod μ B.flip (Prod.swap ⁻¹' T) := hProd
    _ = (∫ᵛ t in Ioc a b, (Function.rightLim f b - Function.leftLim f t) ∂[B; ν]) := hProdR
    _ = (∫ᵛ t in Ioc a b, (Function.rightLim f b - Function.leftLim f t) ∂• hg.vectorMeasure) := rfl
