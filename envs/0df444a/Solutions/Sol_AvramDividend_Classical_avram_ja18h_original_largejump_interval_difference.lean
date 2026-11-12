-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18h_original_largejump_interval_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:47:01.826652+00:00
-- url     : https://prove2.me/submissions/f84ab6d4-8102-4071-9b5a-ccb207dbf2d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largeband_mark_integrable_from_finite_support
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Exact signed (s,t] source window from finite càdlàg large-jump integrals. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) (ω : Ω) :
    avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω -
      avram_p4_h_gaussian_intrinsic_large_jump_sum X s ω =
      ∫ p in (Ioc s t ×ˢ Iic (-1 : ℝ)), p.2 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) := by
  classical
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let B : Set ℝ := Iic (-1 : ℝ)
  let A : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) s ×ˢ B
  let C : Set (ℝ≥0 × ℝ) := Ioc s t ×ˢ B
  let E : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) t ×ˢ B
  have hA : IntegrableOn (fun p : ℝ≥0 × ℝ => p.2) A μ := by
    exact avram_p4_h_gaussian_original_largeband_mark_integrable_from_finite_support X ω s
  have hE : IntegrableOn (fun p : ℝ≥0 × ℝ => p.2) E μ := by
    exact avram_p4_h_gaussian_original_largeband_mark_integrable_from_finite_support X ω t
  have hCE : C ⊆ E := by
    intro p hp
    exact ⟨⟨lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hp.1.1, hp.1.2⟩, hp.2⟩
  have hC : IntegrableOn (fun p : ℝ≥0 × ℝ => p.2) C μ :=
    hE.mono_set hCE
  have hDis : Disjoint A C := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_ge hp.1.2) hq.1.1
  have hUnion : A ∪ C = E := by
    change (Ioc 0 s ×ˢ B) ∪ (Ioc s t ×ˢ B) = Ioc 0 t ×ˢ B
    calc
      (Ioc 0 s ×ˢ B) ∪ (Ioc s t ×ˢ B) =
          (Ioc 0 s ∪ Ioc s t) ×ˢ B := Set.union_prod.symm
      _ = Ioc 0 t ×ˢ B := by
        rw [Set.Ioc_union_Ioc_eq_Ioc (show (0 : ℝ≥0) ≤ s from zero_le) hst]
  have hAdd : (∫ p in E, p.2 ∂μ) =
      (∫ p in A, p.2 ∂μ) + (∫ p in C, p.2 ∂μ) := by
    rw [← hUnion]
    exact setIntegral_union hDis (measurableSet_Ioc.prod measurableSet_Iic) hA hC
  change (∫ p in E, p.2 ∂μ) - (∫ p in A, p.2 ∂μ) =
    ∫ p in C, p.2 ∂μ
  rw [hAdd]
  ring
