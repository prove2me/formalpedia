-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261123_A77_original_single_simple_fibre_from_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T16:55:39.108052+00:00
-- url     : https://prove2.me/submissions/a34af9e9-890c-4e18-af3e-c4ac239ca742

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_finite_simple_exp_fibre_rate
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_physical_single_mark_count_exact
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) (J
    : Ω → ℝ) (hJMeas : Measurable J) (hJEq : J =ᵐ[P] fun ω => ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u else 0) (hSupport : ∀ᵐ ω ∂P, ∃ S : Finset
    ℝ≥0, (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ t ∧ X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0) ∧ J ω = ∑ u ∈ S, (X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u)) (hCountLaw : ∀ (B : Set
    ℝ), MeasurableSet B → B ⊆ Iio (0 : ℝ) → (let N : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0
    => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B)
       ∃ (K : Ω → ℕ) (r : ℝ≥0), Measurable K ∧ HasLaw K (poissonMeasure r) P ∧ (∀ᵐ ω ∂P, (K ω : ℝ) = (N ω).toReal) ∧ (r
    : ℝ) = ((t : ℝ≥0∞) * X.ν B).toReal)) (g : SimpleFunc ℝ ℝ) (hg : ∀ y, g y ≤ 0) (hPartition : ∃ (K : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ), (∀ i ∈ Finset.range K, MeasurableSet (B i) ∧ B i ⊆ Iio (0 :
    ℝ)) ∧ (∀ i ∈ Finset.range K, ∀ j ∈ Finset.range K, i ≠ j → Disjoint (B i) (B j)) ∧ (∀ w : ℝ → ℝ, (∑ i ∈ Finset.range K, w (c i)) = ∑ y ∈ g.range, w y) ∧ (∀ i ∈ Finset.range K, B i = Iio (0 :
    ℝ) ∩ g ⁻¹' {c i})) : ∃ (f : Ω → ℝ) (r : ℝ), Measurable f ∧ (∀ᵐ ω ∂P, f ω ≤ 0) ∧ (∀ᵐ ω ∂P, ∀ (S : Finset ℝ≥0), (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ t ∧ X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω)
    u ≠ 0) → f ω = ∑ u ∈ S, g (X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u)) ∧ (r = (t : ℝ) * (∫ y in Iio (0 : ℝ), Real.exp (g y) - 1 ∂X.ν)) ∧ ∃ (k : ℕ) (B : Fin k → Set ℝ) (a : Fin k →
    ℝ), (∀ i, MeasurableSet (B i)) ∧ (∀ i, B i ⊆ Iio (0 : ℝ)) ∧ (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧ (∀ᵐ ω ∂P, f ω = ∑ i : Fin k, a i * (((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
    Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B i)).toReal) ∧ r = ∑ i : Fin k, (((t : ℝ≥0∞) *
    X.ν (B i)).toReal) * (Real.exp (a i) - 1) := by
  classical
  obtain ⟨K, B, c, hB, hDisj, hTransfer, hFibre⟩ := hPartition
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let f : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range K, c i * (NX ω (Ioc 0 t ×ˢ B i)).toReal
  let r : ℝ := (t : ℝ) *
    (∫ y in Iio (0 : ℝ), Real.exp (g y) - 1 ∂X.ν)
  have hPhysical :=
    AvramDividend.Classical.avram_bridge20261123_A77_original_physical_single_mark_count_exact
      X t J hSupport g hg K B c hB hDisj hTransfer hFibre
  refine ⟨f, r, hPhysical.1, hPhysical.2.1, hPhysical.2.2,
    rfl, K, (fun i : Fin K => B i.val),
    (fun i : Fin K => c i.val), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hB i.val (Finset.mem_range.mpr i.isLt)).1
  · intro i
    exact (hB i.val (Finset.mem_range.mpr i.isLt)).2
  · intro i j hij
    exact hDisj i.val (Finset.mem_range.mpr i.isLt)
      j.val (Finset.mem_range.mpr j.isLt)
      (fun h => hij (Fin.ext h))
  · filter_upwards [] with ω
    change (∑ i ∈ Finset.range K,
      c i * (NX ω (Ioc 0 t ×ˢ B i)).toReal) =
        ∑ i : Fin K, c i.val *
          (NX ω (Ioc 0 t ×ˢ B i.val)).toReal
    exact (Fin.sum_univ_eq_sum_range
      (fun i => c i * (NX ω (Ioc 0 t ×ˢ B i)).toReal) K).symm
  · change (t : ℝ) *
      (∫ y in Iio (0 : ℝ), Real.exp (g y) - 1 ∂X.ν) =
      ∑ i : Fin K,
        (((t : ℝ≥0∞) * X.ν (B i.val)).toReal) *
          (Real.exp (c i.val) - 1)
    calc
      (t : ℝ) *
          (∫ y in Iio (0 : ℝ), Real.exp (g y) - 1 ∂X.ν) =
          (t : ℝ) * ∑ z ∈ g.range,
            (X.ν (Iio (0 : ℝ) ∩ g ⁻¹' {z})).toReal *
              (Real.exp z - 1) := by
        rw [AvramDividend.Classical.avram_bridge20261123_A77_finite_simple_exp_fibre_rate
          X.ν hFinite g]
      _ = ∑ i ∈ Finset.range K, (t : ℝ) *
            (X.ν (B i)).toReal * (Real.exp (c i) - 1) := by
        rw [Finset.mul_sum]
        calc
          ∑ z ∈ g.range,
              (t : ℝ) * ((X.ν (Iio (0 : ℝ) ∩ g ⁻¹' {z})).toReal *
                (Real.exp z - 1)) =
              ∑ i ∈ Finset.range K,
                (t : ℝ) * ((X.ν (Iio (0 : ℝ) ∩ g ⁻¹' {c i})).toReal *
                  (Real.exp (c i) - 1)) :=
            (hTransfer _).symm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hFibre i hi]
            ring
      _ = ∑ i ∈ Finset.range K,
            (((t : ℝ≥0∞) * X.ν (B i)).toReal) *
              (Real.exp (c i) - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [ENNReal.toReal_mul, ENNReal.coe_toReal]
      _ = ∑ i : Fin K,
            (((t : ℝ≥0∞) * X.ν (B i.val)).toReal) *
              (Real.exp (c i.val) - 1) :=
        (Fin.sum_univ_eq_sum_range _ K).symm
