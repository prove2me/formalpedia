-- Prove2me | solution 1 for AvramDividend.Classical.avram_b27_original_random_stopped_compact_mesh_energy_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:51:40.22979+00:00
-- url     : https://prove2.me/submissions/9cb9bb99-79ee-42e7-957d-3e3e1f19de13

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine random stopped original Lévy mesh energy is locally L1 on compact reserve bands. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (a b : ℝ) (hab : a ≤ b) :
    ∀ (A : Set Ω) (S : Finset ℕ)
      (s t : ℕ → Ω → ℝ≥0),
      let z : Ω → ℕ → ℝ := fun ω i =>
        Function.leftLim (fun u : ℝ≥0 =>
          x + X.X u ω - rightLimit D u ω) (s i ω)
      let g : Ω → ℕ → ℝ := fun ω i =>
        X.X (t i ω) ω - X.X (s i ω) ω -
          ((t i ω - s i ω) : ℝ) * X.c
      let Q : Ω → ℝ := fun ω => ∑ i ∈ S, (g ω i) ^ 2
      (∀ i ∈ S, IsStoppingTime 𝓕.rightCont
        (fun ω => (s i ω : WithTop ℝ≥0))) →
      (∀ i ∈ S, IsStoppingTime 𝓕.rightCont
        (fun ω => (t i ω : WithTop ℝ≥0))) →
      (∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S,
        z ω i ∈ Icc a b ∧ z ω i + g ω i ∈ Icc a b) →
      IntegrableOn Q A P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro A S s t
  dsimp only
  intro hs ht hBand
  have hJoint : Measurable
      (fun p : ℝ≥0 × Ω => X.X p.1 p.2) :=
    chat04_levy_joint_time_state_measurable X
  have hQ : Measurable (fun ω : Ω => ∑ i ∈ S,
      (X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω) : ℝ) * X.c) ^ 2) := by
    apply Finset.measurable_sum
    intro i hi
    have hsm : Measurable (s i) :=
      measurable_coe_nnreal_ennreal_iff.mp (hs i hi).measurable'
    have htm : Measurable (t i) :=
      measurable_coe_nnreal_ennreal_iff.mp (ht i hi).measurable'
    have hXs : Measurable (fun ω : Ω => X.X (s i ω) ω) :=
      hJoint.comp (hsm.prodMk measurable_id)
    have hXt : Measurable (fun ω : Ω => X.X (t i ω) ω) :=
      hJoint.comp (htm.prodMk measurable_id)
    have hdt : Measurable (fun ω : Ω =>
        ((t i ω - s i ω) : ℝ)) :=
      (htm.coe_nnreal_real).sub hsm.coe_nnreal_real
    exact ((hXt.sub hXs).sub (hdt.mul measurable_const)).pow_const 2
  have hFinite : P A < ⊤ := measure_lt_top P A
  apply IntegrableOn.of_bound hFinite hQ.aestronglyMeasurable
    ((S.card : ℝ) * (b - a) ^ 2)
  filter_upwards [hBand] with ω hω
  have hNonneg : 0 ≤ ∑ i ∈ S,
      (X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω) : ℝ) * X.c) ^ 2 := by
    apply Finset.sum_nonneg
    intro i hi
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
  calc
    (∑ i ∈ S, (X.X (t i ω) ω - X.X (s i ω) ω -
      ((t i ω - s i ω) : ℝ) * X.c) ^ 2) ≤
        ∑ i ∈ S, (b - a) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hz, hzg⟩ := hω i hi
      rcases Set.mem_Icc.mp hz with ⟨hza, hzb⟩
      rcases Set.mem_Icc.mp hzg with ⟨hga, hgb⟩
      have hMinus : 0 ≤ (b - a) -
          (X.X (t i ω) ω - X.X (s i ω) ω -
            ((t i ω - s i ω) : ℝ) * X.c) := by
        linarith
      have hPlus : 0 ≤ (b - a) +
          (X.X (t i ω) ω - X.X (s i ω) ω -
            ((t i ω - s i ω) : ℝ) * X.c) := by
        linarith
      nlinarith [mul_nonneg hMinus hPlus]
    _ = (S.card : ℝ) * (b - a) ^ 2 := by simp
