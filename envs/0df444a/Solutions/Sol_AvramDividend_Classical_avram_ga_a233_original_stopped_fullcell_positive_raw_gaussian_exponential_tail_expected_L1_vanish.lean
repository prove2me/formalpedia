-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a233_original_stopped_fullcell_positive_raw_gaussian_exponential_tail_expected_L1_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:35:57.8005+00:00
-- url     : https://prove2.me/submissions/7975977f-8ee5-4910-8843-a27b56f4680b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a213_finite_measurable_positive_mask_restriction_preserves_expected_L1_zero
import Theorems.Thm_AvramDividend_Classical_avram_ga_a229_original_gaussian_true_physical_mesh_raw_and_centered_positive_exp_sums_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a231_original_true_physical_raw_gaussian_positive_exponential_tail_expected_L1_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (θ δ : ℝ) (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i + Δ m) ω - X.X (s m i) ω
    let Tail : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω then
          (if δ ≤ R m i ω then Real.exp (θ * R m i ω) else 0)
        else 0
    (∀ m, Integrable (Tail m) P) ∧
      Tendsto (fun m => ∫ ω, Tail m ω ∂P)
        atTop (𝓝 (0 : ℝ)) := by
  classical
  intro Δ s R Tail
  let A : ℕ → ℕ → Ω → Prop := fun m i ω => True
  let B : ℕ → ℕ → Ω → Prop := fun m i ω =>
    s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω
  let f : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    if δ ≤ R m i ω then Real.exp (θ * R m i ω) else 0
  have hfPos (m i : ℕ) (ω : Ω) : 0 ≤ f m i ω := by
    dsimp [f]; split_ifs <;> positivity
  have hfMeas (m i : ℕ) : Measurable (f m i) := by
    have h0 : Measurable (X.X (s m i)) :=
      (X.adapted (s m i)).mono (𝓕.le _) le_rfl
    have h1 : Measurable (X.X (s m i + Δ m)) :=
      (X.adapted (s m i + Δ m)).mono (𝓕.le _) le_rfl
    have hR : Measurable (R m i) := h1.sub h0
    have hs : MeasurableSet {ω : Ω | δ ≤ R m i ω} :=
      (show MeasurableSet (Set.Ici δ : Set ℝ)
        from measurableSet_Ici).preimage hR
    exact Measurable.ite hs
      (Real.continuous_exp.measurable.comp (measurable_const.mul hR))
      measurable_const
  have hρm : Measurable ρ :=
    measurable_coe_nnreal_ennreal_iff.mp hρstop.measurable'
  have hBm (m i : ℕ) : MeasurableSet {ω : Ω | B m i ω} := by
    have h1 : MeasurableSet {ω : Ω | s m i < ρ ω} :=
      (show MeasurableSet (Set.Ioi (s m i) : Set ℝ≥0)
        from measurableSet_Ioi).preimage hρm
    have h2 : MeasurableSet {ω : Ω | s m i + Δ m ≤ ρ ω} :=
      (show MeasurableSet (Set.Ici (s m i + Δ m) : Set ℝ≥0)
        from measurableSet_Ici).preimage hρm
    exact h1.inter h2
  have hInt := (avram_ga_a229_original_gaussian_true_physical_mesh_raw_and_centered_positive_exp_sums_integrable
    X hν hσ n θ δ hθ).1
  have hLim := avram_ga_a231_original_true_physical_raw_gaussian_positive_exponential_tail_expected_L1_vanish
    X hν hσ n hn θ δ hθ hδ
  have hTrans := avram_ga_a213_finite_measurable_positive_mask_restriction_preserves_expected_L1_zero
    P (fun m => Finset.range m) A B f
    (fun m i ω h => trivial) hfPos hfMeas hBm
    (by simpa [A,f] using hInt) (by simpa [A,f] using hLim)
  simpa only [Tail,B,f] using hTrans
