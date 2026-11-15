-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a216_original_combined_fullcell_one_sided_positive_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:17:32.320001+00:00
-- url     : https://prove2.me/submissions/0158be93-f607-4c1f-a840-91769fc4cfa9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a263_original_combined_fullcell_large_raw_increment_positive_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a264_original_combined_fullcell_small_raw_increment_positive_budget
import Theorems.Thm_AvramDividend_Classical_avram_ga_a265_small_budget_large_L1_positive_source_gluing
import Theorems.Thm_AvramDividend_Classical_avram_ga_a266_full_physical_source_positive_small_large_raw_partition
import Theorems.Thm_AvramDividend_Classical_avram_ga_a267_original_combined_fullcell_positive_aestrongly_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let Full : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i =>
      E (s i) * (deriv w (Y (s i)) * R i +
        (iteratedDeriv 2 w (Y (s i)) / 2) * Z i^2)
    let F : ℕ → ℝ := fun i =>
      E (s i + Δ) * (w (Y (s i) + R i) - w (Y (s i))) - H i
    ∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω then F i else 0
    (∀ m, Integrable (fun ω => max (Full m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Full m ω) 0 ∂P) atTop (nhds (0 : ℝ)) := by
  classical
  intro Full
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0)+1)
  let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0)*Δ m
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q*(t : ℝ)))
  let Y := fun (m i : ℕ) (ω : Ω) => x+X.X (s m i) ω-rightLimit D (s m i) ω
  let R := fun (m i : ℕ) (ω : Ω) => X.X (s m i+Δ m) ω-X.X (s m i) ω
  let Z := fun (m i : ℕ) (ω : Ω) => R m i ω-(Δ m : ℝ)*X.c
  let H : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    E (s m i)*(deriv w (Y m i ω)*R m i ω+
      iteratedDeriv 2 w (Y m i ω)/2*(Z m i ω)^2)
  let F := fun (m i : ℕ) (ω : Ω) =>
    E (s m i+Δ m)*(w (Y m i ω+R m i ω)-w (Y m i ω))-H m i ω
  let Small := fun (δ : ℝ) (m : ℕ) (ω : Ω) =>
    ∑ i ∈ Finset.range m, if s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω ∧ |R m i ω| < δ
      then F m i ω else 0
  let Large := fun (δ : ℝ) (m : ℕ) (ω : Ω) =>
    ∑ i ∈ Finset.range m, if s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω ∧ δ ≤ |R m i ω|
      then F m i ω else 0
  have hSmall := avram_ga_a264_original_combined_fullcell_small_raw_increment_positive_budget
    X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen
    x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix
  have hSmallI : ∀ δ, 0 < δ → ∀ m, Integrable (fun ω => max (Small δ m ω) 0) P := by
    simpa only [Small,F,H,Z,R,Y,E,s,Δ] using hSmall.1
  have hSmallBudget : ∀ η, 0 < η → ∃ δ, 0 < δ ∧ ∃ k : ℕ, ∀ m, k ≤ m →
        (∫ ω, max (Small δ m ω) 0 ∂P) ≤ η := by
    simpa only [Small,F,H,Z,R,Y,E,s,Δ] using hSmall.2
  have hLarge (δ : ℝ) (hδ : 0 < δ) :=
    avram_ga_a263_original_combined_fullcell_large_raw_increment_positive_L1
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen
      x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix δ hδ
  have hLargeI : ∀ δ, 0 < δ → ∀ m, Integrable (fun ω => max (Large δ m ω) 0) P := by
    intro δ hδ
    simpa only [Large,F,H,Z,R,Y,E,s,Δ] using (hLarge δ hδ).1
  have hLargeLim : ∀ δ, 0 < δ →
      Tendsto (fun m => ∫ ω, max (Large δ m ω) 0 ∂P) atTop (𝓝 (0:ℝ)) := by
    intro δ hδ
    simpa only [Large,F,H,Z,R,Y,E,s,Δ] using (hLarge δ hδ).2
  have hMeas (m : ℕ) : AEStronglyMeasurable (fun ω => max (Full m ω) 0) P :=
    avram_ga_a267_original_combined_fullcell_positive_aestrongly_measurable
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen
      x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix m
  have hPoint (δ : ℝ) (_ : 0 < δ) (m : ℕ) (ω : Ω) :
      max (Full m ω) 0 ≤ max (Small δ m ω) 0+max (Large δ m ω) 0 := by
    let A := fun (i : ℕ) (ω : Ω) => s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω
    have h := avram_ga_a266_full_physical_source_positive_small_large_raw_partition
      (Finset.range m) A (R m) (F m) δ ω
    simpa only [Full,Small,Large,F,H,Z,R,Y,E,s,Δ,A,and_assoc] using h
  have hFI (m : ℕ) : Integrable (fun ω => max (Full m ω) 0) P := by
    have hi := (hSmallI 1 (by norm_num) m).add (hLargeI 1 (by norm_num) m)
    apply Integrable.mono' hi (hMeas m)
    filter_upwards [] with ω
    simpa only [Pi.add_apply, Real.norm_eq_abs,
      abs_of_nonneg (le_max_right (Full m ω) 0),
      abs_of_nonneg (add_nonneg (le_max_right (Small 1 m ω) 0)
        (le_max_right (Large 1 m ω) 0))] using hPoint 1 (by norm_num) m ω
  refine ⟨hFI,?_⟩
  exact avram_ga_a265_small_budget_large_L1_positive_source_gluing
    P Full Small Large hFI hSmallI hLargeI
    hPoint hLargeLim hSmallBudget
