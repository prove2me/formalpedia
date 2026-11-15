-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a373_original_fullcell_small_ae_Young_rawenergy_cross_discount_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:44:31.411696+00:00
-- url     : https://prove2.me/submissions/644a4d47-822b-4773-bb5c-fcf89331c2b1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a371_original_fullcell_joint_Taylor_Lipschitz_Hessian_selected_cutoff_ae
import Theorems.Thm_AvramDividend_Classical_avram_ga_a372_ae_smallcell_to_fullmask_energy_cross_Young_source
import Theorems.Thm_AvramDividend_Classical_avram_ga_a374_finite_masked_Young_half_epsilon_energy_cross_factor_identity
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false
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
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let Small : ℝ → ℕ → Ω → ℝ := fun δ m ω =>
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
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω ∧ |R i| < δ then F i else 0
    let Energy : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        if s < ρ ω ∧ s + Δ ≤ ρ ω then R^2 else 0
    let Cross : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        let Z : ℝ := R - (Δ : ℝ) * X.c
        if s < ρ ω ∧ s + Δ ≤ ρ ω then |R^2 - Z^2| else 0
    ∃ L M : ℝ, 0 ≤ L ∧ 0 ≤ M ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ m : ℕ, ∀ᵐ ω ∂P,
          max (Small δ m ω) 0 ≤
            ε * Energy m ω + (M / 2) * Cross m ω +
              (m : ℝ) *
                (q * (((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) * L)^2 /
                  (2 * ε) := by
  classical
  intro Small Energy Cross
  obtain ⟨L,M,hL,hM,hJoint⟩ :=
    avram_ga_a371_original_fullcell_joint_Taylor_Lipschitz_Hessian_selected_cutoff_ae
      X x hx D hD.1.1 C hTopCap w hw_smooth q hq.le n ρ j hprefix
  refine ⟨L,M,hL,hM,?_⟩
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨δ,hδ,hJointAE⟩ := hJoint (ε / 2) hε2
  refine ⟨δ,hδ,?_⟩
  intro m
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let R : ℕ → Ω → ℝ := fun i ω => X.X (s i + Δ) ω - X.X (s i) ω
  let Z : ℕ → Ω → ℝ := fun i ω => R i ω - (Δ : ℝ) * X.c
  let Y : ℕ → Ω → ℝ := fun i ω => x + X.X (s i) ω - rightLimit D (s i) ω
  let A : ℕ → Ω → Prop := fun i ω => s i < ρ ω ∧ s i + Δ ≤ ρ ω
  have hBound :=
    avram_ga_a372_ae_smallcell_to_fullmask_energy_cross_Young_source
      (P := P) (Finset.range m) A
      (fun i ω => (s i : ℝ))
      (fun i ω => w (Y i ω))
      (fun i ω => w (Y i ω + R i ω))
      (fun i ω => deriv w (Y i ω))
      (fun i ω => iteratedDeriv 2 w (Y i ω))
      R Z q (Δ : ℝ) δ (ε/2) (ε/2) L M
      hq.le (NNReal.coe_nonneg _) hδ hε2.le hε2 hL hM
      (fun i ω _ => NNReal.coe_nonneg _)
      (by filter_upwards [hJointAE] with ω hω
          intro i hi hr; exact (hω m i hi.1 hi.2 hr).1)
      (by filter_upwards [hJointAE] with ω hω
          intro i hi hr; exact (hω m i hi.1 hi.2 hr).2.1)
      (by filter_upwards [hJointAE] with ω hω
          intro i hi hr; exact (hω m i hi.1 hi.2 hr).2.2)
  filter_upwards [hBound] with ω hb
  have hFact :=
    avram_ga_a374_finite_masked_Young_half_epsilon_energy_cross_factor_identity
      (Finset.range m) (fun i => A i ω)
      (fun i => R i ω) (fun i => Z i ω) ε M q (Δ : ℝ) L hε
  have hBudget := hb.trans_eq hFact
  convert hBudget using 1 <;>
    (simp only [Small,Energy,Cross,A,Y,R,Z,s,Δ,
       Finset.card_range,and_assoc,NNReal.coe_add,mul_div_assoc]; try ring)
