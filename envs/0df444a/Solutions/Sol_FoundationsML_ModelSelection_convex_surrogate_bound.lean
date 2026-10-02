-- Prove2me | solution 1 for FoundationsML.ModelSelection.convex_surrogate_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T18:32:15.635185+00:00
-- url     : https://prove2.me/submissions/21cb4c7f-6477-423f-aa62-fae1dd2fd432

import Mathlib
import Definitions.Def_FoundationsML_ModelSelection_BayesScore
import Definitions.Def_FoundationsML_ModelSelection_PhiLossPointwise
import Definitions.Def_FoundationsML_ModelSelection_ExpectedPhiLoss
import Definitions.Def_FoundationsML_ModelSelection_ScoringRisk

/-! Disproof of 40f4a36e `FoundationsML.ModelSelection.convex_surrogate_bound`.

The statement puts no measurability condition on `η`, `h` or `hΦstar`, and the Bochner integral
of a non-a.e.-measurable function is `0`. Take a two-point type with the trivial σ-algebra
`{∅, univ}` and `μ = ½(δ_hi + δ_lo)`, `η hi = 1`, `η lo = 0`, `Φ t = max (t + 1) 0`,
`hΦstar hi = 1`, `hΦstar lo = -1`, `s = c = 1`, `h hi = -1`, `h lo = 2`.
The risk integrand of `h` is the constant `1` and that of the Bayes score is the constant `0`,
so the left side is `1`. The Φ-loss integrand of `hΦstar` is the constant `0`, while the Φ-loss
integrand of `h` takes the values `2` and `3`, is not a.e.-measurable, and integrates to `0`.
So the right side is `2 * 1 * (0 - 0) ^ 1 = 0 < 1`. -/

set_option autoImplicit false

open MeasureTheory

/-- A two-point type, given the trivial σ-algebra `{∅, univ}` below. -/
inductive CsbTwo : Type
  | hi : CsbTwo
  | lo : CsbTwo

instance CsbTwo.instMeasurableSpace : MeasurableSpace CsbTwo := ⊥

/-- The two-point measure `½(δ_hi + δ_lo)`. -/
noncomputable def csb_mu : Measure CsbTwo :=
  (2⁻¹ : ENNReal) • (Measure.dirac CsbTwo.hi + Measure.dirac CsbTwo.lo)

theorem csb_mu_univ : csb_mu Set.univ = 1 := by
  rw [csb_mu, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, smul_eq_mul,
    one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

instance csb_mu_prob : IsProbabilityMeasure csb_mu := ⟨csb_mu_univ⟩

theorem csb_mu_pos (b : CsbTwo) (S : Set CsbTwo) (hb : b ∈ S) : csb_mu S ≠ 0 := by
  have key : (2⁻¹ : ENNReal) * Measure.dirac b S ≤ csb_mu S := by
    rw [csb_mu, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
    apply mul_le_mul_right
    cases b
    · exact le_self_add
    · exact le_add_self
  rw [Measure.dirac_apply_of_mem hb, mul_one] at key
  intro h
  rw [h] at key
  exact (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top) (le_antisymm key (zero_le))

/-- Any real function on `CsbTwo` with different values at the two points is not a.e.-measurable. -/
theorem csb_not_aemeasurable (f : CsbTwo → ℝ) (hf : f CsbTwo.hi ≠ f CsbTwo.lo) :
    ¬ AEMeasurable f csb_mu := by
  rintro ⟨g, hg, hfg⟩
  have hall : ∀ b : CsbTwo, f b = g b := by
    intro b
    by_contra hne
    exact csb_mu_pos b {ω | f ω ≠ g ω} hne (ae_iff.mp hfg)
  have hmeas : MeasurableSet (g ⁻¹' {g CsbTwo.hi}) := hg (measurableSet_singleton _)
  rcases MeasurableSpace.measurableSet_bot_iff.mp hmeas with h | h
  · have hmem : CsbTwo.hi ∈ g ⁻¹' {g CsbTwo.hi} := rfl
    rw [h] at hmem
    exact hmem
  · have hmem : CsbTwo.lo ∈ g ⁻¹' {g CsbTwo.hi} := by rw [h]; trivial
    have hft : g CsbTwo.lo = g CsbTwo.hi := hmem
    rw [← hall, ← hall] at hft
    exact hf hft.symm

theorem csb_integral_zero (f : CsbTwo → ℝ) (hf : f CsbTwo.hi ≠ f CsbTwo.lo) :
    ∫ x, f x ∂csb_mu = 0 :=
  integral_non_aestronglyMeasurable (fun h => csb_not_aemeasurable f hf h.aemeasurable)

def csb_eta : CsbTwo → ℝ
  | CsbTwo.hi => 1
  | CsbTwo.lo => 0

def csb_star : CsbTwo → ℝ
  | CsbTwo.hi => 1
  | CsbTwo.lo => -1

def csb_h : CsbTwo → ℝ
  | CsbTwo.hi => -1
  | CsbTwo.lo => 2

noncomputable def csb_Phi : ℝ → ℝ := fun t => max (t + 1) 0

theorem csb_Phi_conv : ConvexOn ℝ Set.univ csb_Phi := by
  have h1 : ConvexOn ℝ Set.univ (fun t : ℝ => t + 1) := (convexOn_id convex_univ).add_const 1
  have h2 : ConvexOn ℝ Set.univ (fun _ : ℝ => (0 : ℝ)) := convexOn_const 0 convex_univ
  exact h1.sup h2

theorem csb_Phi_mono : Monotone csb_Phi := by
  intro a b hab
  exact max_le_max (by linarith) le_rfl

open FoundationsML.ModelSelection in
theorem csb_star_min : ∀ x u, PhiLossPointwise csb_eta csb_Phi x (csb_star x) ≤
    PhiLossPointwise csb_eta csb_Phi x u := by
  intro x u
  cases x <;> simp [PhiLossPointwise, csb_eta, csb_star, csb_Phi]

open FoundationsML.ModelSelection in
theorem csb_bound : ∀ x, |BayesScore csb_eta x| ^ (1 : ℝ) ≤
    (1 : ℝ) ^ (1 : ℝ) * (PhiLossPointwise csb_eta csb_Phi x 0 -
      PhiLossPointwise csb_eta csb_Phi x (csb_star x)) := by
  intro x
  cases x <;> norm_num [BayesScore, PhiLossPointwise, csb_eta, csb_star, csb_Phi, abs_of_pos]

open FoundationsML.ModelSelection in
theorem csb_risk_h : ScoringRisk csb_mu csb_eta csb_h = 1 := by
  have : (fun x => csb_eta x * (if csb_h x < 0 then (1 : ℝ) else 0) +
      (1 - csb_eta x) * (if csb_h x ≥ 0 then (1 : ℝ) else 0)) = fun _ => (1 : ℝ) := by
    funext x
    cases x <;> norm_num [csb_eta, csb_h]
  rw [ScoringRisk, this]
  simp

open FoundationsML.ModelSelection in
theorem csb_risk_bayes : ScoringRisk csb_mu csb_eta (BayesScore csb_eta) = 0 := by
  have : (fun x => csb_eta x * (if BayesScore csb_eta x < 0 then (1 : ℝ) else 0) +
      (1 - csb_eta x) * (if BayesScore csb_eta x ≥ 0 then (1 : ℝ) else 0)) = fun _ => (0 : ℝ) := by
    funext x
    cases x <;> norm_num [csb_eta, BayesScore]
  rw [ScoringRisk, this]
  simp

open FoundationsML.ModelSelection in
theorem csb_loss_h : ExpectedPhiLoss csb_mu csb_eta csb_Phi csb_h = 0 := by
  rw [ExpectedPhiLoss]
  apply csb_integral_zero (fun x => PhiLossPointwise csb_eta csb_Phi x (csb_h x))
  norm_num [PhiLossPointwise, csb_eta, csb_h, csb_Phi]

open FoundationsML.ModelSelection in
theorem csb_loss_star : ExpectedPhiLoss csb_mu csb_eta csb_Phi csb_star = 0 := by
  have : (fun x => PhiLossPointwise csb_eta csb_Phi x (csb_star x)) = fun _ => (0 : ℝ) := by
    funext x
    cases x <;> simp [PhiLossPointwise, csb_eta, csb_star, csb_Phi]
  rw [ExpectedPhiLoss, this]
  simp

open FoundationsML.ModelSelection MeasureTheory in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X] (DX : Measure X)
    [IsProbabilityMeasure DX] (η : X → ℝ) (Φ : ℝ → ℝ)
    (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦmono : Monotone Φ)
    (hΦstar : X → ℝ)
    (hΦstar_min : ∀ x u, PhiLossPointwise η Φ x (hΦstar x) ≤ PhiLossPointwise η Φ x u)
    (s c : ℝ) (hs : 1 ≤ s) (hc : 0 < c)
    (hbound : ∀ x, |BayesScore η x| ^ s ≤
      c ^ s * (PhiLossPointwise η Φ x 0 - PhiLossPointwise η Φ x (hΦstar x)))
    (h : X → ℝ),
    ScoringRisk DX η h - ScoringRisk DX η (BayesScore η) ≤
      2 * c * (ExpectedPhiLoss DX η Φ h - ExpectedPhiLoss DX η Φ hΦstar) ^ (1 / s)) := by
  intro H
  have key := @H CsbTwo CsbTwo.instMeasurableSpace csb_mu csb_mu_prob csb_eta csb_Phi
    csb_Phi_conv csb_Phi_mono csb_star csb_star_min 1 1 le_rfl one_pos csb_bound csb_h
  rw [csb_risk_h, csb_risk_bayes, csb_loss_h, csb_loss_star] at key
  norm_num at key
