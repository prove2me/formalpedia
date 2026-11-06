-- Prove2me | solution 1 for FriendlyShadow.Gaussian.lemma_29
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T12:24:14.141611+00:00
-- url     : https://prove2.me/submissions/f79474b0-18e9-4879-8eea-584cf4c4dd35

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Model

set_option autoImplicit false

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace FSL29
open FriendlyShadow.Gaussian

variable {d n : ℕ}

theorem dens_prob {μ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsDensity μ) :
    IsProbabilityMeasure (densityMeasure μ) := by
  constructor
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal h.2.1 (ae_of_all _ h.1), h.2.2, ENNReal.ofReal_one]

/-- One row far from its center: probability at most `cutoffLevel`. -/
theorem bad_row_le (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (hμ : ∀ i, IsDensity (μ i))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (p R : ℝ)
    (hR : ∀ i, CutoffRadiusLE (μ i) (abar i) p R) (i : Fin n) :
    rowLaw μ {a | R ≤ ‖a i - abar i‖} ≤ ENNReal.ofReal p := by
  haveI : ∀ i, IsProbabilityMeasure (densityMeasure (μ i)) := fun i => dens_prob (hμ i)
  have hS : MeasurableSet {x : EuclideanSpace ℝ (Fin d) | R ≤ ‖x - abar i‖} :=
    measurableSet_le measurable_const ((measurable_id.sub_const _).norm)
  have h1 : {a : Fin n → EuclideanSpace ℝ (Fin d) | R ≤ ‖a i - abar i‖} =
      Function.eval i ⁻¹' {x | R ≤ ‖x - abar i‖} := rfl
  rw [h1, rowLaw, (measurePreserving_eval (fun i => densityMeasure (μ i)) i).measure_preimage
    hS.nullMeasurableSet]
  exact hR i

/-- The union over `I` of the far events has probability at most `1/C(n,d)`. -/
theorem bad_le (hd : 3 ≤ d) (hdn : d ≤ n) (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hμ : ∀ i, IsDensity (μ i)) (abar : Fin n → EuclideanSpace ℝ (Fin d)) (R : ℝ)
    (hR : ∀ i, CutoffRadiusLE (μ i) (abar i) (cutoffLevel n d) R)
    (I : Finset (Fin n)) (hI : I.card = d) :
    rowLaw μ (⋃ i ∈ I, {a | R ≤ ‖a i - abar i‖}) ≤ ENNReal.ofReal (1 / (n.choose d : ℝ)) := by
  calc rowLaw μ (⋃ i ∈ I, {a | R ≤ ‖a i - abar i‖})
      ≤ ∑ i ∈ I, rowLaw μ {a | R ≤ ‖a i - abar i‖} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ I, ENNReal.ofReal (cutoffLevel n d) :=
        Finset.sum_le_sum fun i _ => bad_row_le μ hμ abar _ R hR i
    _ = ENNReal.ofReal (1 / (n.choose d : ℝ)) := by
        rw [Finset.sum_const, hI, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
        congr 1
        have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
        have hc0 : (0 : ℝ) < (n.choose d : ℝ) := by exact_mod_cast Nat.choose_pos hdn
        unfold cutoffLevel
        field_simp

/-- Off the far events the bounded-diameter event holds. -/
theorem bdd_of_near (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (habar : ∀ i, ‖abar i‖ ≤ 1) (R : ℝ)
    (I : Finset (Fin n)) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (ha : ∀ i ∈ I, ‖a i - abar i‖ < R) : boundedDiamEvent W a I R := by
  intro i hi j hj
  refine (Submodule.norm_starProjection_apply_le _ _).trans ?_
  have e : a i - a j = (a i - abar i) - (a j - abar j) + (abar i - abar j) := by abel
  rw [e]
  have h1 := norm_add_le ((a i - abar i) - (a j - abar j)) (abar i - abar j)
  have h2 := norm_sub_le (a i - abar i) (a j - abar j)
  have h3 := norm_sub_le (abar i) (abar j)
  have := ha i hi; have := ha j hj; have := habar i; have := habar j
  linarith

/-- `Pr[E_I] ≤ 2 Pr[E_I ∩ D]` for `I ∈ B`. -/
theorem prob_le_two (hd : 3 ≤ d) (hdn : d ≤ n)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (hμ : ∀ i, IsDensity (μ i))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (habar : ∀ i, ‖abar i‖ ≤ 1) (R : ℝ)
    (hR : ∀ i, CutoffRadiusLE (μ i) (abar i) (cutoffLevel n d) R)
    (I : Finset (Fin n)) (hI : I.card = d)
    (hB : ENNReal.ofReal (2 / (n.choose d : ℝ)) ≤ rowLaw μ {a | edgeEvent W a I}) :
    rowLaw μ {a | edgeEvent W a I} ≤
      rowLaw μ {a | edgeEvent W a I ∧ boundedDiamEvent W a I R} * 2 := by
  haveI : ∀ i, IsProbabilityMeasure (densityMeasure (μ i)) := fun i => dens_prob (hμ i)
  haveI : IsProbabilityMeasure (rowLaw μ) := by unfold rowLaw; infer_instance
  set p := rowLaw μ {a | edgeEvent W a I}
  set q := rowLaw μ {a | edgeEvent W a I ∧ boundedDiamEvent W a I R}
  have hsub : {a | edgeEvent W a I} ⊆ {a | edgeEvent W a I ∧ boundedDiamEvent W a I R} ∪
      ⋃ i ∈ I, {a | R ≤ ‖a i - abar i‖} := by
    intro a ha
    by_cases h : ∀ i ∈ I, ‖a i - abar i‖ < R
    · exact Or.inl ⟨ha, bdd_of_near W abar habar R I a h⟩
    · push_neg at h
      obtain ⟨i, hi, hle⟩ := h
      exact Or.inr (Set.mem_biUnion hi hle)
  have hpq : p ≤ q + ENNReal.ofReal (1 / (n.choose d : ℝ)) :=
    (measure_mono hsub).trans ((measure_union_le _ _).trans
      (add_le_add le_rfl (bad_le hd hdn μ hμ abar R hR I hI)))
  have hhalf : ENNReal.ofReal (1 / (n.choose d : ℝ)) ≤ p / 2 := by
    have e : ENNReal.ofReal (1 / (n.choose d : ℝ)) = ENNReal.ofReal (2 / (n.choose d : ℝ)) / 2 := by
      rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    rw [e]; exact ENNReal.div_le_div_right hB 2
  have hp_top : p / 2 ≠ ∞ := ENNReal.div_ne_top (measure_ne_top _ _) two_ne_zero
  have h2 : p / 2 + p / 2 ≤ q + p / 2 := by
    rw [ENNReal.add_halves]; exact hpq.trans (add_le_add le_rfl hhalf)
  have h3 : p / 2 ≤ q := ENNReal.le_of_add_le_add_right hp_top h2
  exact (ENNReal.div_le_iff_le_mul (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)).1 h3

end FSL29

open MeasureTheory FriendlyShadow.Gaussian RealInnerProductSpace ENNReal in
theorem solution {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2)
    (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (hμ : ∀ i, IsDensity (μ i))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (hmean : ∀ i, HasMean (μ i) (abar i))
    (habar : ∀ i, ‖abar i‖ ≤ 1) (R : ℝ)
    (hR : ∀ i, CutoffRadiusLE (μ i) (abar i) (cutoffLevel n d) R)
    (I : Finset (Fin n)) (hI : I.card = d)
    (hB : ENNReal.ofReal (2 / (n.choose d : ℝ)) ≤ rowLaw μ {a | edgeEvent W a I}) :
    (∫⁻ a in {a | edgeEvent W a I ∧ boundedDiamEvent W a I R}, edgeLen W a I ∂(rowLaw μ)) *
        rowLaw μ {a | edgeEvent W a I} ≤
      2 * (∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂(rowLaw μ)) *
        rowLaw μ {a | edgeEvent W a I ∧ boundedDiamEvent W a I R} := by
  have hp := FSL29.prob_le_two hd hdn W μ hμ abar habar R hR I hI hB
  have hint : (∫⁻ a in {a | edgeEvent W a I ∧ boundedDiamEvent W a I R}, edgeLen W a I ∂(rowLaw μ)) ≤
      ∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂(rowLaw μ) :=
    lintegral_mono_set (fun a ha => ha.1)
  calc _ ≤ (∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂(rowLaw μ)) *
        (rowLaw μ {a | edgeEvent W a I ∧ boundedDiamEvent W a I R} * 2) := mul_le_mul' hint hp
    _ = _ := by ring
