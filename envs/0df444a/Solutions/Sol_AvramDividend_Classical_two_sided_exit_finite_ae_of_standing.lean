-- Prove2me | solution 1 for AvramDividend.Classical.two_sided_exit_finite_ae_of_standing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T06:13:37.771949+00:00
-- url     : https://prove2.me/submissions/20ee9f0b-fc00-40e7-9113-12aa3f06fd9c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_bv_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_of_notBV
import Theorems.Thm_AvramDividend_Classical_chat04_all_finite_prefix_increment_cylinder_product

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    ∀ᵐ ω ∂P, min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ := by
  have := X.isProbability
  have hmeas : ∀ t, Measurable (X.X t) := fun t =>
    (X.adapted t).mono (𝓕.le t) le_rfl
  -- step 1: root
  obtain ⟨φ, hφ, hroot⟩ : ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = 1 := by
    by_cases hbv : X.BoundedVariation
    · exact bv_positive_esscher_root X hX 1 one_pos hbv
    · exact unbounded_esscher_root_of_notBV X 1 one_pos hbv
  -- step 2
  set n : ℕ := ⌈φ * a⌉₊ + 1 with hn
  set p : ℝ≥0∞ := P {ω | X.X (n : ℝ≥0) ω ∈ Icc (-a) a} with hp
  have hp1 : p < 1 := by
    by_contra hcon
    have hpe : P {ω | X.X (n : ℝ≥0) ω ∈ Icc (-a) a} = P univ := by
      rw [measure_univ]; exact le_antisymm prob_le_one (not_lt.mp hcon)
    have hae : ∀ᵐ ω ∂P, X.X (n : ℝ≥0) ω ∈ Icc (-a) a :=
      (ae_iff_measure_eq (measurableSet_Icc.preimage (hmeas _)).nullMeasurableSet).mpr hpe
    obtain ⟨hint, heq⟩ := X.laplace (n : ℝ≥0) φ hφ.le
    have hle : ∫ ω, Real.exp (φ * X.X (n : ℝ≥0) ω) ∂P ≤ ∫ _ω, Real.exp (φ * a) ∂P := by
      apply integral_mono_ae hint (integrable_const _)
      filter_upwards [hae] with ω hω
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω.2 hφ.le)
    rw [heq, integral_const] at hle
    simp only [probReal_univ, smul_eq_mul, one_mul] at hle
    have h2 := Real.exp_le_exp.mp hle
    have hψ : laplaceExponent X.c X.σ X.ν φ = 1 := hroot
    rw [hψ, mul_one] at h2
    have h3 : (φ * a) < (n : ℝ) := by
      rw [hn]; push_cast
      have := Nat.le_ceil (φ * a); linarith
    simp only [NNReal.coe_natCast] at h2
    linarith
  -- steps 3-5
  set t : ℕ → ℝ≥0 := fun i => ((i * n : ℕ) : ℝ≥0) with ht
  have htmono : Monotone t := by
    intro i j hij; simp only [ht]; exact_mod_cast Nat.mul_le_mul_right n hij
  have hdiff : ∀ i, t (i + 1) - t i = (n : ℝ≥0) := by
    intro i; simp only [ht]; push_cast; rw [add_mul, one_mul, add_tsub_cancel_left]
  have hstep : ∀ i, P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ Icc (-a) a} = p := by
    intro i
    have := (X.stationaryIncrements (t i) (t (i + 1)) (htmono (Nat.le_succ i))).measure_mem_eq
      (measurableSet_Icc (a := -a) (b := a))
    rw [hdiff] at this
    exact this
  have hbound : ∀ N : ℕ, P {ω | ¬ (min (twoSidedExitUpTime X (a - x) ω)
      (twoSidedExitDownTime X (-x) ω) < ⊤)} ≤ p ^ N := by
    intro N
    have hcyl := chat04_all_finite_prefix_increment_cylinder_product X 0 univ
      MeasurableSet.univ t htmono (by positivity) (fun _ => Icc (-a) a)
      (fun _ => measurableSet_Icc) N
    simp only [univ_inter, measure_univ, one_mul, hstep, Finset.prod_const,
      Finset.card_range] at hcyl
    rw [← hcyl]
    apply measure_mono
    intro ω hω
    simp only [mem_setOf_eq, not_lt, top_le_iff, min_eq_top] at hω
    obtain ⟨hU, hD⟩ := hω
    have hU' : ∀ s : ℝ≥0, X.X s ω ≤ a - x := by
      intro s
      by_contra hs
      push Not at hs
      have : twoSidedExitUpTime X (a - x) ω ≤ s := iInf₂_le s hs
      rw [hU] at this
      exact ENNReal.coe_ne_top (top_le_iff.mp this)
    have hD' : ∀ s : ℝ≥0, -x ≤ X.X s ω := by
      intro s
      by_contra hs
      push Not at hs
      have : twoSidedExitDownTime X (-x) ω ≤ s := iInf₂_le s hs
      rw [hD] at this
      exact ENNReal.coe_ne_top (top_le_iff.mp this)
    intro i _
    constructor
    · have := hU' (t i); have := hD' (t (i + 1)); linarith
    · have := hU' (t (i + 1)); have := hD' (t i); linarith
  rw [ae_iff]
  apply le_antisymm _ (by positivity)
  apply ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hp1) hbound
