-- Prove2me | solution 1 for FastRatesSVM.GeomNoise.theorem_2_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T20:53:25.528374+00:00
-- url     : https://prove2.me/submissions/4cb97790-6b75-4b7e-8bc9-9b5b1a795a79

import Mathlib
import Definitions.Def_FastRatesSVM_GeomNoise_Tau
import Definitions.Def_FastRatesSVM_GeomNoise_TsybakovNoise
import Definitions.Def_FastRatesSVM_GeomNoise_GeometricNoise
import Definitions.Def_FastRatesSVM_GeomNoise_Envelope

set_option autoImplicit false

open MeasureTheory

namespace FastRatesSVM.GeomNoise.A135

/-- The Tsybakov bound extends from `(0, t₀]` to all `s > 0` (with a larger constant),
because `μ` is a probability measure. -/
lemma global_tsybakov {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (η : EuclideanSpace ℝ (Fin d) → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hts : HasTsybakovNoiseExponent X μ η (ENNReal.ofReal q)) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ s : ℝ, 0 < s →
      μ {x | x ∈ X ∧ |2 * η x - 1| ≤ s} ≤ ENNReal.ofReal (C₁ * s ^ q) := by
  obtain ⟨C, t₀, hC, ht₀, -, h⟩ := hts
  have hne : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  have htr : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq
  refine ⟨max C (t₀ ^ (-q)), lt_max_of_lt_left hC, fun s hs => ?_⟩
  rcases le_or_gt s t₀ with hst | hst
  · have h' := h s hs hst
    rw [if_neg hne, htr] at h'
    refine h'.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hs.le _)
  · calc μ {x | x ∈ X ∧ |2 * η x - 1| ≤ s} ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (max C (t₀ ^ (-q)) * s ^ q) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : 1 ≤ (s / t₀) ^ q := Real.one_le_rpow ((one_le_div ht₀).2 hst.le) hq
        have h2 : (s / t₀) ^ q = t₀ ^ (-q) * s ^ q := by
          rw [Real.div_rpow hs.le ht₀.le, Real.rpow_neg ht₀.le, div_eq_inv_mul]
        calc (1:ℝ) ≤ t₀ ^ (-q) * s ^ q := h2 ▸ h1
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hs.le _)

/-- Pointwise estimate on the dyadic shell `r s₀ ≤ f < 2 r s₀`, `s₀ = c t^{γ/2}`. -/
lemma pointwise_bound (γ q c t τ f r : ℝ) (n : ℕ) (hγ : 0 < γ) (hq : 0 ≤ q) (hc : 0 < c)
    (ht : 0 < t) (hτ : 0 ≤ τ) (hn : γ * (q + 2) / 2 ≤ n) (hr : 1 ≤ r)
    (hlo : r * (c * t ^ (γ / 2)) ≤ f) (hhi : f ≤ 2 * r * (c * t ^ (γ / 2)))
    (henv : f ≤ c * τ ^ γ) :
    f * Real.exp (-τ ^ 2 / t) ≤ 2 * n.factorial * (c * t ^ (γ / 2)) / (r * r ^ q) := by
  have hpos : 0 < t ^ (γ / 2) := Real.rpow_pos_of_pos ht _
  have hr0 : 0 < r := by linarith
  have hrq : 0 < r ^ q := Real.rpow_pos_of_pos hr0 _
  have hf0 : 0 ≤ f := le_trans (by positivity) hlo
  set a := τ ^ 2 / t with ha
  have ha0 : 0 ≤ a := div_nonneg (sq_nonneg τ) ht.le
  have haγ : a ^ (γ / 2) = τ ^ γ / t ^ (γ / 2) := by
    rw [ha, Real.div_rpow (sq_nonneg τ) ht.le, ← Real.rpow_natCast τ 2, ← Real.rpow_mul hτ]
    congr 2
    push_cast
    ring
  have hr_le : r ≤ a ^ (γ / 2) := by
    rw [haγ, le_div_iff₀ hpos]
    have h1 : c * (r * t ^ (γ / 2)) ≤ c * τ ^ γ := by
      calc c * (r * t ^ (γ / 2)) = r * (c * t ^ (γ / 2)) := by ring
        _ ≤ f := hlo
        _ ≤ c * τ ^ γ := henv
    exact le_of_mul_le_mul_left h1 hc
  have ha1 : 1 ≤ a := by
    by_contra hlt
    push_neg at hlt
    have : a ^ (γ / 2) < 1 := Real.rpow_lt_one ha0 hlt (by positivity)
    linarith
  have hapos : 0 < a := by linarith
  have hpow : r ^ q * r ^ 2 ≤ a ^ n := by
    have e1 : r ^ q * r ^ 2 = r ^ (q + 2) := by
      rw [Real.rpow_add hr0, Real.rpow_two]
    have e2 : r ^ (q + 2) ≤ (a ^ (γ / 2)) ^ (q + 2) :=
      Real.rpow_le_rpow (by linarith) hr_le (by linarith)
    have e3 : (a ^ (γ / 2)) ^ (q + 2) = a ^ (γ * (q + 2) / 2) := by
      rw [← Real.rpow_mul ha0]
      congr 1
      ring
    have e4 : a ^ (γ * (q + 2) / 2) ≤ a ^ (n : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le ha1 hn
    rw [Real.rpow_natCast] at e4
    rw [e1]
    calc r ^ (q + 2) ≤ (a ^ (γ / 2)) ^ (q + 2) := e2
      _ = a ^ (γ * (q + 2) / 2) := e3
      _ ≤ a ^ n := e4
  have hexp : Real.exp (-τ ^ 2 / t) ≤ n.factorial / a ^ n := by
    have hfac : (0:ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hk := Real.pow_div_factorial_le_exp a ha0 n
    have hapn : 0 < a ^ n := pow_pos hapos n
    rw [neg_div, Real.exp_neg]
    have hq0 : 0 < a ^ n / n.factorial := div_pos hapn hfac
    calc (Real.exp a)⁻¹ ≤ (a ^ n / n.factorial)⁻¹ := inv_anti₀ hq0 hk
      _ = n.factorial / a ^ n := by rw [inv_div]
  have hfac : (0:ℝ) ≤ n.factorial := by positivity
  calc f * Real.exp (-τ ^ 2 / t) ≤ (2 * r * (c * t ^ (γ / 2))) * (n.factorial / a ^ n) :=
        mul_le_mul hhi hexp (Real.exp_pos _).le (by positivity)
    _ ≤ (2 * r * (c * t ^ (γ / 2))) * (n.factorial / (r ^ q * r ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact div_le_div_of_nonneg_left hfac (by positivity) hpow
    _ = 2 * n.factorial * (c * t ^ (γ / 2)) / (r * r ^ q) := by
        field_simp

lemma tau_nonneg {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (η : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ tau X η x := by
  unfold tau
  split_ifs
  · exact Metric.infDist_nonneg
  · exact Metric.infDist_nonneg
  · exact le_rfl

lemma main_bound {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (η : EuclideanSpace ℝ (Fin d) → ℝ)
    (γ q : ℝ) (hq : 0 ≤ q) (henv : HasEnvelope X μ η γ)
    (hts : HasTsybakovNoiseExponent X μ η (ENNReal.ofReal q)) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 < t →
      (∫⁻ x in X, ENNReal.ofReal (|2 * η x - 1| * Real.exp (-(tau X η x) ^ 2 / t)) ∂μ) ≤
        ENNReal.ofReal (K * t ^ ((q + 1) * γ / 2)) := by
  obtain ⟨hγ, c, hc, hae⟩ := henv
  obtain ⟨C₁, hC₁, hT⟩ := global_tsybakov X μ η q hq hts
  set n : ℕ := ⌈γ * (q + 2) / 2⌉₊ with hn_def
  have hn : γ * (q + 2) / 2 ≤ n := Nat.le_ceil _
  have hfac : (0:ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  set D : ℝ := 2 ^ (q + 1) * n.factorial * C₁ with hD
  have hD0 : 0 < D := by positivity
  refine ⟨C₁ * c ^ (q + 1) + D * c ^ (q + 1) * 2, by positivity, fun t ht => ?_⟩
  set s0 : ℝ := c * t ^ (γ / 2) with hs0
  have hs0pos : 0 < s0 := mul_pos hc (Real.rpow_pos_of_pos ht _)
  set F : EuclideanSpace ℝ (Fin d) → ENNReal :=
    fun x => ENNReal.ofReal (|2 * η x - 1| * Real.exp (-(tau X η x) ^ 2 / t)) with hF
  set A : Set (EuclideanSpace ℝ (Fin d)) := {x | x ∈ X ∧ |2 * η x - 1| < s0} with hA_def
  set B : ℕ → Set (EuclideanSpace ℝ (Fin d)) := fun k =>
    {x | x ∈ X ∧ (2:ℝ) ^ k * s0 ≤ |2 * η x - 1| ∧ |2 * η x - 1| ≤ 2 * (2:ℝ) ^ k * s0}
    with hB_def
  have hcover : X ⊆ A ∪ ⋃ k, B k := by
    intro x hx
    by_cases h : |2 * η x - 1| < s0
    · exact Or.inl ⟨hx, h⟩
    · push_neg at h
      obtain ⟨k, hk1, hk2⟩ :=
        exists_nat_pow_near ((one_le_div hs0pos).2 h) (by norm_num : (1:ℝ) < 2)
      refine Or.inr (Set.mem_iUnion.2 ⟨k, hx, ?_, ?_⟩)
      · rwa [le_div_iff₀ hs0pos] at hk1
      · rw [div_lt_iff₀ hs0pos, pow_succ] at hk2
        have e : (2:ℝ) ^ k * 2 * s0 = 2 * (2:ℝ) ^ k * s0 := by ring
        linarith
  have hexp1 : ∀ x, Real.exp (-(tau X η x) ^ 2 / t) ≤ 1 := fun x =>
    Real.exp_le_one_iff.2 (by rw [neg_div]; exact neg_nonpos.2 (div_nonneg (sq_nonneg _) ht.le))
  -- the core region `f < s₀`
  have hAint : ∫⁻ x in A, F x ∂μ ≤ ENNReal.ofReal (C₁ * s0 ^ (q + 1)) := by
    calc ∫⁻ x in A, F x ∂μ ≤ ∫⁻ x in A, ENNReal.ofReal s0 ∂μ := by
          apply setLIntegral_mono_ae aemeasurable_const
          refine ae_of_all _ fun x hx => ENNReal.ofReal_le_ofReal ?_
          exact (mul_le_of_le_one_right (abs_nonneg _) (hexp1 x)).trans hx.2.le
      _ = ENNReal.ofReal s0 * μ A := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal s0 * ENNReal.ofReal (C₁ * s0 ^ q) := by
          gcongr
          have hsub : A ⊆ {x | x ∈ X ∧ |2 * η x - 1| ≤ s0} := fun x hx => ⟨hx.1, hx.2.le⟩
          exact (measure_mono hsub).trans (hT s0 hs0pos)
      _ = ENNReal.ofReal (C₁ * s0 ^ (q + 1)) := by
          rw [← ENNReal.ofReal_mul hs0pos.le, Real.rpow_add_one hs0pos.ne']
          ring_nf
  -- the dyadic shells
  have hBint : ∀ k : ℕ, ∫⁻ x in B k, F x ∂μ ≤ ENNReal.ofReal (D * s0 ^ (q + 1)) * 2⁻¹ ^ k := by
    intro k
    set r : ℝ := (2:ℝ) ^ k with hr
    have hr1 : 1 ≤ r := one_le_pow₀ (by norm_num)
    have hr0 : 0 < r := by linarith
    have hrq : 0 < r ^ q := Real.rpow_pos_of_pos hr0 _
    calc ∫⁻ x in B k, F x ∂μ
        ≤ ∫⁻ x in B k, ENNReal.ofReal (2 * n.factorial * s0 / (r * r ^ q)) ∂μ := by
          apply setLIntegral_mono_ae aemeasurable_const
          refine hae.mono fun x hx hxB => ENNReal.ofReal_le_ofReal ?_
          exact pointwise_bound γ q c t (tau X η x) (|2 * η x - 1|) r n hγ hq hc ht
            (tau_nonneg X η x) hn hr1 hxB.2.1 hxB.2.2 (hx hxB.1)
      _ = ENNReal.ofReal (2 * n.factorial * s0 / (r * r ^ q)) * μ (B k) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (2 * n.factorial * s0 / (r * r ^ q)) *
            ENNReal.ofReal (C₁ * (2 * r * s0) ^ q) := by
          gcongr
          have hsub : B k ⊆ {x | x ∈ X ∧ |2 * η x - 1| ≤ 2 * r * s0} :=
            fun x hx => ⟨hx.1, hx.2.2⟩
          exact (measure_mono hsub).trans (hT _ (by positivity))
      _ = ENNReal.ofReal (D * s0 ^ (q + 1) * (2⁻¹ : ℝ) ^ k) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have e1 : (2 * r * s0) ^ q = 2 ^ q * r ^ q * s0 ^ q := by
            rw [Real.mul_rpow (by positivity) hs0pos.le, Real.mul_rpow (by norm_num) hr0.le]
          have e2 : (2:ℝ) ^ (q + 1) = 2 ^ q * 2 := Real.rpow_add_one (by norm_num) q
          have e3 : s0 ^ (q + 1) = s0 ^ q * s0 := Real.rpow_add_one hs0pos.ne' q
          have e4 : (2⁻¹ : ℝ) ^ k = r⁻¹ := by rw [inv_pow]
          have h2q : (0:ℝ) < 2 ^ q := Real.rpow_pos_of_pos (by norm_num) _
          have hs0q' : (0:ℝ) < s0 ^ q := Real.rpow_pos_of_pos hs0pos _
          rw [e1, hD, e2, e3, e4]
          field_simp
      _ = ENNReal.ofReal (D * s0 ^ (q + 1)) * 2⁻¹ ^ k := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
            ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  have hs0q : s0 ^ (q + 1) = c ^ (q + 1) * t ^ ((q + 1) * γ / 2) := by
    rw [hs0, Real.mul_rpow hc.le (Real.rpow_nonneg ht.le _), ← Real.rpow_mul ht.le]
    congr 2
    ring
  calc ∫⁻ x in X, F x ∂μ ≤ ∫⁻ x in A ∪ ⋃ k, B k, F x ∂μ := lintegral_mono_set hcover
    _ ≤ ∫⁻ x in A, F x ∂μ + ∫⁻ x in ⋃ k, B k, F x ∂μ := lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal (C₁ * s0 ^ (q + 1)) + ∑' k : ℕ, ENNReal.ofReal (D * s0 ^ (q + 1)) * 2⁻¹ ^ k :=
        add_le_add hAint ((lintegral_iUnion_le _ _).trans (ENNReal.tsum_le_tsum hBint))
    _ = ENNReal.ofReal (C₁ * s0 ^ (q + 1)) + ENNReal.ofReal (D * s0 ^ (q + 1) * 2) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
          ENNReal.ofReal_mul (p := D * s0 ^ (q + 1)) (by positivity), ENNReal.ofReal_ofNat]
    _ = ENNReal.ofReal ((C₁ * c ^ (q + 1) + D * c ^ (q + 1) * 2) * t ^ ((q + 1) * γ / 2)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), hs0q]
        congr 1
        ring

end FastRatesSVM.GeomNoise.A135

open MeasureTheory FastRatesSVM.GeomNoise in
theorem solution
    {d : ℕ} (hd : 0 < d) (X : Set (EuclideanSpace ℝ (Fin d))) (hX : IsCompact X)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (hμX : μ Xᶜ = 0)
    (η : EuclideanSpace ℝ (Fin d) → ℝ) (hη : Measurable η) (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (γ q : ℝ) (hq : 0 ≤ q)
    (henv : HasEnvelope X μ η γ)
    (hts : HasTsybakovNoiseExponent X μ η (ENNReal.ofReal q)) :
    (1 ≤ q → HasGeometricNoiseExponent X μ η ((q + 1) * γ / d)) ∧
    (q < 1 → ∀ α : ℝ, 0 < α → α < (q + 1) * γ / d → HasGeometricNoiseExponent X μ η α) := by
  have hγ : 0 < γ := henv.1
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd
  obtain ⟨K, hK, hbound⟩ := A135.main_bound X μ η γ q hq henv hts
  -- trivial bound by `1`
  have htriv : ∀ t : ℝ, 0 < t →
      (∫⁻ x in X, ENNReal.ofReal (|2 * η x - 1| * Real.exp (-(tau X η x) ^ 2 / t)) ∂μ) ≤ 1 := by
    intro t ht
    calc (∫⁻ x in X, ENNReal.ofReal (|2 * η x - 1| * Real.exp (-(tau X η x) ^ 2 / t)) ∂μ)
        ≤ ∫⁻ x in X, (1 : ENNReal) ∂μ := by
          apply setLIntegral_mono_ae aemeasurable_const
          refine ae_of_all _ fun x _ => ?_
          rw [← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          have hf1 : |2 * η x - 1| ≤ 1 := abs_le.2 ⟨by linarith [(hη01 x).1], by linarith [(hη01 x).2]⟩
          have he : Real.exp (-(tau X η x) ^ 2 / t) ≤ 1 :=
            Real.exp_le_one_iff.2 (by rw [neg_div]; exact neg_nonpos.2 (div_nonneg (sq_nonneg _) ht.le))
          exact mul_le_one₀ hf1 (Real.exp_pos _).le he
      _ = μ X := by rw [setLIntegral_const, one_mul]
      _ ≤ 1 := prob_le_one
  refine ⟨fun _ => ⟨by positivity, K, hK, fun t ht => ?_⟩, fun _ α hα hlt => ⟨hα, max K 1, ?_, ?_⟩⟩
  · have e : (q + 1) * γ / (d : ℝ) * (d : ℝ) / 2 = (q + 1) * γ / 2 := by
      field_simp
    rw [e]
    exact hbound t ht
  · exact lt_max_of_lt_right one_pos
  · intro t ht
    have hαd : α * (d : ℝ) < (q + 1) * γ := (lt_div_iff₀ hdpos).1 hlt
    have he0 : 0 ≤ α * (d : ℝ) / 2 := by positivity
    rcases le_or_gt t 1 with ht1 | ht1
    · refine (hbound t ht).trans (ENNReal.ofReal_le_ofReal ?_)
      apply mul_le_mul (le_max_left _ _) _ (Real.rpow_nonneg ht.le _) (by positivity)
      exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
    · refine (htriv t ht).trans ?_
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      exact one_le_mul_of_one_le_of_one_le (le_max_right _ _) (Real.one_le_rpow ht1.le he0)
