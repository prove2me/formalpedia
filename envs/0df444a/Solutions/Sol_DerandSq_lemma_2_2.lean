-- Prove2me | solution 1 for DerandSq.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:10:35.904684+00:00
-- url     : https://prove2.me/submissions/1dd34979-0814-4929-bf76-9c4dbdcc5126

import Mathlib

section
open scoped ComplexOrder

set_option autoImplicit false

namespace DerandSq.Dev.L22

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem tau_nonneg (τ : A →ₗ[ℂ] ℂ) (hpos : ∀ a : A, 0 ≤ τ (star a * a)) {x : A} (hx : 0 ≤ x) :
    0 ≤ τ x := by
  obtain ⟨c, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
  exact hpos c

theorem tau_re_mono (τ : A →ₗ[ℂ] ℂ) (hpos : ∀ a : A, 0 ≤ τ (star a * a)) {x y : A} (h : x ≤ y) :
    (τ x).re ≤ (τ y).re := by
  have h0 : 0 ≤ τ (y - x) := tau_nonneg τ hpos (sub_nonneg.mpr h)
  rw [map_sub] at h0
  have := (Complex.nonneg_iff.mp h0).1
  simp at this
  linarith

theorem tau_re_nonneg (τ : A →ₗ[ℂ] ℂ) (hpos : ∀ a : A, 0 ≤ τ (star a * a)) {x : A} (hx : 0 ≤ x) :
    0 ≤ (τ x).re := (Complex.nonneg_iff.mp (tau_nonneg τ hpos hx)).1

theorem tau_re_pos (τ : A →ₗ[ℂ] ℂ) (hpos : ∀ a : A, 0 ≤ τ (star a * a))
    (hfaith : ∀ a : A, τ (star a * a) = 0 → a = 0) {x : A} (hx : 0 ≤ x) (hne : x ≠ 0) :
    0 < (τ x).re := by
  obtain ⟨c, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
  have h0 := hpos c
  rcases (Complex.nonneg_iff.mp h0) with ⟨hre, him⟩
  by_contra hcon
  have hre0 : (τ (star c * c)).re = 0 := le_antisymm (not_lt.mp hcon) hre
  have : τ (star c * c) = 0 := Complex.ext hre0 (by simp [← him])
  have hc := hfaith c this
  apply hne
  simp [hc]

theorem pow_nonneg' {b : A} (hb : 0 ≤ b) (k : ℕ) : 0 ≤ b ^ k := by
  rw [← cfc_pow_id (R := ℝ) b k (ha := IsSelfAdjoint.of_nonneg hb)]
  exact cfc_nonneg fun x hx => pow_nonneg (spectrum_nonneg_of_nonneg hb hx) k

theorem root_pow (c : ℝ) (hc : 0 ≤ c) (k : ℕ) (hk : 1 ≤ k) :
    ((c ^ 2) ^ k) ^ ((1 : ℝ) / (2 * k)) = c := by
  rw [← pow_mul, one_div]
  have := Real.pow_rpow_inv_natCast hc (n := 2 * k) (by omega)
  push_cast at this
  exact this

/-- spectral measure of the upper end: `f_c`. -/
noncomputable def bump (c s : ℝ) (x : ℝ) : ℝ := max 0 (min 1 ((x - c ^ 2) / (s ^ 2 - c ^ 2)))

theorem bump_cont (c s : ℝ) : Continuous (bump c s) := by
  unfold bump; fun_prop

theorem bump_nonneg (c s x : ℝ) : 0 ≤ bump c s x := le_max_left _ _

theorem bump_le_one (c s x : ℝ) : bump c s x ≤ 1 := by
  unfold bump; exact max_le zero_le_one (min_le_left _ _)

theorem bump_zero_of_le (c s x : ℝ) (h : x ≤ c ^ 2) (hcs : c ^ 2 < s ^ 2) : bump c s x = 0 := by
  unfold bump
  have : (x - c ^ 2) / (s ^ 2 - c ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  simp [min_le_of_right_le this]

theorem bump_at (c s : ℝ) (hcs : c ^ 2 < s ^ 2) : bump c s (s ^ 2) = 1 := by
  unfold bump
  have : (s ^ 2 - c ^ 2) / (s ^ 2 - c ^ 2) = 1 := div_self (by linarith)
  simp [this]

theorem upper (τ : A →ₗ[ℂ] ℂ) (hτ1 : τ 1 = 1) (hpos : ∀ a : A, 0 ≤ τ (star a * a)) (a : A)
    (k : ℕ) (hk : 1 ≤ k) :
    (τ ((star a * a) ^ k)).re ^ ((1 : ℝ) / (2 * k)) ≤ ‖a‖ := by
  haveI : Nontrivial A := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have := hτ1; rw [← h] at this; simp at this
  set b := star a * a with hb
  have hb0 : 0 ≤ b := star_mul_self_nonneg a
  have hnb : ‖b‖ = ‖a‖ ^ 2 := by rw [hb, CStarRing.norm_star_mul_self, sq]
  have hle : b ^ k ≤ algebraMap ℝ A (‖a‖ ^ (2 * k)) := by
    have h1 : b ^ k = cfc (fun x : ℝ => x ^ k) b := (cfc_pow_id b k).symm
    rw [h1]
    have := cfc_le_algebraMap (R := ℝ) (fun x : ℝ => x ^ k) (‖a‖ ^ (2 * k)) b ?_
    · exact this
    intro x hx
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hb0 hx
    have hxn : x ≤ ‖a‖ ^ 2 := by
      have := spectrum.norm_le_norm_of_mem hx
      rw [hnb, Real.norm_eq_abs, abs_of_nonneg hx0] at this
      exact this
    calc x ^ k ≤ (‖a‖ ^ 2) ^ k := pow_le_pow_left₀ hx0 hxn k
      _ = ‖a‖ ^ (2 * k) := by rw [← pow_mul]
  have h2 := tau_re_mono τ hpos hle
  have h3 : (τ (algebraMap ℝ A (‖a‖ ^ (2 * k)))).re = ‖a‖ ^ (2 * k) := by
    rw [Algebra.algebraMap_eq_smul_one]
    have : (‖a‖ ^ (2 * k) : ℝ) • (1 : A) = ((‖a‖ ^ (2 * k) : ℝ) : ℂ) • (1 : A) := by
      rw [Complex.coe_smul]
    rw [this, map_smul, hτ1, smul_eq_mul, mul_one, Complex.ofReal_re]
  rw [h3] at h2
  have h4 : 0 ≤ (τ (b ^ k)).re := tau_re_nonneg τ hpos (pow_nonneg' hb0 k)
  calc (τ (b ^ k)).re ^ ((1 : ℝ) / (2 * k)) ≤ (‖a‖ ^ (2 * k)) ^ ((1 : ℝ) / (2 * k)) :=
        Real.rpow_le_rpow h4 h2 (by positivity)
    _ = ‖a‖ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg a)]
        have : ((2 * k : ℕ) : ℝ) * ((1 : ℝ) / (2 * k)) = 1 := by
          push_cast
          have : (k : ℝ) ≠ 0 := by positivity
          field_simp
        rw [this, Real.rpow_one]

theorem lower (τ : A →ₗ[ℂ] ℂ) (hτ1 : τ 1 = 1) (hpos : ∀ a : A, 0 ≤ τ (star a * a))
    (hfaith : ∀ a : A, τ (star a * a) = 0 → a = 0) (a : A) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c < ‖a‖) :
    ∃ t : ℝ, 0 < t ∧ ∀ k : ℕ, 1 ≤ k → c * t ^ ((1 : ℝ) / (2 * k)) ≤
      (τ ((star a * a) ^ k)).re ^ ((1 : ℝ) / (2 * k)) := by
  haveI : Nontrivial A := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have := hτ1; rw [← h] at this; simp at this
  set b := star a * a with hb
  have hb0 : 0 ≤ b := star_mul_self_nonneg a
  have hnb : ‖b‖ = ‖a‖ ^ 2 := by rw [hb, CStarRing.norm_star_mul_self, sq]
  have hcs : c ^ 2 < ‖a‖ ^ 2 := by nlinarith
  have hsa : IsSelfAdjoint b := .of_nonneg hb0
  set g := cfc (bump c ‖a‖) b with hg
  have hg0 : 0 ≤ g := cfc_nonneg (fun x _ => bump_nonneg c ‖a‖ x)
  have hgne : g ≠ 0 := by
    intro h0
    have hmem : ‖b‖ ∈ spectrum ℝ b := CStarAlgebra.norm_mem_spectrum_of_nonneg hb0
    have h1 : bump c ‖a‖ ‖b‖ ∈ spectrum ℝ g := by
      rw [hg, cfc_map_spectrum (bump c ‖a‖) b (IsSelfAdjoint.of_nonneg hb0)
        (bump_cont c ‖a‖).continuousOn]
      exact ⟨_, hmem, rfl⟩
    rw [hnb, bump_at c ‖a‖ hcs, h0, spectrum.zero_eq] at h1
    simp at h1
  refine ⟨(τ g).re, tau_re_pos τ hpos hfaith hg0 hgne, fun k hk => ?_⟩
  have hle : algebraMap ℝ A ((c ^ 2) ^ k) * g ≤ b ^ k := by
    have h1 : b ^ k = cfc (fun x : ℝ => x ^ k) b := (cfc_pow_id b k).symm
    have h2 : algebraMap ℝ A ((c ^ 2) ^ k) * g = cfc (fun x : ℝ => (c ^ 2) ^ k * bump c ‖a‖ x) b := by
      rw [cfc_const_mul ((c ^ 2) ^ k) (bump c ‖a‖) b (bump_cont c ‖a‖).continuousOn,
        Algebra.smul_def]
    rw [h2, h1]
    refine cfc_mono (hf := ((bump_cont c ‖a‖).const_mul ((c ^ 2) ^ k)).continuousOn)
      (hg := (continuous_pow k).continuousOn) (fun x hx => ?_)
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hb0 hx
    by_cases hxc : x ≤ c ^ 2
    · rw [bump_zero_of_le c ‖a‖ x hxc hcs]; simpa using pow_nonneg hx0 k
    · push_neg at hxc
      calc (c ^ 2) ^ k * bump c ‖a‖ x ≤ (c ^ 2) ^ k * 1 :=
            mul_le_mul_of_nonneg_left (bump_le_one _ _ _) (by positivity)
        _ ≤ x ^ k := by rw [mul_one]; exact pow_le_pow_left₀ (by positivity) hxc.le k
  have h2 := tau_re_mono τ hpos hle
  have h3 : (τ (algebraMap ℝ A ((c ^ 2) ^ k) * g)).re = (c ^ 2) ^ k * (τ g).re := by
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    have : ((c ^ 2) ^ k : ℝ) • g = (((c ^ 2) ^ k : ℝ) : ℂ) • g := by rw [Complex.coe_smul]
    rw [this, map_smul, smul_eq_mul, Complex.re_ofReal_mul]
  rw [h3] at h2
  have htg : 0 ≤ (τ g).re := tau_re_nonneg τ hpos hg0
  calc c * (τ g).re ^ ((1 : ℝ) / (2 * k))
      = ((c ^ 2) ^ k * (τ g).re) ^ ((1 : ℝ) / (2 * k)) := by
        rw [Real.mul_rpow (by positivity) htg, root_pow c hc0 k hk]
    _ ≤ _ := Real.rpow_le_rpow (by positivity) h2 (by positivity)

end DerandSq.Dev.L22

namespace DerandSq
open DerandSq.Dev.L22 in
theorem chk_lemma_2_2 {A : Type*} [CStarAlgebra A] (τ : A →ₗ[ℂ] ℂ) (hτ1 : τ 1 = 1)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) (hpos : ∀ a : A, 0 ≤ τ (star a * a))
    (hfaith : ∀ a : A, τ (star a * a) = 0 → a = 0) (a : A) :
    Filter.Tendsto (fun k : ℕ => (τ ((star a * a) ^ k)).re ^ ((1 : ℝ) / (2 * k)))
      Filter.atTop (nhds ‖a‖) := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  haveI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  rw [tendsto_order]
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · by_cases hc0 : c < 0
    · refine Filter.Eventually.of_forall fun k => lt_of_lt_of_le hc0 ?_
      exact Real.rpow_nonneg (tau_re_nonneg τ hpos (pow_nonneg' (star_mul_self_nonneg a) k)) _
    · push_neg at hc0
      obtain ⟨c', hcc', hc'a⟩ := exists_between hc
      have hc'0 : 0 ≤ c' := hc0.trans hcc'.le
      obtain ⟨t, ht, hk⟩ := lower τ hτ1 hpos hfaith a hc'0 hc'a
      have hlim : Filter.Tendsto (fun k : ℕ => c' * t ^ ((1 : ℝ) / (2 * k))) Filter.atTop
          (nhds (c' * t ^ (0 : ℝ))) := by
        refine Filter.Tendsto.const_mul _ ?_
        have h0 : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / (2 * k)) Filter.atTop (nhds 0) := by
          have := tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ)
          refine this.congr fun k => ?_
          by_cases hk0 : (k : ℝ) = 0
          · simp [hk0]
          · field_simp
        exact ((Real.continuousAt_const_rpow ht.ne').tendsto).comp h0
      rw [Real.rpow_zero, mul_one] at hlim
      have := (hlim.eventually (lt_mem_nhds hcc'))
      filter_upwards [this, Filter.eventually_ge_atTop 1] with k hk1 hk2
      exact lt_of_lt_of_le hk1 (hk k hk2)
  · filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    exact lt_of_le_of_lt (upper τ hτ1 hpos a k hk) hc
end DerandSq
end

theorem solution : type_of% @DerandSq.chk_lemma_2_2 := @DerandSq.chk_lemma_2_2
