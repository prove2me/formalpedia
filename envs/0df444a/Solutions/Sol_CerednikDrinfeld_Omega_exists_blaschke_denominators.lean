-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_blaschke_denominators
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d1e85e01-5d4d-5a22-844e-d93d6900e796

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_blaschke_denominators

set_option autoImplicit false

open Filter CerednikDrinfeld.Omega

namespace BLASCHKE

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem exists_pow_le_v (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) (c : K) (hc : c ≠ 0) :
    ∃ N : ℕ, Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N ≤ Valued.v c := by
  by_cases h : c ∈ Set.range (algebraMap K₀ K)
  · obtain ⟨a, rfl⟩ := h
    have ha : a ≠ 0 := by rintro rfl; exact hc (map_zero _)
    obtain ⟨N, hN, -⟩ := ϖ.scale a ha
    exact ⟨N, hN⟩
  · obtain ⟨j, hj⟩ := hex c h
    refine ⟨j, ?_⟩
    have := ((mem_affinoid_iff' ϖ j c).mp hj).2 0
    rwa [map_zero, sub_zero] at this

theorem ne_zero_of_mem {w : K} (hw : w ∈ upperHalfPlane K₀ K) : w ≠ 0 := by
  rw [mem_upperHalfPlane_iff] at hw
  intro h; exact hw 0 (by rw [map_zero, h])

theorem exists_v_eq_bound (ϖ : PseudoUniformizer K₀ K) (n : ℕ) (w' e : K) :
    ∃ b : K, ∀ x : Γ₀, x ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      max x (Valued.v w') * Valued.v e ≤ Valued.v b := by
  by_cases hw' : Valued.v w' ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n
  · refine ⟨((algebraMap K₀ K ϖ.ϖ)⁻¹ ^ n) * e, fun x hx => ?_⟩
    rw [Valuation.map_mul, Valuation.map_pow, Valuation.map_inv]
    exact mul_le_mul_left (max_le hx hw') _
  · refine ⟨w' * e, fun x hx => ?_⟩
    push Not at hw'
    rw [Valuation.map_mul]
    exact mul_le_mul_left (max_le (hx.trans hw'.le) le_rfl) _

theorem denominator_X_sub_C (ϖ : PseudoUniformizer K₀ K) (t : K₀) :
    (Polynomial.X - Polynomial.C (algebraMap K₀ K t)).natDegree ≤ 1 ∧
    (∀ z ∈ upperHalfPlane K₀ K, (Polynomial.X - Polynomial.C (algebraMap K₀ K t)).eval z ≠ 0) ∧
    (∀ (n : ℕ) (w' : K), ∃ b : K, ∀ z ∈ affinoid ϖ n,
      Valued.v ((z - w') / (Polynomial.X - Polynomial.C (algebraMap K₀ K t)).eval z) ≤ Valued.v b) := by
  refine ⟨(Polynomial.natDegree_X_sub_C _).le, fun z hz => ?_, fun n w' => ?_⟩
  · rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
    exact fun h => ((mem_upperHalfPlane_iff K₀ z).mp hz t) h.symm
  · obtain ⟨b, hb⟩ := exists_v_eq_bound ϖ n w' ((algebraMap K₀ K ϖ.ϖ)⁻¹ ^ n)
    refine ⟨b, fun z hz => ?_⟩
    have hz' := (mem_affinoid_iff' ϖ n z).mp hz
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Valuation.map_div]
    have hden : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n ≤ Valued.v (z - algebraMap K₀ K t) := hz'.2 t
    have hpn : 0 < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n := pow_pos ϖ.pos n
    refine le_trans ?_ (hb (Valued.v z) hz'.1)
    rw [div_eq_mul_inv, Valuation.map_pow, Valuation.map_inv, inv_pow]
    exact mul_le_mul' ((Valuation.map_sub _ _ _).trans le_rfl) ((inv_le_inv₀ (hpn.trans_le hden) hpn).2 hden)

theorem exists_denominator (ϖ : PseudoUniformizer K₀ K) {w : K} (hw : w ∈ upperHalfPlane K₀ K) (m : ℕ)
    (hm : 1 ≤ m → w ∉ affinoid ϖ (m - 1)) :
    ∃ d : Polynomial K, d.natDegree ≤ 1 ∧ (∀ z ∈ upperHalfPlane K₀ K, d.eval z ≠ 0) ∧
      (∀ (n : ℕ) (w' : K), ∃ b : K, ∀ z ∈ affinoid ϖ n, Valued.v ((z - w') / d.eval z) ≤ Valued.v b) ∧
      (1 ≤ m → ∀ n : ℕ, ∀ z ∈ affinoid ϖ n,
        Valued.v ((z - w) / d.eval z - 1) <
          Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (m - 1) * (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n) := by
  set p := Valued.v (algebraMap K₀ K ϖ.ϖ) with hp
  have hp0 : 0 < p := ϖ.pos
  have hp1 : p ≤ 1 := ϖ.lt_one.le
  have hpinv : (1 : Γ₀) ≤ p⁻¹ := (one_le_inv₀ hp0).2 hp1
  by_cases h1 : 1 ≤ m
  · have hnot := hm h1
    rw [affinoid, Set.mem_setOf_eq, not_and_or] at hnot
    rcases hnot with hbig | hclose
    ·
      push Not at hbig
      have hw0 : w ≠ 0 := ne_zero_of_mem hw
      have hvw : 0 < Valued.v w := (Valuation.pos_iff _).2 hw0
      refine ⟨Polynomial.C (-w), (Polynomial.natDegree_C _).le.trans zero_le_one, fun z _ => ?_, fun n w' => ?_,
        fun _ n z hz => ?_⟩
      · rw [Polynomial.eval_C, neg_ne_zero]; exact hw0
      · obtain ⟨b, hb⟩ := exists_v_eq_bound ϖ n w' 1
        refine ⟨b, fun z hz => ?_⟩
        have hz' := (mem_affinoid_iff' ϖ n z).mp hz
        refine le_trans ?_ (hb (Valued.v z) hz'.1)
        rw [Polynomial.eval_C, Valuation.map_one, mul_one, Valuation.map_div, Valuation.map_neg]
        have h1w : 1 ≤ Valued.v w := (one_le_pow₀ hpinv).trans hbig.le
        calc Valued.v (z - w') / Valued.v w ≤ Valued.v (z - w') / 1 := by
              rw [div_one, div_eq_mul_inv]
              exact mul_le_of_le_one_right' (inv_le_one_of_one_le₀ h1w)
          _ ≤ max (Valued.v z) (Valued.v w') := by rw [div_one]; exact Valuation.map_sub _ _ _
      ·
        have hz' := (mem_affinoid_iff' ϖ n z).mp hz
        have heq : (z - w) / (Polynomial.C (-w)).eval z - 1 = -(z / w) := by
          rw [Polynomial.eval_C]; field_simp; ring
        rw [heq, Valuation.map_neg, Valuation.map_div, div_eq_mul_inv, mul_comm (p ^ (m - 1))]
        have hinvw : (Valued.v w)⁻¹ < p ^ (m - 1) := by
          have := (inv_lt_inv₀ hvw (pow_pos (hp0.trans_le (hp1.trans hpinv)) _)).2 hbig
          rwa [inv_pow, inv_inv] at this
        calc Valued.v z * (Valued.v w)⁻¹ ≤ p⁻¹ ^ n * (Valued.v w)⁻¹ := mul_le_mul_left hz'.1 _
          _ < p⁻¹ ^ n * p ^ (m - 1) := mul_lt_mul_of_pos_left hinvw (pow_pos (hp0.trans_le (hp1.trans hpinv)) _)
    ·
      simp only [not_forall, not_le, exists_prop] at hclose
      obtain ⟨t, -, ht⟩ := hclose
      obtain ⟨hdeg, hnz, hbd⟩ := denominator_X_sub_C ϖ t
      refine ⟨_, hdeg, hnz, hbd, fun _ n z hz => ?_⟩
      have hz' := (mem_affinoid_iff' ϖ n z).mp hz
      have hden : p ^ n ≤ Valued.v (z - algebraMap K₀ K t) := hz'.2 t
      have hpn : 0 < p ^ n := pow_pos hp0 n
      have hzt : z - algebraMap K₀ K t ≠ 0 := by
        rw [sub_ne_zero]; exact fun h => ((mem_upperHalfPlane_iff K₀ z).mp (affinoid_subset_upperHalfPlane ϖ n hz) t) h.symm
      have heq : (z - w) / (Polynomial.X - Polynomial.C (algebraMap K₀ K t)).eval z - 1 =
          (algebraMap K₀ K t - w) / (z - algebraMap K₀ K t) := by
        rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        field_simp
        ring
      rw [heq, Valuation.map_div, ← neg_sub w, Valuation.map_neg, div_eq_mul_inv]
      calc Valued.v (w - algebraMap K₀ K t) * (Valued.v (z - algebraMap K₀ K t))⁻¹
          < p ^ (m - 1) * (Valued.v (z - algebraMap K₀ K t))⁻¹ :=
            mul_lt_mul_of_pos_right ht (zero_lt_iff.mpr (inv_ne_zero (hpn.trans_le hden).ne'))
        _ ≤ p ^ (m - 1) * p⁻¹ ^ n := by
            refine mul_le_mul_right ?_ _
            rw [inv_pow]
            exact (inv_le_inv₀ (hpn.trans_le hden) hpn).2 hden
  ·
    obtain ⟨hdeg, hnz, hbd⟩ := denominator_X_sub_C ϖ (0 : K₀)
    exact ⟨_, hdeg, hnz, hbd, fun h => absurd h h1⟩

end BLASCHKE

theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ)
    {ι : Type} (w : ι → K) (hw : ∀ γ, w γ ∈ upperHalfPlane K₀ K)
    (hfin : ∀ n : ℕ, {γ : ι | w γ ∈ affinoid ϖ n}.Finite) :
    ∃ d : ι → Polynomial K,
      (∀ γ, (d γ).natDegree ≤ 1) ∧
      (∀ γ, ∀ z ∈ upperHalfPlane K₀ K, (d γ).eval z ≠ 0) ∧
      (∀ (n : ℕ) (γ : ι) (w' : K), ∃ b : K, ∀ z ∈ affinoid ϖ n, Valued.v ((z - w') / (d γ).eval z) ≤ Valued.v b) ∧
      (∀ (n : ℕ) (c : K), c ≠ 0 →
        ∀ᶠ γ in cofinite, ∀ z ∈ affinoid ϖ n, Valued.v ((z - w γ) / (d γ).eval z - 1) < Valued.v c) := by
  classical
  set p := Valued.v (algebraMap K₀ K ϖ.ϖ) with hp
  have hp0 : 0 < p := ϖ.pos
  have hp1 : p ≤ 1 := ϖ.lt_one.le

  let m : ι → ℕ := fun γ => Nat.find (hex (w γ) (hw γ))
  have hm_spec : ∀ γ, w γ ∈ affinoid ϖ (m γ) := fun γ => Nat.find_spec (hex (w γ) (hw γ))
  have hm_min : ∀ γ k, k < m γ → w γ ∉ affinoid ϖ k := fun γ k hk => Nat.find_min (hex (w γ) (hw γ)) hk
  have key := fun γ => BLASCHKE.exists_denominator ϖ (hw γ) (m γ) (fun h1 => hm_min γ (m γ - 1) (by omega))
  choose d hd1 hd2 hd3 hd4 using key
  refine ⟨d, hd1, hd2, fun n γ w' => hd3 γ n w', fun n c hc => ?_⟩
  obtain ⟨N, hN⟩ := BLASCHKE.exists_pow_le_v ϖ hex c hc
  rw [Filter.eventually_cofinite]
  refine (hfin (n + N)).subset fun γ hγ => ?_
  simp only [Set.mem_setOf_eq] at hγ ⊢
  by_contra hnot
  apply hγ
  intro z hz
  have hmγ : n + N < m γ := by
    by_contra h
    push Not at h
    exact hnot (affinoid_mono ϖ h (hm_spec γ))
  have h1 : 1 ≤ m γ := by omega
  refine (hd4 γ h1 n z hz).trans_le ?_
  obtain ⟨k, hk⟩ : ∃ k, m γ - 1 = n + k := ⟨m γ - 1 - n, by omega⟩
  rw [hk, pow_add, mul_comm (p ^ n), mul_assoc, ← mul_pow, mul_inv_cancel₀ hp0.ne', one_pow, mul_one]
  exact (pow_le_pow_right_of_le_one' hp1 (by omega : N ≤ k)).trans hN

end S_CerednikDrinfeld_Omega_exists_blaschke_denominators
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_blaschke_denominators (solution)
