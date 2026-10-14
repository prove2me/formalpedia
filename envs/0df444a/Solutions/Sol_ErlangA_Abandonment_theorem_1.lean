-- Prove2me | solution 1 for ErlangA.Abandonment.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-13T01:38:50.511833+00:00
-- url     : https://prove2.me/submissions/1689ee3d-892f-4dde-8d9e-de8e47a5464a

-- Complete checked reconstruction of the native Erlang-A abandonment asymptotic theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_ErlangA_Abandonment_Model


-- Begin Canonical

-- End Canonical

-- Begin WeightBasic

open scoped BigOperators
namespace ErlangA.Abandonment.Proof

lemma death_nonneg (N k : ℕ) {μ θ : ℝ} (hμ : 0 < μ) (hθ : 0 < θ) :
    0 ≤ deathRate N μ θ k := by
  unfold deathRate
  positivity

lemma death_lower (N k : ℕ) (μ θ : ℝ) :
    min μ θ * (k : ℝ) ≤ deathRate N μ θ k := by
  unfold deathRate
  have hm : ((min k N : ℕ) : ℝ) + (k - N : ℕ) = k := by
    exact_mod_cast (show min k N + (k-N) = k by omega)
  have h1 := mul_le_mul_of_nonneg_right (min_le_left μ θ) (show 0 ≤ ((min k N : ℕ) : ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_right (min_le_right μ θ) (show 0 ≤ ((k-N:ℕ):ℝ) by positivity)
  rw [← hm, mul_add]
  nlinarith

lemma death_pos (N k : ℕ) {μ θ : ℝ} (hμ : 0 < μ) (hθ : 0 < θ) (hk : 0 < k) :
    0 < deathRate N μ θ k := by
  exact lt_of_lt_of_le (mul_pos (lt_min hμ hθ) (by exact_mod_cast hk)) (death_lower N k μ θ)

lemma weight_pos (N k : ℕ) {lam μ θ : ℝ} (hlam : 0 < lam) (hμ : 0 < μ)
    (hθ : 0 < θ) : 0 < weight N lam μ θ k := by
  unfold weight
  split_ifs with hk
  · positivity
  · apply mul_pos
    · apply Finset.prod_pos
      intro j hj
      have hjN := (Finset.mem_Icc.mp hj).1
      have hs : 0 < j-N := by omega
      exact div_pos hlam (add_pos_of_nonneg_of_pos (by positivity) (mul_pos (by exact_mod_cast hs) hθ))
    · positivity

lemma weight_zero (N : ℕ) (lam μ θ : ℝ) : weight N lam μ θ 0 = 1 := by
  simp [weight]

lemma weight_succ_balance (N k : ℕ) {lam μ θ : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) (hθ : 0 < θ) :
    weight N lam μ θ (k+1) * deathRate N μ θ (k+1) = lam * weight N lam μ θ k := by
  by_cases hk : k+1 ≤ N
  · have hk' : k ≤ N := by omega
    simp only [weight, if_pos hk, if_pos hk', deathRate, Nat.min_eq_left hk,
      Nat.sub_eq_zero_of_le hk, Nat.cast_zero, zero_mul, add_zero, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  · have hNk : N ≤ k := by omega
    have hmin : min (k+1) N = N := Nat.min_eq_right (by omega)
    have hd : (N:ℝ)*μ + ((k+1-N:ℕ):ℝ)*θ ≠ 0 := by
      have := death_pos N (k+1) hμ hθ (by omega)
      simpa only [deathRate, hmin] using ne_of_gt this
    by_cases he : k = N
    · subst k
      simp only [weight, if_neg (show ¬N+1≤N by omega), if_pos (le_refl N),
        Finset.Icc_self, Finset.prod_singleton, deathRate, hmin]
      field_simp
    · have hkN : ¬ k ≤ N := by omega
      rw [weight, if_neg hk, Finset.prod_Icc_succ_top (by omega)]
      rw [weight, if_neg hkN]
      simp only [deathRate, hmin]
      field_simp [hd]
      simp only [mul_comm θ, mul_div_cancel_right₀ _ hd]

end ErlangA.Abandonment.Proof
-- End WeightBasic

-- Begin WeightMoments

open Filter Topology
namespace ErlangA.Abandonment.Proof

lemma weight_shifted_moment_summable (N : ℕ) {lam μ θ : ℝ}
    (hlam : 0 < lam) (hμ : 0 < μ) (hθ : 0 < θ) (r : ℕ) :
    Summable (fun k : ℕ => ((k:ℝ)+1)^r * weight N lam μ θ k) := by
  let δ := min μ θ
  have hδ : 0 < δ := lt_min hμ hθ
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * (2:ℝ)^r * lam / δ)
  apply summable_of_ratio_norm_eventually_le (r := (1/2:ℝ)) (by norm_num)
  filter_upwards [eventually_ge_atTop K] with k hk
  have hw := (weight_pos N k hlam hμ hθ).le
  have hw' := (weight_pos N (k+1) hlam hμ hθ).le
  have hk0 : (0:ℝ) < (k:ℝ)+1 := by positivity
  have hkn : (K:ℝ) ≤ k := by exact_mod_cast hk
  have hb : 2*(2:ℝ)^r*lam ≤ δ*((k:ℝ)+1) := by
    have := (div_lt_iff₀ hδ).mp hK
    nlinarith
  have hd := death_lower N (k+1) μ θ
  have he := weight_succ_balance N k hlam hμ hθ
  have hd' : δ*((k:ℝ)+1)*weight N lam μ θ (k+1) ≤
      lam*weight N lam μ θ k := by
    have := mul_le_mul_of_nonneg_right hd hw'
    simp only [Nat.cast_add, Nat.cast_one] at this
    dsimp [δ]
    nlinarith
  have hp : ((k:ℝ)+2)^r ≤ (2:ℝ)^r*((k:ℝ)+1)^r := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have hb' := mul_le_mul_of_nonneg_right hb hw'
  have hx : (2:ℝ)^r * weight N lam μ θ (k+1) ≤
      (1/2:ℝ)*weight N lam μ θ k := by
    nlinarith
  have hleft := mul_le_mul_of_nonneg_right hp hw'
  have hright := mul_le_mul_of_nonneg_left hx (show 0 ≤ ((k:ℝ)+1)^r by positivity)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  simp only [Nat.cast_add, Nat.cast_one]
  have heq : (k:ℝ)+1+1 = (k:ℝ)+2 := by ring
  rw [heq]
  nlinarith

lemma weight_polynomial_summable (N : ℕ) {lam μ θ : ℝ}
    (hlam : 0 < lam) (hμ : 0 < μ) (hθ : 0 < θ) (r : ℕ) :
    Summable (fun k : ℕ => weight N lam μ θ k * (k:ℝ)^r) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (weight_pos N k hlam hμ hθ).le (by positivity))
    (fun k => ?_) (weight_shifted_moment_summable N hlam hμ hθ r)
  have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (show (0:ℝ)≤k by positivity)
    (show (k:ℝ)≤k+1 by linarith) r) (weight_pos N k hlam hμ hθ).le
  simpa only [mul_comm] using this

lemma weight_summable (N : ℕ) {lam μ θ : ℝ}
    (hlam : 0 < lam) (hμ : 0 < μ) (hθ : 0 < θ) :
    Summable (weight N lam μ θ) := by
  simpa only [pow_zero, mul_one] using weight_polynomial_summable N hlam hμ hθ 0

end ErlangA.Abandonment.Proof
-- End WeightMoments

-- Begin StationaryBasic

namespace ErlangA.Abandonment.Proof

lemma normalizer_pos (N : ℕ) {lam μ θ : ℝ} (hlam : 0 < lam) (hμ : 0 < μ)
    (hθ : 0 < θ) : 0 < ∑' k, weight N lam μ θ k := by
  exact lt_of_lt_of_le (weight_pos N 0 hlam hμ hθ)
    ((weight_summable N hlam hμ hθ).le_tsum 0 (fun k _ => (weight_pos N k hlam hμ hθ).le))

lemma stationary_nonneg (N k : ℕ) {lam μ θ : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) (hθ : 0 < θ) : 0 ≤ stationaryDist N lam μ θ k := by
  exact (div_pos (weight_pos N k hlam hμ hθ) (normalizer_pos N hlam hμ hθ)).le

lemma stationary_hasSum (N : ℕ) {lam μ θ : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) (hθ : 0 < θ) : HasSum (stationaryDist N lam μ θ) 1 := by
  have hh := (weight_summable N hlam hμ hθ).hasSum.div_const (∑' k, weight N lam μ θ k)
  rw [div_self (normalizer_pos N hlam hμ hθ).ne'] at hh
  exact hh

lemma stationary_polynomial_summable (N : ℕ) {lam μ θ : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) (hθ : 0 < θ) (r : ℕ) :
    Summable (fun k : ℕ => stationaryDist N lam μ θ k * (k:ℝ)^r) := by
  have hh := (weight_polynomial_summable N hlam hμ hθ r).div_const (∑' k, weight N lam μ θ k)
  simpa only [stationaryDist, div_mul_eq_mul_div] using hh

lemma stationary_balance (N k : ℕ) {lam μ θ : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) (hθ : 0 < θ) :
    stationaryDist N lam μ θ (k+1) * deathRate N μ θ (k+1) =
      lam * stationaryDist N lam μ θ k := by
  unfold stationaryDist
  rw [div_mul_eq_mul_div, weight_succ_balance N k hlam hμ hθ, mul_div_assoc]

lemma stationary_death_hasSum (N : ℕ) {lam μ θ : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) (hθ : 0 < θ) :
    HasSum (fun k => stationaryDist N lam μ θ k * deathRate N μ θ k) lam := by
  have hh := (stationary_hasSum N hlam hμ hθ).mul_left lam
  simp only [mul_one] at hh
  have hs : HasSum (fun k => stationaryDist N lam μ θ (k+1) * deathRate N μ θ (k+1)) lam := by
    simpa only [stationary_balance N _ hlam hμ hθ] using hh
  rw [← hasSum_nat_add_iff' 1]
  simpa [deathRate] using hs

lemma stationary_first_balance (N : ℕ) {lam μ θ : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) (hθ : 0 < θ) :
    HasSum (fun k => stationaryDist N lam μ θ k * (k:ℝ) * deathRate N μ θ k)
      (lam * ((∑' k, stationaryDist N lam μ θ k * (k:ℝ)) + 1)) := by
  have hm : Summable (fun k => stationaryDist N lam μ θ k * (k:ℝ)) := by
    simpa only [pow_one] using stationary_polynomial_summable N hlam hμ hθ 1
  have hh := (hm.hasSum.add (stationary_hasSum N hlam hμ hθ)).mul_left lam
  have hs : HasSum (fun k => stationaryDist N lam μ θ (k+1) * ((k+1:ℕ):ℝ) *
      deathRate N μ θ (k+1))
      (lam * ((∑' k, stationaryDist N lam μ θ k * (k:ℝ)) + 1)) := by
    convert! hh using 1
    funext k
    have hb := stationary_balance N k hlam hμ hθ
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith
  rw [← hasSum_nat_add_iff' 1]
  simpa only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_mul, sub_zero] using hs

end ErlangA.Abandonment.Proof
-- End StationaryBasic

-- Begin AbandonmentBalance

open scoped BigOperators
namespace ErlangA.Abandonment.Proof

lemma stationary_busy_summable (N : ℕ) {lam μ θ : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) (hθ : 0 < θ) :
    Summable (fun k => stationaryDist N lam μ θ k * (min k N : ℕ)) := by
  have hm : Summable (fun k => stationaryDist N lam μ θ k * (k:ℝ)) := by
    simpa only [pow_one] using stationary_polynomial_summable N hlam hμ hθ 1
  exact Summable.of_nonneg_of_le (fun k => mul_nonneg (stationary_nonneg N k hlam hμ hθ) (by positivity))
    (fun k => mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.min_le_left k N)
      (stationary_nonneg N k hlam hμ hθ)) hm

lemma stationary_wait_summable (N : ℕ) {lam μ θ : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) (hθ : 0 < θ) :
    Summable (fun k => stationaryDist N lam μ θ k * ((k-N:ℕ):ℝ)) := by
  have hm : Summable (fun k => stationaryDist N lam μ θ k * (k:ℝ)) := by
    simpa only [pow_one] using stationary_polynomial_summable N hlam hμ hθ 1
  exact Summable.of_nonneg_of_le (fun k => mul_nonneg (stationary_nonneg N k hlam hμ hθ) (by positivity))
    (fun k => mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le k N)
      (stationary_nonneg N k hlam hμ hθ)) hm

lemma abandonment_wait_identity (N : ℕ) {lam μ θ : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) (hθ : 0 < θ) :
    probAbandon N lam μ θ = (θ/lam) *
      ∑' k, stationaryDist N lam μ θ k * ((k-N:ℕ):ℝ) := by
  have he (n : ℕ) : stationaryDist N lam μ θ (N+n) *
      (((n:ℝ)+1)*θ / ((N:ℝ)*μ+((n:ℝ)+1)*θ)) =
      (θ/lam) * (stationaryDist N lam μ θ (n+(N+1)) * ((n:ℝ)+1)) := by
    have hb := stationary_balance N (N+n) hlam hμ hθ
    have hd : 0 < (N:ℝ)*μ+((n:ℝ)+1)*θ := by positivity
    have hi : min (N+n+1) N = N := Nat.min_eq_right (by omega)
    have hj : N+n+1-N = n+1 := by omega
    simp only [deathRate, hi, hj, Nat.cast_add, Nat.cast_one] at hb
    have hk : N+n+1=n+(N+1) := by omega
    rw [hk] at hb
    field_simp
    nlinarith
  have hs := (stationary_wait_summable N hlam hμ hθ).sum_add_tsum_nat_add (N+1)
  have hz : ∑ k ∈ Finset.range (N+1), stationaryDist N lam μ θ k * ((k-N:ℕ):ℝ) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have : k-N=0 := by have := Finset.mem_range.mp hk; omega
    simp only [this, Nat.cast_zero, mul_zero]
  rw [hz, zero_add] at hs
  unfold probAbandon
  simp_rw [he]
  rw [tsum_mul_left]
  congr 1
  convert hs using 1
  congr 1
  ext n
  have : n+(N+1)-N=n+1 := by omega
  simp only [this, Nat.cast_add, Nat.cast_one]

lemma abandonment_busy_identity (N : ℕ) {lam μ θ : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) (hθ : 0 < θ) :
    probAbandon N lam μ θ = 1 - (μ/lam) *
      ∑' k, stationaryDist N lam μ θ k * (min k N : ℕ) := by
  have hs := ((stationary_busy_summable N hlam hμ hθ).hasSum.mul_left μ).add
    ((stationary_wait_summable N hlam hμ hθ).hasSum.mul_left θ)
  have hd := (stationary_death_hasSum N hlam hμ hθ).tsum_eq
  have he : (fun k => μ*(stationaryDist N lam μ θ k * (min k N : ℕ)) +
      θ*(stationaryDist N lam μ θ k * ((k-N:ℕ):ℝ))) =
      (fun k => stationaryDist N lam μ θ k * deathRate N μ θ k) := by
    funext k
    unfold deathRate
    ring
  rw [he] at hs
  have hbalance := hs.tsum_eq
  rw [hd] at hbalance
  rw [abandonment_wait_identity N hlam hμ hθ]
  field_simp
  nlinarith

end ErlangA.Abandonment.Proof
-- End AbandonmentBalance

-- Begin FluidBasic

namespace ErlangA.Abandonment.Proof

noncomputable def fluidDeath (N μ θ x : ℝ) : ℝ :=
  μ * min x N + θ * max (x - N) 0

noncomputable def equilibrium (N lam μ θ : ℝ) : ℝ :=
  if lam ≤ N * μ then lam / μ else N + (lam - N * μ) / θ

lemma fluidDeath_nat (N k : ℕ) (μ θ : ℝ) :
    fluidDeath N μ θ k = deathRate N μ θ k := by
  unfold fluidDeath deathRate
  rw [Nat.cast_min]
  by_cases h : N ≤ k
  · rw [Nat.cast_sub h, max_eq_left (sub_nonneg.mpr (by exact_mod_cast h))]
    ring
  · rw [Nat.sub_eq_zero_of_le (le_of_not_ge h), Nat.cast_zero,
      max_eq_right (sub_nonpos.mpr (by exact_mod_cast le_of_not_ge h))]
    ring

lemma equilibrium_nonneg {N lam μ θ : ℝ} (hN : 0 ≤ N) (hl : 0 < lam)
    (hm : 0 < μ) (ht : 0 < θ) : 0 ≤ equilibrium N lam μ θ := by
  unfold equilibrium
  split_ifs with h
  · positivity
  · have : 0 ≤ lam - N * μ := sub_nonneg.mpr (le_of_not_ge h)
    positivity

lemma equilibrium_death {N lam μ θ : ℝ} (hm : 0 < μ) (ht : 0 < θ) :
    fluidDeath N μ θ (equilibrium N lam μ θ) = lam := by
  unfold equilibrium fluidDeath
  split_ifs with h
  · have hle : lam / μ ≤ N := (div_le_iff₀ hm).2 h
    rw [min_eq_left hle, max_eq_right (sub_nonpos.mpr hle)]
    field_simp
    ring
  · have hl : 0 ≤ (lam - N * μ) / θ := div_nonneg (sub_nonneg.mpr (le_of_not_ge h)) ht.le
    rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    field_simp
    ring

lemma equilibrium_cap {N lam μ θ : ℝ} (hl : 0 < lam) (hm : 0 < μ)
    (ht : 0 < θ) :
    1 - μ / lam * min (equilibrium N lam μ θ) N = max 0 (1 - N * μ / lam) := by
  unfold equilibrium
  split_ifs with h
  · have hle : lam / μ ≤ N := (div_le_iff₀ hm).2 h
    have hr : 1 - N * μ / lam ≤ 0 := by
      have : (1:ℝ) ≤ N * μ / lam := (le_div_iff₀ hl).2 (by simpa using h)
      linarith
    rw [min_eq_left hle, max_eq_left hr]
    field_simp
    ring
  · have hl' : 0 ≤ (lam - N * μ) / θ := div_nonneg (sub_nonneg.mpr (le_of_not_ge h)) ht.le
    have hr : 0 ≤ 1 - N * μ / lam := by
      have := (div_le_one hl).2 (le_of_not_ge h)
      linarith
    rw [min_eq_right (by linarith), max_eq_right hr]
    ring

lemma fluidDeath_sub_lower {N μ θ δ x y : ℝ} (hm : δ ≤ μ) (ht : δ ≤ θ)
    (hxy : x ≤ y) : δ * (y - x) ≤ fluidDeath N μ θ y - fluidDeath N μ θ x := by
  unfold fluidDeath
  by_cases hx : x ≤ N <;> by_cases hy : y ≤ N
  · rw [min_eq_left hx, min_eq_left hy, max_eq_right (sub_nonpos.mpr hx),
      max_eq_right (sub_nonpos.mpr hy)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hxy)]
  · rw [min_eq_left hx, min_eq_right (le_of_not_ge hy),
      max_eq_right (sub_nonpos.mpr hx), max_eq_left (sub_nonneg.mpr (le_of_not_ge hy))]
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hx),
      mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr (le_of_not_ge hy))]
  · exact False.elim (hx (hxy.trans hy))
  · rw [min_eq_right (le_of_not_ge hx), min_eq_right (le_of_not_ge hy),
      max_eq_left (sub_nonneg.mpr (le_of_not_ge hx)),
      max_eq_left (sub_nonneg.mpr (le_of_not_ge hy))]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hxy)]

lemma fluidDeath_strong {N μ θ δ x y : ℝ} (hm : δ ≤ μ) (ht : δ ≤ θ) :
    δ * (x-y)^2 ≤ (x-y) * (fluidDeath N μ θ x - fluidDeath N μ θ y) := by
  rcases le_total x y with h | h
  · have hle := mul_le_mul_of_nonneg_left (fluidDeath_sub_lower (N := N) hm ht h)
      (sub_nonneg.mpr h)
    nlinarith
  · have hle := mul_le_mul_of_nonneg_left (fluidDeath_sub_lower (N := N) hm ht h)
      (sub_nonneg.mpr h)
    nlinarith

lemma cap_abs_sub_le (N x y : ℝ) : |min x N - min y N| ≤ |x-y| := by
  simpa [Real.dist_eq] using (LipschitzWith.id.min_const N).dist_le_mul x y

end ErlangA.Abandonment.Proof
-- End FluidBasic

-- Begin WeightedVariance

open scoped BigOperators

namespace ErlangA.Abandonment.Proof

lemma weighted_variance {w a : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k)
    (h0 : HasSum w 1) (h1 : Summable (fun k => w k * a k))
    (h2 : Summable (fun k => w k * (a k)^2)) :
    (∑' k, w k * a k)^2 ≤ ∑' k, w k * (a k)^2 := by
  let m := ∑' k, w k * a k
  have hs : HasSum (fun k => w k * (a k - m)^2)
      ((∑' k, w k * (a k)^2) - m^2) := by
    convert! (h2.hasSum.sub (h1.hasSum.mul_left (2*m))).add (h0.mul_left (m^2)) using 1
    · funext k; ring
    · dsimp [m]; ring
  have hn : 0 ≤ ∑' k, w k * (a k-m)^2 := tsum_nonneg (fun k => mul_nonneg (hw k) (sq_nonneg _))
  rw [hs.tsum_eq] at hn
  exact sub_nonneg.mp hn

lemma summable_weighted_of_quadratic {w : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k)
    (h0 : Summable w) (h2 : Summable (fun k => w k * (k:ℝ)^2))
    {a : ℕ → ℝ} {C : ℝ} (_hC : 0 ≤ C)
    (ha : ∀ k, |a k| ≤ C * (1+(k:ℝ)^2)) : Summable (fun k => w k*a k) := by
  apply Summable.of_norm_bounded ((h0.add h2).mul_left C)
  intro k
  have h := mul_le_mul_of_nonneg_left (ha k) (hw k)
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw k)] using
    h.trans_eq (by ring)

end ErlangA.Abandonment.Proof
-- End WeightedVariance

-- Begin WeightedDeviation

namespace ErlangA.Abandonment.Proof

lemma centered_square_summable {w : ℕ → ℝ} (h0 : Summable w)
    (h1 : Summable (fun k => w k*(k:ℝ)))
    (h2 : Summable (fun k => w k*(k:ℝ)^2)) (κ : ℝ) :
    Summable (fun k => w k*((k:ℝ)-κ)^2) := by
  convert! (h2.sub (h1.mul_left (2*κ))).add (h0.mul_left (κ^2)) using 1
  funext k; ring

lemma weighted_deviation_square {w d : ℕ → ℝ} {lam κ δ : ℝ}
    (hw : ∀ k, 0 ≤ w k) (h0 : HasSum w 1)
    (h1 : Summable (fun k => w k*(k:ℝ)))
    (h2 : Summable (fun k => w k*(k:ℝ)^2))
    (hd : HasSum (fun k => w k*d k) lam)
    (hkd : HasSum (fun k => w k*(k:ℝ)*d k)
      (lam*((∑' k,w k*(k:ℝ))+1)))
    (hδ : 0 < δ)
    (hstrong : ∀ k : ℕ, δ*((k:ℝ)-κ)^2 ≤ ((k:ℝ)-κ)*(d k-lam)) :
    (∑' k,w k*((k:ℝ)-κ)^2) ≤ lam/δ := by
  have hs := centered_square_summable h0.summable h1 h2 κ
  have hc : HasSum (fun k => w k*((k:ℝ)-κ)*(d k-lam)) lam := by
    convert! ((hkd.sub (hd.mul_left κ)).sub (h1.hasSum.mul_left lam)).add
      (h0.mul_left (κ*lam)) using 1
    · funext k; ring
    · ring
  have hle : δ*(∑' k,w k*((k:ℝ)-κ)^2) ≤ lam := by
    rw [← hc.tsum_eq, ← tsum_mul_left]
    apply Summable.tsum_le_tsum _ (hs.mul_left δ) hc.summable
    intro k
    nlinarith [mul_le_mul_of_nonneg_left (hstrong k) (hw k)]
  exact (le_div_iff₀ hδ).2 (by simpa [mul_comm] using hle)

lemma weighted_lipschitz_square {w f : ℕ → ℝ} {κ : ℝ}
    (hw : ∀ k, 0 ≤ w k) (h0 : HasSum w 1)
    (hs : Summable (fun k => w k*((k:ℝ)-κ)^2))
    (hf : ∀ k, |f k| ≤ |(k:ℝ)-κ|) :
    Summable (fun k => w k*f k) ∧
    (∑' k,w k*f k)^2 ≤ ∑' k,w k*((k:ℝ)-κ)^2 := by
  have hsq : ∀ k, (f k)^2 ≤ ((k:ℝ)-κ)^2 := fun k => (sq_le_sq).2 (hf k)
  have hs2 : Summable (fun k => w k*(f k)^2) := by
    apply Summable.of_norm_bounded hs
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw k) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hsq k) (hw k)
  have hs1 : Summable (fun k => w k*f k) := by
    apply Summable.of_norm_bounded (h0.summable.add hs)
    intro k
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw k)]
    have hbound : |f k| ≤ 1+((k:ℝ)-κ)^2 := by
      have ha := sq_nonneg (|f k|-1)
      have he := sq_abs (f k)
      nlinarith [hsq k]
    nlinarith [mul_le_mul_of_nonneg_left hbound (hw k)]
  refine ⟨hs1, (weighted_variance hw h0 hs1 hs2).trans ?_⟩
  exact hs2.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hsq k) (hw k)) hs

end ErlangA.Abandonment.Proof
-- End WeightedDeviation

-- Begin MomentApproximation

namespace ErlangA.Abandonment.Proof

lemma cap_mean_square {w : ℕ → ℝ} {N : ℕ} {lam μ θ δ : ℝ}
    (hw : ∀ k, 0 ≤ w k) (h0 : HasSum w 1)
    (h1 : Summable (fun k => w k*(k:ℝ)))
    (h2 : Summable (fun k => w k*(k:ℝ)^2))
    (hd : HasSum (fun k => w k*deathRate N μ θ k) lam)
    (hkd : HasSum (fun k => w k*(k:ℝ)*deathRate N μ θ k)
      (lam*((∑' k,w k*(k:ℝ))+1)))
    (hm : 0 < μ) (ht : 0 < θ) (hδ : 0 < δ) (hδm : δ ≤ μ) (hδt : δ ≤ θ) :
    ((∑' k,w k*min (k:ℝ) (N:ℝ))-min (equilibrium N lam μ θ) N)^2 ≤ lam/δ := by
  let κ := equilibrium N lam μ θ
  have hs := centered_square_summable h0.summable h1 h2 κ
  have hb : (∑' k,w k*((k:ℝ)-κ)^2) ≤ lam/δ := by
    apply weighted_deviation_square hw h0 h1 h2 hd hkd hδ
    intro k
    simpa only [κ, fluidDeath_nat, equilibrium_death hm ht] using
      (fluidDeath_strong (N := (N:ℝ)) (x := (k:ℝ)) (y := κ) hδm hδt)
  obtain ⟨hfs,hfv⟩ := weighted_lipschitz_square hw h0 hs (fun k => cap_abs_sub_le (N:ℝ) (k:ℝ) κ)
  have hcap : Summable (fun k => w k*min (k:ℝ) (N:ℝ)) := by
    convert! hfs.add (h0.summable.mul_right (min κ (N:ℝ))) using 1
    funext k; ring
  have he : (∑' k,w k*(min (k:ℝ) (N:ℝ)-min κ (N:ℝ))) =
      (∑' k,w k*min (k:ℝ) (N:ℝ))-min κ (N:ℝ) := by
    have hh := hcap.hasSum.sub (h0.mul_right (min κ (N:ℝ)))
    have hh' : HasSum (fun k => w k*(min (k:ℝ) (N:ℝ)-min κ (N:ℝ)))
        ((∑' k,w k*min (k:ℝ) (N:ℝ))-min κ (N:ℝ)) := by
      convert! hh using 1
      · funext k; ring
      · ring
    exact hh'.tsum_eq
  rw [he] at hfv
  exact hfv.trans hb

lemma abandonment_squared_error {w : ℕ → ℝ} {N : ℕ} {lam μ θ δ a : ℝ}
    (hw : ∀ k, 0 ≤ w k) (h0 : HasSum w 1)
    (h1 : Summable (fun k => w k*(k:ℝ)))
    (h2 : Summable (fun k => w k*(k:ℝ)^2))
    (hd : HasSum (fun k => w k*deathRate N μ θ k) lam)
    (hkd : HasSum (fun k => w k*(k:ℝ)*deathRate N μ θ k)
      (lam*((∑' k,w k*(k:ℝ))+1)))
    (hl : 0 < lam) (hm : 0 < μ) (ht : 0 < θ)
    (hδ : 0 < δ) (hδm : δ ≤ μ) (hδt : δ ≤ θ)
    (ha : a = 1 - μ/lam*(∑' k,w k*min (k:ℝ) (N:ℝ))) :
    (a-max 0 (1-(N:ℝ)*μ/lam))^2 ≤ (μ^2/δ)/lam := by
  have h := mul_le_mul_of_nonneg_left
    (cap_mean_square hw h0 h1 h2 hd hkd hm ht hδ hδm hδt) (sq_nonneg (μ/lam))
  rw [ha, ← equilibrium_cap hl hm ht]
  convert! h using 1
  · ring
  · field_simp [ne_of_gt hl, ne_of_gt hδ]

end ErlangA.Abandonment.Proof
-- End MomentApproximation

-- Begin NativeEstimate

namespace ErlangA.Abandonment.Proof

lemma native_squared_error (N : ℕ) {lam μ θ δ : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) (hθ : 0 < θ) (hδ : 0 < δ) (hδμ : δ ≤ μ) (hδθ : δ ≤ θ) :
    (probAbandon N lam μ θ - max 0 (1-(N:ℝ)*μ/lam))^2 ≤ (μ^2/δ)/lam := by
  apply abandonment_squared_error (fun k => stationary_nonneg N k hlam hμ hθ)
    (stationary_hasSum N hlam hμ hθ)
    (by simpa only [pow_one] using stationary_polynomial_summable N hlam hμ hθ 1)
    (stationary_polynomial_summable N hlam hμ hθ 2)
    (stationary_death_hasSum N hlam hμ hθ)
    (stationary_first_balance N hlam hμ hθ) hlam hμ hθ hδ hδμ hδθ
  simpa only [Nat.cast_min] using abandonment_busy_identity N hlam hμ hθ

end ErlangA.Abandonment.Proof
-- End NativeEstimate

-- Begin FluidLimit

open Filter Topology

namespace ErlangA.Abandonment.Proof

noncomputable def loadLimit (r : ENNReal) : ℝ := 1 - (min r⁻¹ 1).toReal

lemma continuous_loadLimit : Continuous loadLimit := by
  apply continuous_iff_continuousAt.2
  intro r
  apply continuousAt_const.sub
  apply (ENNReal.continuousAt_toReal _).comp
  · exact continuousAt_inv.min continuousAt_const
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)

lemma loadLimit_eq (r : ENNReal) :
    loadLimit r = if r ≤ 1 then 0 else (1-r⁻¹).toReal := by
  unfold loadLimit
  split_ifs with h
  · rw [min_eq_right (ENNReal.one_le_inv.2 h)]
    simp
  · have hi : r⁻¹ ≤ 1 := ENNReal.inv_le_one.2 (le_of_not_ge h)
    rw [min_eq_left hi, ENNReal.toReal_sub_of_le hi ENNReal.one_ne_top]
    simp

lemma loadLimit_ofReal {r : ℝ} (hr : 0 < r) :
    loadLimit (ENNReal.ofReal r) = max 0 (1-r⁻¹) := by
  unfold loadLimit
  have hi : (ENNReal.ofReal r)⁻¹ ≠ ⊤ := by
    simp [ENNReal.ofReal_pos.mpr hr |>.ne']
  rw [ENNReal.toReal_min hi ENNReal.one_ne_top, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hr.le, ENNReal.toReal_one]
  rcases le_total r⁻¹ 1 with h | h
  · rw [min_eq_left h, max_eq_right (sub_nonneg.mpr h)]
  · rw [min_eq_right h, max_eq_left (sub_nonpos.mpr h)]
    ring

lemma fluid_load_tendsto (μ : ℝ) (lam : ℕ → ℝ) (hm : 0 < μ)
    (hl : ∀ N, 1 ≤ N → 0 < lam N) (r : ENNReal)
    (hr : Tendsto (fun N : ℕ => ENNReal.ofReal (lam N / ((N:ℝ)*μ))) atTop (𝓝 r)) :
    Tendsto (fun N : ℕ => max 0 (1-(N:ℝ)*μ/lam N)) atTop
      (𝓝 (if r≤1 then 0 else (1-r⁻¹).toReal)) := by
  rw [← loadLimit_eq]
  apply (continuous_loadLimit.tendsto r |>.comp hr).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  simp only [Function.comp_apply]
  rw [loadLimit_ofReal (div_pos (hl N hN) (mul_pos hn hm))]
  simp only [inv_div]

lemma convergence_of_squared_error {a b lam : ℕ → ℝ} {C L : ℝ}
    (_hC : 0 ≤ C) (hl : Tendsto lam atTop atTop) (hb : Tendsto b atTop (𝓝 L))
    (he : ∀ᶠ n in atTop, (a n-b n)^2 ≤ C/lam n) : Tendsto a atTop (𝓝 L) := by
  have hc : Tendsto (fun n => C/lam n) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hl)
  have hs : Tendsto (fun n => (a n-b n)^2) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun n => sq_nonneg _)) he hc
  have ha : Tendsto (fun n => |a n-b n|) atTop (𝓝 0) := by
    have hh : Tendsto (fun n => Real.sqrt ((a n-b n)^2)) atTop (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hs
    simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hh
  have hd : Tendsto (fun n => a n-b n) atTop (𝓝 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using ha)
  simpa only [sub_add_cancel, zero_add] using hd.add hb

end ErlangA.Abandonment.Proof
-- End FluidLimit

-- Begin ApproximationLimit

open Filter Topology

namespace ErlangA.Abandonment.Proof

lemma abandonment_limit_of_bound (μ θ : ℝ) (lam θN a : ℕ → ℝ)
    (hm : 0 < μ) (ht : 0 < θ)
    (hl : ∀ N, 1 ≤ N → 0 < lam N) (hlinfty : Tendsto lam atTop atTop)
    (htlim : Tendsto θN atTop (𝓝 θ))
    (hbound : ∀ N : ℕ, 1 ≤ N → ∀ δ : ℝ, 0 < δ → δ ≤ μ → δ ≤ θN N →
      (a N-max 0 (1-(N:ℝ)*μ/lam N))^2 ≤ (μ^2/δ)/lam N)
    (r : ENNReal)
    (hr : Tendsto (fun N : ℕ => ENNReal.ofReal (lam N / ((N:ℝ)*μ))) atTop (𝓝 r)) :
    Tendsto a atTop (𝓝 (if r≤1 then 0 else (1-r⁻¹).toReal)) := by
  let δ := min μ (θ/2)
  have hd : 0 < δ := lt_min hm (by positivity)
  apply convergence_of_squared_error (C := μ^2/δ) (by positivity) hlinfty
    (fluid_load_tendsto μ lam hm hl r hr)
  have he : ∀ᶠ N in atTop, θ/2 < θN N := (tendsto_order.1 htlim).1 _ (by linarith)
  filter_upwards [he, eventually_ge_atTop 1] with N hθ hN
  exact hbound N hN δ hd (min_le_left _ _) ((min_le_right _ _).trans hθ.le)

end ErlangA.Abandonment.Proof
-- End ApproximationLimit

-- Begin RootAssembly
open Filter Topology

namespace ErlangA.Abandonment

/-- **Theorem 1**, p. 215. Standing assumptions of §4 (p. 215): `μ_N ≡ μ > 0`, `λ_N > 0` with
`λ_N → ∞`, `θ_N > 0` with `θ_N → θ ∈ (0, ∞)`. If `ρ_N = λ_N/(Nμ) → ρ_∞ ∈ [0, ∞]` (convergence
in `ℝ≥0∞`), then `P_N{Ab} → 0` when `ρ_∞ ≤ 1` and `P_N{Ab} → 1 − 1/ρ_∞` when `ρ_∞ > 1`
(with `1 − 1/∞ = 1`). -/
theorem theorem_1 (μ θ : ℝ) (lam θN : ℕ → ℝ) (hμ : 0 < μ)
    (hlam : ∀ N : ℕ, 1 ≤ N → 0 < lam N) (hlam_infty : Tendsto lam atTop atTop)
    (hθN : ∀ N : ℕ, 1 ≤ N → 0 < θN N) (hθ : 0 < θ) (hθlim : Tendsto θN atTop (𝓝 θ))
    (ρinf : ENNReal)
    (hρ : Tendsto (fun N : ℕ => ENNReal.ofReal (lam N / ((N : ℝ) * μ))) atTop (𝓝 ρinf)) :
    Tendsto (fun N : ℕ => probAbandon N (lam N) μ (θN N)) atTop
      (𝓝 (if ρinf ≤ 1 then 0 else (1 - ρinf⁻¹).toReal)) := by
  apply Proof.abandonment_limit_of_bound μ θ lam θN
    (fun N => probAbandon N (lam N) μ (θN N)) hμ hθ hlam hlam_infty hθlim
  · intro N hN δ hδ hδμ hδθ
    exact Proof.native_squared_error N (hlam N hN) hμ (hθN N hN) hδ hδμ hδθ
  · exact hρ

end ErlangA.Abandonment
-- End RootAssembly

-- Begin Solution
open Filter Topology ErlangA.Abandonment

theorem solution (μ θ : ℝ) (lam θN : ℕ → ℝ) (hμ : 0 < μ)
    (hlam : ∀ N : ℕ, 1 ≤ N → 0 < lam N) (hlam_infty : Tendsto lam atTop atTop)
    (hθN : ∀ N : ℕ, 1 ≤ N → 0 < θN N) (hθ : 0 < θ) (hθlim : Tendsto θN atTop (𝓝 θ))
    (ρinf : ENNReal)
    (hρ : Tendsto (fun N : ℕ => ENNReal.ofReal (lam N / ((N : ℝ) * μ))) atTop (𝓝 ρinf)) :
    Tendsto (fun N : ℕ => probAbandon N (lam N) μ (θN N)) atTop
      (𝓝 (if ρinf ≤ 1 then 0 else (1 - ρinf⁻¹).toReal)) := by
  exact ErlangA.Abandonment.theorem_1 μ θ lam θN hμ hlam hlam_infty hθN hθ hθlim ρinf hρ

-- End Solution
