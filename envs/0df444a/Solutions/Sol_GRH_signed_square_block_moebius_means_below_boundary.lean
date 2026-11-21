-- Prove2me | solution 1 for GRH.signed_square_block_moebius_means_below_boundary
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pragyan
-- created : 2026-11-21T04:20:20.986254+00:00
-- url     : https://prove2.me/submissions/fa505545-6174-4cfb-8c22-6fa0ea216c3c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_NymanBeurling_finite_remainder_zero_obstruction
import Theorems.Thm_NymanBeurling_arbitrarily_small_remainder_certificates
import Theorems.Thm_GRH_uniform_mobius_liouville_progressions_of_zero_free
import Theorems.Thm_GRH_reduced_liouville_harmonic_power_decay
import Theorems.Thm_GRH_reduced_moebius_harmonic_le_of_liouville_harmonic_le
import Definitions.Def_GRH_MoebiusBilinear
import Theorems.Thm_GRH_nonprincipal_corrected_prime_ramp_upper_windows

set_option autoImplicit false
open scoped BigOperators
open Finset ArithmeticFunction Filter Asymptotics

namespace MobiusProgression

abbrev mu : ArithmeticFunction ℝ := ArithmeticFunction.moebius
abbrev zeta : ArithmeticFunction ℝ := ArithmeticFunction.zeta

noncomputable def short (u : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun k => if k ≤ u then (ArithmeticFunction.moebius k : ℝ) else 0, by simp⟩

-- Two factors above the square-root cutoff cannot have product at most n.
private theorem tail_square_zero (n k : ℕ) (hk : k ≤ n) :
    ((mu - short n.sqrt) * (mu - short n.sqrt)) k = 0 := by
  rw [ArithmeticFunction.mul_apply]
  refine sum_eq_zero fun p hp => ?_
  obtain ⟨heq, _⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have hsmall : p.1 ≤ n.sqrt ∨ p.2 ≤ n.sqrt := by
    by_contra! h
    have hh := Nat.mul_le_mul h.1 h.2
    have hn := Nat.lt_succ_sqrt n
    omega
  change ((ArithmeticFunction.moebius p.1 : ℝ) - (if p.1 ≤ n.sqrt then _ else 0)) *
      ((ArithmeticFunction.moebius p.2 : ℝ) - (if p.2 ≤ n.sqrt then _ else 0)) = 0
  rcases hsmall with h | h <;> simp [h]

theorem truncated_coefficient (n k : ℕ) (hk : k ≤ n) :
    mu k = short n.sqrt k + short n.sqrt k - (short n.sqrt * (short n.sqrt * zeta)) k := by
  let s := short n.sqrt
  have hinv : mu * zeta = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
  have halg : (mu - s) * (mu - s) * zeta = mu - s - s + s * (s * zeta) := by
    calc
      _ = mu * (mu * zeta) - s * (mu * zeta) - s * (mu * zeta) + s * (s * zeta) := by ring
      _ = _ := by rw [hinv]; simp
  have hzero : ((mu - s) * (mu - s) * zeta) k = 0 := by
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    refine sum_eq_zero fun d hd => tail_square_zero n d ?_
    obtain ⟨hdvd,hk0⟩ := Nat.mem_divisors.mp hd
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hdvd).trans hk
  rw [halg] at hzero
  change mu k - s k - s k + (s * (s * zeta)) k = 0 at hzero
  change mu k = s k + s k - (s * (s * zeta)) k
  linarith

-- Weighted version of the divisor-pair reindexing in Mathlib's
-- ArithmeticFunction.sum_Ioc_mul_eq_sum_sum. The weight need not be multiplicative.
private theorem weighted_convolution (n : ℕ) (w : ℕ → ℝ) (f g : ArithmeticFunction ℝ) :
    (∑ k ∈ Ioc 0 n, w k * (f * g) k) =
    ∑ d ∈ Ioc 0 n, f d * ∑ e ∈ Ioc 0 (n / d), w (d * e) * g e := by
  classical
  let box := (Ioc 0 n) ×ˢ (Ioc 0 n)
  calc
    _ = ∑ k ∈ Ioc 0 n, ∑ p ∈ box, if p.1 * p.2 = k then
          w (p.1 * p.2) * (f p.1 * g p.2) else 0 := by
      refine sum_congr rfl fun k hk => ?_
      obtain ⟨hk0, hkn⟩ := mem_Ioc.mp hk
      rw [ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_eq_prod_filter_of_le hk0.ne' hkn,
        mul_sum, ← sum_filter]
      refine sum_congr rfl fun p hp => ?_
      rw [(mem_filter.mp hp).2]
    _ = ∑ p ∈ box, if p.1 * p.2 ≤ n then w (p.1 * p.2) * (f p.1 * g p.2) else 0 := by
      rw [sum_comm]
      refine sum_congr rfl fun p hp => ?_
      have hp' := mem_product.mp hp
      have hpos := Nat.mul_pos (mem_Ioc.mp hp'.1).1 (mem_Ioc.mp hp'.2).1
      simp [mem_Ioc, hpos]
    _ = _ := by
      rw [show box = _ from rfl, sum_product]
      refine sum_congr rfl fun d hd => ?_
      have hd0 := (mem_Ioc.mp hd).1
      rw [mul_sum]
      have heq : (Ioc 0 (n / d)) = (Ioc 0 n).filter (fun e => d * e ≤ n) := by
        ext e
        simp only [mem_Ioc, mem_filter]
        rw [Nat.le_div_iff_mul_le hd0, Nat.mul_comm e d]
        constructor
        · rintro ⟨he, h⟩
          exact ⟨⟨he, ((Nat.le_div_iff_mul_le hd0).mpr (by simpa [Nat.mul_comm] using h)).trans
            (Nat.div_le_self n d)⟩, h⟩
        · rintro ⟨⟨he, _⟩, h⟩
          exact ⟨he, h⟩
      rw [heq, sum_filter]
      apply sum_congr rfl
      intro e _
      dsimp only
      split_ifs <;> ring

private theorem truncate_sum (N u : ℕ) (hu : u ≤ N) (F : ℕ → ℝ) :
    (∑ k ∈ Ioc 0 N, short u k * F k) = ∑ k ∈ Ioc 0 u, mu k * F k := by
  calc
    _ = ∑ k ∈ Ioc 0 u, short u k * F k := by
      symm
      apply sum_subset
      · intro k hk
        exact mem_Ioc.mpr ⟨(mem_Ioc.mp hk).1, (mem_Ioc.mp hk).2.trans hu⟩
      · intro k hk hk'
        have h : ¬ k ≤ u := fun h => hk' (mem_Ioc.mpr ⟨(mem_Ioc.mp hk).1,h⟩)
        simp [short, h]
    _ = _ := by
      refine sum_congr rfl fun k hk => ?_
      simp [short, (mem_Ioc.mp hk).2, mu]

noncomputable def residueWeight {q : ℕ} (a : ZMod q) (k : ℕ) : ℝ :=
  if (k : ZMod q) = a then 1 else 0

noncomputable def bilinear {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 n.sqrt, mu d * ∑ e ∈ Ioc 0 n.sqrt, mu e *
    (((Ioc 0 (n / (d * e))).filter (fun r => ((d * e * r : ℕ) : ZMod q) = a)).card : ℝ)

theorem reindex_bilinear {q : ℕ} (a : ZMod q) (n : ℕ) :
    (∑ k ∈ Finset.Ioc 0 n, residueWeight a k * (short n.sqrt * (short n.sqrt * zeta)) k) =
    bilinear a n := by
  classical
  unfold bilinear
  rw [weighted_convolution, truncate_sum n _ (Nat.sqrt_le_self n)]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' := Finset.mem_Ioc.mp hd
  have hu : n.sqrt ≤ n / d := (Nat.le_div_iff_mul_le hd'.1).mpr <|
    (Nat.mul_le_mul_left n.sqrt hd'.2).trans (Nat.sqrt_le n)
  apply congrArg (fun x : ℝ => mu d * x)
  rw [weighted_convolution (n / d) (fun k => residueWeight a (d * k)), truncate_sum _ _ hu]
  refine Finset.sum_congr rfl fun e _ => ?_
  apply congrArg (fun x : ℝ => mu e * x)
  rw [Nat.div_div_eq_div_mul, Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr0 := (Finset.mem_Ioc.mp hr).1.ne'
  simp only [residueWeight, zeta, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne hr0, Nat.cast_one, mul_one, Nat.mul_assoc]

noncomputable def partialSum {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  ∑ k ∈ Ioc 0 n, mu k * residueWeight a k

theorem weighted_identity {q : ℕ} (a : ZMod q) (n : ℕ) :
    partialSum a n = 2 * partialSum a n.sqrt - bilinear a n := by
  unfold partialSum
  rw [← reindex_bilinear, ← truncate_sum n _ (Nat.sqrt_le_self n)]
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun k hk => ?_
  rw [truncated_coefficient n k (mem_Ioc.mp hk).2]
  ring

private theorem parent_sum {q : ℕ} (a : ZMod q) (n : ℕ) :
    (∑ k ∈ range (n + 1),
      if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0) = partialSum a n := by
  classical
  have hr : range (n + 1) = insert 0 (Ioc 0 n) := by
    ext k
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  rw [hr, sum_insert (by simp)]
  have hz : (ArithmeticFunction.moebius 0 : ℝ) = 0 := by simp
  simp only [hz, ite_self, zero_add]
  refine sum_congr rfl fun k _ => ?_
  simp only [residueWeight, mu, ArithmeticFunction.intCoe_apply]
  split_ifs <;> simp_all

private theorem partialSum_abs_le {q : ℕ} (a : ZMod q) (u : ℕ) :
    |partialSum a u| ≤ (u : ℝ) := by
  unfold partialSum
  calc
    _ ≤ ∑ k ∈ Ioc 0 u, |mu k * residueWeight a k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Ioc 0 u, (1 : ℝ) := by
      refine sum_le_sum fun k _ => ?_
      have hmu : |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))
      by_cases h : (k : ZMod q) = a <;> simp [residueWeight, h, mu, hmu]
    _ = _ := by simp

theorem short_bound {q : ℕ} (a : ZMod q) (n : ℕ) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) ≤ σ) : |partialSum a n.sqrt| ≤ ((n : ℝ) + 1) ^ σ := by
  calc
    _ ≤ (n.sqrt : ℝ) := partialSum_abs_le a n.sqrt
    _ ≤ Real.sqrt ((n : ℝ) + 1) := by
      apply (Real.le_sqrt (by positivity) (by positivity)).mpr
      have h : (n.sqrt : ℝ) ^ 2 ≤ n := by exact_mod_cast Nat.sqrt_le' n
      linarith
    _ ≤ _ := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by simp) hhalf

theorem reduction {q : ℕ} (a : ZMod q) (σ : ℝ) (hhalf : (1 / 2 : ℝ) ≤ σ)
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |bilinear a n| ≤ C * ((n : ℝ) + 1) ^ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |∑ k ∈ range (n + 1), if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0|
        ≤ C * ((n : ℝ) + 1) ^ σ := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨2 + C, by positivity, fun n => ?_⟩
  rw [parent_sum, weighted_identity]
  calc
    _ ≤ |2 * partialSum a n.sqrt| + |bilinear a n| := abs_sub _ _
    _ = 2 * |partialSum a n.sqrt| + |bilinear a n| := by rw [abs_mul]; norm_num
    _ ≤ 2 * (((n : ℝ) + 1) ^ σ) + C * ((n : ℝ) + 1) ^ σ :=
      add_le_add (mul_le_mul_of_nonneg_left (short_bound a n σ hhalf) (by norm_num)) (h n)
    _ = _ := by ring

end MobiusProgression

/-!
# Signed square-block reduction via analytic prime-ramp windows

Analytic window argument adapted from marozols’s Apache-2.0 Prove2Me
submission 3b624c39-dee9-49c9-9609-80039f047978. The principal zero exclusion
uses the finite-certificate argument from e87e9854-dba7-4bb6-9fe7-e23f23a0a723.
Möbius truncation follows meadowlark’s 509e229b-7ae5-4fe8-b643-d32c7895621a
and Helfgott–Thompson §2, doi:10.1007/s40993-022-00408-8.

This proof uses our earlier real-moment and pole argument for the rational
prime ramp, and extends it to simple real poles with positive residues. A
nonprincipal L-function multiplied by its reflected conjugate packages all
the twisted poles into one entire factor. Its half log derivative creates
the real part of the corrected von Mangoldt ramp. The rational arithmetic
input is imported directly so no zero-free reduction depends on itself.

The motivating window criterion is from Levent Alpöge's 20 November 2026
release, `Deduction.zeroFree_of_rpow_window`. <https://alpo.ge/remark.pdf>
-/

set_option autoImplicit false

open Real Set Filter MeasureTheory Topology

namespace MasulloDirichletRamp

/-- Normalized exponential moment on the positive half-line. -/
noncomputable def gammaMoment (a : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  u^n * Real.exp (-(a*u)) / (n.factorial : ℝ)

theorem gammaMoment_nonneg (a : ℝ) (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ gammaMoment a n u := by
  unfold gammaMoment
  positivity

theorem gammaMoment_integrable {a : ℝ} (ha : 0 < a) (n : ℕ) :
    IntegrableOn (gammaMoment a n) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n:ℝ))
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) zero_lt_one ha
  unfold gammaMoment
  simpa only [IntegrableOn, Real.rpow_one, Real.rpow_natCast, neg_mul] using
    h.div_const (n.factorial : ℝ)

private theorem gammaMoment_mass {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (∫ u in Ioi (0:ℝ), gammaMoment a n u) = 1/a^(n+1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n:ℝ)+1) (by positivity) ha
  simp only [Real.Gamma_nat_eq_factorial, add_sub_cancel_right, Real.rpow_natCast] at h
  have hp : 0 < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hcast : (n:ℝ)+1 = ((n+1:ℕ):ℝ) := by simp
  rw [hcast] at h
  simp only [Real.rpow_natCast] at h
  simp [gammaMoment, integral_div, h, one_div, inv_pow, hp.ne']

theorem exp_mul_gammaMoment (a r : ℝ) (n : ℕ) (u : ℝ) :
    Real.exp (r*u) * gammaMoment a n u = gammaMoment (a-r) n u := by
  unfold gammaMoment
  calc
    _ = u^n * (Real.exp (r*u) * Real.exp (-(a*u))) / (n.factorial : ℝ) := by ring
    _ = _ := by rw [← Real.exp_add, show r*u+(-(a*u)) = -((a-r)*u) by ring]

/-- Two exponential tilts control the moments outside a scale interval. -/
theorem gammaMoment_tail_le {a r U V : ℝ} (hr : 0 < r) (ha : r < a) (n : ℕ) :
    (∫ u in Ioi (0:ℝ) \ Icc U V, gammaMoment a n u) ≤
      Real.exp (r*U)/(a+r)^(n+1) + Real.exp (-r*V)/(a-r)^(n+1) := by
  let S := Ioi (0:ℝ) \ Icc U V
  let F (u : ℝ) := Real.exp (r*U)*gammaMoment (a+r) n u +
    Real.exp (-r*V)*gammaMoment (a-r) n u
  have hai : 0 < a := hr.trans ha
  have hap : 0 < a+r := by positivity
  have ham : 0 < a-r := sub_pos.mpr ha
  have hl := (gammaMoment_integrable hap n).const_mul (Real.exp (r*U))
  have hR := (gammaMoment_integrable ham n).const_mul (Real.exp (-r*V))
  have hi : IntegrableOn F (Ioi 0) := hl.add hR
  have hF {u : ℝ} (hu : 0 ≤ u) : 0 ≤ F u := by
    exact add_nonneg (mul_nonneg (Real.exp_nonneg _) (gammaMoment_nonneg _ _ hu))
      (mul_nonneg (Real.exp_nonneg _) (gammaMoment_nonneg _ _ hu))
  have hs : MeasurableSet S := measurableSet_Ioi.diff measurableSet_Icc
  have hsub : S ⊆ Ioi 0 := sdiff_subset
  refine (setIntegral_mono_on ((gammaMoment_integrable hai n).mono_set hsub)
    (hi.mono_set hsub) hs ?_).trans ?_
  · intro u hu
    have hpos : 0 ≤ u := (hsub hu).le
    have hw := gammaMoment_nonneg a n hpos
    by_cases h : u < U
    · have hE : 1 ≤ Real.exp (r*(U-u)) := Real.one_le_exp (by positivity)
      calc
        _ ≤ Real.exp (r*(U-u))*gammaMoment a n u := le_mul_of_one_le_left hw hE
        _ = Real.exp (r*U)*gammaMoment (a+r) n u := by
          rw [show r*(U-u) = r*U+(-r)*u by ring, Real.exp_add, mul_assoc, exp_mul_gammaMoment]
          rw [sub_neg_eq_add]
        _ ≤ F u := le_add_of_nonneg_right (mul_nonneg (Real.exp_nonneg _) (gammaMoment_nonneg _ _ hpos))
    · have h' : V < u := lt_of_not_ge (fun hn => hu.2 ⟨le_of_not_gt h,hn⟩)
      have hE : 1 ≤ Real.exp (r*(u-V)) := Real.one_le_exp (by positivity)
      calc
        _ ≤ Real.exp (r*(u-V))*gammaMoment a n u := le_mul_of_one_le_left hw hE
        _ = Real.exp (-r*V)*gammaMoment (a-r) n u := by
          rw [show r*(u-V) = -r*V + r*u by ring, Real.exp_add, mul_assoc, exp_mul_gammaMoment]
        _ ≤ F u := le_add_of_nonneg_left (mul_nonneg (Real.exp_nonneg _) (gammaMoment_nonneg _ _ hpos))
  · have hnon : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioi 0)] F :=
      (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => hF hu.le)
    refine (setIntegral_mono_set hi hnon (Eventually.of_forall hsub)).trans_eq ?_
    unfold F
    rw [integral_add hl hR, integral_const_mul, integral_const_mul, gammaMoment_mass hap,
      gammaMoment_mass ham]
    ring

private theorem gammaMoment_tail_div_pow {a r U V b : ℝ} (hr : 0 < r) (ha : r < a)
    (hb : 0 < b) (n : ℕ)
    (hL : r*U ≤ (n:ℝ) * Real.log ((a+r)/b))
    (hR : -r*V + (n:ℝ) * Real.log (b/(a-r)) ≤ Real.log (b/(a-r))) :
    (∫ u in Ioi (0:ℝ) \ Icc U V, gammaMoment a n u) ≤
      ((a+r)⁻¹ + (b/(a-r))/(a-r)) / b^n := by
  have ha₀ : 0 < a := hr.trans ha
  have hp : 0 < a+r := by positivity
  have hm : 0 < a-r := sub_pos.mpr ha
  have hleL := Real.exp_le_exp.mpr hL
  rw [Real.exp_nat_mul, Real.exp_log (div_pos hp hb)] at hleL
  have hleR := Real.exp_le_exp.mpr hR
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (div_pos hb hm)] at hleR
  have h₁ : Real.exp (r*U)/(a+r)^(n+1) ≤ (a+r)⁻¹ / b^n := by
    calc
      _ ≤ ((a+r)/b)^n/(a+r)^(n+1) :=
        div_le_div_of_nonneg_right hleL (by positivity)
      _ = _ := by
        rw [div_pow, pow_succ]
        field_simp [hp.ne', hb.ne']
  have h₂ : Real.exp (-r*V)/(a-r)^(n+1) ≤ (b/(a-r))/(a-r)/b^n := by
    calc
      _ = (Real.exp (-r*V)*(b/(a-r))^n)/(a-r)/b^n := by
        rw [div_pow, pow_succ]
        field_simp [hm.ne', hb.ne']
      _ ≤ _ := div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hleR hm.le) (by positivity)
  exact (gammaMoment_tail_le hr ha n).trans (by rw [add_div]; exact add_le_add h₁ h₂)

private theorem log_tilt_lower (τ : ℝ) (hτ : 0 < τ) :
    τ/(1+τ) ≤ Real.log (1+τ) := by
  have hp : 0 < 1+τ := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hp
  have he : τ/(1+τ) = 1-(1+τ)⁻¹ := by field_simp; ring
  exact he ▸ h

private theorem log_tilt_upper (τ : ℝ) (hτ : τ < 1) :
    -Real.log (1-τ) ≤ τ/(1-τ) := by
  have hp : 0 < 1-τ := sub_pos.mpr hτ
  have h := Real.one_sub_inv_le_log_of_pos hp
  have he : (1-τ)⁻¹-1 = τ/(1-τ) := by field_simp; ring
  rw [← he]
  linarith

/-- For every relative window length and every fixed rate increment, a large
enough base rate admits a moment whose two tilted tails have the stronger
rate. The order is the ceiling of the base rate times the window midpoint. -/
theorem gammaMoment_localization (δ D : ℝ) (hδ : 0 < δ) (hD : 0 ≤ D) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℝ, A ≤ a →
      ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U → ∃ n : ℕ, U ≤ (n:ℝ) ∧
        (∫ u in Ioi (0:ℝ) \ Icc U ((1+δ)*U), gammaMoment a n u) ≤ C/(a+D)^n := by
  let τ := δ/(4*(1+δ))
  let mid := 1+δ/2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hmid : 1 ≤ mid := by dsimp [mid]; linarith
  have hmid₀ : 0 < mid := zero_lt_one.trans_le hmid
  have hτe : (1+δ)*τ = δ/4 := by
    dsimp [τ]
    have h₁ : 1+δ ≠ 0 := by positivity
    field_simp [h₁]
  have hτpos : τ < 1 := by
    dsimp [τ]
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have hτlt : τ < δ/2 := by
    dsimp [τ]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [sq_nonneg δ]
  let mL := mid*(τ/(1+τ))-τ
  let mR := τ*(1+δ)-mid*(τ/(1-τ))
  have hmL : 0 < mL := by
    dsimp [mL]
    rw [sub_pos, ← mul_div_assoc, lt_div_iff₀ (by positivity)]
    have h : 1+τ < mid := by dsimp [mid]; linarith
    simpa only [mul_comm] using mul_lt_mul_of_pos_left h hτ
  have hmR : 0 < mR := by
    dsimp [mR]
    rw [sub_pos, ← mul_div_assoc, div_lt_iff₀ (sub_pos.mpr hτpos)]
    have h : mid < (1+δ)*(1-τ) := by dsimp [mid]; nlinarith
    calc
      mid*τ < ((1+δ)*(1-τ))*τ := mul_lt_mul_of_pos_right h hτ
      _ = _ := by ring
  let A := max 1 (max (mid*D/mL) (mid*D/mR))
  refine ⟨A, zero_lt_one.trans_le (le_max_left _ _), fun a ha => ?_⟩
  have ha₁ : 1 ≤ a := (le_max_left _ _).trans ha
  have ha₀ : 0 < a := zero_lt_one.trans_le ha₁
  have hLa : mid*D/mL ≤ a := ((le_max_left _ _).trans (le_max_right _ _)).trans ha
  have hRa : mid*D/mR ≤ a := ((le_max_right _ _).trans (le_max_right _ _)).trans ha
  have hsmallL : mid*(D/a) ≤ mL := by
    rw [← mul_div_assoc, div_le_iff₀ ha₀]
    simpa only [mul_comm mL] using (div_le_iff₀ hmL).mp hLa
  have hsmallR : mid*(D/a) ≤ mR := by
    rw [← mul_div_assoc, div_le_iff₀ ha₀]
    simpa only [mul_comm mR] using (div_le_iff₀ hmR).mp hRa
  let r := τ*a
  let b := a+D
  have hr : 0 < r := mul_pos hτ ha₀
  have hra : r < a := by
    dsimp [r]
    simpa using mul_lt_mul_of_pos_right hτpos ha₀
  have hb : 0 < b := by dsimp [b]; positivity
  let qL := (a+r)/b
  let qR := b/(a-r)
  have hp : 0 < a+r := by positivity
  have hm : 0 < a-r := sub_pos.mpr hra
  have hqL : 0 < qL := div_pos hp hb
  have hqR : 0 < qR := div_pos hb hm
  have hqR₁ : 1 ≤ qR := by
    dsimp [qR, b]
    exact (le_div_iff₀ hm).mpr (by linarith)
  have hp₁ : 0 < 1+(D/a) := by positivity
  have hp₂ : 0 < 1+τ := by positivity
  have hp₃ : 0 < 1-τ := sub_pos.mpr hτpos
  have hlL : Real.log qL = Real.log (1+τ) - Real.log (1+D/a) := by
    have e : qL = (1+τ)/(1+D/a) := by
      dsimp [qL,r,b]
      field_simp [ha₀.ne', show a+D ≠ 0 by positivity]
    rw [e, Real.log_div hp₂.ne' hp₁.ne']
  have hlR : Real.log qR = Real.log (1+D/a) - Real.log (1-τ) := by
    have e : qR = (1+D/a)/(1-τ) := by
      dsimp [qR,r,b]
      have hne : a-τ*a ≠ 0 := hm.ne'
      field_simp [ha₀.ne', hp₃.ne', hne]
    rw [e, Real.log_div hp₁.ne' hp₃.ne']
  have hlogD : Real.log (1+D/a) ≤ D/a := by
    have h := Real.log_le_sub_one_of_pos hp₁
    linarith
  have hL : τ ≤ mid*Real.log qL := by
    rw [hlL, mul_sub]
    have h := mul_le_mul_of_nonneg_left (log_tilt_lower τ hτ) hmid₀.le
    have hD' := mul_le_mul_of_nonneg_left hlogD hmid₀.le
    dsimp [mL] at hsmallL
    linarith
  have hR : mid*Real.log qR ≤ τ*(1+δ) := by
    rw [hlR, mul_sub]
    have h := mul_le_mul_of_nonneg_left (log_tilt_upper τ hτpos) hmid₀.le
    have hD' := mul_le_mul_of_nonneg_left hlogD hmid₀.le
    dsimp [mR] at hsmallR
    linarith
  have hL₀ : 0 ≤ Real.log qL := by
    by_contra! h
    exact (not_le_of_gt (mul_neg_of_pos_of_neg hmid₀ h)) (hτ.le.trans hL)
  have hR₀ : 0 ≤ Real.log qR := Real.log_nonneg hqR₁
  refine ⟨(a+r)⁻¹+qR/(a-r), by positivity, fun U hU => ?_⟩
  have hU₀ : 0 ≤ U := zero_le_one.trans hU
  let n := ⌈a*mid*U⌉₊
  have hn₁ : a*mid*U ≤ (n:ℝ) := Nat.le_ceil _
  have hn₂ : (n:ℝ) < a*mid*U+1 := Nat.ceil_lt_add_one (by positivity)
  have hn₀ : U ≤ (n:ℝ) := by
    refine le_trans ?_ hn₁
    exact le_mul_of_one_le_left hU₀ (one_le_mul_of_one_le_of_one_le ha₁ hmid)
  refine ⟨n, hn₀, gammaMoment_tail_div_pow hr hra hb n ?_ ?_⟩
  · change r*U ≤ (n:ℝ)*Real.log qL
    calc
      r*U = a*U*τ := by dsimp [r]; ring
      _ ≤ a*U*(mid*Real.log qL) := mul_le_mul_of_nonneg_left hL (by positivity)
      _ = (a*mid*U)*Real.log qL := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hn₁ hL₀
  · change -r*((1+δ)*U) + (n:ℝ)*Real.log qR ≤ Real.log qR
    have hu := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ a*U)
    have hn := mul_le_mul_of_nonneg_right hn₂.le hR₀
    dsimp [r] at *
    nlinarith only [hu, hn]

/-- The complex Laplace moment with real decay parameter and Fourier frequency. -/
noncomputable def windowMoment (g : ℝ → ℝ) (σ γ : ℝ) (n : ℕ) : ℂ :=
  ∫ u in Ioi (0:ℝ), ((g u * gammaMoment σ n u : ℝ) : ℂ) *
    Complex.exp (-(Complex.I * (γ:ℂ) * (u:ℂ)))

private theorem windowMoment_zero_re (g : ℝ → ℝ) (σ : ℝ) (n : ℕ) :
    (windowMoment g σ 0 n).re = ∫ u in Ioi (0:ℝ), g u * gammaMoment σ n u := by
  unfold windowMoment
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero,
    mul_one, integral_complex_ofReal, Complex.ofReal_re]

private theorem windowMoment_norm_le (g : ℝ → ℝ) (σ γ : ℝ) (n : ℕ) :
    ‖windowMoment g σ γ n‖ ≤ ∫ u in Ioi (0:ℝ), |g u| * gammaMoment σ n u := by
  unfold windowMoment
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hc : (-(Complex.I * (γ:ℂ) * (u:ℂ))).re = 0 := by simp
  change ‖((g u * gammaMoment σ n u : ℝ):ℂ) * Complex.exp (-(Complex.I*(γ:ℂ)*(u:ℂ)))‖ =
    |g u| * gammaMoment σ n u
  rw [norm_mul, Complex.norm_exp, hc, Real.exp_zero, mul_one, Complex.norm_real, norm_mul,
    Real.norm_of_nonneg (gammaMoment_nonneg _ _ hu.le), Real.norm_eq_abs]

/-- A one-sided bound on a single scale interval yields an inequality between
the vertical and real moments. Outside the interval only a crude bound is used. -/
theorem windowMoment_le_of_one_sided {g : ℝ → ℝ} (hg : Measurable g)
    {B K θ C σ U V : ℝ} (_hK : 0 ≤ K) (hC : 0 ≤ C)
    (hB : B < σ) (hθ : θ < σ)
    (hglobal : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K * Real.exp (B*u))
    (hwin : ∀ u ∈ Icc U V, g u ≤ C * Real.exp (θ*u)) (n : ℕ) (γ : ℝ) :
    ‖windowMoment g σ γ n‖ + (windowMoment g σ 0 n).re ≤
      (2*C)/(σ-θ)^(n+1) +
        (2*K)*(∫ u in Ioi (0:ℝ) \ Icc U V, gammaMoment (σ-B) n u) := by
  let S := Ioi (0:ℝ) \ Icc U V
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  have hS : MeasurableSet S := measurableSet_Ioi.diff measurableSet_Icc
  have hsub : S ⊆ Ioi 0 := sdiff_subset
  have hwmeas : Measurable (gammaMoment σ n) := by unfold gammaMoment; fun_prop
  have hiB : Integrable (gammaMoment (σ-B) n) μ :=
    gammaMoment_integrable (sub_pos.mpr hB) n
  have hiθ : Integrable (gammaMoment (σ-θ) n) μ :=
    gammaMoment_integrable (sub_pos.mpr hθ) n
  have hM (u : ℝ) (hu : 0 ≤ u) :
      |g u| * gammaMoment σ n u ≤ K * gammaMoment (σ-B) n u := by
    calc
      _ ≤ (K*Real.exp (B*u))*gammaMoment σ n u :=
        mul_le_mul_of_nonneg_right (hglobal u hu) (gammaMoment_nonneg _ _ hu)
      _ = _ := by rw [mul_assoc, exp_mul_gammaMoment]
  have hiAbs : Integrable (fun u => |g u| * gammaMoment σ n u) μ := by
    refine (hiB.const_mul K).mono' (hg.abs.mul hwmeas).aestronglyMeasurable ?_
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    refine Eventually.of_forall fun u hu => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (gammaMoment_nonneg _ _ hu.le))]
    exact hM u hu.le
  have hiG : Integrable (fun u => g u * gammaMoment σ n u) μ := by
    refine hiAbs.mono' (hg.mul hwmeas).aestronglyMeasurable ?_
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    refine Eventually.of_forall fun u hu => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (gammaMoment_nonneg _ _ hu.le)]
  let H (u : ℝ) := (2*C)*gammaMoment (σ-θ) n u
  let T (u : ℝ) := (2*K)*gammaMoment (σ-B) n u
  have hiH : Integrable H μ := hiθ.const_mul _
  have hiT : Integrable T μ := hiB.const_mul _
  have hnonH (u : ℝ) (hu : 0 ≤ u) : 0 ≤ H u :=
    mul_nonneg (by positivity) (gammaMoment_nonneg _ _ hu)
  have hme : (∫ u, S.indicator T u ∂μ) = (2*K) * (∫ u in S, gammaMoment (σ-B) n u) := by
    rw [integral_indicator hS]
    dsimp only [μ, T]
    rw [Measure.restrict_restrict hS, inter_eq_left.mpr hsub, integral_const_mul]
  have hiM : Integrable (fun u => H u + S.indicator T u) μ := hiH.add (hiT.indicator hS)
  calc
    _ ≤ (∫ u, |g u| * gammaMoment σ n u ∂μ) + (∫ u, g u*gammaMoment σ n u ∂μ) := by
      rw [windowMoment_zero_re]
      exact add_le_add (windowMoment_norm_le _ _ _ _) le_rfl
    _ = ∫ u, |g u| * gammaMoment σ n u+g u*gammaMoment σ n u ∂μ := (integral_add hiAbs hiG).symm
    _ ≤ ∫ u, H u + S.indicator T u ∂μ := by
      apply integral_mono_ae (hiAbs.add hiG) hiM
      apply (ae_restrict_iff' measurableSet_Ioi).mpr
      refine Eventually.of_forall fun u hu => ?_
      change |g u| * gammaMoment σ n u + g u * gammaMoment σ n u ≤ H u + S.indicator T u
      by_cases hw : u ∈ Icc U V
      · have hs : u ∉ S := fun h => h.2 hw
        rw [indicator_of_notMem hs, add_zero, ← add_mul]
        have hg' : |g u|+g u ≤ (2*C)*Real.exp (θ*u) := by
          rcases le_or_gt 0 (g u) with h | h
          · rw [abs_of_nonneg h]
            have he := hwin u hw
            linarith
          · rw [abs_of_neg h]
            linarith [mul_nonneg hC (Real.exp_nonneg (θ*u))]
        calc
          _ ≤ ((2*C)*Real.exp (θ*u))*gammaMoment σ n u :=
            mul_le_mul_of_nonneg_right hg' (gammaMoment_nonneg _ _ hu.le)
          _ = _ := by rw [mul_assoc, exp_mul_gammaMoment]
      · have hs : u ∈ S := ⟨hu, hw⟩
        rw [indicator_of_mem hs]
        have hle := mul_le_mul_of_nonneg_right (le_abs_self (g u))
          (gammaMoment_nonneg σ n hu.le)
        have hM' := hM u hu.le
        dsimp [T]
        linarith [hnonH u hu.le]
    _ = _ := by
      rw [integral_add hiH (hiT.indicator hS), hme]
      dsimp only [H, μ]
      rw [integral_const_mul, gammaMoment_mass (sub_pos.mpr hθ)]
      ring

/-- Arbitrarily late one-sided bounds throughout relative scale intervals
force arbitrarily high moments to satisfy one uniform coefficient bound. -/
theorem windowMoment_bound_along_orders {g : ℝ → ℝ} (hg : Measurable g)
    {B K θ C δ : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hθB : θ ≤ B) (hδ : 0 < δ)
    (hglobal : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K * Real.exp (B*u))
    (hwin : ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∀ u ∈ Icc U ((1+δ)*U),
      g u ≤ C * Real.exp (θ*u)) :
    ∃ σ : ℝ, B < σ ∧ ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∀ γ : ℝ,
      ‖windowMoment g σ γ n‖ + (windowMoment g σ 0 n).re ≤ D/(σ-θ)^n := by
  obtain ⟨a, ha, hl⟩ := gammaMoment_localization δ (B-θ) hδ (sub_nonneg.mpr hθB)
  obtain ⟨L, hL, hL'⟩ := hl a le_rfl
  let σ := a+B
  have hB : B < σ := by dsimp [σ]; linarith
  have hθ : θ < σ := hθB.trans_lt hB
  let D := (2*C)/(σ-θ)+(2*K)*L
  refine ⟨σ, hB, D, by dsimp [D]; positivity, fun N => ?_⟩
  obtain ⟨U, hU, hu⟩ := hwin (max 1 (N:ℝ))
  obtain ⟨n, hn, htail⟩ := hL' U ((le_max_left _ _).trans hU)
  have hn' : N ≤ n := by exact_mod_cast ((le_max_right _ _).trans hU).trans hn
  have haeq : a = σ-B := by dsimp [σ]; ring
  have hbeq : a+(B-θ) = σ-θ := by dsimp [σ]; ring
  rw [hbeq, haeq] at htail
  refine ⟨n, hn', fun γ => ?_⟩
  have hM := windowMoment_le_of_one_sided hg hK hC hB hθ hglobal hu n γ
  calc
    _ ≤ (2*C)/(σ-θ)^(n+1)+(2*K)*(L/(σ-θ)^n) :=
      hM.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left htail (by positivity)))
    _ = _ := by
      dsimp [D]
      rw [pow_succ]
      field_simp [(sub_pos.mpr hθ).ne']

end MasulloDirichletRamp

set_option autoImplicit false

open Complex Filter Set MeasureTheory Metric Topology

namespace MasulloDirichletRamp

private noncomputable def weightedIntegrand (g : ℝ → ℝ) (n : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  (g u : ℂ) * (u:ℂ)^n * Complex.exp (-s*(u:ℂ))

private noncomputable def weightedLaplace (g : ℝ → ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  ∫ u in Ioi (0:ℝ), weightedIntegrand g n s u

private theorem weightedIntegrand_measurable {g : ℝ → ℝ} (hg : Measurable g) (n : ℕ) (s : ℂ) :
    Measurable (weightedIntegrand g n s) := by
  unfold weightedIntegrand
  fun_prop

private theorem weightedIntegrand_bound {g : ℝ → ℝ} {K B b : ℝ}
    (hK : 0 ≤ K) (hg : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K*Real.exp (B*u))
    {s : ℂ} (hs : B+b ≤ s.re) (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    ‖weightedIntegrand g n s u‖ ≤ ((n.factorial:ℝ)*K)*gammaMoment b n u := by
  have hfact : 0 < (n.factorial:ℝ) := by exact_mod_cast n.factorial_pos
  have he : (-s*(u:ℂ)).re = -s.re*u := by simp [Complex.mul_re]
  unfold weightedIntegrand
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_of_nonneg hu, Complex.norm_exp, he]
  have hG : |g u| * ((u^n)*Real.exp (-s.re*u)) ≤
      (K*Real.exp (B*u))*((u^n)*Real.exp (-s.re*u)) :=
    mul_le_mul_of_nonneg_right (hg u hu) (by positivity)
  have hshift : Real.exp (B*u) * Real.exp (-s.re*u) = Real.exp (-((s.re-B)*u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he' : Real.exp (-((s.re-B)*u)) ≤ Real.exp (-(b*u)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (by linarith) hu))
  calc
    _ = |g u| * ((u^n)*Real.exp (-s.re*u)) := by ring
    _ ≤ (K*Real.exp (B*u))*((u^n)*Real.exp (-s.re*u)) := hG
    _ = K*(u^n)*(Real.exp (B*u)*Real.exp (-s.re*u)) := by ring
    _ ≤ K*(u^n)*Real.exp (-(b*u)) := by rw [hshift]; exact mul_le_mul_of_nonneg_left he' (by positivity)
    _ = _ := by unfold gammaMoment; field_simp [hfact.ne']

private theorem integrable_weightedIntegrand {g : ℝ → ℝ} (hg : Measurable g) {K B b : ℝ}
    (hK : 0 ≤ K) (hb : 0 < b) (hgK : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K*Real.exp (B*u))
    {s : ℂ} (hs : B+b ≤ s.re) (n : ℕ) :
    IntegrableOn (weightedIntegrand g n s) (Ioi 0) := by
  refine ((gammaMoment_integrable hb n).const_mul ((n.factorial:ℝ)*K)).mono'
    (weightedIntegrand_measurable hg n s).aestronglyMeasurable ?_
  exact (ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun u hu => weightedIntegrand_bound hK hgK hs n hu.le)

private theorem hasDerivAt_weightedLaplace {g : ℝ → ℝ} (hg : Measurable g) {K B : ℝ}
    (hK : 0 ≤ K) (hgK : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K*Real.exp (B*u))
    {s : ℂ} (hs : B < s.re) (n : ℕ) :
    HasDerivAt (weightedLaplace g n) (-weightedLaplace g (n+1) s) s := by
  let b := (s.re-B)/2
  have hb : 0 < b := by dsimp [b]; linarith
  have hz (z : ℂ) (hz : z ∈ ball s b) : B+b ≤ z.re := by
    have hd : ‖z-s‖ < b := by simpa only [mem_ball, dist_eq_norm] using hz
    have hr := (abs_lt.mp ((Complex.abs_re_le_norm (z-s)).trans_lt hd)).1
    simp only [Complex.sub_re] at hr
    dsimp [b] at hr ⊢
    linarith
  have hbnd : ∀ᵐ u ∂(volume : Measure ℝ).restrict (Ioi 0), ∀ z ∈ ball s b,
      ‖-weightedIntegrand g (n+1) z u‖ ≤ (((n+1).factorial:ℝ)*K)*gammaMoment b (n+1) u :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu z hzs => by
      rw [norm_neg]
      exact weightedIntegrand_bound hK hgK (hz z hzs) (n+1) hu.le)
  have hder (u : ℝ) (z : ℂ) :
      HasDerivAt (fun w => weightedIntegrand g n w u) (-weightedIntegrand g (n+1) z u) z := by
    have he : HasDerivAt (fun w : ℂ => -w*(u:ℂ)) (-(u:ℂ)) z := by
      simpa using (hasDerivAt_id z).neg.mul_const (u:ℂ)
    refine (he.cexp.const_mul ((g u : ℂ)*(u:ℂ)^n)).congr_deriv ?_
    unfold weightedIntegrand
    rw [pow_succ]
    ring
  have hi := (gammaMoment_integrable hb (n+1)).const_mul (((n+1).factorial:ℝ)*K)
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := weightedIntegrand g n) (F' := fun z u => -weightedIntegrand g (n+1) z u)
    (ball_mem_nhds s hb)
    (Eventually.of_forall fun z => (weightedIntegrand_measurable hg n z).aestronglyMeasurable)
    (integrable_weightedIntegrand hg hK hb hgK (hz s (mem_ball_self hb)) n)
    ((weightedIntegrand_measurable hg (n+1) s).neg.aestronglyMeasurable)
    hbnd hi (Eventually.of_forall fun u z _ => hder u z)).2
  unfold weightedLaplace
  rw [← integral_neg]
  exact hh

private theorem iteratedDeriv_weightedLaplace {g : ℝ → ℝ} (hg : Measurable g) {K B : ℝ}
    (hK : 0 ≤ K) (hgK : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K*Real.exp (B*u))
    (n : ℕ) :
    ∀ s : ℂ, B < s.re →
      iteratedDeriv n (weightedLaplace g 0) s = (-1:ℂ)^n*weightedLaplace g n s := by
  induction n with
  | zero => intro s _; simp
  | succ n ih =>
    intro s hs
    have hopen : IsOpen {z : ℂ | B < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hnear : ∀ᶠ z : ℂ in 𝓝 s, B < z.re := hopen.mem_nhds hs
    have he : iteratedDeriv n (weightedLaplace g 0) =ᶠ[𝓝 s]
        (fun z => (-1:ℂ)^n * weightedLaplace g n z) :=
      hnear.mono (fun z hz => ih z hz)
    rw [iteratedDeriv_succ, he.deriv_eq,
      ((hasDerivAt_weightedLaplace hg hK hgK hs n).const_mul ((-1:ℂ)^n)).deriv]
    rw [pow_succ]
    ring

/-- The signed Taylor coefficient at a point in the half-plane. -/
noncomputable def windowCoefficient (Φ : ℂ → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  (-1:ℂ)^n * iteratedDeriv n Φ s / (n.factorial : ℂ)

/-- The integral window moments are precisely the signed Taylor coefficients
of the analytic continuation on the initial half-plane. -/
theorem windowCoefficient_eq_moment {g : ℝ → ℝ} {Φ : ℂ → ℂ} (hg : Measurable g)
    {K B : ℝ} (hK : 0 ≤ K) (hgK : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K*Real.exp (B*u))
    (hΦ : ∀ s : ℂ, B < s.re → Φ s =
      ∫ u in Ioi (0:ℝ), (g u : ℂ)*Complex.exp (-s*(u:ℂ)))
    {σ : ℝ} (hσ : B < σ) (γ : ℝ) (n : ℕ) :
    windowCoefficient Φ ((σ:ℂ)+(γ:ℂ)*I) n = windowMoment g σ γ n := by
  let s := (σ:ℂ)+(γ:ℂ)*I
  have hs : B < s.re := by simpa [s] using hσ
  have hlo : IsOpen {z : ℂ | B < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hnear : ∀ᶠ z : ℂ in 𝓝 s, B < z.re := hlo.mem_nhds hs
  have he : Φ =ᶠ[𝓝 s] weightedLaplace g 0 := by
    refine hnear.mono ?_
    intro z hz
    simpa [weightedLaplace, weightedIntegrand] using hΦ z hz
  change windowCoefficient Φ s n = _
  unfold windowCoefficient
  rw [he.iteratedDeriv_eq, iteratedDeriv_weightedLaplace hg hK hgK n s hs, ← mul_assoc, ← mul_pow]
  simp only [neg_mul_neg, one_mul, one_pow]
  unfold weightedLaplace windowMoment
  rw [← integral_div]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  have hphase : Complex.exp (-s*(u:ℂ)) = ((Real.exp (-σ*u):ℝ):ℂ) *
      Complex.exp (-(I*(γ:ℂ)*(u:ℂ))) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    dsimp [s]
    push_cast
    ring
  change weightedIntegrand g n s u/(n.factorial:ℂ) = _
  unfold weightedIntegrand gammaMoment
  rw [hphase]
  push_cast
  ring

theorem laplace_integrable_of_exponential_bound {g : ℝ → ℝ} (hg : Measurable g)
    {K B : ℝ} (hK : 0 ≤ K) (hgK : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K*Real.exp (B*u))
    {s : ℂ} (hs : B < s.re) :
    IntegrableOn (fun u : ℝ => (g u:ℂ)*Complex.exp (-s*(u:ℂ))) (Ioi 0) := by
  have hb : 0 < s.re-B := sub_pos.mpr hs
  have hσ : B+(s.re-B) ≤ s.re := by linarith
  have h := integrable_weightedIntegrand hg hK hb hgK hσ 0
  have he : weightedIntegrand g 0 s = (fun u : ℝ => (g u:ℂ)*Complex.exp (-s*(u:ℂ))) := by
    funext u
    simp [weightedIntegrand]
  rwa [he] at h

theorem linear_exponential_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun u : ℝ => (u:ℂ)*Complex.exp (-s*(u:ℂ))) (Ioi 0) := by
  have h := integrable_weightedIntegrand
    (g := fun _ => (1:ℝ)) measurable_const (K := 1) (B := 0) zero_le_one hs
      (fun u _ => by simp) (s := s) (by simp : (0:ℝ)+s.re ≤ s.re) 1
  have he : weightedIntegrand (fun _ => 1) 1 s =
      (fun u : ℝ => (u:ℂ)*Complex.exp (-s*(u:ℂ))) := by
    funext u
    simp [weightedIntegrand]
  rwa [he] at h

/-- The first moment of a complex exponential with positive decay. -/
theorem linear_exponential_integral {s : ℂ} (hs : 0 < s.re) :
    (∫ u in Ioi (0:ℝ), (u:ℂ)*Complex.exp (-s*(u:ℂ))) = 1/s^2 := by
  have he (z : ℂ) (hz : 0 < z.re) :
      weightedLaplace (fun _ => 1) 0 z = z⁻¹ := by
    have h := integral_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 0
    simpa [weightedLaplace, weightedIntegrand, div_eq_mul_inv] using h
  have hnear : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  have hlocal : weightedLaplace (fun _ => 1) 0 =ᶠ[𝓝 s] (fun z : ℂ => z⁻¹) :=
    hnear.mono he
  have hd : HasDerivAt (weightedLaplace (fun _ => 1) 0) (-weightedLaplace (fun _ => 1) 1 s) s :=
    hasDerivAt_weightedLaplace measurable_const (K := 1) (B := 0) zero_le_one
      (fun u _ => by simp) hs 0
  have hz : s ≠ 0 := ne_zero_of_re_pos hs
  have hInv := hasDerivAt_inv (x := s) hz
  have ht := hd.deriv.symm.trans (hlocal.deriv_eq.trans hInv.deriv)
  simpa [weightedLaplace, weightedIntegrand, div_eq_mul_inv] using neg_injective ht

end MasulloDirichletRamp

set_option autoImplicit false

open Complex Filter MeasureTheory Metric Set Topology

namespace MasulloDirichletRamp

/-- Move along the vertical line with real part `σ`. -/
def windowCenter (σ γ : ℝ) : ℂ := (σ:ℂ)+(γ:ℂ)*I

@[simp] theorem windowCenter_re (σ γ : ℝ) : (windowCenter σ γ).re = σ := by simp [windowCenter]
@[simp] theorem windowCenter_im (σ γ : ℝ) : (windowCenter σ γ).im = γ := by simp [windowCenter]

private theorem windowCenter_dist (σ γ γ₀ : ℝ) :
    dist (windowCenter σ γ) (windowCenter σ γ₀) = |γ-γ₀| := by
  rw [dist_eq_norm]
  have he : windowCenter σ γ-windowCenter σ γ₀ = (((γ-γ₀:ℝ):ℂ))*I := by
    unfold windowCenter
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

private theorem dist_windowCenter_sq (z : ℂ) (σ γ : ℝ) :
    (dist z (windowCenter σ γ))^2 = (z.re-σ)^2+(z.im-γ)^2 := by
  rw [dist_eq_norm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, windowCenter_re, windowCenter_im]
  ring

private theorem dist_projection_lt (z : ℂ) (σ : ℝ) (hz : z.im ≠ 0) :
    dist z (windowCenter σ z.im) < dist z (σ:ℂ) := by
  have hn (γ : ℝ) : 0 ≤ dist z (windowCenter σ γ) := dist_nonneg
  have hz0 : windowCenter σ 0 = (σ:ℂ) := by simp [windowCenter]
  have hS := dist_windowCenter_sq z σ z.im
  have hZ := dist_windowCenter_sq z σ 0
  rw [hz0] at hZ
  have hp : 0 < z.im^2 := sq_pos_of_ne_zero hz
  by_contra! he
  have hs := pow_le_pow_left₀ (show 0 ≤ dist z (σ:ℂ) from dist_nonneg) he 2
  nlinarith

private theorem continuous_distance_to (c : ℂ) : Continuous (fun z : ℂ => dist z c) :=
  continuous_id.dist continuous_const

private theorem compact_poles_in_disk {Z : Set ℂ} (hZ : IsClosed Z) (hDisc : IsDiscrete Z)
    (s : ℂ) (r : ℝ) : (closedBall s r ∩ Z).Finite := by
  exact ((isCompact_closedBall s r).inter_right hZ).finite (hDisc.mono inter_subset_right)

private noncomputable def collisionHeight (σ : ℝ) (a b : ℂ) : ℝ :=
  ((a.re-σ)^2+a.im^2-((b.re-σ)^2+b.im^2))/(2*(a.im-b.im))

private theorem collisionHeight_of_equal_distance {a b : ℂ} (hab : a ≠ b)
    {σ γ : ℝ} (ha : a.re < σ) (hb : b.re < σ)
    (he : dist a (windowCenter σ γ) = dist b (windowCenter σ γ)) :
    γ = collisionHeight σ a b := by
  have h := congrArg (fun x : ℝ => x^2) he
  rw [dist_windowCenter_sq, dist_windowCenter_sq] at h
  have him : a.im ≠ b.im := by
    intro heq
    have hre : (a.re-σ)^2 = (b.re-σ)^2 := by rw [heq] at h; linarith
    have hmul : ((a.re-σ)-(b.re-σ))*((a.re-σ)+(b.re-σ)) = 0 := by nlinarith only [hre]
    have hs : (a.re-σ)+(b.re-σ) ≠ 0 := by linarith
    have hr : a.re = b.re := by
      rcases mul_eq_zero.mp hmul with h' | h'
      · linarith
      · exact False.elim (hs h')
    exact hab (Complex.ext hr heq)
  unfold collisionHeight
  apply (eq_div_iff (mul_ne_zero (by norm_num) (sub_ne_zero.mpr him))).mpr
  nlinarith only [h]

private theorem pick_vertical_center {Z : Set ℂ} (hZ : IsClosed Z) (hDisc : IsDiscrete Z)
    (σ : ℝ) (hRe : ∀ z ∈ Z, z.re < σ) {R : ℝ}
    (γ₀ : ℝ) {p : ℂ} (hpR : dist p (windowCenter σ γ₀) < R) :
    ∃ γ : ℝ, dist p (windowCenter σ γ) < R ∧
      ∀ a b : ℂ, a ∈ Z → b ∈ Z → dist a (windowCenter σ γ) < R →
        dist b (windowCenter σ γ) < R →
        dist a (windowCenter σ γ) = dist b (windowCenter σ γ) → a = b := by
  let C := closedBall (windowCenter σ γ₀) (R+1) ∩ Z
  have hC : C.Finite := compact_poles_in_disk hZ hDisc _ _
  let Bad := (fun ab : ℂ × ℂ => collisionHeight σ ab.1 ab.2) '' (C.prod C)
  have hBad : Bad.Finite := (hC.prod hC).image _
  let ε := min 1 ((R-dist p (windowCenter σ γ₀))/2)
  have hε : 0 < ε := lt_min zero_lt_one (by linarith)
  have hε₁ : ε ≤ 1 := min_le_left _ _
  have hε₂ : ε ≤ (R-dist p (windowCenter σ γ₀))/2 := min_le_right _ _
  obtain ⟨γ,hγ,hnot⟩ := ((Set.Ioo_infinite (a:=γ₀-ε) (b:=γ₀+ε) (by linarith )).sdiff hBad).nonempty
  have hdist : dist (windowCenter σ γ) (windowCenter σ γ₀) < ε := by
    rw [windowCenter_dist, abs_lt]
    exact ⟨by linarith [hγ.1], by linarith [hγ.2]⟩
  have hC' (a : ℂ) (ha : a ∈ Z) (h : dist a (windowCenter σ γ) < R) : a ∈ C := by
    refine ⟨mem_closedBall.mpr ?_,ha⟩
    have hT := dist_triangle a (windowCenter σ γ) (windowCenter σ γ₀)
    linarith
  have hp' : dist p (windowCenter σ γ) < R := by
    have hT := dist_triangle p (windowCenter σ γ₀) (windowCenter σ γ)
    rw [dist_comm (windowCenter σ γ₀)] at hT
    linarith
  refine ⟨γ,hp',fun a b ha hb haR hbR he => ?_⟩
  by_contra hn
  have h := collisionHeight_of_equal_distance hn (hRe a ha) (hRe b hb) he
  exact hnot ⟨(a,b), ⟨hC' a ha haR,hC' b hb hbR⟩, h.symm⟩


private theorem windowCoefficient_bound {f : ℂ → ℂ} {z : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hf : DifferentiableOn ℂ f (ball z R)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ‖windowCoefficient f z n‖ ≤ M/r^n := by
  have h₁ : sphere z r ⊆ ball z R := fun w hw => by
    rw [mem_ball, mem_sphere.mp hw]
    exact hrR
  have h₂ : closedBall z r ⊆ ball z R := fun w hw => by
    exact mem_ball.mpr ((mem_closedBall.mp hw).trans_lt hrR)
  have hF : DiffContOnCl ℂ f (ball z r) := by
    refine ⟨hf.mono (ball_subset_ball hrR.le), ?_⟩
    rw [closure_ball _ hr.ne']
    exact hf.continuousOn.mono h₂
  obtain ⟨Q,hQ⟩ := (isCompact_sphere z r).exists_bound_of_continuousOn (hf.continuousOn.mono h₁)
  let M := max 0 Q
  refine ⟨M, le_max_left _ _, fun n => ?_⟩
  have hbound := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (C := M) n hr hF
    (fun w hw => (hQ w hw).trans (le_max_right _ _))
  have hfac : 0 < (n.factorial:ℝ) := by exact_mod_cast n.factorial_pos
  unfold windowCoefficient
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
  rw [div_le_iff₀ hfac]
  simpa only [mul_comm _ (n.factorial:ℝ), mul_div_assoc] using hbound

private theorem windowCoefficient_simplePole (c ρ z : ℂ) {n : ℕ} :
    windowCoefficient (fun w => c/(w-ρ)) z n = c/(z-ρ)^(n+1) := by
  have h₁ := iteratedDerivWithin_one_div (𝕜 := ℂ) n
    (s := (univ : Set ℂ)) isOpen_univ (mem_univ (z-ρ))
  simp only [iteratedDerivWithin_univ] at h₁
  unfold windowCoefficient
  have hs :
      iteratedDeriv n (fun w : ℂ => 1/(w-ρ)) z =
        (-1:ℂ)^n*(n.factorial:ℂ)*(z-ρ)^(-1-(n:ℤ)) := by
    have hg := congrFun (iteratedDeriv_comp_sub_const (n := n) (f := fun w : ℂ => 1/w) (s := ρ)) z
    exact hg.trans h₁
  rw [show (fun w : ℂ => c/(w-ρ)) = (fun w : ℂ => c*(1/(w-ρ))) by
      funext w; rw [mul_one_div],
    iteratedDeriv_const_mul_field, hs]
  have hneq : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have he : (-1:ℤ)-(n:ℤ) = -((n+1:ℕ):ℤ) := by push_cast; omega
  rw [he, zpow_neg, zpow_natCast]
  calc
    _ = ((-1:ℂ)^n*(-1:ℂ)^n)*c*((n.factorial:ℂ)/(n.factorial:ℂ))*((z-ρ)^(n+1))⁻¹ := by ring
    _ = _ := by rw [← mul_pow, neg_mul_neg, one_mul, one_pow, div_self hneq, one_mul, mul_one, div_eq_mul_inv]

private theorem subtract_pole_on_disk {Φ : ℂ → ℂ} {z ρ c : ℂ} {R : ℝ}
    (hρ : ρ ∈ ball z R) (hf : DifferentiableOn ℂ Φ (ball z R \ {ρ}))
    (hp : ∃ H : ℂ → ℂ, AnalyticAt ℂ H ρ ∧
      ∀ᶠ w in 𝓝[≠] ρ, Φ w = c/(w-ρ)+H w) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (ball z R) ∧
      ∀ w ∈ ball z R \ {ρ}, Φ w = c/(w-ρ)+f w := by
  obtain ⟨H,hHan,hH⟩ := hp
  let f : ℂ → ℂ := Function.update (fun w => Φ w-c/(w-ρ)) ρ (H ρ)
  have hEq : f =ᶠ[𝓝 ρ] H := by
    rw [eventually_nhdsWithin_iff] at hH
    filter_upwards [hH] with w hw
    rcases eq_or_ne w ρ with rfl | hne
    · simp [f]
    · have h := hw (mem_compl_singleton_iff.mpr hne)
      rw [show f w = Φ w-c/(w-ρ) from Function.update_of_ne hne _ _ ,h]
      ring
  refine ⟨f, ?_, ?_⟩
  · intro w hw
    rcases eq_or_ne w ρ with rfl | hne
    · exact (hEq.differentiableAt_iff.mpr hHan.differentiableAt).differentiableWithinAt
    · have hmem : w ∈ ball z R \ {ρ} := ⟨hw,hne⟩
      have hopen : IsOpen (ball z R \ {ρ}) := isOpen_ball.sdiff isClosed_singleton
      have hnear : ∀ᶠ v : ℂ in 𝓝 w, v ∈ ball z R \ {ρ} := hopen.mem_nhds hmem
      have hwΦ := (hf w hmem).differentiableAt (hopen.mem_nhds hmem)
      have hwf : f =ᶠ[𝓝 w] (fun v => Φ v-c/(v-ρ)) :=
        hnear.mono (fun v hv => Function.update_of_ne hv.2 _ _)
      have hd : DifferentiableAt ℂ (fun v : ℂ => c/(v-ρ)) w :=
        (differentiableAt_const c).div (differentiableAt_id.sub_const _) (sub_ne_zero.mpr hne)
      exact (hwf.differentiableAt_iff.mpr (hwΦ.sub hd)).differentiableWithinAt
  · intro w hw
    rw [show f w = Φ w-c/(w-ρ) from Function.update_of_ne hw.2 _ _]
    ring

/-- A simple pole isolated inside a larger analytic disk gives a leading
Taylor term, with all other terms bounded at the larger radius. -/
theorem windowCoefficient_pole_asymptotic {Φ : ℂ → ℂ} {z ρ c : ℂ} {r R : ℝ}
    (hρ : ρ ∈ ball z R) (hzρ : z ≠ ρ) (hr : 0 < r) (hrR : r < R)
    (hf : DifferentiableOn ℂ Φ (ball z R \ {ρ}))
    (hp : ∃ H : ℂ → ℂ, AnalyticAt ℂ H ρ ∧
      ∀ᶠ w in 𝓝[≠] ρ, Φ w = c/(w-ρ)+H w) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
      ‖windowCoefficient Φ z n - c/(z-ρ)^(n+1)‖ ≤ M/r^n := by
  obtain ⟨f,hf₁,hf₂⟩ := subtract_pole_on_disk hρ hf hp
  obtain ⟨M,hM,hbound⟩ := windowCoefficient_bound hr hrR hf₁
  refine ⟨M,hM,fun n => ?_⟩
  have hR : 0 < R := hr.trans hrR
  have hn : ∀ᶠ w : ℂ in 𝓝 z, w ∈ ball z R \ {ρ} :=
    (isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨mem_ball_self hR, hzρ⟩
  have he : Φ =ᶠ[𝓝 z] (fun w : ℂ => c/(w-ρ)) + f := hn.mono (fun w hw => hf₂ w hw)
  have hcp : ContDiffAt ℂ n (fun w : ℂ => c/(w-ρ)) z :=
    contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) (sub_ne_zero.mpr hzρ)
  have hcf : ContDiffAt ℂ n f z := (hf₁.contDiffOn isOpen_ball).contDiffAt
    (isOpen_ball.mem_nhds (mem_ball_self hR))
  have hsum :
      windowCoefficient Φ z n =
        windowCoefficient (fun w : ℂ => c/(w-ρ)) z n + windowCoefficient f z n := by
    unfold windowCoefficient
    rw [he.iteratedDeriv_eq, iteratedDeriv_add hcp hcf]
    ring
  rw [hsum, windowCoefficient_simplePole, add_sub_cancel_left]
  exact hbound n

private theorem positive_constant_not_bounded_by_two_smaller_rates
    {c d e E M D : ℝ} (hc : 0 < c) (hd : 0 < d) (he : d < e) (heE : e ≤ E)
    (h : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ c/d^n ≤ M/e^n + D/E^n) :
    False := by
  have he₀ : 0 < e := hd.trans he
  have hE : 0 < E := he₀.trans_le heE
  have hl : Tendsto (fun n : ℕ => M*(d/e)^n + D*(d/E)^n) atTop (𝓝 0) := by
    have h₁ := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hd.le he₀.le)
      ((div_lt_one he₀).mpr he)
    have h₂ := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hd.le hE.le)
      ((div_lt_one hE).mpr (he.trans_le heE))
    simpa only [mul_zero, add_zero] using (h₁.const_mul M).add (h₂.const_mul D)
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp hl).2 c hc)
  obtain ⟨n,hn,hb⟩ := h N
  have hsmall := hN n hn
  have hb' := mul_le_mul_of_nonneg_right hb (pow_nonneg hd.le n)
  rw [div_mul_cancel₀ _ (pow_ne_zero _ hd.ne'), add_mul] at hb'
  have h₁ : M/e^n*d^n = M*(d/e)^n := by rw [div_pow]; ring
  have h₂ : D/E^n*d^n = D*(d/E)^n := by rw [div_pow]; ring
  rw [h₁,h₂] at hb'
  exact (not_lt_of_ge hb') hsmall

/-- A one-sided bound on arbitrarily late relative windows rules out poles
right of the window exponent, when the poles are disjoint from the real line. -/
private theorem dist_vertical_projection (z : ℂ) {σ : ℝ} (hz : z.re < σ) :
    dist z (windowCenter σ z.im) = σ-z.re := by
  rw [dist_eq_norm]
  have he : z-windowCenter σ z.im = ((z.re-σ:ℝ):ℂ) := by apply Complex.ext <;> simp
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (sub_neg.mpr hz), neg_sub]

private theorem isolate_unique_minimum {Z : Set ℂ} (hZ : IsClosed Z) (hDisc : IsDiscrete Z)
    {c z : ℂ} {R : ℝ} (hdR : dist z c < R)
    (hmin : ∀ w ∈ closedBall c R ∩ Z, w ≠ z → dist z c < dist w c) :
    ∃ r : ℝ, dist z c < r ∧ r ≤ R ∧ ∀ w ∈ Z, w ∈ ball c r → w = z := by
  let T := (closedBall c R ∩ Z) \ {z}
  have hTf : T.Finite := (compact_poles_in_disk hZ hDisc c R).subset sdiff_subset
  have hT := hTf.isCompact
  have hex : ∃ r : ℝ, dist z c < r ∧ r ≤ R ∧ ∀ w ∈ T, r ≤ dist w c := by
    by_cases hn : T.Nonempty
    · obtain ⟨w,hw,hm⟩ := hT.exists_isMinOn hn (continuous_distance_to c).continuousOn
      refine ⟨min R (dist w c), lt_min hdR (hmin w hw.1 hw.2), min_le_left _ _, fun v hv => ?_⟩
      exact (min_le_right _ _).trans ((isMinOn_iff.mp hm) v hv)
    · exact ⟨R,hdR,le_rfl,fun w hw => False.elim (hn ⟨w,hw⟩)⟩
  obtain ⟨r,hr,hrR,hrw⟩ := hex
  refine ⟨r,hr,hrR,fun w hw hwball => ?_⟩
  by_contra hn
  have hwr : dist w c < r := hwball
  exact not_lt_of_ge (hrw w ⟨⟨mem_closedBall.mpr (hwr.le.trans hrR),hw⟩, hn⟩) hwr

private theorem window_pole_dichotomy {Z : Set ℂ} (hZ : IsClosed Z) (hDisc : IsDiscrete Z)
    {σ θ : ℝ} (hRe : ∀ z ∈ Z, z.re < σ)
    {ρ : ℂ} (hρ : ρ ∈ Z) (hρθ : θ < ρ.re) :
    (∃ R γ : ℝ, ∃ p ∈ Z, dist p (windowCenter σ γ) < R ∧ R ≤ σ-θ ∧
      Disjoint (ball (σ:ℂ) R) Z) ∨
    (∃ r : ℝ, ∃ z ∈ Z, z.im = 0 ∧ 0 < dist z (σ:ℂ) ∧ dist z (σ:ℂ) < r ∧
      r ≤ σ-θ ∧ ∀ w ∈ Z, w ∈ ball (σ:ℂ) r → w = z) := by
  let E := σ-θ
  have hE : 0 < E := by dsimp [E]; linarith [hRe ρ hρ]
  by_cases h : (ball (σ:ℂ) E ∩ Z).Nonempty
  · obtain ⟨w, hw⟩ := h
    let C := closedBall (σ:ℂ) (dist w (σ:ℂ)) ∩ Z
    have hwC : w ∈ C := ⟨mem_closedBall.mpr le_rfl, hw.2⟩
    have hC : IsCompact C := (isCompact_closedBall _ _).inter_right hZ
    obtain ⟨z,hz,hm⟩ := hC.exists_isMinOn ⟨w,hwC⟩ (continuous_distance_to (σ:ℂ)).continuousOn
    let d := dist z (σ:ℂ)
    have hmin := isMinOn_iff.mp hm
    have hdw : d ≤ dist w (σ:ℂ) := hmin w hwC
    have hdE : d < E := hdw.trans_lt hw.1
    have hd0 : 0 < d := dist_pos.mpr (by
      intro he
      have hr := hRe z hz.2
      rw [he, Complex.ofReal_re] at hr
      exact (lt_irrefl _ hr))
    have hglobal (v : ℂ) (hv : v ∈ Z) : d ≤ dist v (σ:ℂ) := by
      by_cases hd : dist v (σ:ℂ) ≤ dist w (σ:ℂ)
      · exact hmin v ⟨mem_closedBall.mpr hd, hv⟩
      · exact hdw.trans (le_of_not_ge hd)
    by_cases hn : ∃ p ∈ Z, p.im ≠ 0 ∧ dist p (σ:ℂ) = d
    · obtain ⟨p,hp,hpi,hpd⟩ := hn
      refine Or.inl ⟨d,p.im,p,hp,(dist_projection_lt p σ hpi).trans_le hpd.le,hdE.le,?_⟩
      exact disjoint_left.mpr (fun v hv hvZ => (not_lt_of_ge (hglobal v hvZ)) hv)
    · have hzi : z.im = 0 := by
        by_contra he
        exact hn ⟨z,hz.2,he,rfl⟩
      have hR (p : ℂ) (hp : p ∈ Z) (hi : p.im = 0) : dist p (σ:ℂ) = σ-p.re := by
        simpa [hi,windowCenter] using dist_vertical_projection p (hRe p hp)
      have hstrict (v : ℂ) (hv : v ∈ closedBall (σ:ℂ) E ∩ Z) (hneq : v ≠ z) :
          d < dist v (σ:ℂ) := by
        apply lt_of_le_of_ne (hglobal v hv.2)
        intro he
        have hvi : v.im = 0 := by
          by_contra hnz
          exact hn ⟨v,hv.2,hnz,he.symm⟩
        have hEq : dist z (σ:ℂ) = dist v (σ:ℂ) := he
        rw [hR z hz.2 hzi,hR v hv.2 hvi] at hEq
        exact hneq (Complex.ext (by linarith) (hvi.trans hzi.symm))
      obtain ⟨r,hr,hrE,hsole⟩ := isolate_unique_minimum hZ hDisc hdE hstrict
      exact Or.inr ⟨r,z,hz.2,hzi,hd0,hr,hrE,hsole⟩
  · refine Or.inl ⟨E,ρ.im,ρ,hρ,?_,le_rfl,disjoint_left.mpr (fun w hw hwZ => h ⟨w,hw,hwZ⟩)⟩
    rw [dist_vertical_projection ρ (hRe ρ hρ)]
    dsimp [E]
    linarith

private theorem isolate_vertical_pole {Z : Set ℂ} (hZ : IsClosed Z) (hDisc : IsDiscrete Z)
    {σ R γ₀ : ℝ} (hRe : ∀ z ∈ Z, z.re < σ)
    {p : ℂ} (hp : p ∈ Z) (hpR : dist p (windowCenter σ γ₀) < R) :
    ∃ γ r : ℝ, ∃ z ∈ Z, 0 < dist z (windowCenter σ γ) ∧
      dist z (windowCenter σ γ) < r ∧ r ≤ R ∧
      ∀ w ∈ Z, w ∈ ball (windowCenter σ γ) r → w = z := by
  obtain ⟨γ,hp',hg⟩ := pick_vertical_center hZ hDisc σ hRe γ₀ hpR
  let c := windowCenter σ γ
  let S := closedBall c (dist p c) ∩ Z
  have hS : IsCompact S := (isCompact_closedBall _ _).inter_right hZ
  obtain ⟨z,hz,hmin⟩ := hS.exists_isMinOn ⟨p,mem_closedBall.mpr le_rfl,hp⟩ (continuous_distance_to c).continuousOn
  let d := dist z c
  have hd₀ : 0 < d := dist_pos.mpr (by
    intro he
    have hzre := hRe z hz.2
    rw [he, show c.re = σ from windowCenter_re σ γ] at hzre
    exact lt_irrefl _ hzre)
  have hdR : d < R := ((mem_closedBall.mp hz.1).trans_lt hp')
  have ht (w : ℂ) (hw : w ∈ closedBall c R ∩ Z) (hn : w ≠ z) : d < dist w c := by
    by_contra! he
    have hw' : w ∈ S := ⟨mem_closedBall.mpr (he.trans (mem_closedBall.mp hz.1)),hw.2⟩
    have hl : d ≤ dist w c := (isMinOn_iff.mp hmin) w hw'
    exact hn (hg z w hz.2 hw.2 hdR (he.trans_lt hdR) (le_antisymm hl he)).symm
  obtain ⟨r,hr,hrR,hsole⟩ := isolate_unique_minimum hZ hDisc hdR ht
  exact ⟨γ,r,z,hz.2,hd₀,hr,hrR,hsole⟩

/-- A one-sided window criterion allowing real poles with positive residues.
Nonreal closest poles are isolated after a small vertical perturbation. A
unique closest real pole contributes a positive real Taylor coefficient,
which the same one-sided moment bound excludes. -/
theorem no_poles_of_upper_windows {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ}
    (hZ : IsClosed Z) (hZd : IsDiscrete Z)
    (hg : Measurable g) {B K θ C δ : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hθB : θ ≤ B) (hδ : 0 < δ)
    (hglobal : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K*Real.exp (B*u))
    (hwin : ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∀ u ∈ Icc U ((1+δ)*U),
      g u ≤ C * Real.exp (θ*u))
    (hΦ : ∀ s : ℂ, B < s.re → Φ s =
      ∫ u in Ioi (0:ℝ), (g u:ℂ)*Complex.exp (-s*(u:ℂ)))
    (hRe : ∀ z ∈ Z, z.re ≤ B)
    (hdiff : ∀ s : ℂ, θ < s.re → s ∉ Z → DifferentiableAt ℂ Φ s)
    (hPole : ∀ ρ ∈ Z, θ < ρ.re → ∃ c : ℂ, c ≠ 0 ∧ (ρ.im = 0 → 0 < c.re) ∧
      ∃ H : ℂ → ℂ, AnalyticAt ℂ H ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, Φ s = c/(s-ρ)+H s) :
    ∀ ρ ∈ Z, ρ.re ≤ θ := by
  intro ρ hρ
  by_contra! hρθ
  obtain ⟨σ,hσ,D,hD,hM⟩ := windowMoment_bound_along_orders hg hK hC hθB hδ hglobal hwin
  have hRe' (s : ℂ) (hs : s ∈ Z) : s.re < σ := (hRe s hs).trans_lt hσ
  have hhalf (c : ℂ) (hc : c.re = σ) (s : ℂ) (h : s ∈ ball c (σ-θ)) : θ < s.re := by
    have hnorm : ‖s-c‖ < σ-θ := by simpa only [mem_ball, dist_eq_norm] using h
    have h' := (abs_lt.mp ((Complex.abs_re_le_norm (s-c)).trans_lt hnorm)).1
    rw [Complex.sub_re,hc] at h'
    linarith
  rcases window_pole_dichotomy hZ hZd hRe' hρ hρθ with hvert | hreal
  · obtain ⟨R,γ₀,p,hp,hpR,hRE,hfree⟩ := hvert
    obtain ⟨γ,r,w,hw,hpos,hwr,hrR,hsole⟩ := isolate_vertical_pole hZ hZd hRe' hp hpR
    let z := windowCenter σ γ
    let d := dist w z
    let e := (d+r)/2
    have he₁ : d < e := by dsimp [e]; linarith
    have her : e < r := by dsimp [e]; linarith
    have he₀ : 0 < e := hpos.trans he₁
    have heR : e < R := her.trans_le hrR
    have hzρ : z ≠ w := by
      intro he
      rw [← he, dist_self] at hpos
      exact (lt_irrefl _) hpos
    have hreal : DifferentiableOn ℂ Φ (ball (σ:ℂ) R) := by
      intro s hs
      exact (hdiff s (hhalf _ (Complex.ofReal_re _) s (ball_subset_ball hRE hs))
        (fun hz' => (Set.disjoint_left.mp hfree) hs hz')).differentiableWithinAt
    have hvertical : DifferentiableOn ℂ Φ (ball z r \ {w}) := by
      intro s hs
      exact (hdiff s (hhalf z (windowCenter_re _ _) s (ball_subset_ball (hrR.trans hRE) hs.1))
        (fun he => hs.2 (hsole s he hs.1))).differentiableWithinAt
    have hwθ := hhalf z (windowCenter_re _ _) w (ball_subset_ball (hrR.trans hRE) (mem_ball.mpr hwr))
    obtain ⟨c,hcnz,_,hP⟩ := hPole w hw hwθ
    obtain ⟨M,hM₀,hv⟩ := windowCoefficient_pole_asymptotic (mem_ball.mpr hwr) hzρ he₀ her hvertical hP
    obtain ⟨M',hM'₀,hr'⟩ := windowCoefficient_bound he₀ heR hreal
    have hc : 0 < ‖c‖/d := div_pos (norm_pos_iff.mpr hcnz) hpos
    refine positive_constant_not_bounded_by_two_smaller_rates hc hpos he₁
      (heR.le.trans hRE) (M := M+M') (D := D) (fun N => ?_)
    obtain ⟨n,hn,hN⟩ := hM N
    refine ⟨n,hn,?_⟩
    have hz := hN γ
    rw [← windowCoefficient_eq_moment hg hK hglobal hΦ hσ γ n,
      ← windowCoefficient_eq_moment hg hK hglobal hΦ hσ 0 n] at hz
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hz
    have hV : ‖windowCoefficient Φ z n‖+(windowCoefficient Φ (σ:ℂ) n).re ≤ D/(σ-θ)^n := hz
    have hU := hv n
    have hRnorm := hr' n
    have hre : -‖windowCoefficient Φ (σ:ℂ) n‖ ≤ (windowCoefficient Φ (σ:ℂ) n).re :=
      (abs_le.mp (Complex.abs_re_le_norm _)).1
    have hcoef := norm_sub_norm_le (c/(z-w)^(n+1)) (windowCoefficient Φ z n)
    rw [norm_sub_rev] at hcoef
    have hdist : ‖z-w‖ = d := by rw [← dist_eq_norm, dist_comm]
    rw [norm_div, norm_pow, hdist, pow_succ', ← div_div] at hcoef
    rw [add_div]
    linarith
  · obtain ⟨r,w,hw,hwi,hpos,hwr,hrE,hsole⟩ := hreal
    let z : ℂ := σ
    let d : ℝ := dist w z
    let e : ℝ := (d+r)/2
    have hd : d = σ-w.re := by
      simpa [z,hwi,windowCenter] using dist_vertical_projection w (hRe' w hw)
    have hzw : z-w = (d:ℂ) := by apply Complex.ext <;> simp [z,hwi,hd]
    have he₁ : d < e := by dsimp [e]; linarith
    have her : e < r := by dsimp [e]; linarith
    have he₀ : 0 < e := hpos.trans he₁
    have hne : z ≠ w := by
      intro he
      have hzre := hRe' w hw
      rw [← he, show z.re = σ from Complex.ofReal_re _] at hzre
      exact (lt_irrefl _ hzre)
    have hDiff : DifferentiableOn ℂ Φ (ball z r \ {w}) := by
      intro s hs
      exact (hdiff s (hhalf z (Complex.ofReal_re _) s (ball_subset_ball hrE hs.1))
        (fun he => hs.2 (hsole s he hs.1))).differentiableWithinAt
    have hwθ := hhalf z (Complex.ofReal_re _) w (ball_subset_ball hrE (mem_ball.mpr hwr))
    obtain ⟨c,_,hc,hP⟩ := hPole w hw hwθ
    obtain ⟨M,_,hM'⟩ := windowCoefficient_pole_asymptotic (mem_ball.mpr hwr) hne he₀ her hDiff hP
    refine positive_constant_not_bounded_by_two_smaller_rates (div_pos (hc hwi) hpos) hpos he₁
      (her.le.trans hrE) (M := M) (D := D) (fun N => ?_)
    obtain ⟨n,hn,hN⟩ := hM N
    refine ⟨n,hn,?_⟩
    have hz := hN 0
    rw [← windowCoefficient_eq_moment hg hK hglobal hΦ hσ 0 n] at hz
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hz
    have hv : (windowCoefficient Φ z n).re ≤ D/(σ-θ)^n := by
      exact (le_add_of_nonneg_left (norm_nonneg _)).trans hz
    have hU := hM' n
    change ‖windowCoefficient Φ z n - c/(z-w)^(n+1)‖ ≤ _ at hU
    rw [hzw, ← Complex.ofReal_pow, pow_succ'] at hU
    have hcoef := (abs_le.mp (Complex.abs_re_le_norm
      (windowCoefficient Φ z n - c/(z-w)^(n+1)))).1
    rw [Complex.sub_re, hzw, ← Complex.ofReal_pow, Complex.div_ofReal_re,
      pow_succ', ← div_div] at hcoef
    linarith

end MasulloDirichletRamp

set_option autoImplicit false

open Complex Set Filter Topology
open scoped ComplexConjugate

namespace MasulloDirichletRamp

private theorem analyticAt_dslope_of_analyticAt {f : ℂ → ℂ} {z : ℂ}
    (h : AnalyticAt ℂ f z) : AnalyticAt ℂ (dslope f z) z := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

private theorem logFactor_order_finite {J : ℂ → ℂ} (hJ : Differentiable ℂ J)
    (hJ1 : J 1 ≠ 0) (ρ : ℂ) : analyticOrderAt J ρ ≠ ⊤ := by
  have h : AnalyticOnNhd ℂ J univ := fun s _ => hJ.analyticAt s
  exact h.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (1:ℂ)) (mem_univ ρ) (by
      rw [analyticOrderAt_eq_zero.mpr (Or.inr hJ1)]
      simp)

private theorem logDerived_eq_order_term {J : ℂ → ℂ} (hJ : Differentiable ℂ J)
    (hJ1 : J 1 ≠ 0) {ρ : ℂ} (hρ : J ρ = 0) :
    ∃ (m : ℕ) (H : ℂ → ℂ), 0 < m ∧ AnalyticAt ℂ H ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, deriv J s / J s = (m:ℂ)/(s-ρ) + H s := by
  have hAnalytic : AnalyticAt ℂ J ρ := hJ.analyticAt _
  obtain ⟨F,hF,hFρ,hFactor⟩ := hAnalytic.analyticOrderAt_ne_top.mp (logFactor_order_finite hJ hJ1 ρ)
  let m := analyticOrderNatAt J ρ
  have hm : 0 < m := by
    have hn := hAnalytic.analyticOrderAt_ne_zero.mpr hρ
    rw [← Nat.cast_analyticOrderNatAt (logFactor_order_finite hJ hJ1 ρ)] at hn
    by_contra! h
    apply hn
    change (m:ℕ∞) = 0
    rw [Nat.eq_zero_of_le_zero h, Nat.cast_zero]
  let H := fun s : ℂ => deriv F s / F s
  refine ⟨m,H,hm,hF.deriv.div hF hFρ,?_⟩
  have hFact : J =ᶠ[𝓝 ρ] fun s => (s-ρ)^m*F s :=
    hFactor.mono (fun _ h => by simpa only [smul_eq_mul] using h)
  have hLoc : ∀ᶠ s : ℂ in 𝓝 ρ, J =ᶠ[𝓝 s] fun z => (z-ρ)^m*F z :=
    eventually_eventually_nhds.mpr hFact
  have hFnear : ∀ᶠ s in 𝓝 ρ, F s ≠ 0 := hF.continuousAt.eventually_ne hFρ
  have ha := hF.eventually_analyticAt
  filter_upwards [hLoc.filter_mono nhdsWithin_le_nhds, hFnear.filter_mono nhdsWithin_le_nhds,
    ha.filter_mono nhdsWithin_le_nhds, eventually_mem_nhdsWithin] with s hs hFn hAn hsρ
  have hs' : s ≠ ρ := hsρ
  have hdiff : HasDerivAt (fun z : ℂ => (z-ρ)^m) ((m:ℂ)*(s-ρ)^(m-1)) s := by
    have he := (hasDerivAt_pow m (s-ρ)).comp s ((hasDerivAt_id s).sub_const ρ)
    simpa only [Function.comp_def, id_eq, mul_one] using he
  have hequiv : (s-ρ)^m = (s-ρ)^(m-1)*(s-ρ) := by
    conv_lhs => rw [show m = (m-1)+1 by omega, pow_succ]
  rw [hs.deriv_eq, hs.self_of_nhds]
  change deriv ((fun z : ℂ => (z-ρ)^m) * F) s / ((s-ρ)^m * F s) = _
  rw [(hdiff.mul hAn.differentiableAt.hasDerivAt).deriv]
  change (((m:ℂ)*(s-ρ)^(m-1))*F s+(s-ρ)^m*deriv F s)/((s-ρ)^m*F s) =
    (m:ℂ)/(s-ρ)+deriv F s / F s
  rw [hequiv]
  field_simp [hFn, sub_ne_zero.mpr hs', pow_ne_zero _ (sub_ne_zero.mpr hs')]

private noncomputable def reflected (f : ℂ → ℂ) : ℂ → ℂ := conj ∘ f ∘ conj

private theorem reflected_hasDerivAt {f : ℂ → ℂ} {z : ℂ} {a : ℂ} (h : HasDerivAt f a (conj z)) :
    HasDerivAt (reflected f) (conj a) z := by
  simpa only [reflected, conj_conj] using h.conj_conj

private theorem reflected_differentiable {f : ℂ → ℂ} (h : Differentiable ℂ f) :
    Differentiable ℂ (reflected f) :=
  fun z => (reflected_hasDerivAt (h (conj z)).hasDerivAt).differentiableAt

variable {q : ℕ} [NeZero q]

/-- Multiplying the Dirichlet L-function by its reflected conjugate packages
both sets of zeros into one entire function. -/
private noncomputable def dirichletPair (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  χ.LFunction s * reflected χ.LFunction s

private theorem dirichletL_differentiable {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    Differentiable ℂ χ.LFunction := fun z => χ.differentiableAt_LFunction z (.inr hχ)

private theorem dirichletPair_differentiable {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    Differentiable ℂ (dirichletPair χ) :=
  (dirichletL_differentiable hχ).mul (reflected_differentiable (dirichletL_differentiable hχ))

private theorem dirichletPair_ne_zero_of_one_le_re {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 ≤ s.re) : dirichletPair χ s ≠ 0 := by
  exact mul_ne_zero (χ.LFunction_ne_zero_of_one_le_re (.inl hχ) hs)
    ((map_ne_zero (starRingEnd ℂ)).mpr
      (χ.LFunction_ne_zero_of_one_le_re (.inl hχ) (by simpa only [conj_re] using hs)))

private theorem dirichletPair_ne_zero_one {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    dirichletPair χ 1 ≠ 0 := dirichletPair_ne_zero_of_one_le_re hχ (by simp)

private theorem dirichletPair_zeros_isClosed_and_isDiscrete {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    IsClosed {s : ℂ | dirichletPair χ s = 0} ∧ IsDiscrete {s : ℂ | dirichletPair χ s = 0} := by
  have hA : AnalyticOnNhd ℂ (dirichletPair χ) univ := fun s _ => (dirichletPair_differentiable hχ).analyticAt s
  have h := hA.preimage_zero_mem_codiscrete (dirichletPair_ne_zero_one hχ)
  refine ⟨isClosed_eq (dirichletPair_differentiable hχ).continuous continuous_const, ?_⟩
  have he : {s : ℂ | dirichletPair χ s = 0} = dirichletPair χ ⁻¹' {0} := by ext s; simp
  rw [he]
  simpa only [preimage_compl, compl_compl] using (mem_codiscrete'.mp h).2

private noncomputable def dirichletLogDerivative (χ : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  deriv χ.LFunction z / χ.LFunction z

private noncomputable def halfPairLogDerivative (χ : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  (deriv (dirichletPair χ) z / dirichletPair χ z)/2

private theorem halfPairLogDerivative_eq {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {z : ℂ} (hL : χ.LFunction z ≠ 0) (hLc : χ.LFunction (conj z) ≠ 0) :
    halfPairLogDerivative χ z = (dirichletLogDerivative χ z + conj (dirichletLogDerivative χ (conj z)))/2 := by
  have hD := dirichletL_differentiable hχ
  have hd := (reflected_hasDerivAt (hD (conj z)).hasDerivAt).deriv
  unfold halfPairLogDerivative dirichletPair dirichletLogDerivative
  rw [deriv_fun_mul (hD z) ((reflected_differentiable hD) z), hd, map_div₀]
  change ((deriv χ.LFunction z * conj (χ.LFunction (conj z)) +
    χ.LFunction z * conj (deriv χ.LFunction (conj z))) /
    (χ.LFunction z * conj (χ.LFunction (conj z))))/2 = _
  field_simp [hL, (map_ne_zero (starRingEnd ℂ)).mpr hLc]

private theorem halfPairLogDerivative_one {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    halfPairLogDerivative χ 1 = ((dirichletLogDerivative χ 1).re : ℂ) := by
  have h := DirichletCharacter.LFunction_apply_one_ne_zero hχ
  rw [halfPairLogDerivative_eq hχ h (by simpa only [map_one] using h), map_one,
    ← Complex.re_eq_add_conj]

private noncomputable def dirichletWindowNumerator (χ : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  z*halfPairLogDerivative χ 1 - halfPairLogDerivative χ z

private noncomputable def dirichletWindowTransform (χ : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  dslope (dirichletWindowNumerator χ) 1 z / z

private theorem dirichletWindowTransform_eq {χ : DirichletCharacter ℂ q} {z : ℂ} (h₁ : z ≠ 1) :
    dirichletWindowTransform χ z =
      (z*halfPairLogDerivative χ 1 - halfPairLogDerivative χ z) / (z*(z-1)) := by
  unfold dirichletWindowTransform
  rw [dslope_of_ne _ h₁, slope_def_field, show dirichletWindowNumerator χ 1 = 0 by simp [dirichletWindowNumerator],
    sub_zero, div_div, mul_comm (z-1), dirichletWindowNumerator]

private theorem dirichletWindowTransform_analytic {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {z : ℂ} (hz : z ≠ 0) (hJ : dirichletPair χ z ≠ 0) : AnalyticAt ℂ (dirichletWindowTransform χ) z := by
  have hA := (dirichletPair_differentiable hχ).analyticAt z
  have hNum : AnalyticAt ℂ (dirichletWindowNumerator χ) z :=
    (analyticAt_id.mul analyticAt_const).sub ((hA.deriv.div hA hJ).div analyticAt_const (by norm_num))
  unfold dirichletWindowTransform
  apply AnalyticAt.div _ analyticAt_id hz
  by_cases h₁ : z = 1
  · subst z
    exact analyticAt_dslope_of_analyticAt hNum
  · have hEq : dslope (dirichletWindowNumerator χ) 1 =ᶠ[𝓝 z]
        fun p => (dirichletWindowNumerator χ p - dirichletWindowNumerator χ 1)/(p-1) := by
      filter_upwards [isOpen_ne.mem_nhds h₁] with p hp
      rw [dslope_of_ne _ hp,slope_def_field]
    exact ((hNum.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr h₁)).congr hEq.symm

private theorem dirichletWindowTransform_has_pole {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hz : dirichletPair χ ρ = 0) :
    ∃ c : ℂ, c ≠ 0 ∧ (ρ.im = 0 → 0 < c.re) ∧ ∃ F : ℂ → ℂ, AnalyticAt ℂ F ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, dirichletWindowTransform χ s = c/(s-ρ)+F s := by
  have hρ₀ : ρ ≠ 0 := ne_zero_of_re_pos hρ
  have hρR : ρ.re < 1 := lt_of_not_ge fun hh => (dirichletPair_ne_zero_of_one_le_re hχ hh) hz
  have hρ₁ : ρ ≠ 1 := fun e => dirichletPair_ne_zero_one hχ (e ▸ hz)
  obtain ⟨m,H,hm,hH,hmH⟩ := logDerived_eq_order_term (dirichletPair_differentiable hχ)
    (dirichletPair_ne_zero_one hχ) hz
  let b (s : ℂ) := 1/(s*(s-1))
  have hb : AnalyticAt ℂ b ρ := analyticAt_const.div
    (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
    (mul_ne_zero hρ₀ (sub_ne_zero.mpr hρ₁))
  let c := -((m:ℂ)/2)*b ρ
  have hmC : (m:ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hc : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (div_ne_zero hmC (by norm_num)))
    (one_div_ne_zero (mul_ne_zero hρ₀ (sub_ne_zero.mpr hρ₁)))
  have hSign (h : ρ.im = 0) : 0 < c.re := by
    have he : ρ = (ρ.re:ℂ) := by apply Complex.ext <;> simp [h]
    have hCe : c = ((-((m:ℝ)/2)*(1/(ρ.re*(ρ.re-1))) : ℝ) : ℂ) := by
      dsimp [c,b]
      conv_lhs => rw [he]
      push_cast
      rfl
    rw [hCe, ofReal_re]
    have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
    exact mul_pos_of_neg_of_neg (by linarith) (one_div_neg.mpr (mul_neg_of_pos_of_neg hρ (by linarith)))
  let F (s : ℂ) := (s*halfPairLogDerivative χ 1-H s/2)*b s - ((m:ℂ)/2)*dslope b ρ s
  have hf : AnalyticAt ℂ F ρ :=
    ((analyticAt_id.mul analyticAt_const).sub (hH.div analyticAt_const (by norm_num))).mul hb |>.sub
      (analyticAt_const.mul (analyticAt_dslope_of_analyticAt hb))
  refine ⟨c,hc,hSign,F,hf,?_⟩
  have hnear₁ : ∀ᶠ s : ℂ in 𝓝 ρ, s ≠ 1 := isOpen_ne.mem_nhds hρ₁
  filter_upwards [hmH,hnear₁.filter_mono nhdsWithin_le_nhds,eventually_mem_nhdsWithin] with s hs hs₁ hsρ
  have hs' : s ≠ ρ := hsρ
  rw [dirichletWindowTransform_eq hs₁]
  unfold halfPairLogDerivative
  rw [hs]
  dsimp [c,F]
  rw [dslope_of_ne _ hs', slope_def_field]
  simp only [b, halfPairLogDerivative, div_eq_mul_inv, one_mul]
  ring

end MasulloDirichletRamp

set_option autoImplicit false
set_option maxHeartbeats 3000000

open ArithmeticFunction Complex Filter Finset Set MeasureTheory Topology
open scoped ComplexConjugate

namespace MasulloDirichletRamp

private noncomputable def rampWeight (n : ℕ) (x : ℝ) : ℝ := max (x/(n:ℝ)-1) 0

private theorem rampWeight_zero_off_range {n : ℕ} {x : ℝ} (h : n ∉ Finset.range (⌊x⌋₊+1)) :
    rampWeight n x = 0 := by
  have hn : ⌊x⌋₊+1 ≤ n := by simpa using h
  have hn₀ : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx : x ≤ (n:ℝ) := (Nat.lt_floor_add_one x).le.trans (by exact_mod_cast hn)
  unfold rampWeight
  exact max_eq_right (sub_nonpos.mpr ((div_le_one hn₀).mpr hx))

private theorem vonMangoldt_le_nat (n : ℕ) : vonMangoldt n ≤ (n:ℝ) :=
  vonMangoldt_le_log.trans (Real.log_le_self (Nat.cast_nonneg n))

private noncomputable def rampLaplaceTerm (n : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  (rampWeight n (Real.exp u) : ℂ) * Complex.exp (-s*(u:ℂ))

private theorem rampLaplaceTerm_zero (s : ℂ) : rampLaplaceTerm 0 s = 0 := by
  funext u
  simp [rampLaplaceTerm, rampWeight]

private theorem rampLaplaceTerm_integrable {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    IntegrableOn (rampLaplaceTerm n s) (Ioi 0) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [rampLaplaceTerm_zero]
    exact integrable_zero ℝ ℂ ((volume : Measure ℝ).restrict (Ioi 0))
  have hn₀ : 0 < (n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hdec : 1-s.re < 0 := by linarith
  have hi := (integrableOn_exp_mul_Ioi hdec 0).const_mul ((n:ℝ)⁻¹)
  have hmeas : Measurable (rampLaplaceTerm n s) := by unfold rampLaplaceTerm rampWeight; fun_prop
  refine hi.mono' hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
  have he : (-s*(u:ℂ)).re = -s.re*u := by simp [Complex.mul_re]
  have hle : rampWeight n (Real.exp u) ≤ Real.exp u/(n:ℝ) :=
    max_le (by linarith) (by positivity)
  have hh : 0 ≤ rampWeight n (Real.exp u) := le_max_right _ _
  change ‖rampLaplaceTerm n s u‖ ≤ (n:ℝ)⁻¹*Real.exp ((1-s.re)*u)
  rw [rampLaplaceTerm, norm_mul, Complex.norm_real, Real.norm_of_nonneg hh, Complex.norm_exp, he]
  calc
    _ ≤ (Real.exp u/(n:ℝ)) * Real.exp (-s.re*u) :=
      mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _)
    _ = (n:ℝ)⁻¹*(Real.exp u*Real.exp (-s.re*u)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

private theorem rampLaplaceTerm_integral {n : ℕ} (hn : 0 < n) {s : ℂ} (hs : 1 < s.re) :
    (∫ u in Ioi (0:ℝ), rampLaplaceTerm n s u) = (n:ℂ)^(-s)/(s*(s-1)) := by
  have hn₀ : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn₁ : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  let l := Real.log (n:ℝ)
  have hl : 0 ≤ l := Real.log_nonneg (by exact_mod_cast hn)
  have hr : (-(s-1)).re < 0 := by simp [Complex.sub_re]; linarith
  have hr' : (-s).re < 0 := by simp; linarith
  let F (u : ℝ) := (n:ℂ)⁻¹*Complex.exp (-(s-1)*(u:ℂ))-Complex.exp (-s*(u:ℂ))
  have he : rampLaplaceTerm n s = (Ioi l).indicator F := by
    funext u
    by_cases hu : u ∈ Ioi l
    · have hx : (n:ℝ) < Real.exp u := by
        simpa [l, Real.exp_log hn₀] using Real.exp_lt_exp.mpr hu
      have hw : 0 ≤ Real.exp u/(n:ℝ)-1 := sub_nonneg.mpr ((one_le_div hn₀).mpr hx.le)
      rw [indicator_of_mem hu, rampLaplaceTerm, rampWeight, max_eq_left hw]
      push_cast
      have h : Complex.exp (-(s-1)*(u:ℂ)) = Complex.exp (u:ℂ)*Complex.exp (-s*(u:ℂ)) := by
        rw [← Complex.exp_add]; congr 1; ring
      dsimp [F]
      rw [h]
      ring
    · have hx : Real.exp u ≤ (n:ℝ) := by
        have h : u ≤ l := le_of_not_gt hu
        simpa [l, Real.exp_log hn₀] using Real.exp_le_exp.mpr h
      rw [indicator_of_notMem hu, rampLaplaceTerm, rampWeight,
        max_eq_right (sub_nonpos.mpr ((div_le_one hn₀).mpr hx)), Complex.ofReal_zero, zero_mul]
  have hs₀ : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hs₁ : s-1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  rw [he, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi hl)]
  dsimp [F]
  rw [integral_sub ((integrableOn_exp_mul_complex_Ioi hr l).const_mul _)
    (integrableOn_exp_mul_complex_Ioi hr' l), integral_const_mul,
    integral_exp_mul_complex_Ioi hr, integral_exp_mul_complex_Ioi hr']
  have hcp : Complex.exp (-s*(l:ℂ)) = (n:ℂ)^(-s) := by
    rw [Complex.cpow_def_of_ne_zero hn₁, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn₀.le]
    dsimp [l]
    rw [mul_comm]
  have hex : Complex.exp (-(s-1)*(l:ℂ)) = Complex.exp (-s*(l:ℂ))*(n:ℂ) := by
    rw [show -(s-1)*(l:ℂ) = -s*(l:ℂ)+(l:ℂ) by ring, Complex.exp_add,
      ← Complex.ofReal_exp, show Real.exp l = (n:ℝ) by exact Real.exp_log hn₀,
      Complex.ofReal_natCast]
  rw [hex,hcp]
  field_simp [hs₀,hs₁,hn₁]
  ring

private theorem norm_rampLaplaceTerm_eq_real_cast (n : ℕ) (s : ℂ) (u : ℝ) :
    (‖rampLaplaceTerm n s u‖:ℂ) = rampLaplaceTerm n ((s.re:ℝ):ℂ) u := by
  have hre : (-s*(u:ℂ)).re = -s.re*u := by simp [Complex.mul_re]
  have h : 0 ≤ rampWeight n (Real.exp u) := le_max_right _ _
  simp only [rampLaplaceTerm, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg h, Complex.norm_exp, hre]
  push_cast
  rfl

private theorem rampLaplaceTerm_integral_norm {n : ℕ} (hn : 0 < n) {s : ℂ} (hs : 1 < s.re) :
    (∫ u in Ioi (0:ℝ), ‖rampLaplaceTerm n s u‖) =
      (n:ℝ)^(-s.re)/(s.re*(s.re-1)) := by
  apply Complex.ofReal_injective
  have hnorm : ((∫ u in Ioi (0:ℝ), ‖rampLaplaceTerm n s u‖ : ℝ) : ℂ) =
      ∫ u in Ioi (0:ℝ), rampLaplaceTerm n ((s.re:ℝ):ℂ) u := by
    rw [← integral_complex_ofReal]
    exact setIntegral_congr_fun measurableSet_Ioi (fun u _ => norm_rampLaplaceTerm_eq_real_cast n s u)
  rw [hnorm, rampLaplaceTerm_integral hn (by simpa : 1 < ((s.re:ℝ):ℂ).re)]
  push_cast
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rfl

private noncomputable def weightedRampTerm (n : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  (vonMangoldt n : ℂ) * rampLaplaceTerm n s u

private theorem weightedRampTerm_integrable {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    IntegrableOn (weightedRampTerm n s) (Ioi 0) := (rampLaplaceTerm_integrable hs n).const_mul _

private theorem summable_weightedRamp_integral_norm {s : ℂ} (hs : 2 < s.re) :
    Summable (fun n : ℕ => ∫ u in Ioi (0:ℝ), ‖weightedRampTerm n s u‖) := by
  let D : ℝ := s.re*(s.re-1)
  have hσ : 1 < s.re := by linarith
  have hD : 0 < D := mul_pos (by linarith) (sub_pos.mpr hσ)
  have hsum : Summable (fun n : ℕ => ((n:ℝ)^(s.re-1))⁻¹ / D) :=
    (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < s.re-1)).div_const _
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _))
    (fun n => ?_) hsum
  rcases eq_or_ne n 0 with rfl | hn
  · simp [weightedRampTerm, div_nonneg, inv_nonneg, Real.rpow_nonneg, hD.le]
  · rw [show (fun u => ‖weightedRampTerm n s u‖) =
        (fun u => vonMangoldt n * ‖rampLaplaceTerm n s u‖) by
      funext u
      rw [weightedRampTerm, norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]]
    rw [integral_const_mul, rampLaplaceTerm_integral_norm (Nat.pos_of_ne_zero hn) hσ]
    have hn₀ : 0 < (n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have h : (n:ℝ)*(n:ℝ)^(-s.re) = ((n:ℝ)^(s.re-1))⁻¹ := by
      conv_lhs => arg 1; rw [← Real.rpow_one (n:ℝ)]
      rw [← Real.rpow_add hn₀, ← Real.rpow_neg hn₀.le]
      congr 1
      ring
    calc
      _ ≤ (n:ℝ)*((n:ℝ)^(-s.re)/D) :=
        mul_le_mul_of_nonneg_right (vonMangoldt_le_nat n) (by positivity)
      _ = _ := by rw [← mul_div_assoc, h]

private theorem weightedRampTerm_integral {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    (∫ u in Ioi (0:ℝ), weightedRampTerm n s u) =
      LSeries.term (fun k => (vonMangoldt k:ℂ)) s n/(s*(s-1)) := by
  by_cases hn : n = 0
  · simp [hn, weightedRampTerm]
  · unfold weightedRampTerm
    rw [integral_const_mul, rampLaplaceTerm_integral (Nat.pos_of_ne_zero hn) hs,
      LSeries.term_of_ne_zero hn, Complex.cpow_neg]
    ring

private noncomputable def realPrimeRamp (a : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ n ∈ range (⌊y⌋₊+1), vonMangoldt n * a n * rampWeight n y

private theorem realPrimeRamp_measurable (a : ℕ → ℝ) : Measurable (realPrimeRamp a) := by
  have h (y : ℝ) : realPrimeRamp a y = ∑' n : ℕ, vonMangoldt n * a n * rampWeight n y := by
    symm
    exact tsum_eq_sum (fun n hn => by rw [rampWeight_zero_off_range hn, mul_zero])
  rw [funext h]
  apply Measurable.tsum
  intro n
  unfold rampWeight
  fun_prop

private theorem realPrimeRamp_growth (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1) {y : ℝ} (hy : 1 ≤ y) :
    |realPrimeRamp a y| ≤ 2*y^2 := by
  have hy₀ : 0 ≤ y := zero_le_one.trans hy
  have hterm (n : ℕ) : vonMangoldt n * rampWeight n y ≤ y := by
    by_cases hn : n = 0
    · subst n
      simpa using hy₀
    · have hn₀ : 0 < (n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hnon : 0 ≤ y/(n:ℝ) := div_nonneg hy₀ hn₀.le
      have hl : rampWeight n y ≤ y/(n:ℝ) := max_le (by linarith) hnon
      calc
        _ ≤ (n:ℝ)*(y/(n:ℝ)) :=
          mul_le_mul (vonMangoldt_le_nat n) hl (le_max_right _ _) hn₀.le
        _ = y := by field_simp
  have hf : (⌊y⌋₊:ℝ) ≤ y := Nat.floor_le hy₀
  unfold realPrimeRamp
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ n ∈ range (⌊y⌋₊+1), y := by
      apply sum_le_sum
      intro n _
      rw [abs_mul, abs_mul (vonMangoldt n) (a n), abs_of_nonneg vonMangoldt_nonneg,
        abs_of_nonneg (show 0 ≤ rampWeight n y from le_max_right _ _)]
      exact (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right vonMangoldt_nonneg (ha n)) (le_max_right _ _)).trans (hterm n)
    _ = ((⌊y⌋₊:ℝ)+1)*y := by simp [Nat.cast_add]
    _ ≤ (y+1)*y := mul_le_mul_of_nonneg_right (add_le_add hf le_rfl) hy₀
    _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hy) hy₀]

private theorem realPrimeRamp_laplace (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1) {s : ℂ} (hs : 2 < s.re) :
    (∫ u in Ioi (0:ℝ), (realPrimeRamp a (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ))) =
      LSeries (fun n => ((vonMangoldt n * a n : ℝ):ℂ)) s/(s*(s-1)) := by
  have hσ : 1 < s.re := by linarith
  let H (n : ℕ) (u : ℝ) : ℂ := (a n:ℂ)*weightedRampTerm n s u
  have hi (n : ℕ) : IntegrableOn (H n) (Ioi (0:ℝ)) :=
    (weightedRampTerm_integrable hσ n).const_mul _
  have hNorm (n : ℕ) : (∫ u in Ioi (0:ℝ), ‖H n u‖) = |a n| * ∫ u in Ioi (0:ℝ), ‖weightedRampTerm n s u‖ := by
    simp only [H,norm_mul,Complex.norm_real,Real.norm_eq_abs,integral_const_mul]
  have hsum : Summable fun n => ∫ u in Ioi (0:ℝ), ‖H n u‖ := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) _
      (summable_weightedRamp_integral_norm hs)
    intro n
    rw [hNorm]
    exact mul_le_of_le_one_left (integral_nonneg fun _ => norm_nonneg _) (ha n)
  have hhs := hasSum_integral_of_summable_integral_norm hi hsum
  have hPoint (u : ℝ) : (∑' n, H n u) =
      (realPrimeRamp a (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ)) := by
    rw [tsum_eq_sum (s := range (⌊Real.exp u⌋₊+1)) (by
      intro n hn
      dsimp only [H,weightedRampTerm,rampLaplaceTerm]
      rw [rampWeight_zero_off_range hn, Complex.ofReal_zero,zero_mul,mul_zero,mul_zero])]
    simp only [realPrimeRamp, Complex.ofReal_mul, Complex.ofReal_sum, sum_mul]
    apply sum_congr rfl
    intro n _
    dsimp [H,weightedRampTerm,rampLaplaceTerm]
    ring
  have hTerm (n : ℕ) : (∫ u in Ioi (0:ℝ), H n u) =
      LSeries.term (fun n => ((vonMangoldt n*a n : ℝ):ℂ)) s n/(s*(s-1)) := by
    dsimp [H]
    rw [integral_const_mul, weightedRampTerm_integral hσ]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp only [LSeries.term_of_ne_zero hn, Complex.ofReal_mul]
      ring
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun u _ => hPoint u), ← hhs.tsum_eq]
  simp_rw [hTerm]
  rw [tsum_div_const]
  rfl

private theorem real_twist_term_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) :
    let a : ℕ → ℂ := fun j => χ (j:ZMod q)*(vonMangoldt j:ℂ)
    (LSeries.term a s n+conj (LSeries.term a (conj s) n))/2 =
      LSeries.term (fun j => ((vonMangoldt j*(χ (j:ZMod q)).re : ℝ):ℂ)) s n := by
  intro a
  by_cases hn : n = 0
  · simp [hn]
  have harg : (n:ℂ).arg ≠ Real.pi := by rw [Complex.natCast_arg]; exact Real.pi_pos.ne
  have hpow : conj ((n:ℂ)^(conj s)) = (n:ℂ)^s := by
    simpa using (Complex.conj_cpow (n:ℂ) s harg).symm
  simp only [LSeries.term_of_ne_zero hn, map_div₀, hpow, Complex.ofReal_mul, a, map_mul,
    Complex.conj_ofReal]
  rw [Complex.re_eq_add_conj]
  ring

private theorem real_twist_LSeries_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (fun n => ((vonMangoldt n * (χ (n:ZMod q)).re : ℝ):ℂ)) s =
      (-deriv χ.LFunction s / χ.LFunction s +
        conj (-deriv χ.LFunction (conj s) / χ.LFunction (conj s)))/2 := by
  let a : ℕ → ℂ := fun n => χ (n:ZMod q)*(vonMangoldt n:ℂ)
  have hc : 1 < (conj s).re := by simpa only [conj_re] using hs
  have hA : HasSum (LSeries.term a s) (LSeries a s) := (χ.LSeriesSummable_twist_vonMangoldt hs).LSeriesHasSum
  have hB : HasSum (LSeries.term a (conj s)) (LSeries a (conj s)) :=
    (χ.LSeriesSummable_twist_vonMangoldt hc).LSeriesHasSum
  have hC : HasSum (fun n => conj (LSeries.term a (conj s) n)) (conj (LSeries a (conj s))) :=
    Complex.conjCLE.toContinuousLinearMap.hasSum hB
  have hSum : HasSum (fun n => (LSeries.term a s n+conj (LSeries.term a (conj s) n))/2)
      ((LSeries a s+conj (LSeries a (conj s)))/2) := (hA.add hC).div_const (2:ℂ)
  have hL (z : ℂ) (hz : 1 < z.re) : LSeries a z = -deriv χ.LFunction z / χ.LFunction z := by
    rw [χ.deriv_LFunction_eq_deriv_LSeries hz, χ.LFunction_eq_LSeries hz]
    exact χ.LSeries_twist_vonMangoldt_eq hz
  rw [← hL s hs, ← hL (conj s) hc]
  exact (hSum.congr_fun (fun n => (real_twist_term_eq χ s n).symm)).tsum_eq

end MasulloDirichletRamp

namespace MasulloDirichletRamp

private theorem exponential_const_integral {s : ℂ} (hs : 0 < s.re) :
    (∫ u in Ioi (0:ℝ), Complex.exp (-s*(u:ℂ))) = 1/s := by
  have h := integral_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0
  simpa [div_eq_mul_inv] using h

theorem upper_windows_in_log_coordinate {g : ℝ → ℝ} {θ C δ : ℝ}
    (h : ∀ X : ℝ, ∃ Y : ℝ, X ≤ Y ∧ ∀ x ∈ Icc Y (Y^(1+δ)), g x ≤ C*x^θ) :
    ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∀ u ∈ Icc U ((1+δ)*U),
      g (Real.exp u) ≤ C*Real.exp (θ*u) := by
  intro U₀
  obtain ⟨Y,hY,hWin⟩ := h (Real.exp U₀)
  have hY₀ := (Real.exp_pos U₀).trans_le hY
  let U := Real.log Y
  have hu₀ : U₀ ≤ U := by
    exact (Real.le_log_iff_exp_le hY₀).mpr hY
  refine ⟨U,hu₀,fun u hu => ?_⟩
  have hLo : Y ≤ Real.exp u := by
    rw [← Real.exp_log hY₀]
    exact Real.exp_le_exp.mpr hu.1
  have hHi : Real.exp u ≤ Y^(1+δ) := by
    rw [Real.rpow_def_of_pos hY₀]
    exact Real.exp_le_exp.mpr (by simpa [U, mul_comm] using hu.2)
  have h := hWin _ ⟨hLo,hHi⟩
  simpa [Real.exp_mul, mul_comm θ] using h

section Dirichlet

variable {q : ℕ} [NeZero q]

/-- The physical input is the real character twist with its linear correction. -/
private noncomputable def dirichletRampError (χ : DirichletCharacter ℂ q) (y : ℝ) : ℝ :=
  realPrimeRamp (fun n => (χ (n:ZMod q)).re) y + y*(dirichletLogDerivative χ 1).re

private theorem dirichletRampError_measurable (χ : DirichletCharacter ℂ q) :
    Measurable (dirichletRampError χ) :=
  (realPrimeRamp_measurable _).add (measurable_id.mul_const _)

omit [NeZero q] in
private theorem realTwist_abs_le (χ : DirichletCharacter ℂ q) (n : ℕ) : |(χ (n:ZMod q)).re| ≤ 1 :=
  (Complex.abs_re_le_norm _).trans (χ.norm_le_one _)

private theorem dirichletRampError_growth (χ : DirichletCharacter ℂ q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, 0 ≤ u → |dirichletRampError χ (Real.exp u)| ≤ K*Real.exp (2*u) := by
  let c : ℝ := (dirichletLogDerivative χ 1).re
  refine ⟨2+|c|,by positivity, fun u hu => ?_⟩
  let y := Real.exp u
  have hy : 1 ≤ y := Real.one_le_exp hu
  have hY : y^2 = Real.exp (2*u) := by simpa [y] using (Real.exp_nat_mul u 2).symm
  rw [← hY]
  change |realPrimeRamp (fun n => (χ (n:ZMod q)).re) y + y*c| ≤ (2+|c|)*y^2
  calc
    _ ≤ |realPrimeRamp (fun n => (χ (n:ZMod q)).re) y|+|y*c| := abs_add_le _ _
    _ ≤ 2*y^2 + |c| * y^2 := by
      apply add_le_add (realPrimeRamp_growth _ (realTwist_abs_le χ) hy)
      rw [abs_mul, abs_of_nonneg (zero_le_one.trans hy), mul_comm y]
      exact mul_le_mul_of_nonneg_left (le_self_pow₀ hy (by decide)) (abs_nonneg _)
    _ = _ := by ring

private theorem dirichletWindowTransform_laplace {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {s : ℂ} (hs : 2 < s.re) :
    dirichletWindowTransform χ s =
      ∫ u in Ioi (0:ℝ), (dirichletRampError χ (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ)) := by
  let P (u : ℝ) := (realPrimeRamp (fun n => (χ (n:ZMod q)).re) (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ))
  let Q (u : ℝ) := (halfPairLogDerivative χ 1)*Complex.exp (-(s-1)*(u:ℂ))
  have ha : 0 < (s-1).re := by rw [sub_re,one_re]; linarith
  have hQ : IntegrableOn Q (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi (a := -(s-1)) (by simpa using ha) 0).const_mul _
  have hQI : (∫ u in Ioi (0:ℝ), Q u) = halfPairLogDerivative χ 1/(s-1) := by
    dsimp [Q]
    rw [integral_const_mul, exponential_const_integral ha]
    ring
  have hEq (u : ℝ) : (dirichletRampError χ (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ)) = P u+Q u := by
    dsimp [dirichletRampError,P,Q]
    rw [halfPairLogDerivative_one hχ]
    have he : Complex.exp (-(s-1)*(u:ℂ)) = Complex.exp (u:ℂ)*Complex.exp (-s*(u:ℂ)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [he]
    push_cast
    ring
  obtain ⟨K,hK,hg⟩ := dirichletRampError_growth χ
  have hi := laplace_integrable_of_exponential_bound
    ((dirichletRampError_measurable χ).comp Real.continuous_exp.measurable) hK hg hs
  have he : (fun u : ℝ => ((dirichletRampError χ ∘ Real.exp) u:ℂ)*Complex.exp (-s*(u:ℂ))) = P+Q := funext hEq
  rw [he] at hi
  have hP : IntegrableOn P (Ioi 0) := by
    simpa only [add_sub_cancel_right] using hi.sub hQ
  have hPI : (∫ u in Ioi (0:ℝ), P u) = -(halfPairLogDerivative χ s)/(s*(s-1)) := by
    dsimp [P]
    rw [realPrimeRamp_laplace _ (realTwist_abs_le χ) hs, real_twist_LSeries_eq χ (by linarith : 1 < s.re)]
    rw [halfPairLogDerivative_eq hχ (χ.LFunction_ne_zero_of_one_le_re (.inl hχ) (by linarith))
      (χ.LFunction_ne_zero_of_one_le_re (.inl hχ) (by rw [conj_re]; linarith))]
    simp only [dirichletLogDerivative,neg_div,map_neg]
    ring
  have h0 : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  have h1 : s ≠ 1 := by intro he; rw [he,one_re] at hs; norm_num at hs
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hEq u),integral_add hP hQ,hPI,hQI,
    dirichletWindowTransform_eq h1]
  field_simp [h0,sub_ne_zero.mpr h1]
  ring

private theorem dirichlet_ne_zero_to_right_of_upper_windows {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {θ δ C : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) (hδ : 0 < δ) (hC : 0 ≤ C)
    (h : ∀ X : ℝ, ∃ Y : ℝ, X ≤ Y ∧ ∀ y ∈ Icc Y (Y^(1+δ)), dirichletRampError χ y ≤ C*y^θ) :
    ∀ s : ℂ, θ < s.re → χ.LFunction s ≠ 0 := by
  let Z := {z : ℂ | dirichletPair χ z = 0}
  obtain ⟨hZ,hZd⟩ := dirichletPair_zeros_isClosed_and_isDiscrete hχ
  obtain ⟨K,hK,hg⟩ := dirichletRampError_growth χ
  have hRe (z : ℂ) (hz : z ∈ Z) : z.re ≤ 2 := by
    by_contra! hc
    exact (dirichletPair_ne_zero_of_one_le_re hχ (by linarith : 1 ≤ z.re)) hz
  have hd (z : ℂ) (hz : θ < z.re) (hn : z ∉ Z) : DifferentiableAt ℂ (dirichletWindowTransform χ) z :=
    (dirichletWindowTransform_analytic hχ (ne_zero_of_re_pos (hθ.trans hz)) hn).differentiableAt
  have hz := no_poles_of_upper_windows (Z := Z) hZ hZd
    ((dirichletRampError_measurable χ).comp Real.continuous_exp.measurable) hK hC
    (by linarith : θ ≤ 2) hδ hg (upper_windows_in_log_coordinate h)
    (fun _ hs => dirichletWindowTransform_laplace hχ hs) hRe hd
    (fun ρ hρ hre => dirichletWindowTransform_has_pole hχ (hθ.trans hre) hρ)
  intro s hs hzero
  exact (not_le_of_gt hs) (hz s (show dirichletPair χ s = 0 by simp [dirichletPair,hzero]))

private theorem nonprincipal_dirichlet_zero_free_right (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 1/2 < s.re) : χ.LFunction s ≠ 0 := by
  by_cases h₁ : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (.inl hχ) h₁
  let θ := (1/2+s.re)/2
  have ht₀ : 1/2 < θ := by dsimp [θ]; linarith
  have ht₁ : θ < 1 := by dsimp [θ]; linarith
  have ht₂ : θ < s.re := by dsimp [θ]; linarith
  obtain ⟨δ,C,hδ,hC,hwin⟩ := GRH.nonprincipal_corrected_prime_ramp_upper_windows q χ hχ θ ht₀ ht₁
  apply dirichlet_ne_zero_to_right_of_upper_windows hχ (by linarith) ht₁ hδ hC _ s ht₂
  intro X
  obtain ⟨Y,hY,hw⟩ := hwin (max 1 X) (le_max_left _ _)
  exact ⟨Y,(le_max_right _ _).trans hY,hw⟩

private theorem nb_right_zero_free (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hpos : 0 < 2*s.re-1 := by linarith
  obtain ⟨J,hJ⟩ := exists_nat_gt (‖s‖^2 / (2*s.re-1))
  obtain ⟨c,H,hC⟩ := NymanBeurling.arbitrarily_small_remainder_certificates J
  let M : ℚ := ((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ)
  change M < 1/(J+1 : ℚ) at hC
  have hc : (M:ℝ) < 1/(J+1:ℝ) := by
    have ht := (Rat.cast_lt (K := ℝ)).mpr hC
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_add,Rat.cast_natCast] using ht
  have hh := NymanBeurling.finite_remainder_zero_obstruction s hs hs_one hz c H
  change 2*s.re-1 ≤ (M:ℝ)*‖s‖^2 at hh
  apply (not_lt_of_ge hh)
  calc
    _ ≤ (1/(J+1:ℝ))*‖s‖^2 := mul_le_mul_of_nonneg_right hc.le (sq_nonneg _)
    _ < 2*s.re-1 := by
      rw [one_div,inv_mul_eq_div,div_lt_iff₀ (by positivity)]
      have hh := (div_lt_iff₀ hpos).mp hJ
      nlinarith

private theorem principal_dirichlet_zero_free_right {s : ℂ} (hs : 1/2 < s.re) (h1 : s ≠ 1) :
    (1 : DirichletCharacter ℂ q).LFunction s ≠ 0 := by
  change DirichletCharacter.LFunctionTrivChar q s ≠ 0
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) h1]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro p hp hp0
    have hPr := Nat.prime_of_mem_primeFactors hp
    have hN : (1:ℝ) < p := by exact_mod_cast hPr.one_lt
    have he := congrArg norm (sub_eq_zero.mp hp0)
    rw [norm_one, norm_natCast_cpow_of_pos hPr.pos, neg_re] at he
    have hn : -s.re < 0 := by linarith
    exact (Real.rpow_lt_one_of_one_lt_of_neg hN hn).ne he.symm
  · exact nb_right_zero_free s hs h1

end Dirichlet

end MasulloDirichletRamp


private theorem all_dirichlet_zero_free_right (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : (1/2:ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : χ.LFunction s ≠ 0 := by
  by_cases hχ : χ = 1
  · subst χ
    exact MasulloDirichletRamp.principal_dirichlet_zero_free_right hs (fun h => hpole ⟨rfl,h⟩)
  · exact MasulloDirichletRamp.nonprincipal_dirichlet_zero_free_right χ hχ s hs


open scoped BigOperators
open Finset ArithmeticFunction



private theorem factored_sum {α : Type*} (s : Finset α) (l h : α → ℝ) (K : ℝ) :
    (∑ d ∈ s, l d * ∑ e ∈ s, l e * (K * h d * h e)) =
      K * (∑ d ∈ s, l d * h d) ^ 2 := by
  rw [pow_two, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  ring

private theorem centered_sum {α : Type*} (s : Finset α) (l h : α → ℝ)
    (A : α → α → ℝ) (K : ℝ) :
    (∑ d ∈ s, l d * ∑ e ∈ s, l e * A d e) =
      (∑ d ∈ s, l d * ∑ e ∈ s, l e * (A d e - K * h d * h e)) +
        K * (∑ d ∈ s, l d * h d) ^ 2 := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [factored_sum]
  ring


theorem GRH.moebius_bilinear_eq_centered
    (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) :
    (∑ d ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.moebius d : ℝ) *
      ∑ e ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.moebius e : ℝ) *
        (((Finset.Ioc 0 (N / (d * e))).filter
          (fun r => ((d * e * r : ℕ) : ZMod q) = a)).card : ℝ)) =
      GRH.centeredMoebiusBilinear q a N +
        (1 / (q : ℝ)) * (N : ℝ) *
          (GRH.reducedMoebiusHarmonic q N.sqrt) ^ 2 := by
  classical
  let h : ℕ → ℝ := fun d => if IsUnit (d : ZMod q) then 1 / (d : ℝ) else 0
  have harmonic :
      (∑ d ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.moebius d : ℝ) * h d) =
        GRH.reducedMoebiusHarmonic q N.sqrt := by
    unfold GRH.reducedMoebiusHarmonic
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hu : IsUnit (d : ZMod q) <;> simp [h, hu, div_eq_mul_inv]
  have kernel (d e : ℕ) :
      (if IsUnit (d : ZMod q) ∧ IsUnit (e : ZMod q) then
        (1 / (q : ℝ)) * (N : ℝ) / ((d : ℝ) * (e : ℝ)) else 0) =
      ((1 / (q : ℝ)) * (N : ℝ)) * h d * h e := by
    by_cases hd : IsUnit (d : ZMod q) <;> by_cases he : IsUnit (e : ZMod q) <;>
      simp [h, hd, he, div_eq_mul_inv, mul_inv_rev] <;> ring
  change (∑ d ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.moebius d : ℝ) *
      ∑ e ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.moebius e : ℝ) *
        GRH.moebiusProgressionCount q a N d e) = _
  unfold GRH.centeredMoebiusBilinear
  simp_rw [kernel]
  rw [← harmonic]
  exact centered_sum (Finset.Ioc 0 N.sqrt)
    (fun d => (ArithmeticFunction.moebius d : ℝ)) h
    (GRH.moebiusProgressionCount q a N) ((1 / (q : ℝ)) * (N : ℝ))


namespace GRH

lemma sqrt_rpow_weight_bound (N : ℕ) (σ : ℝ) (hone : σ < 1) :
    (N : ℝ) * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2 ≤ ((N : ℝ) + 1) ^ σ := by
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hU : 0 < (N.sqrt : ℝ) + 1 := by positivity
  have hX : 0 < (N : ℝ) + 1 := by positivity
  have hsqrt : (N : ℝ) + 1 ≤ ((N.sqrt : ℝ) + 1) ^ 2 := by
    have h := Nat.lt_succ_sqrt' N
    have h' : N + 1 ≤ (N.sqrt + 1) ^ 2 := by simpa [Nat.succ_eq_add_one] using Nat.succ_le_iff.mpr h
    exact_mod_cast h'
  have hp : (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2 ≤
      ((N : ℝ) + 1) ^ (σ - 1) := by
    have h := Real.rpow_le_rpow_of_nonpos hX hsqrt (by linarith : σ - 1 ≤ 0)
    rw [← Real.rpow_natCast_mul hU.le] at h
    rw [← Real.rpow_mul_natCast hU.le]
    convert h using 1 <;> congr 1 <;> ring
  calc
    (N : ℝ) * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2
        ≤ (N : ℝ) * (((N : ℝ) + 1) ^ (σ - 1)) := mul_le_mul_of_nonneg_left hp hN
    _ ≤ ((N : ℝ) + 1) * (((N : ℝ) + 1) ^ (σ - 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hX.le _)
    _ = ((N : ℝ) + 1) ^ σ := by
      nth_rw 1 [← Real.rpow_one ((N : ℝ) + 1)]
      rw [← Real.rpow_add hX]
      congr 1
      ring

lemma harmonic_main_weight_bound (N : ℕ) (σ K x : ℝ) (hone : σ < 1)
    (hK : 0 ≤ K) (hx : |x| ≤ K * ((N.sqrt : ℝ) + 1) ^ (σ - 1)) :
    (N : ℝ) * x ^ 2 ≤ K ^ 2 * ((N : ℝ) + 1) ^ σ := by
  have hs : x ^ 2 ≤ K ^ 2 * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2 := by
    have h := sq_le_sq₀ (abs_nonneg x) (by positivity : 0 ≤ K * ((N.sqrt : ℝ) + 1) ^ (σ - 1))
    have := h.mpr hx
    simpa only [sq_abs, mul_pow] using this
  calc
    (N : ℝ) * x ^ 2 ≤ (N : ℝ) *
        (K ^ 2 * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2) :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg N)
    _ = K ^ 2 * ((N : ℝ) * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2) := by ring
    _ ≤ K ^ 2 * ((N : ℝ) + 1) ^ σ :=
      mul_le_mul_of_nonneg_left (sqrt_rpow_weight_bound N σ hone) (sq_nonneg K)

end GRH



/- The only open inputs are corrected prime-ramp windows and the existing
Nyman--Beurling certificate/harmonic inputs.  The finite truncation and
averaging arguments below are proved here, without any bilinear ancestor. -/
private theorem centered_bound_from_windows
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : 1/2 < σ) (hone : σ < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ,
      |GRH.centeredMoebiusBilinear q a N| ≤ D*((N:ℝ)+1)^σ := by
  obtain ⟨C,hC,hP⟩ := GRH.uniform_mobius_liouville_progressions_of_zero_free
    (1/2) le_rfl (by norm_num) all_dirichlet_zero_free_right q σ hhalf
  have hB (N : ℕ) : |MobiusProgression.bilinear a N| ≤ (2+C)*((N:ℝ)+1)^σ := by
    have hi := MobiusProgression.weighted_identity a N
    have hb : MobiusProgression.bilinear a N =
        2 * MobiusProgression.partialSum a N.sqrt - MobiusProgression.partialSum a N := by linarith
    rw [hb]
    calc
      _ ≤ |2 * MobiusProgression.partialSum a N.sqrt| + |MobiusProgression.partialSum a N| := abs_sub _ _
      _ = 2 * |MobiusProgression.partialSum a N.sqrt| + |MobiusProgression.partialSum a N| := by
        rw [abs_mul]; norm_num
      _ ≤ 2 * ((N:ℝ)+1)^σ + C*((N:ℝ)+1)^σ := add_le_add
        (mul_le_mul_of_nonneg_left (MobiusProgression.short_bound a N σ hhalf.le) (by norm_num))
        (by rw [← MobiusProgression.parent_sum]; exact (hP a ha N).1)
      _ = _ := by ring
  obtain ⟨L,hL,hH⟩ := GRH.reduced_liouville_harmonic_power_decay q σ hhalf hone
  let K : ℝ := L * ∑' d : ℕ, ((d:ℝ)^(2*σ))⁻¹
  have hK : 0 ≤ K := mul_nonneg hL (tsum_nonneg (fun d => by positivity))
  have hM (U : ℕ) : |GRH.reducedMoebiusHarmonic q U| ≤ K*((U:ℝ)+1)^(σ-1) :=
    GRH.reduced_moebius_harmonic_le_of_liouville_harmonic_le q σ L hhalf hone.le hL hH U
  refine ⟨2+C+|(1/(q:ℝ))| *K^2, by positivity, fun N => ?_⟩
  have hid := GRH.moebius_bilinear_eq_centered q a N
  change MobiusProgression.bilinear a N = _ at hid
  have heq : GRH.centeredMoebiusBilinear q a N = MobiusProgression.bilinear a N -
      (1/(q:ℝ))*(N:ℝ)*(GRH.reducedMoebiusHarmonic q N.sqrt)^2 := by linarith
  rw [heq]
  calc
    _ ≤ |MobiusProgression.bilinear a N| +
        |(1/(q:ℝ))*(N:ℝ)*(GRH.reducedMoebiusHarmonic q N.sqrt)^2| := abs_sub _ _
    _ = |MobiusProgression.bilinear a N| +
        |(1/(q:ℝ))| *((N:ℝ)*(GRH.reducedMoebiusHarmonic q N.sqrt)^2) := by
      have hnabs : |(N:ℝ)| = (N:ℝ) := abs_of_nonneg (Nat.cast_nonneg N)
      have hsabs : |(GRH.reducedMoebiusHarmonic q N.sqrt)^2| =
          (GRH.reducedMoebiusHarmonic q N.sqrt)^2 := abs_of_nonneg (sq_nonneg _)
      simp only [abs_mul, hnabs, hsabs]
      ring
    _ ≤ (2+C)*((N:ℝ)+1)^σ + |(1/(q:ℝ))| *(K^2*((N:ℝ)+1)^σ) :=
      add_le_add (hB N) (mul_le_mul_of_nonneg_left
        (GRH.harmonic_main_weight_bound N σ K _ hone hK (hM N.sqrt)) (abs_nonneg _))
    _ = _ := by ring

private theorem square_block_mean_bound (F : ℕ → ℝ) (D σ : ℝ) (hD : 0 ≤ D) (hσ : 0 ≤ σ)
    (hF : ∀ N, |F N| ≤ D*((N:ℝ)+1)^σ) (u : ℕ) :
    |(∑ j ∈ Finset.range (2*u+1), F (u^2+j))/((2*u+1:ℕ):ℝ)| ≤
      (D*2^σ)*((u:ℝ)^2+1)^σ := by
  have hlen : (0:ℝ) < ((2*u+1:ℕ):ℝ) := by positivity
  have hb (j : ℕ) (hj : j ∈ Finset.range (2*u+1)) :
      |F (u^2+j)| ≤ (D*2^σ)*((u:ℝ)^2+1)^σ := by
    have hj' : j < 2*u+1 := Finset.mem_range.mp hj
    have hjr : (j:ℝ) ≤ 2*(u:ℝ) := by exact_mod_cast (by omega : j ≤ 2*u)
    have hx : ((u^2+j:ℕ):ℝ)+1 ≤ 2*((u:ℝ)^2+1) := by
      push_cast
      nlinarith [sq_nonneg ((u:ℝ)-1)]
    apply (hF _).trans
    calc
      _ ≤ D*(2*((u:ℝ)^2+1))^σ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hx hσ) hD
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity)]; ring
  rw [abs_div, abs_of_pos hlen]
  apply (div_le_iff₀ hlen).mpr
  calc
    _ ≤ ∑ j ∈ Finset.range (2*u+1), |F (u^2+j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (2*u+1), (D*2^σ)*((u:ℝ)^2+1)^σ := Finset.sum_le_sum hb
    _ = ((D*2^σ)*((u:ℝ)^2+1)^σ)*((2*u+1:ℕ):ℝ) := by simp [mul_comm]

open Finset in
theorem solution (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (σ : ℝ) (hhalf : 1/2 < σ) (hcap : σ ≤ 0.8749570698) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℕ,
      |(∑ j ∈ range (2*u+1), GRH.centeredMoebiusBilinear q a (u^2+j))/((2*u+1:ℕ):ℝ)| ≤
        C*((u:ℝ)^2+1)^σ := by
  obtain ⟨D,hD,hE⟩ := centered_bound_from_windows q a ha σ hhalf (by linarith)
  exact ⟨D*2^σ, by positivity, square_block_mean_bound _ D σ hD (by linarith) hE⟩
