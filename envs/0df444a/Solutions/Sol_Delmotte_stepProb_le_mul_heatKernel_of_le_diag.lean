-- Prove2me | solution 1 for Delmotte.stepProb_le_mul_heatKernel_of_le_diag
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-04T11:37:14.106154+00:00
-- url     : https://prove2.me/submissions/774107bd-4db2-433c-84fe-4075608e77b3

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels
universe u

section
/-!
# Kernel library for the Markov heat-kernel package

Substochastic kernels on a type `X` (no countability needed): non-negative entries, summable rows
with sums at most one. Their powers `stepProb`, Chapman–Kolmogorov, symmetry of powers, column
sums, and Poisson series facts used by the heat kernel.
-/

open DurrettProbability MarkovChain

namespace MarkovHK

variable {X : Type*}

/-- A substochastic kernel. -/
def IsSub (p : X → X → ℝ) : Prop :=
  (∀ x y, 0 ≤ p x y) ∧ (∀ x, Summable (p x)) ∧ ∀ x, ∑' y, p x y ≤ 1

lemma isSub_of_isTransition {p : X → X → ℝ} (h : IsTransition p) : IsSub p :=
  ⟨h.1, h.2.1, fun x => (h.2.2 x).le⟩

lemma IsSub.le_one {p : X → X → ℝ} (h : IsSub p) (x y : X) : p x y ≤ 1 :=
  le_trans ((h.2.1 x).le_tsum y fun z _ => h.1 x z) (h.2.2 x)

/-- Fubini for `a(w) q(w, z) r(z)`, `a ≥ 0` summable, `q` substochastic, `0 ≤ r ≤ 1`. -/
lemma summable_triple {a : X → ℝ} (ha0 : ∀ w, 0 ≤ a w) (has : Summable a) {q : X → X → ℝ}
    (hq : IsSub q) {r : X → ℝ} (hr0 : ∀ z, 0 ≤ r z) (hr1 : ∀ z, r z ≤ 1) :
    Summable (fun p : X × X => a p.1 * q p.1 p.2 * r p.2) := by
  have h0 : 0 ≤ (fun p : X × X => a p.1 * q p.1 p.2 * r p.2) := fun p =>
    mul_nonneg (mul_nonneg (ha0 _) (hq.1 _ _)) (hr0 _)
  have hrow : ∀ w, Summable (fun z => a w * q w z * r z) := fun w =>
    Summable.of_nonneg_of_le (fun z => h0 (w, z))
      (fun z => by
        have := mul_le_mul_of_nonneg_left (hr1 z) (mul_nonneg (ha0 w) (hq.1 w z))
        simpa using this)
      ((hq.2.1 w).mul_left (a w))
  refine (summable_prod_of_nonneg h0).mpr ⟨hrow, ?_⟩
  refine Summable.of_nonneg_of_le (fun w => tsum_nonneg fun z => h0 (w, z)) (fun w => ?_) has
  calc ∑' z, a w * q w z * r z ≤ ∑' z, a w * q w z :=
        Summable.tsum_le_tsum (fun z => by
          have := mul_le_mul_of_nonneg_left (hr1 z) (mul_nonneg (ha0 w) (hq.1 w z))
          simpa using this) (hrow w) ((hq.2.1 w).mul_left (a w))
    _ = a w * ∑' z, q w z := tsum_mul_left
    _ ≤ a w * 1 := mul_le_mul_of_nonneg_left (hq.2.2 w) (ha0 w)
    _ = a w := mul_one _

/-- Exchange of the order of summation for `a(w) q(w, z) r(z)`. -/
lemma tsum_comm_triple {a : X → ℝ} (ha0 : ∀ w, 0 ≤ a w) (has : Summable a) {q : X → X → ℝ}
    (hq : IsSub q) {r : X → ℝ} (hr0 : ∀ z, 0 ≤ r z) (hr1 : ∀ z, r z ≤ 1) :
    ∑' w, a w * ∑' z, q w z * r z = ∑' z, (∑' w, a w * q w z) * r z := by
  have hs := summable_triple ha0 has hq hr0 hr1
  have hcomm := Summable.tsum_comm (f := fun w z => a w * q w z * r z) hs
  have hcol : ∀ z, Summable (fun w => a w * q w z * r z) :=
    fun z => hs.prod_symm.prod_factor z
  calc ∑' w, a w * ∑' z, q w z * r z = ∑' w, ∑' z, a w * q w z * r z := by
        refine tsum_congr fun w => ?_
        rw [← tsum_mul_left]; exact tsum_congr fun z => by ring
    _ = ∑' z, ∑' w, a w * q w z * r z := hcomm.symm
    _ = ∑' z, (∑' w, a w * q w z) * r z := by
        refine tsum_congr fun z => ?_
        rw [← tsum_mul_right]

/-- The weighted column sums `z ↦ ∑_w a(w) q(w, z)` are summable with total `≤ ∑ a`. -/
lemma summable_col {a : X → ℝ} (ha0 : ∀ w, 0 ≤ a w) (has : Summable a) {q : X → X → ℝ}
    (hq : IsSub q) :
    Summable (fun z => ∑' w, a w * q w z) ∧ (∀ z, Summable (fun w => a w * q w z)) ∧
      ∑' z, ∑' w, a w * q w z ≤ ∑' w, a w := by
  have hs := summable_triple ha0 has hq (r := fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl)
  simp only [mul_one] at hs
  refine ⟨?_, fun z => ?_, ?_⟩
  · have := hs.prod_symm.prod
    simpa using this
  · have := hs.prod_symm.prod_factor z
    simpa using this
  · have h := tsum_comm_triple ha0 has hq (r := fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl)
    simp only [mul_one] at h
    rw [← h]
    refine Summable.tsum_le_tsum (fun w => ?_) ?_ has
    · calc a w * ∑' z, q w z ≤ a w * 1 := mul_le_mul_of_nonneg_left (hq.2.2 w) (ha0 w)
        _ = a w := mul_one _
    · refine Summable.of_nonneg_of_le (fun w => mul_nonneg (ha0 w) (tsum_nonneg (hq.1 w)))
        (fun w => ?_) has
      calc a w * ∑' z, q w z ≤ a w * 1 := mul_le_mul_of_nonneg_left (hq.2.2 w) (ha0 w)
        _ = a w := mul_one _

variable [DecidableEq X]

lemma stepProb_zero (p : X → X → ℝ) (x y : X) :
    stepProb p 0 x y = if x = y then 1 else 0 := rfl

lemma stepProb_succ (p : X → X → ℝ) (n : ℕ) (x y : X) :
    stepProb p (n + 1) x y = ∑' z, p x z * stepProb p n z y := rfl

lemma isSub_stepProb {p : X → X → ℝ} (hp : IsSub p) : ∀ n, IsSub (stepProb p n) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun x y => by simp only [stepProb_zero]; split_ifs <;> norm_num, fun x => ?_,
      fun x => ?_⟩
    · exact (hasSum_ite_eq x (1 : ℝ)).summable.congr fun y => by
        simp only [stepProb_zero]; split_ifs <;> simp_all [eq_comm]
    · have : (fun y => stepProb p 0 x y) = fun y => if y = x then 1 else 0 := by
        funext y; simp only [stepProb_zero]; split_ifs <;> simp_all [eq_comm]
      rw [this, tsum_ite_eq]
  | succ n ih =>
    refine ⟨fun x y => tsum_nonneg fun z => mul_nonneg (hp.1 x z) (ih.1 z y), fun x => ?_,
      fun x => ?_⟩
    · exact (summable_col (hp.1 x) (hp.2.1 x) ih).1
    · exact le_trans (summable_col (hp.1 x) (hp.2.1 x) ih).2.2 (hp.2.2 x)

lemma stepProb_nonneg {p : X → X → ℝ} (hp : IsSub p) (n : ℕ) (x y : X) :
    0 ≤ stepProb p n x y := (isSub_stepProb hp n).1 x y

lemma stepProb_le_one {p : X → X → ℝ} (hp : IsSub p) (n : ℕ) (x y : X) :
    stepProb p n x y ≤ 1 := (isSub_stepProb hp n).le_one x y

/-! ## The heat kernel -/

lemma uniformize_eq_self {J : X → X → ℝ} (hJ : IsTransition J) : uniformize J = J := by
  funext a b; simp [uniformize, hJ.2.2 a]

/-- The Poisson weights. -/
noncomputable def poi (t : ℝ) (n : ℕ) : ℝ := Real.exp (-t) * t ^ n / n.factorial

lemma poi_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ poi t n := by
  unfold poi; positivity

lemma hasSum_poi (t : ℝ) : HasSum (poi t) 1 := by
  have h := NormedSpace.expSeries_div_hasSum_exp t
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-t))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  have e : poi t = fun i => Real.exp (-t) * (t ^ i / ↑i.factorial) := by
    funext n; unfold poi; ring
  rw [e]; exact h2

lemma summable_poi (t : ℝ) : Summable (poi t) := (hasSum_poi t).summable

lemma heatKernel_eq {J : X → X → ℝ} (t : ℝ) (x y : X) :
    heatKernel J t x y = ∑' n, poi t n * stepProb (uniformize J) n x y := rfl

lemma summable_heat {p : X → X → ℝ} (hp : IsSub p) {t : ℝ} (ht : 0 ≤ t) (x y : X) :
    Summable (fun n => poi t n * stepProb p n x y) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (poi_nonneg ht n) (stepProb_nonneg hp n x y))
    (fun n => by
      have := mul_le_mul_of_nonneg_left (stepProb_le_one hp n x y) (poi_nonneg ht n)
      simpa using this)
    (summable_poi t)

end MarkovHK
end

section
/-!
# H9, the coefficient bound (Delmotte, Lemma 3.5)

For `0 < α` and `k ≤ n`: `C(n, k) α^{n−k} ≤ K(α) · e^{−n} nᵏ / k! · e^{αn}`, with
`K(α) = 1 + e / √(3α/20)`. Stirling: `n! ≤ e √n (n/e)ⁿ`, `m! ≥ √π √(2m) (m/e)ᵐ`; the Poisson weight
`(αn)ᵐ e^{−αn}/m!` is at most `e^{−3αn/20}` when `2m ≤ αn` and at most `1/√(2πm)` otherwise.
-/

namespace Delmotte

namespace H9

open Real

/-- `√y ≤ eʸ` for `y ≥ 0`. -/
lemma sqrt_le_exp {y : ℝ} (hy : 0 ≤ y) : Real.sqrt y ≤ Real.exp y := by
  rw [Real.sqrt_le_iff]
  refine ⟨(Real.exp_pos y).le, ?_⟩
  rw [← Real.exp_nat_mul]  -- (exp y)^2 = exp (2 * y)
  have := Real.add_one_le_exp (2 * y)
  push_cast
  linarith

/-- Stirling upper bound: `n! ≤ e √n (n/e)ⁿ` for `n ≥ 1`. -/
lemma factorial_le_stirling {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n := by
  have hanti := Stirling.stirlingSeq'_antitone
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : Stirling.stirlingSeq (m + 1) ≤ Stirling.stirlingSeq 1 :=
    hanti (Nat.zero_le m)
  rw [Stirling.stirlingSeq_one] at h1
  unfold Stirling.stirlingSeq at h1
  have hpos : 0 < Real.sqrt (2 * ((m + 1 : ℕ) : ℝ)) * (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1) := by
    positivity
  rw [div_le_iff₀ hpos] at h1
  have hs : Real.sqrt (2 * ((m + 1 : ℕ) : ℝ)) = Real.sqrt 2 * Real.sqrt ((m + 1 : ℕ) : ℝ) :=
    Real.sqrt_mul (by norm_num) _
  rw [hs] at h1
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  calc ((m + 1).factorial : ℝ)
      ≤ Real.exp 1 / Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt ((m + 1 : ℕ) : ℝ) *
          (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1)) := h1
    _ = _ := by field_simp

/-- Stirling lower bound: `√π √(2m) (m/e)ᵐ ≤ m!` for `m ≥ 1`. -/
lemma stirling_le_factorial {m : ℕ} (hm : m ≠ 0) :
    Real.sqrt Real.pi * Real.sqrt (2 * m) * ((m : ℝ) / Real.exp 1) ^ m ≤ (m.factorial : ℝ) := by
  have h := Stirling.sqrt_pi_le_stirlingSeq hm
  unfold Stirling.stirlingSeq at h
  have hpos : 0 < Real.sqrt (2 * (m : ℝ)) * ((m : ℝ) / Real.exp 1) ^ m := by
    have : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    positivity
  rw [le_div_iff₀ hpos] at h
  linarith

/-- The Poisson weight bound: `√n (αn)ᵐ e^{−αn} / m! ≤ 1/√(3α/20)` for `n ≥ 1`. -/
lemma poisson_bound {α : ℝ} (hα : 0 < α) (n m : ℕ) (hn : 1 ≤ n) :
    Real.sqrt n * ((α * n) ^ m * Real.exp (-(α * n)) / m.factorial) ≤
      1 / Real.sqrt (3 / 20 * α) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlam0 : 0 < α * n := mul_pos hα hnpos
  set lam := α * (n : ℝ) with hlam
  have hc : 0 < 3 / 20 * α := by positivity
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hc)]
  rcases le_or_gt (2 * (m : ℝ)) lam with hA | hB
  · -- `2m ≤ λ`: the weight is at most `e^{−3λ/20}`
    have h1 : lam ^ m / m.factorial ≤ 2 ^ m * Real.exp (lam / 2) := by
      have := Real.pow_div_factorial_le_exp (lam / 2) (by positivity) m
      calc lam ^ m / m.factorial = 2 ^ m * ((lam / 2) ^ m / m.factorial) := by
            rw [div_pow]; field_simp
        _ ≤ 2 ^ m * Real.exp (lam / 2) := mul_le_mul_of_nonneg_left this (by positivity)
    have h2 : (2 : ℝ) ^ m ≤ Real.exp (7 / 20 * lam) := by
      have hl2 : Real.log 2 < 7 / 10 := by
        have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
      calc (2 : ℝ) ^ m = Real.exp (m * Real.log 2) := by
            rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul, Real.exp_log]
            norm_num
        _ ≤ Real.exp (7 / 20 * lam) := by
            apply Real.exp_le_exp.mpr
            have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
            have : (m : ℝ) * Real.log 2 ≤ m * (7 / 10) :=
              mul_le_mul_of_nonneg_left hl2.le hm0
            linarith
    have hP : lam ^ m * Real.exp (-lam) / m.factorial ≤ Real.exp (-(3 / 20 * lam)) := by
      calc lam ^ m * Real.exp (-lam) / m.factorial = lam ^ m / m.factorial * Real.exp (-lam) := by
            ring
        _ ≤ 2 ^ m * Real.exp (lam / 2) * Real.exp (-lam) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ ≤ Real.exp (7 / 20 * lam) * Real.exp (lam / 2) * Real.exp (-lam) := by
            gcongr
        _ = Real.exp (-(3 / 20 * lam)) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hy : 0 ≤ 3 / 20 * lam := by positivity
    have hsq : Real.sqrt n * Real.sqrt (3 / 20 * α) = Real.sqrt (3 / 20 * lam) := by
      rw [← Real.sqrt_mul hnpos.le, hlam]; congr 1; ring
    calc Real.sqrt n * (lam ^ m * Real.exp (-lam) / m.factorial) * Real.sqrt (3 / 20 * α)
        = Real.sqrt (3 / 20 * lam) * (lam ^ m * Real.exp (-lam) / m.factorial) := by
          rw [← hsq]; ring
      _ ≤ Real.exp (3 / 20 * lam) * Real.exp (-(3 / 20 * lam)) := by
          exact mul_le_mul (sqrt_le_exp hy) hP (by positivity) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  · -- `2m > λ`: then `m ≥ 1` and the weight is at most `1/√(2πm)`
    have hm : m ≠ 0 := by
      rintro rfl; simp at hB; linarith
    have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hst := stirling_le_factorial hm
    -- `(λ/m)ᵐ e^{m−λ} ≤ 1`
    have hxm : (lam / m) ^ m ≤ Real.exp (lam - m) := by
      have h := Real.add_one_le_exp (lam / m - 1)
      have h0 : 0 ≤ lam / m := by positivity
      calc (lam / m) ^ m ≤ Real.exp (lam / m - 1) ^ m :=
            pow_le_pow_left₀ h0 (by linarith) m
        _ = Real.exp (m * (lam / m - 1)) := by rw [← Real.exp_nat_mul]
        _ = Real.exp (lam - m) := by congr 1; field_simp
    have hP : lam ^ m * Real.exp (-lam) / m.factorial ≤
        1 / (Real.sqrt Real.pi * Real.sqrt (2 * m)) := by
      have hden : 0 < Real.sqrt Real.pi * Real.sqrt (2 * m) * ((m : ℝ) / Real.exp 1) ^ m := by
        positivity
      have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
      rw [div_le_div_iff₀ hfac (by positivity)]
      calc lam ^ m * Real.exp (-lam) * (Real.sqrt Real.pi * Real.sqrt (2 * m))
          = (lam / m) ^ m * Real.exp (-lam) * Real.exp m *
              (Real.sqrt Real.pi * Real.sqrt (2 * m) * ((m : ℝ) / Real.exp 1) ^ m) := by
            rw [div_pow, div_pow, ← Real.exp_nat_mul, mul_one]
            field_simp
        _ ≤ Real.exp (lam - m) * Real.exp (-lam) * Real.exp m *
              (Real.sqrt Real.pi * Real.sqrt (2 * m) * ((m : ℝ) / Real.exp 1) ^ m) := by
            gcongr
        _ = Real.sqrt Real.pi * Real.sqrt (2 * m) * ((m : ℝ) / Real.exp 1) ^ m := by
            rw [← Real.exp_add, ← Real.exp_add, show lam - (m : ℝ) + -lam + m = 0 by ring,
              Real.exp_zero, one_mul]
        _ ≤ 1 * m.factorial := by rw [one_mul]; exact hst
    -- `√n / (√π √(2m)) * √(3α/20) ≤ 1`
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hkey : Real.sqrt n * Real.sqrt (3 / 20 * α) ≤ Real.sqrt Real.pi * Real.sqrt (2 * m) := by
      rw [← Real.sqrt_mul hnpos.le, ← Real.sqrt_mul Real.pi_pos.le]
      apply Real.sqrt_le_sqrt
      have : (n : ℝ) * (3 / 20 * α) ≤ lam := by rw [hlam]; nlinarith
      nlinarith
    have hs0 : 0 < Real.sqrt Real.pi * Real.sqrt (2 * m) := by positivity
    calc Real.sqrt n * (lam ^ m * Real.exp (-lam) / m.factorial) * Real.sqrt (3 / 20 * α)
        = (Real.sqrt n * Real.sqrt (3 / 20 * α)) * (lam ^ m * Real.exp (-lam) / m.factorial) := by
          ring
      _ ≤ (Real.sqrt Real.pi * Real.sqrt (2 * m)) *
            (1 / (Real.sqrt Real.pi * Real.sqrt (2 * m))) := by
          gcongr
      _ = 1 := by field_simp

/-- The constant of H9. -/
noncomputable def K (α : ℝ) : ℝ := 1 + Real.exp 1 / Real.sqrt (3 / 20 * α)

lemma one_le_K {α : ℝ} (hα : 0 < α) : 1 ≤ K α := by
  unfold K; have : 0 ≤ Real.exp 1 / Real.sqrt (3 / 20 * α) := by positivity
  linarith

/-- Delmotte's Lemma 3.5. -/
lemma coef_bound {α : ℝ} (hα : 0 < α) (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℝ) * α ^ (n - k) ≤
      K α * (Real.exp (-n) * (n : ℝ) ^ k / k.factorial * Real.exp (α * n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : k = 0 := by omega
    subst this
    simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, mul_one, CharP.cast_eq_zero,
      neg_zero, Real.exp_zero, Nat.factorial_zero, div_one, mul_zero]
    exact one_le_K hα
  set m := n - k with hm
  have hnk : n = k + m := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hchoose : (n.choose k : ℝ) * k.factorial * m.factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hkf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hmf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hP := poisson_bound hα n m hn
  have hS := factorial_le_stirling hn
  -- reduce to `n! αᵐ / m! ≤ (K − 1) e^{−n} nᵏ e^{αn}` and use Stirling
  have hmain : (n.factorial : ℝ) * α ^ m / m.factorial ≤
      Real.exp 1 / Real.sqrt (3 / 20 * α) * (Real.exp (-n) * (n : ℝ) ^ k * Real.exp (α * n)) := by
    have hnn : ((n : ℝ) / Real.exp 1) ^ n = (n : ℝ) ^ k * (n : ℝ) ^ m * Real.exp (-n) := by
      rw [div_pow, hnk, pow_add, ← Real.exp_nat_mul]
      push_cast
      rw [Real.exp_neg]
      field_simp
    calc (n.factorial : ℝ) * α ^ m / m.factorial
        ≤ Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n * α ^ m / m.factorial := by
          gcongr
      _ = Real.exp 1 * (Real.exp (-n) * (n : ℝ) ^ k * Real.exp (α * n)) *
            (Real.sqrt n * ((α * n) ^ m * Real.exp (-(α * n)) / m.factorial)) := by
          rw [hnn, mul_pow, Real.exp_neg (α * n)]
          have he : Real.exp (α * n) ≠ 0 := (Real.exp_pos _).ne'
          field_simp
      _ ≤ Real.exp 1 * (Real.exp (-n) * (n : ℝ) ^ k * Real.exp (α * n)) *
            (1 / Real.sqrt (3 / 20 * α)) := by
          gcongr
      _ = _ := by ring
  have hK : (n.choose k : ℝ) * α ^ m = n.factorial * α ^ m / m.factorial / k.factorial := by
    rw [← hchoose]; field_simp
  rw [hK]
  calc (n.factorial : ℝ) * α ^ m / m.factorial / k.factorial
      ≤ Real.exp 1 / Real.sqrt (3 / 20 * α) * (Real.exp (-n) * (n : ℝ) ^ k * Real.exp (α * n)) /
          k.factorial := by gcongr
    _ ≤ K α * (Real.exp (-n) * (n : ℝ) ^ k / k.factorial * Real.exp (α * n)) := by
        unfold K
        have h0 : 0 ≤ Real.exp (-n) * (n : ℝ) ^ k / k.factorial * Real.exp (α * n) := by positivity
        have : Real.exp 1 / Real.sqrt (3 / 20 * α) * (Real.exp (-n) * (n : ℝ) ^ k *
            Real.exp (α * n)) / k.factorial = Real.exp 1 / Real.sqrt (3 / 20 * α) *
            (Real.exp (-n) * (n : ℝ) ^ k / k.factorial * Real.exp (α * n)) := by ring
        rw [this, add_mul, one_mul]
        linarith

end H9

end Delmotte
end

section
/-!
# Binomial and shifted-exponential identities (shared by H9 and H8)
-/

open DurrettProbability MarkovChain

namespace MarkovHK

/-- One Pascal step of the binomial theorem, for a sequence `b`. -/
lemma binom_step (a : ℝ) (b : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 2), ((n + 1).choose k : ℝ) * a ^ (n + 1 - k) * b k =
      a * ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ (n - k) * b k +
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ (n - k) * b (k + 1) := by
  rw [Finset.sum_range_succ' _ (n + 1)]
  have h1 : ∀ k ∈ Finset.range (n + 1),
      ((n + 1).choose (k + 1) : ℝ) * a ^ (n + 1 - (k + 1)) * b (k + 1) =
        (n.choose k : ℝ) * a ^ (n - k) * b (k + 1) +
          (n.choose (k + 1) : ℝ) * a ^ (n - k) * b (k + 1) := by
    intro k _
    rw [Nat.choose_succ_succ', Nat.succ_sub_succ]; push_cast; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (fun k => (n.choose k : ℝ) * a ^ (n - k) * b k) n]
  rw [Finset.sum_range_succ (fun k => (n.choose (k + 1) : ℝ) * a ^ (n - k) * b (k + 1)) n]
  simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero, Nat.choose_zero_right,
    Nat.cast_one, one_mul, Nat.sub_zero]
  rw [mul_add, Finset.mul_sum]
  have h2 : ∀ k ∈ Finset.range n, a * ((n.choose (k + 1) : ℝ) * a ^ (n - (k + 1)) * b (k + 1)) =
      (n.choose (k + 1) : ℝ) * a ^ (n - k) * b (k + 1) := by
    intro k hk
    have : n - k = (n - (k + 1)) + 1 := by have := Finset.mem_range.mp hk; omega
    rw [this, pow_succ]; ring
  rw [Finset.sum_congr rfl h2]
  ring

/-- The shifted exponential series: `∑_j poi(t, j) C(j, k) α^{j−k} = poi(t, k) e^{αt}`. -/
lemma hasSum_shift (t α : ℝ) (k : ℕ) :
    HasSum (fun j => poi t j * (j.choose k : ℝ) * α ^ (j - k)) (poi t k * Real.exp (α * t)) := by
  have hexp := NormedSpace.expSeries_div_hasSum_exp (α * t)
  rw [← Real.exp_eq_exp_ℝ] at hexp
  have h := hexp.mul_left (poi t k)
  rw [← hasSum_nat_add_iff' k]
  have hz : ∑ i ∈ Finset.range k, poi t i * (i.choose k : ℝ) * α ^ (i - k) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hi)]; simp
  rw [hz, sub_zero]
  have e : (fun m => poi t (m + k) * ((m + k).choose k : ℝ) * α ^ (m + k - k)) =
      fun m => poi t k * ((α * t) ^ m / m.factorial) := by
    funext m
    have hc : ((m + k).choose k : ℝ) * m.factorial * k.factorial = (m + k).factorial := by
      exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial m k
    have hmf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    have hkf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hmkf : ((m + k).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hch : ((m + k).choose k : ℝ) = (m + k).factorial / (m.factorial * k.factorial) := by
      rw [← hc]; field_simp
    unfold poi
    rw [Nat.add_sub_cancel, hch, mul_pow, pow_add]
    field_simp
  rw [e]; exact h

variable {X : Type*} [DecidableEq X]

lemma summable_ite (x : X) (c : ℝ) : Summable (fun z : X => if x = z then c else 0) :=
  (hasSum_ite_eq x c).summable.congr fun z => by split_ifs <;> simp_all [eq_comm]

lemma tsum_ite (x : X) (c : ℝ) : ∑' z : X, (if x = z then c else 0) = c := by
  rw [show (fun z : X => if x = z then c else 0) = fun z => if z = x then c else 0 by
    funext z; split_ifs <;> simp_all [eq_comm]]
  exact tsum_ite_eq x (fun _ => c)

/-- `q = J − αI`. -/
def qk (J : X → X → ℝ) (α : ℝ) : X → X → ℝ := fun x y => J x y - if x = y then α else 0

lemma isSub_qk {J : X → X → ℝ} (hJ : IsTransition J) {α : ℝ} (hα : 0 ≤ α)
    (hdiag : ∀ x, α ≤ J x x) : IsSub (qk J α) := by
  refine ⟨fun x y => ?_, fun x => ?_, fun x => ?_⟩
  · unfold qk; split_ifs with h
    · subst h; linarith [hdiag x]
    · linarith [hJ.1 x y]
  · exact (hJ.2.1 x).sub (summable_ite x α)
  · unfold qk
    rw [(hJ.2.1 x).tsum_sub (summable_ite x α), hJ.2.2 x, tsum_ite]
    linarith

/-- The binomial expansion `Jⁿ = ∑_{k ≤ n} C(n, k) α^{n−k} qᵏ`. -/
lemma stepProb_binom {J : X → X → ℝ} (hJ : IsTransition J) {α : ℝ} (hα : 0 ≤ α)
    (hdiag : ∀ x, α ≤ J x x) (n : ℕ) :
    ∀ x y, stepProb J n x y =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * α ^ (n - k) * stepProb (qk J α) k x y := by
  have hq := isSub_qk hJ hα hdiag
  have hJS := isSub_of_isTransition hJ
  induction n with
  | zero => intro x y; simp [stepProb_zero]
  | succ n ih =>
    intro x y
    have hsplit : ∀ z, J x z * stepProb J n z y =
        qk J α x z * stepProb J n z y + (if x = z then α * stepProb J n x y else 0) := by
      intro z; unfold qk; split_ifs with h
      · subst h; ring
      · ring
    have hs1 : Summable (fun z => qk J α x z * stepProb J n z y) :=
      Summable.of_nonneg_of_le (fun z => mul_nonneg (hq.1 x z) (stepProb_nonneg hJS n z y))
        (fun z => by
          have := mul_le_mul_of_nonneg_left (stepProb_le_one hJS n z y) (hq.1 x z)
          simpa using this) (hq.2.1 x)
    have hs2 : ∀ k, Summable (fun z => qk J α x z * stepProb (qk J α) k z y) := fun k =>
      Summable.of_nonneg_of_le (fun z => mul_nonneg (hq.1 x z) (stepProb_nonneg hq k z y))
        (fun z => by
          have := mul_le_mul_of_nonneg_left (stepProb_le_one hq k z y) (hq.1 x z)
          simpa using this) (hq.2.1 x)
    rw [stepProb_succ]
    simp only [hsplit]
    rw [hs1.tsum_add (summable_ite x _), tsum_ite]
    have hmid : ∑' z, qk J α x z * stepProb J n z y =
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * α ^ (n - k) *
          stepProb (qk J α) (k + 1) x y := by
      simp only [ih]
      simp_rw [Finset.mul_sum]
      rw [Summable.tsum_finsetSum fun k _ => ?_]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [stepProb_succ, ← tsum_mul_left]
        exact tsum_congr fun z => by ring
      · exact ((hs2 k).mul_left ((n.choose k : ℝ) * α ^ (n - k))).congr fun z => by ring
    rw [hmid, ih x y, binom_step α (fun k => stepProb (qk J α) k x y) n]
    ring

end MarkovHK
end

section
/-!
# H9: discrete versus continuous time (Delmotte, Theorem 3.6)

`q = J − αI ≥ 0` is substochastic. `Jⁿ = ∑_{k ≤ n} C(n, k) α^{n−k} qᵏ` (binomial expansion, peeling on
the left), and `p(n) = ∑_j e^{−n} nʲ/j! Jʲ ≥ ∑_{k ≤ n} e^{−n} nᵏ/k! e^{αn} qᵏ` (expand each `Jʲ`, drop
`k > n`, and sum the shifted exponential series). Termwise, `C(n, k) α^{n−k} ≤ K(α) e^{−n} nᵏ/k! e^{αn}`
(`H9Coef`). Symmetry of `J` is not used.
-/


open DurrettProbability MarkovChain MarkovHK

namespace Delmotte

namespace H9

variable {X : Type*} [DecidableEq X]

/-- The heat-kernel lower bound `p(n, x, y) ≥ ∑_{k ≤ n} poi(n, k) e^{αn} qᵏ(x, y)`. -/
lemma heat_ge {J : X → X → ℝ} (hJ : IsTransition J) {α : ℝ} (hα : 0 ≤ α)
    (hdiag : ∀ x, α ≤ J x x) (n : ℕ) (x y : X) :
    ∑ k ∈ Finset.range (n + 1), poi n k * Real.exp (α * n) * stepProb (qk J α) k x y ≤
      heatKernel J n x y := by
  have hq := isSub_qk hJ hα hdiag
  have hJS := isSub_of_isTransition hJ
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [heatKernel_eq, uniformize_eq_self hJ]
  -- termwise summability in `j`
  have hsk : ∀ k, Summable (fun j : ℕ => poi n j * (j.choose k : ℝ) * α ^ (j - k) *
      stepProb (qk J α) k x y) := fun k =>
    ((hasSum_shift n α k).summable.mul_right _)
  have hrhs := summable_heat hJS hn0 x y
  have hlhs : Summable (fun j : ℕ => ∑ k ∈ Finset.range (n + 1),
      poi n j * (j.choose k : ℝ) * α ^ (j - k) * stepProb (qk J α) k x y) :=
    summable_sum fun k _ => hsk k
  calc ∑ k ∈ Finset.range (n + 1), poi n k * Real.exp (α * n) * stepProb (qk J α) k x y
      = ∑ k ∈ Finset.range (n + 1), ∑' j : ℕ,
          poi n j * (j.choose k : ℝ) * α ^ (j - k) * stepProb (qk J α) k x y := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [tsum_mul_right, (hasSum_shift n α k).tsum_eq]
    _ = ∑' j : ℕ, ∑ k ∈ Finset.range (n + 1),
          poi n j * (j.choose k : ℝ) * α ^ (j - k) * stepProb (qk J α) k x y :=
        (Summable.tsum_finsetSum fun k _ => hsk k).symm
    _ ≤ ∑' j : ℕ, poi n j * stepProb J j x y := by
        refine Summable.tsum_le_tsum (fun j => ?_) hlhs hrhs
        rw [stepProb_binom hJ hα hdiag j x y, Finset.mul_sum]
        have hf0 : ∀ k, 0 ≤ poi n j * ((j.choose k : ℝ) * α ^ (j - k) *
            stepProb (qk J α) k x y) := fun k =>
          mul_nonneg (poi_nonneg hn0 j) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
            (pow_nonneg hα _)) (stepProb_nonneg hq k x y))
        calc ∑ k ∈ Finset.range (n + 1),
              poi n j * (j.choose k : ℝ) * α ^ (j - k) * stepProb (qk J α) k x y
            = ∑ k ∈ Finset.range (n + 1),
                poi n j * ((j.choose k : ℝ) * α ^ (j - k) * stepProb (qk J α) k x y) :=
              Finset.sum_congr rfl fun k _ => by ring
          _ ≤ ∑ k ∈ Finset.range (n + 1) ∪ Finset.range (j + 1),
                poi n j * ((j.choose k : ℝ) * α ^ (j - k) * stepProb (qk J α) k x y) :=
              Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
                (fun k _ _ => hf0 k)
          _ = ∑ k ∈ Finset.range (j + 1),
                poi n j * ((j.choose k : ℝ) * α ^ (j - k) * stepProb (qk J α) k x y) := by
              refine (Finset.sum_subset Finset.subset_union_right fun k _ hk => ?_).symm
              rw [Finset.mem_range, not_lt] at hk
              rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

end H9

end Delmotte
end

section
open DurrettProbability MarkovChain MarkovHK
open Delmotte
open H9 in
theorem solution (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Type u) [Countable X] [DecidableEq X] (J : X → X → ℝ),
      IsTransition J → IsSymmetric J → (∀ x, α ≤ J x x) →
      ∀ (t : ℕ) (x y : X), stepProb J t x y ≤ C * heatKernel J t x y := by
  refine ⟨K α, lt_of_lt_of_le one_pos (one_le_K hα), ?_⟩
  intro X _ _ J hJ _ hdiag t x y
  have hq := isSub_qk hJ hα.le hdiag
  rw [stepProb_binom hJ hα.le hdiag t x y]
  calc ∑ k ∈ Finset.range (t + 1), (t.choose k : ℝ) * α ^ (t - k) * stepProb (qk J α) k x y
      ≤ ∑ k ∈ Finset.range (t + 1), K α * (poi t k * Real.exp (α * t)) *
          stepProb (qk J α) k x y := by
        refine Finset.sum_le_sum fun k hk => ?_
        refine mul_le_mul_of_nonneg_right ?_ (stepProb_nonneg hq k x y)
        have := coef_bound hα t k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
        unfold poi; exact this
    _ = K α * ∑ k ∈ Finset.range (t + 1), poi t k * Real.exp (α * t) *
          stepProb (qk J α) k x y := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ K α * heatKernel J t x y :=
        mul_le_mul_of_nonneg_left (heat_ge hJ hα.le hdiag t x y)
          (le_trans zero_le_one (one_le_K hα))
end
