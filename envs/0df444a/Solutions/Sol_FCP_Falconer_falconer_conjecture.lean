-- Prove2me | solution 1 for FCP.Falconer.falconer_conjecture
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-23T12:19:48.138069+00:00
-- url     : https://prove2.me/submissions/b888de36-e252-43a2-b056-ca600e82cc44

import Mathlib

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace FalconerCE

/-! ### Geometric tail bounds -/

theorem summ (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (v : ℕ → ℝ) (M : ℝ)
    (hv : ∀ k, |v k| ≤ M) : Summable (fun k => v k * q ^ (k + 1)) := by
  have hg : Summable (fun k : ℕ => M * q ^ (k + 1)) := by
    have := (summable_geometric_of_lt_one hq0 hq1).mul_left (M * q)
    refine this.congr (fun k => ?_)
    ring
  refine Summable.of_norm_bounded hg (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hq0 _)]
  exact mul_le_mul_of_nonneg_right (hv k) (pow_nonneg hq0 _)

theorem tsum_bound (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (v : ℕ → ℝ) (M : ℝ)
    (hv : ∀ k, |v k| ≤ M) : |∑' k, v k * q ^ (k + 1)| ≤ M * q / (1 - q) := by
  have hg : HasSum (fun k : ℕ => M * q ^ (k + 1)) (M * q / (1 - q)) := by
    have := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (M * q)
    have e1 : (fun k : ℕ => M * q ^ (k + 1)) = fun i => M * q * q ^ i := by
      funext k; ring
    have e2 : M * q / (1 - q) = M * q * (1 - q)⁻¹ := by rw [div_eq_mul_inv]
    rw [e1, e2]; exact this
  have hs := summ q hq0 hq1 v M hv
  have habs : Summable (fun k => |v k * q ^ (k + 1)|) := hs.abs
  calc |∑' k, v k * q ^ (k + 1)| ≤ ∑' k, |v k * q ^ (k + 1)| := by
        have h1 := norm_tsum_le_tsum_norm (f := fun k => v k * q ^ (k + 1))
          (by simpa only [Real.norm_eq_abs] using habs)
        simpa only [Real.norm_eq_abs] using h1
    _ ≤ ∑' k, M * q ^ (k + 1) := by
        refine habs.tsum_le_tsum (fun k => ?_) hg.summable
        rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 _)]
        exact mul_le_mul_of_nonneg_right (hv k) (pow_nonneg hq0 _)
    _ = M * q / (1 - q) := hg.tsum_eq

theorem tsum_shift (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (v : ℕ → ℝ) (M : ℝ)
    (hv : ∀ k, |v k| ≤ M) (n : ℕ) :
    ∑' k, v k * q ^ (k + 1) =
      (∑ k ∈ Finset.range n, v k * q ^ (k + 1)) + q ^ n * ∑' k, v (k + n) * q ^ (k + 1) := by
  have hs := summ q hq0 hq1 v M hv
  rw [← hs.sum_add_tsum_nat_add n, ← tsum_mul_left]
  congr 1
  refine tsum_congr (fun k => ?_)
  rw [show k + n + 1 = (k + 1) + n by omega, pow_add]
  ring


/-! ### The digit maps -/

noncomputable def dig (a : ℕ → Fin 4) (k : ℕ) : ℝ := ((a k : ℕ) : ℝ)

theorem dig_nonneg (a : ℕ → Fin 4) (k : ℕ) : 0 ≤ dig a k := Nat.cast_nonneg _

theorem dig_le (a : ℕ → Fin 4) (k : ℕ) : dig a k ≤ 3 := by
  unfold dig
  have : (a k : ℕ) ≤ 3 := by omega
  exact_mod_cast this

theorem abs_dig (a : ℕ → Fin 4) (k : ℕ) : |dig a k| ≤ 3 := by
  rw [abs_of_nonneg (dig_nonneg a k)]; exact dig_le a k

theorem abs_dig_sub (a b : ℕ → Fin 4) (k : ℕ) : |dig a k - dig b k| ≤ 3 := by
  have h1 := dig_nonneg a k; have h2 := dig_le a k
  have h3 := dig_nonneg b k; have h4 := dig_le b k
  rw [abs_le]; constructor <;> linarith

noncomputable def g (a : ℕ → Fin 4) : ℝ := ∑' k, dig a k * (1 / 10 : ℝ) ^ (k + 1)
noncomputable def h (a : ℕ → Fin 4) : ℝ := ∑' k, dig a k * (1 / 4 : ℝ) ^ (k + 1)

theorem sub_series (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (a b : ℕ → Fin 4) :
    (∑' k, dig a k * q ^ (k + 1)) - (∑' k, dig b k * q ^ (k + 1)) =
      ∑' k, (dig a k - dig b k) * q ^ (k + 1) := by
  rw [← (summ q hq0 hq1 _ 3 (abs_dig a)).tsum_sub (summ q hq0 hq1 _ 3 (abs_dig b))]
  refine tsum_congr (fun k => ?_); ring

theorem one_le_abs_sub (a b : ℕ → Fin 4) (n : ℕ) (hn : a n ≠ b n) :
    1 ≤ |dig a n - dig b n| := by
  unfold dig
  have hne : (a n : ℕ) ≠ (b n : ℕ) := fun h => hn (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have : ((a n : ℕ) : ℝ) + 1 ≤ ((b n : ℕ) : ℝ) := by exact_mod_cast hlt
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  · have : ((b n : ℕ) : ℝ) + 1 ≤ ((a n : ℕ) : ℝ) := by exact_mod_cast hlt
    rw [abs_of_nonneg (by linarith)]; linarith

/-- separation for base 10 -/
theorem g_sep (a b : ℕ → Fin 4) (n : ℕ) (hlt : ∀ k < n, a k = b k) (hn : a n ≠ b n) :
    (2 / 3 : ℝ) * (1 / 10 : ℝ) ^ (n + 1) ≤ |g a - g b| := by
  have hq0 : (0 : ℝ) ≤ 1 / 10 := by norm_num
  have hq1 : (1 / 10 : ℝ) < 1 := by norm_num
  set v : ℕ → ℝ := fun k => dig a k - dig b k with hv
  have hvb : ∀ k, |v k| ≤ 3 := fun k => abs_dig_sub a b k
  have e : g a - g b = ∑' k, v k * (1 / 10 : ℝ) ^ (k + 1) := sub_series _ hq0 hq1 a b
  rw [e, tsum_shift _ hq0 hq1 v 3 hvb (n + 1), Finset.sum_range_succ]
  have hz : ∑ k ∈ Finset.range n, v k * (1 / 10 : ℝ) ^ (k + 1) = 0 := by
    refine Finset.sum_eq_zero (fun k hk => ?_)
    have := hlt k (Finset.mem_range.1 hk)
    simp only [hv, dig, this, sub_self, zero_mul]
  rw [hz, zero_add]
  set T := ∑' k, v (k + (n + 1)) * (1 / 10 : ℝ) ^ (k + 1)
  have hT : |T| ≤ 1 / 3 := by
    have := tsum_bound _ hq0 hq1 (fun k => v (k + (n + 1))) 3 (fun k => hvb _)
    have e3 : (3 : ℝ) * (1 / 10) / (1 - 1 / 10) = 1 / 3 := by norm_num
    rw [e3] at this; exact this
  have h1 := one_le_abs_sub a b n hn
  have hp : (0 : ℝ) < (1 / 10 : ℝ) ^ (n + 1) := by positivity
  have : v n * (1 / 10 : ℝ) ^ (n + 1) + (1 / 10 : ℝ) ^ (n + 1) * T =
      (1 / 10 : ℝ) ^ (n + 1) * (v n + T) := by ring
  rw [this, abs_mul, abs_of_pos hp]
  have : 2 / 3 ≤ |v n + T| := by
    have := abs_sub_abs_le_abs_sub (v n) (-T)
    rw [sub_neg_eq_add, abs_neg] at this
    linarith
  nlinarith

/-- upper bound for base 4 -/
theorem h_close (a b : ℕ → Fin 4) (n : ℕ) (hlt : ∀ k < n, a k = b k) :
    |h a - h b| ≤ (1 / 4 : ℝ) ^ n := by
  have hq0 : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hq1 : (1 / 4 : ℝ) < 1 := by norm_num
  set v : ℕ → ℝ := fun k => dig a k - dig b k with hv
  have hvb : ∀ k, |v k| ≤ 3 := fun k => abs_dig_sub a b k
  have e : h a - h b = ∑' k, v k * (1 / 4 : ℝ) ^ (k + 1) := sub_series _ hq0 hq1 a b
  rw [e, tsum_shift _ hq0 hq1 v 3 hvb n]
  have hz : ∑ k ∈ Finset.range n, v k * (1 / 4 : ℝ) ^ (k + 1) = 0 := by
    refine Finset.sum_eq_zero (fun k hk => ?_)
    have := hlt k (Finset.mem_range.1 hk)
    simp only [hv, dig, this, sub_self, zero_mul]
  rw [hz, zero_add]
  have hT := tsum_bound _ hq0 hq1 (fun k => v (k + n)) 3 (fun k => hvb _)
  have e3 : (3 : ℝ) * (1 / 4) / (1 - 1 / 4) = 1 := by norm_num
  rw [e3] at hT
  rw [abs_mul, abs_of_nonneg (by positivity)]
  calc (1 / 4 : ℝ) ^ n * |∑' k, v (k + n) * (1 / 4 : ℝ) ^ (k + 1)| ≤ (1 / 4 : ℝ) ^ n * 1 :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = (1 / 4 : ℝ) ^ n := mul_one _


theorem pow_quarter_le (n : ℕ) : (1 / 4 : ℝ) ^ n ≤ ((1 / 10 : ℝ) ^ n) ^ (3 / 5 : ℝ) := by
  have h0 : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ n := by positivity
  have h1 : (0 : ℝ) ≤ (1 / 10 : ℝ) ^ n := by positivity
  have eA : (1 / 4 : ℝ) ^ n = (((1 / 4 : ℝ) ^ n) ^ (5 : ℕ)) ^ ((5 : ℕ)⁻¹ : ℝ) :=
    (Real.pow_rpow_inv_natCast h0 (by norm_num)).symm
  have eB : ((1 / 10 : ℝ) ^ n) ^ (3 / 5 : ℝ) = (((1 / 10 : ℝ) ^ n) ^ (3 : ℕ)) ^ ((5 : ℕ)⁻¹ : ℝ) := by
    have e3 : (((1 / 10 : ℝ) ^ n) ^ (3 : ℕ)) = ((1 / 10 : ℝ) ^ n) ^ ((3 : ℕ) : ℝ) :=
      (Real.rpow_natCast _ 3).symm
    rw [e3, ← Real.rpow_mul h1]; norm_num
  rw [eA, eB]
  refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
  rw [← pow_mul, ← pow_mul, mul_comm n 5, mul_comm n 3, pow_mul, pow_mul]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) n

theorem holder_key (a b : ℕ → Fin 4) :
    |h a - h b| ≤ 15 * |g a - g b| ^ (3 / 5 : ℝ) := by
  classical
  by_cases hab : a = b
  · subst hab; simp
  have hex : ∃ n, a n ≠ b n := by
    by_contra hc; push Not at hc; exact hab (funext hc)
  let n := Nat.find hex
  have hn : a n ≠ b n := Nat.find_spec hex
  have hlt : ∀ k < n, a k = b k := fun k hk => by
    have := Nat.find_min hex hk; push Not at this; exact this
  have hs := g_sep a b n hlt hn
  have hc := h_close a b n hlt
  have hx : (1 / 15 : ℝ) * (1 / 10 : ℝ) ^ n ≤ |g a - g b| := by
    have : (2 / 3 : ℝ) * (1 / 10 : ℝ) ^ (n + 1) = (1 / 15 : ℝ) * (1 / 10 : ℝ) ^ n := by
      rw [pow_succ]; ring
    linarith
  have hmono : ((1 / 15 : ℝ) * (1 / 10 : ℝ) ^ n) ^ (3 / 5 : ℝ) ≤ |g a - g b| ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hx (by norm_num)
  rw [Real.mul_rpow (by norm_num) (by positivity)] at hmono
  have h15 : (1 / 15 : ℝ) ≤ (1 / 15 : ℝ) ^ (3 / 5 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_ge (x := (1 / 15 : ℝ)) (y := 1) (z := 3 / 5)
      (by norm_num) (by norm_num) (by norm_num)
    simpa using this
  have hq := pow_quarter_le n
  have hpos : (0 : ℝ) ≤ ((1 / 10 : ℝ) ^ n) ^ (3 / 5 : ℝ) := by positivity
  have : (1 / 15 : ℝ) * (1 / 4 : ℝ) ^ n ≤ |g a - g b| ^ (3 / 5 : ℝ) := by
    calc (1 / 15 : ℝ) * (1 / 4 : ℝ) ^ n ≤ (1 / 15 : ℝ) ^ (3 / 5 : ℝ) * ((1 / 10 : ℝ) ^ n) ^ (3 / 5 : ℝ) :=
          mul_le_mul h15 hq (by positivity) (by positivity)
      _ ≤ _ := hmono
  linarith


theorem h_surj (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) : ∃ a, h a = t := by
  set F : ℕ → ℤ := fun k => ⌊(4 : ℝ) ^ k * t⌋ with hFdef
  have hF0 : F 0 = 0 := by
    simp only [hFdef, pow_zero, one_mul]
    exact Int.floor_eq_zero_iff.2 ⟨ht0, ht1⟩
  have hlo : ∀ k, 4 * F k ≤ F (k + 1) := by
    intro k
    simp only [hFdef]
    apply Int.le_floor.2
    push_cast
    have := Int.floor_le ((4 : ℝ) ^ k * t)
    rw [pow_succ]; nlinarith
  have hhi : ∀ k, F (k + 1) ≤ 4 * F k + 3 := by
    intro k
    have : F (k + 1) < 4 * F k + 4 := by
      simp only [hFdef]
      apply Int.floor_lt.2
      push_cast
      have := Int.lt_floor_add_one ((4 : ℝ) ^ k * t)
      rw [pow_succ]; nlinarith
    omega
  set D : ℕ → ℤ := fun k => F (k + 1) - 4 * F k with hD
  have hD0 : ∀ k, 0 ≤ D k := fun k => by simp only [hD]; linarith [hlo k]
  have hD3 : ∀ k, D k ≤ 3 := fun k => by simp only [hD]; linarith [hhi k]
  let a : ℕ → Fin 4 := fun k => ⟨(D k).toNat, by have := hD0 k; have := hD3 k; omega⟩
  have hdig : ∀ k, dig a k = (D k : ℝ) := by
    intro k
    simp only [dig, a]
    have : ((D k).toNat : ℤ) = D k := Int.toNat_of_nonneg (hD0 k)
    rw [← this]; push_cast; rfl
  refine ⟨a, ?_⟩
  have hterm : ∀ k, dig a k * (1 / 4 : ℝ) ^ (k + 1) =
      (F (k + 1) : ℝ) * (1 / 4 : ℝ) ^ (k + 1) - (F k : ℝ) * (1 / 4 : ℝ) ^ k := by
    intro k; rw [hdig k]; simp only [hD]; push_cast; rw [pow_succ]; ring
  have hpart : ∀ n, ∑ k ∈ Finset.range n, dig a k * (1 / 4 : ℝ) ^ (k + 1) =
      (F n : ℝ) * (1 / 4 : ℝ) ^ n := by
    intro n
    simp only [hterm]
    rw [Finset.sum_range_sub (fun k => (F k : ℝ) * (1 / 4 : ℝ) ^ k), hF0]
    simp
  have hbd : ∀ n, t - (1 / 4 : ℝ) ^ n ≤ (F n : ℝ) * (1 / 4 : ℝ) ^ n ∧
      (F n : ℝ) * (1 / 4 : ℝ) ^ n ≤ t := by
    intro n
    have h1 := Int.floor_le ((4 : ℝ) ^ n * t)
    have h2 := Int.lt_floor_add_one ((4 : ℝ) ^ n * t)
    have hp : (0 : ℝ) < (1 / 4 : ℝ) ^ n := by positivity
    have hinv : (4 : ℝ) ^ n * (1 / 4 : ℝ) ^ n = 1 := by
      rw [← mul_pow]; norm_num
    have hF : (F n : ℝ) = (⌊(4 : ℝ) ^ n * t⌋ : ℝ) := rfl
    rw [hF]
    constructor
    · have := mul_le_mul_of_nonneg_right h2.le hp.le
      have e : ((4 : ℝ) ^ n * t) * (1 / 4 : ℝ) ^ n = t := by
        calc ((4 : ℝ) ^ n * t) * (1 / 4 : ℝ) ^ n = ((4 : ℝ) ^ n * (1 / 4 : ℝ) ^ n) * t := by ring
          _ = t := by rw [hinv, one_mul]
      nlinarith
    · have := mul_le_mul_of_nonneg_right h1 hp.le
      have e : ((4 : ℝ) ^ n * t) * (1 / 4 : ℝ) ^ n = t := by
        calc ((4 : ℝ) ^ n * t) * (1 / 4 : ℝ) ^ n = ((4 : ℝ) ^ n * (1 / 4 : ℝ) ^ n) * t := by ring
          _ = t := by rw [hinv, one_mul]
      linarith
  have htend : Tendsto (fun n => ∑ k ∈ Finset.range n, dig a k * (1 / 4 : ℝ) ^ (k + 1))
      atTop (𝓝 t) := by
    simp only [hpart]
    have hlow : Tendsto (fun n : ℕ => t - (1 / 4 : ℝ) ^ n) atTop (𝓝 t) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1)).const_sub t
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun n => (hbd n).1) (fun n => (hbd n).2)
  have hs : HasSum (fun k => dig a k * (1 / 4 : ℝ) ^ (k + 1)) t :=
    (hasSum_iff_tendsto_nat_of_nonneg
      (fun k => mul_nonneg (dig_nonneg a k) (by positivity)) t).2 htend
  exact hs.tsum_eq


/-! ### Compactness -/

theorem g_cont : Continuous g := by
  have hq0 : (0 : ℝ) ≤ 1 / 10 := by norm_num
  have hq1 : (1 / 10 : ℝ) < 1 := by norm_num
  have hu : Summable (fun k : ℕ => (3 : ℝ) * (1 / 10 : ℝ) ^ (k + 1)) :=
    summ _ hq0 hq1 (fun _ => 3) 3 (fun _ => by norm_num)
  refine continuous_tsum (f := fun k (a : ℕ → Fin 4) => dig a k * (1 / 10 : ℝ) ^ (k + 1))
    (fun k => ?_) hu (fun k a => ?_)
  · have : Continuous (fun a : ℕ → Fin 4 => dig a k) :=
      (continuous_of_discreteTopology (f := fun i : Fin 4 => ((i : ℕ) : ℝ))).comp
        (continuous_apply k)
    exact this.mul continuous_const
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 / 10 : ℝ) ^ (k + 1))]
    exact mul_le_mul_of_nonneg_right (abs_dig a k) (by positivity)

theorem range_g_compact : IsCompact (range g) := isCompact_range g_cont

/-! ### Dimension lower bound -/

open Classical in
noncomputable def fsel (x : ℝ) : ℝ :=
  if hx : ∃ a, g a = x then h (Classical.choose hx) else 0

theorem fsel_g (a : ℕ → Fin 4) : fsel (g a) = h a := by
  have hx : ∃ a', g a' = g a := ⟨a, rfl⟩
  simp only [fsel, dif_pos hx]
  have hc := Classical.choose_spec hx
  have := holder_key (Classical.choose hx) a
  rw [hc, sub_self, abs_zero, Real.zero_rpow (by norm_num), mul_zero] at this
  have := abs_nonneg (h (Classical.choose hx) - h a)
  have h0 : |h (Classical.choose hx) - h a| = 0 := by linarith
  exact sub_eq_zero.1 (abs_eq_zero.1 h0)

theorem fsel_holder : HolderOnWith 15 (3 / 5) fsel (range g) := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [fsel_g, fsel_g, edist_dist, edist_dist, Real.dist_eq, Real.dist_eq]
  have hk := holder_key a b
  have e1 : ((3 / 5 : ℝ≥0) : ℝ) = 3 / 5 := by norm_num
  rw [e1, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  have e2 : ((15 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal 15 := by simp
  rw [e2, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal hk

theorem dimH_range_g : (3 / 5 : ℝ≥0∞) ≤ dimH (range g) := by
  have hIoo : Ioo (0 : ℝ) 1 ⊆ range h := by
    intro t ht
    obtain ⟨a, ha⟩ := h_surj t ht.1.le ht.2
    exact ⟨a, ha⟩
  have hsub : range h ⊆ fsel '' range g := by
    rintro _ ⟨a, rfl⟩
    exact ⟨g a, ⟨a, rfl⟩, fsel_g a⟩
  have hint : (interior (range h)).Nonempty := by
    refine ⟨1 / 2, ?_⟩
    exact interior_mono hIoo (by rw [interior_Ioo]; constructor <;> norm_num)
  have h1 : dimH (range h) = 1 := by
    rw [Real.dimH_of_nonempty_interior hint, Module.finrank_self]; simp
  have h2 := fsel_holder.dimH_image_le (by norm_num)
  have h3 : (1 : ℝ≥0∞) ≤ dimH (range g) / ((3 / 5 : ℝ≥0) : ℝ≥0∞) := by
    calc (1 : ℝ≥0∞) = dimH (range h) := h1.symm
      _ ≤ dimH (fsel '' range g) := dimH_mono hsub
      _ ≤ _ := h2
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl ENNReal.coe_ne_top), one_mul] at h3
  have e : ((3 / 5 : ℝ≥0) : ℝ≥0∞) = (3 / 5 : ℝ≥0∞) := by
    rw [ENNReal.coe_div (by norm_num)]; rfl
  rw [e] at h3
  exact h3


/-! ### The distance set is null -/

noncomputable def ctr (n : ℕ) (c : Fin n → Fin 7) : ℝ :=
  |∑ k : Fin n, (((c k : ℕ) : ℝ) - 3) * (1 / 10 : ℝ) ^ ((k : ℕ) + 1)|

theorem dist_mem (n : ℕ) (a b : ℕ → Fin 4) :
    dist (g a) (g b) ∈ ⋃ c : Fin n → Fin 7, Metric.closedBall (ctr n c) ((1 / 10 : ℝ) ^ n / 3) := by
  have hq0 : (0 : ℝ) ≤ 1 / 10 := by norm_num
  have hq1 : (1 / 10 : ℝ) < 1 := by norm_num
  set v : ℕ → ℝ := fun k => dig a k - dig b k with hv
  have hvb : ∀ k, |v k| ≤ 3 := fun k => abs_dig_sub a b k
  let c : Fin n → Fin 7 := fun k => ⟨(a k : ℕ) + 3 - (b k : ℕ), by omega⟩
  refine mem_iUnion.2 ⟨c, ?_⟩
  have hc : ∀ k : Fin n, ((c k : ℕ) : ℝ) - 3 = v k := by
    intro k
    simp only [c, hv, dig]
    have hle : (b k : ℕ) ≤ (a k : ℕ) + 3 := by omega
    rw [Nat.cast_sub hle]; push_cast; ring
  have hsum : ∑ k : Fin n, (((c k : ℕ) : ℝ) - 3) * (1 / 10 : ℝ) ^ ((k : ℕ) + 1) =
      ∑ k ∈ Finset.range n, v k * (1 / 10 : ℝ) ^ (k + 1) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => v k * (1 / 10 : ℝ) ^ (k + 1))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hc k]
  have e : g a - g b = ∑' k, v k * (1 / 10 : ℝ) ^ (k + 1) := sub_series _ hq0 hq1 a b
  rw [tsum_shift _ hq0 hq1 v 3 hvb n] at e
  set T := ∑' k, v (k + n) * (1 / 10 : ℝ) ^ (k + 1)
  have hT : |T| ≤ 1 / 3 := by
    have := tsum_bound _ hq0 hq1 (fun k => v (k + n)) 3 (fun k => hvb _)
    have e3 : (3 : ℝ) * (1 / 10) / (1 - 1 / 10) = 1 / 3 := by norm_num
    rw [e3] at this; exact this
  rw [Metric.mem_closedBall, Real.dist_eq, Real.dist_eq, ctr, hsum, e]
  set P := ∑ k ∈ Finset.range n, v k * (1 / 10 : ℝ) ^ (k + 1)
  have hp : (0 : ℝ) < (1 / 10 : ℝ) ^ n := by positivity
  calc |abs (P + (1 / 10 : ℝ) ^ n * T) - abs P| ≤ |(P + (1 / 10 : ℝ) ^ n * T) - P| :=
        abs_abs_sub_abs_le_abs_sub _ _
    _ = (1 / 10 : ℝ) ^ n * |T| := by
        rw [add_sub_cancel_left, abs_mul, abs_of_pos hp]
    _ ≤ (1 / 10 : ℝ) ^ n * (1 / 3) := mul_le_mul_of_nonneg_left hT hp.le
    _ = (1 / 10 : ℝ) ^ n / 3 := by ring

theorem vol_le (n : ℕ) :
    volume (image2 dist (range g) (range g)) ≤ ENNReal.ofReal ((2 / 3) * (7 / 10 : ℝ) ^ n) := by
  have hsub : image2 dist (range g) (range g) ⊆
      ⋃ c : Fin n → Fin 7, Metric.closedBall (ctr n c) ((1 / 10 : ℝ) ^ n / 3) := by
    rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    exact dist_mem n a b
  calc volume (image2 dist (range g) (range g))
      ≤ volume (⋃ c : Fin n → Fin 7, Metric.closedBall (ctr n c) ((1 / 10 : ℝ) ^ n / 3)) :=
        measure_mono hsub
    _ ≤ ∑ c : Fin n → Fin 7, volume (Metric.closedBall (ctr n c) ((1 / 10 : ℝ) ^ n / 3)) :=
        measure_iUnion_fintype_le _ _
    _ = ∑ _c : Fin n → Fin 7, ENNReal.ofReal (2 * ((1 / 10 : ℝ) ^ n / 3)) := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [Real.volume_closedBall]
    _ = ENNReal.ofReal ((2 / 3) * (7 / 10 : ℝ) ^ n) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        have : ((7 ^ n : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((7 : ℝ) ^ n) := by
          rw [← ENNReal.ofReal_natCast]; push_cast; rfl
        rw [this, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have h7 : (7 / 10 : ℝ) ^ n = 7 ^ n * (1 / 10 : ℝ) ^ n := by
          rw [← mul_pow]; norm_num
        rw [h7]; ring

theorem vol_zero : volume (image2 dist (range g) (range g)) = 0 := by
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal ((2 / 3) * (7 / 10 : ℝ) ^ n)) atTop
      (𝓝 (ENNReal.ofReal ((2 / 3) * 0))) := by
    refine ENNReal.tendsto_ofReal ?_
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
  rw [mul_zero, ENNReal.ofReal_zero] at ht
  exact le_antisymm (ge_of_tendsto' ht vol_le) zero_le

/-! ### Transfer to `EuclideanSpace ℝ (Fin 1)` -/

noncomputable def φ (x : ℝ) : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 x

theorem φ_iso : Isometry φ := Isometry.of_dist_eq (fun x y => by simp [φ])

end FalconerCE

namespace FCP.Falconer

theorem _root_.solution : ¬ (∀ (d : ℕ) (E : Set (EuclideanSpace ℝ (Fin d))), IsCompact E →
    (d : ℝ≥0∞) < 2 * dimH E → 0 < volume (image2 dist E E)) := by
  intro H
  have hc : IsCompact (FalconerCE.φ '' range FalconerCE.g) :=
    FalconerCE.range_g_compact.image FalconerCE.φ_iso.continuous
  have hd : ((1 : ℕ) : ℝ≥0∞) < 2 * dimH (FalconerCE.φ '' range FalconerCE.g) := by
    rw [FalconerCE.φ_iso.dimH_image, Nat.cast_one]
    have h1 := FalconerCE.dimH_range_g
    have e35 : ((3 / 5 : ℝ≥0) : ℝ≥0∞) = (3 / 5 : ℝ≥0∞) := by
      rw [ENNReal.coe_div (by norm_num)]; rfl
    calc (1 : ℝ≥0∞) < 2 * (3 / 5 : ℝ≥0∞) := by
          rw [← e35, ← ENNReal.coe_ofNat, ← ENNReal.coe_mul, ← ENNReal.coe_one,
            ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
          push_cast; norm_num
      _ ≤ 2 * dimH (range FalconerCE.g) := by gcongr
  have := H 1 _ hc hd
  have e : image2 dist (FalconerCE.φ '' range FalconerCE.g) (FalconerCE.φ '' range FalconerCE.g)
      = image2 dist (range FalconerCE.g) (range FalconerCE.g) := by
    rw [image2_image_left, image2_image_right]
    congr 1
    funext x y
    exact FalconerCE.φ_iso.dist_eq x y
  rw [e, FalconerCE.vol_zero] at this
  exact lt_irrefl _ this

end FCP.Falconer

#print axioms solution
