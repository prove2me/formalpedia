-- Prove2me | solution 1 for Freiman.cf_convergence
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T02:32:11.359911+00:00
-- url     : https://prove2.me/submissions/5f3b72e3-7e04-4254-adc5-f95db13d7d08

import Definitions.Def_Freiman_cfValue
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter Topology
open Freiman

namespace FreimanCFProof

abbrev tail (b : ℕ → ℕ+) : ℕ → ℕ+ := fun n => b (n + 1)

/-- The first `n` digits, with the remaining tail replaced by `x`. -/
noncomputable def truncCF (b : ℕ → ℕ+) : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => 1 / (((b 0 : ℕ) : ℝ) + truncCF (tail b) n x)

lemma digit_ge_one (d : ℕ+) : (1 : ℝ) ≤ (d : ℕ) := by
  exact_mod_cast d.pos

lemma prefix_nonneg (b : ℕ → ℕ+) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ truncCF b n x := by
  induction n generalizing b with
  | zero => exact hx
  | succ n ih =>
    simp only [truncCF]
    have hd := digit_ge_one (b 0)
    have ht := ih (tail b)
    positivity

lemma prefix_mem (b : ℕ → ℕ+) (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    truncCF b n x ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨prefix_nonneg b n hx.1, ?_⟩
  cases n with
  | zero => exact hx.2
  | succ n =>
    have hd := digit_ge_one (b 0)
    have ht := prefix_nonneg (tail b) n hx.1
    dsimp only [truncCF]
    apply (div_le_one (by linarith)).2
    linarith

lemma prefix_add (b : ℕ → ℕ+) (n m : ℕ) (x : ℝ) :
    truncCF b (n + m) x = truncCF b n (truncCF (fun k => b (n + k)) m x) := by
  induction n generalizing b with
  | zero => simp [truncCF]
  | succ n ih =>
    simp only [Nat.succ_add, truncCF, ih]

lemma prefix_zero_eq (b : ℕ → ℕ+) (n : ℕ) :
    truncCF b n 0 = cfConvergent b n := by
  induction n generalizing b with
  | zero => simp [truncCF, cfConvergent, finiteCF]
  | succ n ih =>
    simp only [truncCF, ih, cfConvergent, List.range_succ_eq_map, List.map_cons,
      List.map_map, finiteCF]
    rfl

/-- The exact difference formula for two successive digits. -/
lemma pair_difference (a c x y : ℝ) (ha : 1 ≤ a) (hc : 1 ≤ c)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    1 / (a + 1 / (c + y)) - 1 / (a + 1 / (c + x)) =
      (y - x) / ((a * (c + x) + 1) * (a * (c + y) + 1)) := by
  have hcx : c + x ≠ 0 := by linarith
  have hcy : c + y ≠ 0 := by linarith
  have hdx : a * (c + x) + 1 ≠ 0 := by positivity
  have hdy : a * (c + y) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma pair_estimate (a c x y : ℝ) (ha : 1 ≤ a) (hc : 1 ≤ c)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    0 ≤ 1 / (a + 1 / (c + y)) - 1 / (a + 1 / (c + x)) ∧
    1 / (a + 1 / (c + y)) - 1 / (a + 1 / (c + x)) ≤ (y - x) / 4 := by
  have hy : 0 ≤ y := hx.trans hxy
  rw [pair_difference a c x y ha hc hx hy]
  have hdx : 2 ≤ a * (c + x) + 1 := by nlinarith
  have hdy : 2 ≤ a * (c + y) + 1 := by nlinarith
  have hd : 4 ≤ (a * (c + x) + 1) * (a * (c + y) + 1) := by nlinarith
  constructor
  · exact div_nonneg (sub_nonneg.mpr hxy) (by linarith)
  · exact div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) (by norm_num) hd

/-- Every pair of positive digits contracts differences by at least a factor of four. -/
lemma prefix_estimate (b : ℕ → ℕ+) (n : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    0 ≤ truncCF b (2 * n) y - truncCF b (2 * n) x ∧
    truncCF b (2 * n) y - truncCF b (2 * n) x ≤ (1 / 4 : ℝ) ^ n * (y - x) := by
  induction n generalizing b with
  | zero => simpa [truncCF] using (show 0 ≤ y-x ∧ y-x ≤ y-x from ⟨sub_nonneg.mpr hxy, le_rfl⟩)
  | succ n ih =>
    have hi := ih (tail (tail b))
    have hpx := prefix_nonneg (tail (tail b)) (2*n) hx
    have hp := pair_estimate ((b 0 : ℕ) : ℝ) ((b 1 : ℕ) : ℝ)
      (truncCF (tail (tail b)) (2*n) x) (truncCF (tail (tail b)) (2*n) y)
      (digit_ge_one _) (digit_ge_one _) hpx (sub_nonneg.mp hi.1)
    have hform : 2 * (n+1) = (2*n+1)+1 := by omega
    rw [hform]
    simp only [truncCF, tail, Nat.zero_add] at hp ⊢
    refine ⟨hp.1, ?_⟩
    rw [pow_succ]
    linarith [hi.2]

lemma convergent_mem (b : ℕ → ℕ+) (n : ℕ) :
    cfConvergent b n ∈ Set.Icc (0 : ℝ) 1 := by
  rw [← prefix_zero_eq]
  exact prefix_mem b n ⟨le_rfl, by norm_num⟩

/-- Every extension of an even truncation lies in the same small interval. -/
lemma convergent_bounds (b : ℕ → ℕ+) (n m : ℕ) :
    0 ≤ cfConvergent b (2*n+m) - cfConvergent b (2*n) ∧
    cfConvergent b (2*n+m) - cfConvergent b (2*n) ≤ (1/4 : ℝ)^n := by
  have ht := prefix_mem (fun k => b (2*n+k)) m (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, by norm_num⟩)
  have he := prefix_estimate b n (x := 0) (y := truncCF (fun k => b (2*n+k)) m 0)
    le_rfl ht.1
  rw [← prefix_zero_eq b (2*n+m), prefix_add, ← prefix_zero_eq b (2*n)]
  refine ⟨he.1, he.2.trans ?_⟩
  simpa using mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ (1/4 : ℝ)^n by positivity)

lemma even_mono (b : ℕ → ℕ+) : Monotone (fun n => cfConvergent b (2*n)) := by
  intro n k hnk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnk
  simpa [Nat.mul_add] using sub_nonneg.mp (convergent_bounds b n (2*m)).1

lemma evens_bdd (b : ℕ → ℕ+) :
    BddAbove (Set.range (fun n => cfConvergent b (2*n))) := by
  refine ⟨1, ?_⟩
  rintro y ⟨n, rfl⟩
  exact (convergent_mem b (2*n)).2

lemma even_le_value (b : ℕ → ℕ+) (n : ℕ) : cfConvergent b (2*n) ≤ cfValue b :=
  le_csSup (evens_bdd b) (Set.mem_range_self n)

lemma value_mem (b : ℕ → ℕ+) : cfValue b ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · simpa [cfConvergent, finiteCF] using even_le_value b 0
  · apply csSup_le (Set.range_nonempty _)
    rintro y ⟨n, rfl⟩
    exact (convergent_mem b (2*n)).2

lemma value_bounds (b : ℕ → ℕ+) (n : ℕ) :
    cfConvergent b (2*n) ≤ cfValue b ∧
    cfValue b ≤ cfConvergent b (2*n) + (1/4 : ℝ)^n := by
  refine ⟨even_le_value b n, ?_⟩
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨k, rfl⟩
  by_cases h : n ≤ k
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (Nat.mul_le_mul_left 2 h)
    have hb := (convergent_bounds b n m).2
    rw [← hm] at hb
    linarith
  · have hm := even_mono b (show k ≤ n by omega)
    have hp : 0 ≤ (1/4 : ℝ)^n := by positivity
    linarith

lemma converges (b : ℕ → ℕ+) :
    Tendsto (cfConvergent b) atTop (𝓝 (cfValue b)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (show (1/4 : ℝ) < 1 by norm_num)
  refine ⟨2*n, ?_⟩
  intro k hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hb := convergent_bounds b n m
  have hv := value_bounds b n
  rw [Real.dist_eq]
  apply (abs_lt).2
  constructor <;> linarith

lemma value_pos (b : ℕ → ℕ+) : 0 < cfValue b := by
  have h := even_le_value b 1
  have hc : 0 < cfConvergent b 2 := by
    rw [← prefix_zero_eq]
    simp only [truncCF, tail, Nat.zero_add]
    have h0 := digit_ge_one (b 0)
    have h1 := digit_ge_one (b 1)
    positivity
  exact lt_of_lt_of_le hc h

lemma convergent_succ (b : ℕ → ℕ+) (n : ℕ) :
    cfConvergent b (n+1) = 1 / (((b 0 : ℕ) : ℝ) + cfConvergent (tail b) n) := by
  simp only [← prefix_zero_eq, truncCF]

lemma value_tail (b : ℕ → ℕ+) :
    cfValue b = 1 / (((b 0 : ℕ) : ℝ) + cfValue (tail b)) := by
  have hd := digit_ge_one (b 0)
  have ht := (value_mem (tail b)).1
  have hne : ((b 0 : ℕ) : ℝ) + cfValue (tail b) ≠ 0 := by linarith
  have hlim : Tendsto (fun n => 1 / (((b 0 : ℕ) : ℝ) + cfConvergent (tail b) n))
      atTop (𝓝 (1 / (((b 0 : ℕ) : ℝ) + cfValue (tail b)))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.add (converges (tail b))) hne
  have hseq : (fun n => 1 / (((b 0 : ℕ) : ℝ) + cfConvergent (tail b) n)) =
      (fun n => cfConvergent b (n+1)) := by
    funext n
    exact (convergent_succ b n).symm
  rw [hseq] at hlim
  exact tendsto_nhds_unique ((converges b).comp (tendsto_add_atTop_nat 1)) hlim

lemma value_lt_one (b : ℕ → ℕ+) : cfValue b < 1 := by
  rw [value_tail]
  have hd := digit_ge_one (b 0)
  have ht := value_pos (tail b)
  apply (div_lt_one (by linarith)).2
  linarith

/-- A rational value would give a rational tail with a strictly smaller denominator. -/
lemma value_ne_rat : ∀ (q : ℚ) (b : ℕ → ℕ+), cfValue b ≠ (q : ℝ) := by
  have main : ∀ N : ℕ, ∀ q : ℚ, q.den = N → ∀ b : ℕ → ℕ+, cfValue b ≠ (q : ℝ) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro q hden b heq
      have hq0 : (0 : ℚ) < q := by
        have h := value_pos b
        rw [heq] at h
        exact_mod_cast h
      have hq1 : q < (1 : ℚ) := by
        have h := value_lt_one b
        rw [heq] at h
        exact_mod_cast h
      have hnum0 : 0 ≤ q.num := (Rat.num_pos.mpr hq0).le
      have hnumlt : q.num < (q.den : ℤ) := by
        have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
        have hn : (q.num : ℚ) / (q.den : ℚ) < 1 := by
          simpa only [Rat.num_div_den] using hq1
        exact_mod_cast (div_lt_one hd).mp hn
      let r : ℚ := q⁻¹ - ((b 0 : ℕ) : ℚ)
      have hrden : r.den < N := by
        dsimp [r]
        rw [Rat.sub_natCast_den, Rat.den_inv_of_ne_zero (ne_of_gt hq0), ← hden]
        exact_mod_cast (show (q.num.natAbs : ℤ) < (q.den : ℤ) by
          simpa [Int.natCast_natAbs, abs_of_nonneg hnum0] using hnumlt)
      have htail : cfValue (tail b) = (r : ℝ) := by
        have ht := value_tail b
        rw [heq] at ht
        have hd := digit_ge_one (b 0)
        have hp := value_pos (tail b)
        have hnz : ((b 0 : ℕ) : ℝ) + cfValue (tail b) ≠ 0 := by linarith
        have hqz : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq0)
        dsimp [r]
        push_cast
        have hm : (q : ℝ) * (((b 0 : ℕ) : ℝ) + cfValue (tail b)) = 1 :=
          (eq_div_iff hnz).mp ht
        apply (eq_sub_iff_add_eq).2
        rw [← one_div]
        apply (eq_div_iff hqz).2
        nlinarith
      exact ih r.den hrden r rfl (tail b) htail
  intro q b
  exact main q.den q rfl b

lemma value_irrational (b : ℕ → ℕ+) : Irrational (cfValue b) := by
  rintro ⟨q, hq⟩
  exact value_ne_rat q b hq.symm

end FreimanCFProof

open FreimanCFProof in
theorem solution (b : ℕ → ℕ+) :
    Filter.Tendsto (cfConvergent b) Filter.atTop (nhds (cfValue b)) ∧
    Irrational (cfValue b) ∧
    0 < cfValue b ∧ cfValue b < 1 ∧
    cfValue b = 1 / (((b 0 : ℕ) : ℝ) + cfValue (fun n => b (n + 1))) := by
  exact ⟨converges b, value_irrational b, value_pos b, value_lt_one b, value_tail b⟩
