-- Prove2me | solution 1 for CloudCostOpt.eq_12_14_gap_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T17:28:25.621132+00:00
-- url     : https://prove2.me/submissions/9a55fde9-d3b8-4c22-a939-16e17209feff

import Mathlib
import Definitions.Def_CloudCostOpt_piStar
import Definitions.Def_CloudCostOpt_opt
import Definitions.Def_CloudCostOpt_avgCost
import Definitions.Def_CloudCostOpt_IsStable
import Definitions.Def_CloudCostOpt_mu
import Definitions.Def_CloudCostOpt_zCoef
import Definitions.Def_CloudCostOpt_rateX
import Definitions.Def_CloudCostOpt_Standing
import Theorems.Thm_CloudCostOpt_eq_11_piStar_cost
import Theorems.Thm_CloudCostOpt_eq_8_9_piHat_optimal

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

theorem c1_rateX_succ (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (i : Fin S.I) (s l : ℕ) (hl : l < S.L i) :
    (rateX S sel lam i (s + 1) l : ℝ) =
      (if l = 0 then 0 else S.β i (sel.jStar i s (l - 1)) * rateX S sel lam i s (l - 1)) +
        (1 - S.β i (sel.jStar i s l)) * rateX S sel lam i s l := by
  have h1 := hS.β_nonneg i (sel.jStar i s l)
  have h2 := hS.β_le_one i (sel.jStar i s l)
  have h3 := hS.β_nonneg i (sel.jStar i s (l - 1))
  have e1 : (((1 - S.β i (sel.jStar i s l)).toNNReal : ℝ≥0) : ℝ) = 1 - S.β i (sel.jStar i s l) :=
    Real.coe_toNNReal _ (by linarith)
  have e2 : (((S.β i (sel.jStar i s (l - 1))).toNNReal : ℝ≥0) : ℝ) = S.β i (sel.jStar i s (l - 1)) :=
    Real.coe_toNNReal _ h3
  rw [rateX]
  simp only [not_le.2 hl, if_false]
  split_ifs with h0
  · simp [e1]
  · simp [e1, e2]

/-- potential: remaining steps of the age-`s` cohort, in expectation -/
noncomputable def c1Pot (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (i : Fin S.I)
    (s : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (S.L i), ((S.L i : ℝ) - l) * rateX S sel lam i s l

theorem c1_pot_succ (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (i : Fin S.I) (s : ℕ) :
    c1Pot S sel lam i (s + 1) = c1Pot S sel lam i s -
      ∑ l ∈ Finset.range (S.L i), S.β i (sel.jStar i s l) * rateX S sel lam i s l := by
  obtain ⟨K, hK⟩ : ∃ K, S.L i = K + 1 := ⟨S.L i - 1, by have := hS.one_le_L i; omega⟩
  unfold c1Pot
  have hc : ∀ l ∈ Finset.range (S.L i), ((S.L i : ℝ) - l) * rateX S sel lam i (s + 1) l =
      ((S.L i : ℝ) - l) * (if l = 0 then 0 else
        S.β i (sel.jStar i s (l - 1)) * rateX S sel lam i s (l - 1)) +
      ((S.L i : ℝ) - l) * ((1 - S.β i (sel.jStar i s l)) * rateX S sel lam i s l) := by
    intro l hl
    rw [c1_rateX_succ S hS sel lam i s l (Finset.mem_range.1 hl), mul_add]
  rw [Finset.sum_congr rfl hc, Finset.sum_add_distrib]
  rw [hK]
  rw [Finset.sum_range_succ' (fun l => ((((K + 1 : ℕ) : ℝ)) - l) * (if l = 0 then 0 else
        S.β i (sel.jStar i s (l - 1)) * rateX S sel lam i s (l - 1)))]
  have hlast : ∑ l ∈ Finset.range (K + 1), ((K : ℝ) - l) *
      (S.β i (sel.jStar i s l) * rateX S sel lam i s l) =
      ∑ l ∈ Finset.range K, ((K : ℝ) - l) *
      (S.β i (sel.jStar i s l) * rateX S sel lam i s l) := by
    rw [Finset.sum_range_succ]; simp
  have hA : ∑ l ∈ Finset.range K, ((((K + 1 : ℕ) : ℝ)) - ((l + 1 : ℕ) : ℝ)) *
      (if l + 1 = 0 then 0 else
        S.β i (sel.jStar i s (l + 1 - 1)) * rateX S sel lam i s (l + 1 - 1)) =
      ∑ l ∈ Finset.range K, ((K : ℝ) - l) *
      (S.β i (sel.jStar i s l) * rateX S sel lam i s l) := by
    apply Finset.sum_congr rfl
    intro l _
    simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false]
    push_cast; ring
  rw [hA, ← hlast]
  simp only [if_true, mul_zero, add_zero]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  push_cast; ring

theorem c1_pot_le (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (i : Fin S.I) (s : ℕ) :
    c1Pot S sel lam i (s + 1) ≤ c1Pot S sel lam i s := by
  rw [c1_pot_succ S hS sel lam i s]
  have : 0 ≤ ∑ l ∈ Finset.range (S.L i), S.β i (sel.jStar i s l) * rateX S sel lam i s l :=
    Finset.sum_nonneg fun l _ => mul_nonneg (hS.β_nonneg _ _) (NNReal.coe_nonneg _)
  linarith

theorem c1_pot_le0 (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (i : Fin S.I) : ∀ s, c1Pot S sel lam i s ≤ c1Pot S sel lam i 0 := by
  intro s
  induction s with
  | zero => exact le_refl _
  | succ s ih => exact (c1_pot_le S hS sel lam i s).trans ih

theorem c1_mass_le_pot (S : System) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (i : Fin S.I) (s : ℕ) :
    ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i s l : ℝ) ≤ c1Pot S sel lam i s := by
  unfold c1Pot
  apply Finset.sum_le_sum
  intro l hl
  have : (l : ℝ) + 1 ≤ S.L i := by
    have := Finset.mem_range.1 hl; exact_mod_cast this
  have h0 : (0 : ℝ) ≤ rateX S sel lam i s l := NNReal.coe_nonneg _
  nlinarith

theorem c1_mass_bound (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (i : Fin S.I) (N : ℕ) :
    ∑ s ∈ Finset.range N, ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i s l : ℝ) ≤
      S.δ i * c1Pot S sel lam i 0 + c1Pot S sel lam i 0 / S.β i (sel.jLate i) := by
  set b := S.β i (sel.jLate i) with hb
  have hbpos : 0 < b := sel.jLate_pos i
  set P0 := c1Pot S sel lam i 0
  have hP0 : 0 ≤ P0 := (le_trans (Finset.sum_nonneg fun l _ => NNReal.coe_nonneg _)
    (c1_mass_le_pot S sel lam i 0))
  have key : ∀ s, ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i s l : ℝ) ≤
      (if s < S.δ i then P0 else 0) +
        (c1Pot S sel lam i s - c1Pot S sel lam i (s + 1)) / b := by
    intro s
    have hd : 0 ≤ c1Pot S sel lam i s - c1Pot S sel lam i (s + 1) := by
      linarith [c1_pot_le S hS sel lam i s]
    split_ifs with hs
    · have := c1_mass_le_pot S sel lam i s
      have := c1_pot_le0 S hS sel lam i s
      have : 0 ≤ (c1Pot S sel lam i s - c1Pot S sel lam i (s + 1)) / b := div_nonneg hd hbpos.le
      linarith
    · rw [c1_pot_succ S hS sel lam i s]
      have hj : ∀ l, sel.jStar i s l = sel.jLate i := by
        intro l; simp [Selection.jStar, hs]
      simp only [hj, ← Finset.mul_sum]
      rw [← hb]
      field_simp
      linarith
  calc ∑ s ∈ Finset.range N, ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i s l : ℝ)
      ≤ ∑ s ∈ Finset.range N, ((if s < S.δ i then P0 else 0) +
        (c1Pot S sel lam i s - c1Pot S sel lam i (s + 1)) / b) := Finset.sum_le_sum fun s _ => key s
    _ = ∑ s ∈ Finset.range N, (if s < S.δ i then P0 else 0) +
        (P0 - c1Pot S sel lam i N) / b := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_range_sub']
    _ ≤ S.δ i * P0 + P0 / b := by
      gcongr
      · rw [← Finset.sum_filter]
        calc ∑ s ∈ (Finset.range N).filter (· < S.δ i), P0
            ≤ ∑ s ∈ Finset.range (S.δ i), P0 := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro s hs; simp only [Finset.mem_filter] at hs; exact Finset.mem_range.2 hs.2
              · intro _ _ _; exact hP0
          _ = S.δ i * P0 := by simp
      · have : 0 ≤ c1Pot S sel lam i N :=
          le_trans (Finset.sum_nonneg fun l _ => NNReal.coe_nonneg _)
            (c1_mass_le_pot S sel lam i N)
        linarith

/-- the total expected sojourn of type-`i` orders is finite -/
theorem c1_G_lt_top (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (i : Fin S.I) :
    ∑' s, ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i s l : ℝ≥0∞) < ⊤ := by
  refine lt_of_le_of_lt (ENNReal.tsum_le_of_sum_range_le (c := ENNReal.ofReal
    (S.δ i * c1Pot S sel lam i 0 + c1Pot S sel lam i 0 / S.β i (sel.jLate i))) fun N => ?_)
    ENNReal.ofReal_lt_top
  have := c1_mass_bound S hS sel lam i N
  refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal this)
  rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => Finset.sum_nonneg fun l _ => NNReal.coe_nonneg _)]
  apply Finset.sum_congr rfl; intro s _
  rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => NNReal.coe_nonneg _)]
  apply Finset.sum_congr rfl; intro l _
  simp

/-! ## Part 3: Cesàro averages in `ℝ≥0∞` -/
theorem c1_poisson_mean (r : ℝ≥0) : ∫⁻ k, (k : ℝ≥0∞) ∂(poissonMeasure r) = r := by
  have e : ∫⁻ k, (k : ℝ≥0∞) ∂(poissonMeasure r) = ∑' n : ℕ,
      ENNReal.ofReal (Real.exp (-r) * r ^ n / (Nat.factorial n : ℝ)) * (n : ℝ≥0∞) := by
    rw [poissonMeasure, lintegral_sum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [e, tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, mul_zero, zero_add]
  have h : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-r) * r ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) *
      ((n + 1 : ℕ) : ℝ≥0∞)
      = (r : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-r) * r ^ n / (Nat.factorial n : ℝ)) := by
    intro n
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Nat.factorial_succ]; push_cast
    have : (Nat.factorial n : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [tsum_congr h, ENNReal.tsum_mul_left,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hasSum_one_poissonMeasure r).summable,
    (hasSum_one_poissonMeasure r).tsum_eq]
  simp
theorem cor6_avgCost_mono (S : System) (hS : Standing S) (lam : Fin S.I → ℝ≥0) (π : Policy S) :
    avgCost S S.R S.R lam π ≤ avgCost S S.R S.V lam π := by
  unfold avgCost
  refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun T => ?_)
  refine ENNReal.div_le_div_right ?_ _
  refine Finset.sum_le_sum fun n _ => lintegral_mono fun ω => ?_
  unfold periodCost
  gcongr with j
  first
  | exact ENNReal.ofReal_le_ofReal (hS.R_le_V j)
  | exact hS.R_le_V j

theorem cor6_opt_mono (S : System) (hS : Standing S) (lam : Fin S.I → ℝ≥0) :
    opt S S.R S.R lam ≤ opt S S.R S.V lam := by
  unfold opt
  exact iInf₂_mono fun π _ => cor6_avgCost_mono S hS lam π

theorem cor6_opt_le (S : System) (A B : Fin S.J → ℝ) (lam : Fin S.I → ℝ≥0) (π : Policy S)
    (h : IsStable S lam π) : opt S A B lam ≤ avgCost S A B lam π := by
  unfold opt
  exact iInf₂_le π h


/-! ## Poisson moments and the Gallego (Scarf) bound -/

theorem g14_lint_poisson (r : ℝ≥0) (f : ℕ → ℝ≥0∞) :
    ∫⁻ k, f k ∂(poissonMeasure r) =
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (-r) * r ^ n / (Nat.factorial n : ℝ)) * f n := by
  rw [poissonMeasure, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

theorem g14_hasSum_first (r : ℝ≥0) :
    HasSum (fun n : ℕ => (n : ℝ) * (Real.exp (-r) * r ^ n / (Nat.factorial n : ℝ))) r := by
  have h0 := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  rw [mul_one] at h0
  refine (hasSum_nat_add_iff' 1).1 ?_
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
  refine h0.congr_fun fun n => ?_
  rw [Nat.factorial_succ]; push_cast
  have : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem g14_hasSum_second (r : ℝ≥0) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 2 * (Real.exp (-r) * r ^ n / (Nat.factorial n : ℝ)))
      ((r : ℝ) ^ 2 + r) := by
  have h0 := ((g14_hasSum_first r).add (hasSum_one_poissonMeasure r)).mul_left (r : ℝ)
  rw [show (r : ℝ) * (r + 1) = (r : ℝ) ^ 2 + r by ring] at h0
  refine (hasSum_nat_add_iff' 1).1 ?_
  simp only [Finset.sum_range_one, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_mul, sub_zero]
  refine h0.congr_fun fun n => ?_
  rw [Nat.factorial_succ]; push_cast
  have : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem g14_hasSum_sq (r : ℝ≥0) (b : ℝ) :
    HasSum (fun n : ℕ => (Real.exp (-r) * r ^ n / (Nat.factorial n : ℝ)) * ((n : ℝ) - b) ^ 2)
      ((r : ℝ) + ((r : ℝ) - b) ^ 2) := by
  have h := ((g14_hasSum_second r).sub ((g14_hasSum_first r).mul_left (2 * b))).add
    ((hasSum_one_poissonMeasure r).mul_left (b ^ 2))
  rw [show (r : ℝ) + ((r : ℝ) - b) ^ 2 = (r : ℝ) ^ 2 + r - 2 * b * r + b ^ 2 * 1 by ring]
  refine h.congr_fun fun n => ?_
  ring

theorem g14_poisson_sq (r : ℝ≥0) (b : ℝ) :
    ∫⁻ k, ENNReal.ofReal (((k : ℝ) - b) ^ 2) ∂(poissonMeasure r) =
      ENNReal.ofReal ((r : ℝ) + ((r : ℝ) - b) ^ 2) := by
  rw [g14_lint_poisson]
  have hs := g14_hasSum_sq r b
  rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable]
  refine tsum_congr fun n => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]

/-- Gallego's bound `E (U - q)⁺ ≤ (√(σ² + (q - μ)²) - (q - μ)) / 2` for `U ~ Poisson(μ)`,
`q = μ + z √μ`. -/
theorem g14_scarf (r : ℝ≥0) (μ z : ℝ) (hr : (r : ℝ) = μ) :
    ∫⁻ k, ENNReal.ofReal ((k : ℝ) - (μ + z * √μ)) ∂(poissonMeasure r) ≤
      ENNReal.ofReal ((√(μ * (1 + z ^ 2)) - z * √μ) / 2) := by
  subst hr
  rcases eq_or_ne r 0 with h0 | hpos
  · subst h0
    have e : ∀ k : ℕ, ENNReal.ofReal ((k : ℝ) - (((0 : ℝ≥0) : ℝ) + z * √(((0 : ℝ≥0) : ℝ)))) =
        (k : ℝ≥0∞) := by
      intro k; simp
    simp only [e, c1_poisson_mean]
    simp
  · have hr0 : (0 : ℝ) < r := by
      have := pos_iff_ne_zero.2 hpos; exact_mod_cast this
    set a : ℝ := z * √(r : ℝ) with ha
    set c : ℝ := √((r : ℝ) * (1 + z ^ 2)) with hc
    have hcpos : 0 < c := Real.sqrt_pos.2 (by positivity)
    have hc2 : c ^ 2 = (r : ℝ) + a ^ 2 := by
      rw [hc, Real.sq_sqrt (by positivity), ha, mul_pow, Real.sq_sqrt hr0.le]; ring
    have hpt : ∀ k : ℕ, ENNReal.ofReal ((k : ℝ) - ((r : ℝ) + a)) ≤
        ENNReal.ofReal (((k : ℝ) - ((r : ℝ) + a - c)) ^ 2) * ENNReal.ofReal (1 / (4 * c)) := by
      intro k
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg ((k : ℝ) - ((r : ℝ) + a) - c)]
    calc ∫⁻ k, ENNReal.ofReal ((k : ℝ) - ((r : ℝ) + a)) ∂(poissonMeasure r)
        ≤ ∫⁻ k, ENNReal.ofReal (((k : ℝ) - ((r : ℝ) + a - c)) ^ 2) * ENNReal.ofReal (1 / (4 * c))
            ∂(poissonMeasure r) := lintegral_mono fun k => hpt k
      _ = ENNReal.ofReal ((r : ℝ) + ((r : ℝ) - ((r : ℝ) + a - c)) ^ 2) *
            ENNReal.ofReal (1 / (4 * c)) := by
          rw [lintegral_mul_const _ (measurable_of_countable _), g14_poisson_sq]
      _ = ENNReal.ofReal ((c - a) / 2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have : (r : ℝ) + ((r : ℝ) - ((r : ℝ) + a - c)) ^ 2 = 2 * c * (c - a) := by
            nlinarith [hc2]
          rw [this]
          field_simp
          ring

theorem g14_scarf_nonneg (μ z : ℝ) (hμ : 0 ≤ μ) :
    0 ≤ (√(μ * (1 + z ^ 2)) - z * √μ) / 2 := by
  have h1 : (z * √μ) ^ 2 ≤ μ * (1 + z ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hμ]; nlinarith [sq_nonneg z]
  have h2 := Real.abs_le_sqrt h1
  have h3 := le_abs_self (z * √μ)
  linarith

/-! ## Finiteness of the late-cost tail -/

theorem g14_late_lt_top (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) :
    ∑ i, ∑' k : ℕ, ∑ l ∈ Finset.range (S.L i),
      ENNReal.ofReal (S.W i) * (rateX S sel lam i (S.δ i + k) l : ℝ≥0∞) < ⊤ := by
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  have e : ∑' k : ℕ, ∑ l ∈ Finset.range (S.L i),
      ENNReal.ofReal (S.W i) * (rateX S sel lam i (S.δ i + k) l : ℝ≥0∞) =
      ENNReal.ofReal (S.W i) * ∑' k : ℕ, ∑ l ∈ Finset.range (S.L i),
        (rateX S sel lam i (S.δ i + k) l : ℝ≥0∞) := by
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [Finset.mul_sum]
  rw [e]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt ?_ (c1_G_lt_top S hS sel lam i))
  exact ENNReal.tsum_comp_le_tsum_of_injective (add_right_injective (S.δ i))
    (fun s => ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i s l : ℝ≥0∞))

/-! ## Assembly -/

theorem g14_main (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i)
    (hR : ∀ j, 0 < S.R j) (hRV : ∀ j, S.R j < S.V j)
    (hM : ∀ j, 0 ≤ (mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal)) :
    let μr : Fin S.J → ℝ := fun j => (mu S sel lam j).toReal
    let Δ : ℝ := (avgCost S S.R S.V lam (piStar S sel lam)).toReal - (opt S S.R S.R lam).toReal
    avgCost S S.R S.V lam (piStar S sel lam) ≠ ⊤ ∧ opt S S.R S.R lam ≠ ⊤ ∧
    opt S S.R S.V lam ≠ ⊤ ∧
    (avgCost S S.R S.V lam (piStar S sel lam)).toReal - (opt S S.R S.V lam).toReal ≤ Δ ∧
    Δ = ∑ j, (S.R j * zCoef S j * √(μr j) + S.V j *
      (∫⁻ k : ℕ, ENNReal.ofReal ((k : ℝ) - (μr j + zCoef S j * √(μr j)))
        ∂(poissonMeasure (mu S sel lam j).toNNReal)).toReal) ∧
    Δ ≤ ∑ j, (S.R j * zCoef S j * √(μr j) +
      S.V j * (√(μr j * (1 + zCoef S j ^ 2)) - zCoef S j * √(μr j)) / 2) ∧
    ∑ j, (S.R j * zCoef S j * √(μr j) +
        S.V j * (√(μr j * (1 + zCoef S j ^ 2)) - zCoef S j * √(μr j)) / 2) =
      ∑ j, (S.R j * zCoef S j + S.V j * (√(1 + zCoef S j ^ 2) - zCoef S j) / 2) *
        √(μr j) := by
  dsimp only
  obtain ⟨hst, hf⟩ := eq_11_piStar_cost S hS sel lam hlam hR hRV hM
  obtain ⟨-, hLB0, hopt⟩ := eq_8_9_piHat_optimal S hS sel lam hlam
  have hLB := hopt.trans hLB0
  -- abbreviations
  set E : Fin S.J → ℝ≥0∞ := fun j => ∫⁻ k : ℕ, ENNReal.ofReal ((k : ℝ) -
      ((mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal)))
      ∂(poissonMeasure (mu S sel lam j).toNNReal) with hE
  set Late := ∑ i, ∑' k : ℕ, ∑ l ∈ Finset.range (S.L i),
      ENNReal.ofReal (S.W i) * (rateX S sel lam i (S.δ i + k) l : ℝ≥0∞) with hLate
  have hf' : avgCost S S.R S.V lam (piStar S sel lam) =
      ∑ j, ENNReal.ofReal
          (S.R j * ((mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal))) +
      ∑ j, ENNReal.ofReal (S.V j) * E j + Late := hf
  have hEle : ∀ j, E j ≤ ENNReal.ofReal ((√((mu S sel lam j).toReal * (1 + zCoef S j ^ 2)) -
      zCoef S j * √((mu S sel lam j).toReal)) / 2) := fun j =>
    g14_scarf _ _ _ (ENNReal.coe_toNNReal_eq_toReal _)
  have hEt : ∀ j, E j ≠ ⊤ := fun j => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hEle j)
  have hLt : Late ≠ ⊤ := (g14_late_lt_top S hS sel lam).ne
  have hA1 : ∀ j, ENNReal.ofReal
      (S.R j * ((mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal))) ≠ ⊤ :=
    fun j => ENNReal.ofReal_ne_top
  have hA2 : ∀ j, ENNReal.ofReal (S.V j) * E j ≠ ⊤ :=
    fun j => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hEt j)
  have hfT : avgCost S S.R S.V lam (piStar S sel lam) ≠ ⊤ := by
    rw [hf']
    exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun j _ => hA1 j,
      ENNReal.sum_ne_top.2 fun j _ => hA2 j⟩, hLt⟩
  have hRV_le : opt S S.R S.V lam ≤ avgCost S S.R S.V lam (piStar S sel lam) :=
    cor6_opt_le S S.R S.V lam _ hst
  have hRVt : opt S S.R S.V lam ≠ ⊤ := ne_top_of_le_ne_top hfT hRV_le
  have hmono := cor6_opt_mono S hS lam
  have hRRt : opt S S.R S.R lam ≠ ⊤ := ne_top_of_le_ne_top hRVt hmono
  -- finiteness of `μ_j`
  have hB : ∀ j, ENNReal.ofReal (S.R j) * mu S sel lam j ≠ ⊤ := by
    intro j
    have h1 : ∑ j, ENNReal.ofReal (S.R j) * mu S sel lam j ≠ ⊤ := by
      intro h; apply hRRt; rw [hLB, h]; exact top_add _
    exact (ENNReal.sum_ne_top.1 h1) j (Finset.mem_univ j)
  have hmu : ∀ j, mu S sel lam j ≠ ⊤ := by
    intro j h
    apply hB j
    rw [h]
    exact ENNReal.mul_top (by simpa using hR j)
  have hmu0 : ∀ j, 0 ≤ (mu S sel lam j).toReal := fun j => ENNReal.toReal_nonneg
  -- real forms
  have hfR : (avgCost S S.R S.V lam (piStar S sel lam)).toReal =
      ∑ j, S.R j * ((mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal)) +
      ∑ j, S.V j * (E j).toReal + Late.toReal := by
    rw [hf', ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun j _ => hA1 j,
      ENNReal.sum_ne_top.2 fun j _ => hA2 j⟩) hLt,
      ENNReal.toReal_add (ENNReal.sum_ne_top.2 fun j _ => hA1 j)
        (ENNReal.sum_ne_top.2 fun j _ => hA2 j),
      ENNReal.toReal_sum (fun j _ => hA1 j), ENNReal.toReal_sum (fun j _ => hA2 j)]
    congr 2
    · refine Finset.sum_congr rfl fun j _ => ?_
      exact ENNReal.toReal_ofReal (mul_nonneg (hR j).le (hM j))
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith [hR j, hRV j])]
  have hoR : (opt S S.R S.R lam).toReal =
      ∑ j, S.R j * (mu S sel lam j).toReal + Late.toReal := by
    rw [hLB, ENNReal.toReal_add (ENNReal.sum_ne_top.2 fun j _ => hB j) hLt,
      ENNReal.toReal_sum (fun j _ => hB j)]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hR j).le]
  have hΔ : (avgCost S S.R S.V lam (piStar S sel lam)).toReal - (opt S S.R S.R lam).toReal =
      ∑ j, (S.R j * zCoef S j * √((mu S sel lam j).toReal) + S.V j * (E j).toReal) := by
    rw [hfR, hoR, Finset.sum_add_distrib]
    have : ∑ j, S.R j * ((mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal)) =
        ∑ j, S.R j * (mu S sel lam j).toReal +
          ∑ j, S.R j * zCoef S j * √((mu S sel lam j).toReal) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]; ring
  refine ⟨hfT, hRRt, hRVt, ?_, hΔ, ?_, ?_⟩
  · have := ENNReal.toReal_mono hRVt hmono
    linarith
  · rw [hΔ]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 : (E j).toReal ≤ (√((mu S sel lam j).toReal * (1 + zCoef S j ^ 2)) -
        zCoef S j * √((mu S sel lam j).toReal)) / 2 :=
      ENNReal.toReal_le_of_le_ofReal (g14_scarf_nonneg _ _ (hmu0 j)) (hEle j)
    have hV : 0 ≤ S.V j := by linarith [hR j, hRV j]
    have := mul_le_mul_of_nonneg_left h1 hV
    linarith
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.sqrt_mul (hmu0 j)]
    ring

end CloudCostOpt

open MeasureTheory ProbabilityTheory Filter Topology NNReal ENNReal CloudCostOpt in
theorem solution (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i)
    (hR : ∀ j, 0 < S.R j) (hRV : ∀ j, S.R j < S.V j)
    (hM : ∀ j, 0 ≤ (mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal)) :
    let μr : Fin S.J → ℝ := fun j => (mu S sel lam j).toReal
    let Δ : ℝ := (avgCost S S.R S.V lam (piStar S sel lam)).toReal - (opt S S.R S.R lam).toReal
    avgCost S S.R S.V lam (piStar S sel lam) ≠ ⊤ ∧ opt S S.R S.R lam ≠ ⊤ ∧
    opt S S.R S.V lam ≠ ⊤ ∧
    (avgCost S S.R S.V lam (piStar S sel lam)).toReal - (opt S S.R S.V lam).toReal ≤ Δ ∧
    Δ = ∑ j, (S.R j * zCoef S j * √(μr j) + S.V j *
      (∫⁻ k : ℕ, ENNReal.ofReal ((k : ℝ) - (μr j + zCoef S j * √(μr j)))
        ∂(poissonMeasure (mu S sel lam j).toNNReal)).toReal) ∧
    Δ ≤ ∑ j, (S.R j * zCoef S j * √(μr j) +
      S.V j * (√(μr j * (1 + zCoef S j ^ 2)) - zCoef S j * √(μr j)) / 2) ∧
    ∑ j, (S.R j * zCoef S j * √(μr j) +
        S.V j * (√(μr j * (1 + zCoef S j ^ 2)) - zCoef S j * √(μr j)) / 2) =
      ∑ j, (S.R j * zCoef S j + S.V j * (√(1 + zCoef S j ^ 2) - zCoef S j) / 2) *
        √(μr j) := by
  exact g14_main S hS sel lam hlam hR hRV hM
