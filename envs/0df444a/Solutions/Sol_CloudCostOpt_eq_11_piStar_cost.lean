-- Prove2me | solution 1 for CloudCostOpt.eq_11_piStar_cost
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T17:15:52.596993+00:00
-- url     : https://prove2.me/submissions/d2a19fcc-c442-4fa6-86fc-869d01d5692b

import Mathlib
import Definitions.Def_CloudCostOpt_piStar
import Definitions.Def_CloudCostOpt_piHat
import Definitions.Def_CloudCostOpt_avgCost
import Definitions.Def_CloudCostOpt_IsStable
import Definitions.Def_CloudCostOpt_mu
import Definitions.Def_CloudCostOpt_zCoef
import Definitions.Def_CloudCostOpt_rateX
import Definitions.Def_CloudCostOpt_stateAt
import Definitions.Def_CloudCostOpt_sampleMeasure
import Definitions.Def_CloudCostOpt_Standing
import Theorems.Thm_CloudCostOpt_corollary_4_usage_poisson
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


/-! ## mu is finite (Lemma 3) -/

theorem e11_rateX_zero (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (i : Fin S.I) :
    ∀ s l, s < l → rateX S sel lam i s l = 0 := by
  intro s
  induction s with
  | zero => intro l hl; simp [rateX]; intro _ h; omega
  | succ s ih =>
    intro l hl
    simp only [rateX]
    rw [ih (l - 1) (by omega), ih l (by omega)]
    simp

theorem e11_mu (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (j : Fin S.J) :
    mu S sel lam j = ∑ i, ∑' s, ∑ l ∈ Finset.range (S.L i),
      (if j.succ = sel.jStar i s l then (rateX S sel lam i s l : ℝ≥0∞) else 0) := by
  unfold mu
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (ENNReal.tsum_prod (f := fun s l => if l ≤ s ∧ l < S.L i ∧ sel.jStar i s l = j.succ then
    (rateX S sel lam i s l : ℝ≥0∞) else 0)).trans ?_
  refine tsum_congr fun s => ?_
  rw [tsum_eq_sum (s := Finset.range (S.L i)) (fun l hl => by
    rw [if_neg]; rintro ⟨_, h, _⟩; exact hl (Finset.mem_range.2 h))]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  by_cases hls : l ≤ s
  · by_cases hj : sel.jStar i s l = j.succ
    · rw [if_pos ⟨hls, hl', hj⟩, if_pos hj.symm]
    · rw [if_neg (fun h => hj h.2.2), if_neg (fun h => hj h.symm)]
  · rw [e11_rateX_zero S sel lam i s l (by omega)]
    simp

theorem e11_mu_ne_top (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (j : Fin S.J) : mu S sel lam j ≠ ⊤ := by
  have hG : ∑ i, ∑' s, ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i s l : ℝ≥0∞) ≠ ⊤ :=
    (ENNReal.sum_lt_top.2 fun i _ => c1_G_lt_top S hS sel lam i).ne
  refine ne_top_of_le_ne_top hG ?_
  rw [e11_mu]
  refine Finset.sum_le_sum fun i _ => ENNReal.tsum_le_tsum fun s => Finset.sum_le_sum fun l _ => ?_
  split_ifs <;> simp

/-! ## Cesàro averages in `ℝ≥0∞` -/

theorem c1_cesaro (a : ℕ → ℝ≥0∞) (c : ℝ≥0) (ha : Tendsto a atTop (𝓝 (c : ℝ≥0∞)))
    (hfin : ∀ n, a n ≠ ⊤) :
    Tendsto (fun T : ℕ => (∑ n ∈ Finset.range T, a n) / (T : ℝ≥0∞)) atTop (𝓝 (c : ℝ≥0∞)) := by
  have hr : Tendsto (fun n => (a n).toReal) atTop (𝓝 (c : ℝ)) := by
    have := (ENNReal.tendsto_toReal ENNReal.coe_ne_top).comp ha
    rw [ENNReal.coe_toReal] at this
    exact this
  have h2 := ENNReal.tendsto_ofReal hr.cesaro
  rw [ENNReal.ofReal_coe_nnreal] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  rw [ENNReal.ofReal_mul (inv_nonneg.2 hTpos.le), ENNReal.ofReal_inv_of_pos hTpos,
    ENNReal.ofReal_natCast,
    ENNReal.ofReal_sum_of_nonneg (fun n _ => ENNReal.toReal_nonneg)]
  simp only [ENNReal.ofReal_toReal (hfin _)]
  rw [div_eq_mul_inv, mul_comm]

/-- `liminf (Z + L) = lim Z + liminf L` when `Z` converges to a finite limit -/
theorem e11_liminf (Z L : ℕ → ℝ≥0∞) (z : ℝ≥0∞) (hz : z ≠ ⊤) (hZ : Tendsto Z atTop (𝓝 z)) :
    liminf (fun T => Z T + L T) atTop = z + liminf L atTop := by
  have h1 : Tendsto (fun T => Z T - z) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.sub hZ tendsto_const_nhds (Or.inr hz)
  have h2 : Tendsto (fun T => z - Z T) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds hZ (Or.inl hz)
  have hc : liminf (fun T => z + L T) atTop = z + liminf L atTop :=
    liminf_const_add _ L z (by isBoundedDefault) (by isBoundedDefault)
  have e1 := ENNReal.liminf_add_of_right_tendsto_zero h1 (fun T => z + L T)
  have e2 := ENNReal.liminf_add_of_right_tendsto_zero h2 (fun T => Z T + L T)
  apply le_antisymm
  · rw [← hc, ← e1]
    refine liminf_le_liminf (Eventually.of_forall fun T => ?_)
    simp only [Pi.add_apply]
    calc Z T + L T ≤ (z + (Z T - z)) + L T := by gcongr; exact le_add_tsub
      _ = z + L T + (Z T - z) := by ring
  · rw [← hc, ← e2]
    refine liminf_le_liminf (Eventually.of_forall fun T => ?_)
    simp only [Pi.add_apply]
    calc z + L T ≤ (Z T + (z - Z T)) + L T := by gcongr; exact le_add_tsub
      _ = Z T + L T + (z - Z T) := by ring

/-! ## The Poisson expectation `E (U − M)⁺` and its continuity in the mean -/

theorem g14_lint_poisson (r : ℝ≥0) (f : ℕ → ℝ≥0∞) :
    ∫⁻ k, f k ∂(poissonMeasure r) =
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (-r) * r ^ n / (Nat.factorial n : ℝ)) * f n := by
  rw [poissonMeasure, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

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

theorem e11_pmf_sum (r : ℝ≥0) :
    ∑' n : ℕ, ENNReal.ofReal (Real.exp (-r) * r ^ n / (Nat.factorial n : ℝ)) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hasSum_one_poissonMeasure r).summable,
    (hasSum_one_poissonMeasure r).tsum_eq]
  simp

/-- pointwise: `(k − M)⁺ + M = k + (M − k)⁺` -/
theorem e11_pt (M : ℝ) (hM : 0 ≤ M) (k : ℕ) :
    ENNReal.ofReal ((k : ℝ) - M) + ENNReal.ofReal M =
      (k : ℝ≥0∞) + ENNReal.ofReal (M - k) := by
  rcases le_total M (k : ℝ) with h | h
  · rw [← ENNReal.ofReal_add (by linarith) hM, ENNReal.ofReal_of_nonpos (by linarith : M - k ≤ 0)]
    simp
  · rw [ENNReal.ofReal_of_nonpos (by linarith : (k : ℝ) - M ≤ 0), zero_add,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_add (by positivity) (by linarith)]
    congr 1; ring

/-- `E (U − M)⁺ + M = r + Σ_{k ≤ ⌊M⌋} P(U = k) (M − k)` for `U ~ Poisson(r)` -/
theorem e11_pp (r : ℝ≥0) (M : ℝ) (hM : 0 ≤ M) :
    ∫⁻ k, ENNReal.ofReal ((k : ℝ) - M) ∂(poissonMeasure r) + ENNReal.ofReal M =
      (r : ℝ≥0∞) + ∑ k ∈ Finset.range (⌊M⌋₊ + 1),
        ENNReal.ofReal (Real.exp (-r) * r ^ k / (Nat.factorial k : ℝ) * (M - k)) := by
  set p : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (Real.exp (-r) * r ^ n / (Nat.factorial n : ℝ))
    with hp
  have hM' : ENNReal.ofReal M = ∑' n, p n * ENNReal.ofReal M := by
    rw [ENNReal.tsum_mul_right, hp, e11_pmf_sum, one_mul]
  have hr : (r : ℝ≥0∞) = ∑' n, p n * (n : ℝ≥0∞) := by
    rw [← c1_poisson_mean r, g14_lint_poisson]
  have hfin : ∑ k ∈ Finset.range (⌊M⌋₊ + 1),
      ENNReal.ofReal (Real.exp (-r) * r ^ k / (Nat.factorial k : ℝ) * (M - k)) =
      ∑' n, p n * ENNReal.ofReal (M - n) := by
    rw [tsum_eq_sum (s := Finset.range (⌊M⌋₊ + 1)) (fun n hn => by
      have hn' : ⌊M⌋₊ < n := by simpa [Finset.mem_range, Nat.lt_succ_iff, not_le] using hn
      have : M < n := Nat.lt_of_floor_lt hn'
      rw [ENNReal.ofReal_of_nonpos (by linarith), mul_zero])]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hp]; dsimp only
    rw [← ENNReal.ofReal_mul (by positivity)]
  rw [g14_lint_poisson, hM', hr, hfin, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine tsum_congr fun n => ?_
  rw [← mul_add, ← mul_add, e11_pt M hM n]

theorem e11_pp_ne_top (r : ℝ≥0) (M : ℝ) (hM : 0 ≤ M) :
    ∫⁻ k, ENNReal.ofReal ((k : ℝ) - M) ∂(poissonMeasure r) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ k, ENNReal.ofReal ((k : ℝ) - M) ∂(poissonMeasure r) +
    ENNReal.ofReal M) ?_ le_self_add
  rw [e11_pp r M hM]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top,
    (ENNReal.sum_lt_top.2 fun k _ => ENNReal.ofReal_lt_top).ne⟩

theorem e11_pp_tendsto (ν : ℕ → ℝ≥0) (r : ℝ≥0) (hν : Tendsto ν atTop (𝓝 r)) (M : ℝ)
    (hM : 0 ≤ M) :
    Tendsto (fun n => ∫⁻ k, ENNReal.ofReal ((k : ℝ) - M) ∂(poissonMeasure (ν n))) atTop
      (𝓝 (∫⁻ k, ENNReal.ofReal ((k : ℝ) - M) ∂(poissonMeasure r))) := by
  have hG : Tendsto (fun n => ∫⁻ k, ENNReal.ofReal ((k : ℝ) - M) ∂(poissonMeasure (ν n)) +
      ENNReal.ofReal M) atTop
      (𝓝 (∫⁻ k, ENNReal.ofReal ((k : ℝ) - M) ∂(poissonMeasure r) + ENNReal.ofReal M)) := by
    simp only [e11_pp _ M hM]
    refine Tendsto.add (ENNReal.tendsto_coe.2 hν) (tendsto_finsetSum _ fun k _ => ?_)
    refine ENNReal.tendsto_ofReal ?_
    have hc : Continuous fun x : ℝ≥0 =>
        Real.exp (-(x : ℝ)) * (x : ℝ) ^ k / (Nat.factorial k : ℝ) * (M - k) := by fun_prop
    exact (hc.tendsto r).comp hν
  have := ENNReal.Tendsto.sub hG (tendsto_const_nhds (x := ENNReal.ofReal M))
    (Or.inr ENNReal.ofReal_ne_top)
  simpa only [ENNReal.add_sub_cancel_right ENNReal.ofReal_ne_top] using this

/-! ## π* and π̂ share the trajectory -/

theorem e8_hist (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (ω : Omega S) :
    ∀ n, history S (piHat S sel) ω n = history S (piStar S sel lam) ω n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [history, ih]; rfl

theorem e8_st (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (ω : Omega S) (n : ℕ) :
    stateAt S (piHat S sel) ω n = stateAt S (piStar S sel lam) ω n := by
  simp only [stateAt, e8_hist S sel lam ω n]

/-- the reserve level `M_j = μ_j + z_j √μ_j` -/
noncomputable def e11M (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (j : Fin S.J) : ℝ :=
  (mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal)

theorem e11_m (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (j : Fin S.J)
    (hM : 0 ≤ e11M S sel lam j) (ω : Omega S) (n : ℕ) :
    ((piStar S sel lam).m n (history S (piStar S sel lam) ω n) j : ℝ≥0∞) =
      ENNReal.ofReal ((usage S sel n (stateAt S (piHat S sel) ω n) j : ℝ) - e11M S sel lam j) := by
  rw [e8_st S sel lam ω n]
  show (((usage S sel n (stateAt S (piStar S sel lam) ω n) j : ℝ≥0) -
    Real.toNNReal (e11M S sel lam j) : ℝ≥0) : ℝ≥0∞) = _
  rw [ENNReal.ofReal]
  congr 1
  apply NNReal.eq
  rw [NNReal.coe_sub_def, Real.coe_toNNReal', Real.coe_toNNReal', max_eq_left hM]
  simp

/-- Corollary 4, in the form used here -/
theorem e11_law (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (hlam : ∀ i, 0 < lam i) (j : Fin S.J) :
    ∃ ν : ℕ → ℝ≥0, (∀ n, HasLaw (fun ω => usage S sel n (stateAt S (piHat S sel) ω n) j)
        (poissonMeasure (ν n)) (sampleMeasure S lam)) ∧
      Tendsto (fun n => (ν n : ℝ≥0∞)) atTop (𝓝 (mu S sel lam j)) := by
  have h := corollary_4_usage_poisson S hS sel lam hlam j
  dsimp only at h
  obtain ⟨hlaw, htend, -⟩ := h
  refine ⟨fun n => ∑ i, ∑ s ∈ Finset.range (n + 1 - 1),
      ∑ l ∈ Finset.range (min (S.L i - 1) s + 1),
        if sel.jStar i s l = j.succ then rateX S sel lam i s l else 0,
    fun n => ?_, ?_⟩
  · have := (hlaw (n + 1) (by omega)).1
    simpa only [Nat.add_sub_cancel] using this
  · have h2 := (Filter.tendsto_add_atTop_iff_nat 1).2 htend
    refine h2.congr fun n => ?_
    exact (hlaw (n + 1) (by omega)).2.1

theorem e11_lin (r : ℝ≥0) (c d : ℝ≥0∞) (g : ℕ → ℝ≥0∞) :
    ∫⁻ k, (c + d * g k) ∂(poissonMeasure r) = c + d * ∫⁻ k, g k ∂(poissonMeasure r) := by
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_const_mul _ measurable_from_nat]

theorem e11_ces (a : ℕ → ℝ≥0∞) (x : ℝ≥0∞) (hx : x ≠ ⊤) (ha : Tendsto a atTop (𝓝 x))
    (hfin : ∀ n, a n ≠ ⊤) :
    Tendsto (fun T : ℕ => (∑ n ∈ Finset.range T, a n) / (T : ℝ≥0∞)) atTop (𝓝 x) := by
  have := c1_cesaro a x.toNNReal (by rwa [ENNReal.coe_toNNReal hx]) hfin
  rwa [ENNReal.coe_toNNReal hx] at this

/-- the late-cost part of period `n + 1` (the same for `π̂` and `π*`) -/
noncomputable def e11Late (S : System) (sel : Selection S) (ω : Omega S) (n : ℕ) : ℝ≥0∞ :=
  ∑ i, ∑ s ∈ Finset.Ico (S.δ i) n, ∑ l ∈ Finset.range (S.L i),
    ENNReal.ofReal (S.W i) * (stateAt S (piHat S sel) ω n i s l : ℝ≥0∞)

theorem e11_pc_star (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (hM : ∀ j, 0 ≤ e11M S sel lam j) (ω : Omega S) (n : ℕ) :
    periodCost S S.R S.V (piStar S sel lam) ω n =
      (∑ j, (ENNReal.ofReal (S.R j) * ENNReal.ofReal (e11M S sel lam j) +
        ENNReal.ofReal (S.V j) * ENNReal.ofReal
          ((usage S sel n (stateAt S (piHat S sel) ω n) j : ℝ) - e11M S sel lam j))) +
      e11Late S sel ω n := by
  unfold periodCost e11Late
  simp only [e11_m S sel lam _ (hM _), ← e8_st S sel lam ω n]
  rfl

theorem e11_pc_hat (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (ω : Omega S) (n : ℕ) :
    periodCost S S.R S.R (piHat S sel) ω n =
      (∑ j, ENNReal.ofReal (S.R j) *
        ((usage S sel n (stateAt S (piHat S sel) ω n) j : ℕ) : ℝ≥0∞)) +
      e11Late S sel ω n := by
  unfold periodCost e11Late
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [piHat, stateAt]

theorem e11_main (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i)
    (hR : ∀ j, 0 < S.R j)
    (hM : ∀ j, 0 ≤ (mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal)) :
    IsStable S lam (piStar S sel lam) ∧
    avgCost S S.R S.V lam (piStar S sel lam) =
      ∑ j, ENNReal.ofReal
          (S.R j * ((mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal))) +
      ∑ j, ENNReal.ofReal (S.V j) * ∫⁻ k : ℕ,
          ENNReal.ofReal ((k : ℝ) -
            ((mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal)))
          ∂(poissonMeasure (mu S sel lam j).toNNReal) +
      ∑ i, ∑' k : ℕ, ∑ l ∈ Finset.range (S.L i),
        ENNReal.ofReal (S.W i) * (rateX S sel lam i (S.δ i + k) l : ℝ≥0∞) := by
  have hM' : ∀ j, 0 ≤ e11M S sel lam j := hM
  choose ν hlaw hν using fun j => e11_law S hS sel lam hlam j
  have hmu := fun j => e11_mu_ne_top S hS sel lam j
  have hνr : ∀ j, Tendsto (ν j) atTop (𝓝 (mu S sel lam j).toNNReal) := fun j => by
    have := hν j
    rw [← ENNReal.coe_toNNReal (hmu j)] at this
    exact ENNReal.tendsto_coe.1 this
  -- the on-demand part
  have hEm : ∀ j n, ∫⁻ ω, ((piStar S sel lam).m n (history S (piStar S sel lam) ω n) j : ℝ≥0∞)
      ∂(sampleMeasure S lam) =
      ∫⁻ k : ℕ, ENNReal.ofReal ((k : ℝ) - e11M S sel lam j) ∂(poissonMeasure (ν j n)) := by
    intro j n
    simp only [e11_m S sel lam j (hM' j)]
    exact (hlaw j n).lintegral_comp
      (f := fun k : ℕ => ENNReal.ofReal ((k : ℝ) - e11M S sel lam j))
      measurable_from_nat.aemeasurable
  set y : Fin S.J → ℝ≥0∞ := fun j => ∫⁻ k : ℕ, ENNReal.ofReal ((k : ℝ) - e11M S sel lam j)
    ∂(poissonMeasure (mu S sel lam j).toNNReal) with hy
  have hy_ne : ∀ j, y j ≠ ⊤ := fun j => e11_pp_ne_top _ _ (hM' j)
  have hyt : ∀ j, Tendsto (fun n => ∫⁻ k : ℕ, ENNReal.ofReal ((k : ℝ) - e11M S sel lam j)
      ∂(poissonMeasure (ν j n))) atTop (𝓝 (y j)) := fun j =>
    e11_pp_tendsto _ _ (hνr j) _ (hM' j)
  -- stability
  have hstab : IsStable S lam (piStar S sel lam) := by
    refine ⟨fun j => ⟨(y j).toNNReal, ?_⟩, fun i s l => ?_⟩
    · rw [ENNReal.coe_toNNReal (hy_ne j)]
      simp only [hEm]
      exact e11_ces _ _ (hy_ne j) (hyt j) fun n => e11_pp_ne_top _ _ (hM' j)
    · obtain ⟨c, hc⟩ := (eq_8_9_piHat_optimal S hS sel lam hlam).1.2 i s l
      refine ⟨c, ?_⟩
      simpa only [e8_st S sel lam] using hc
  refine ⟨hstab, ?_⟩
  -- expected period costs
  set El : ℕ → ℝ≥0∞ := fun n => ∫⁻ ω, e11Late S sel ω n ∂(sampleMeasure S lam) with hEl
  set A : ℕ → ℝ≥0∞ := fun n => ∑ j, (ENNReal.ofReal (S.R j) * ENNReal.ofReal (e11M S sel lam j) +
      ENNReal.ofReal (S.V j) * ∫⁻ k : ℕ, ENNReal.ofReal ((k : ℝ) - e11M S sel lam j)
        ∂(poissonMeasure (ν j n))) with hA
  set B : ℕ → ℝ≥0∞ := fun n => ∑ j, ENNReal.ofReal (S.R j) * (ν j n : ℝ≥0∞) with hB
  have hcS : ∀ n, ∫⁻ ω, periodCost S S.R S.V (piStar S sel lam) ω n ∂(sampleMeasure S lam) =
      A n + El n := by
    intro n
    simp only [e11_pc_star S sel lam hM']
    have hmeas : ∀ j, AEMeasurable (fun ω => ENNReal.ofReal (S.R j) *
        ENNReal.ofReal (e11M S sel lam j) + ENNReal.ofReal (S.V j) *
        ENNReal.ofReal ((usage S sel n (stateAt S (piHat S sel) ω n) j : ℝ) - e11M S sel lam j))
        (sampleMeasure S lam) := fun j =>
      (measurable_from_nat (f := fun k : ℕ => ENNReal.ofReal (S.R j) *
          ENNReal.ofReal (e11M S sel lam j) + ENNReal.ofReal (S.V j) *
          ENNReal.ofReal ((k : ℝ) - e11M S sel lam j))).comp_aemeasurable (hlaw j n).aemeasurable
    have hsum : AEMeasurable (fun ω => ∑ j, (ENNReal.ofReal (S.R j) *
        ENNReal.ofReal (e11M S sel lam j) + ENNReal.ofReal (S.V j) *
        ENNReal.ofReal ((usage S sel n (stateAt S (piHat S sel) ω n) j : ℝ) - e11M S sel lam j)))
        (sampleMeasure S lam) := Finset.aemeasurable_fun_sum _ fun j _ => hmeas j
    rw [lintegral_add_left' hsum, lintegral_finsetSum' _ fun j _ => hmeas j]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hlaw j n).lintegral_comp (f := fun k : ℕ => ENNReal.ofReal (S.R j) *
          ENNReal.ofReal (e11M S sel lam j) + ENNReal.ofReal (S.V j) *
          ENNReal.ofReal ((k : ℝ) - e11M S sel lam j)) measurable_from_nat.aemeasurable,
      e11_lin]
  have hcH : ∀ n, ∫⁻ ω, periodCost S S.R S.R (piHat S sel) ω n ∂(sampleMeasure S lam) =
      B n + El n := by
    intro n
    simp only [e11_pc_hat S sel lam]
    have hmeas : ∀ j, AEMeasurable (fun ω => ENNReal.ofReal (S.R j) *
        ((usage S sel n (stateAt S (piHat S sel) ω n) j : ℕ) : ℝ≥0∞)) (sampleMeasure S lam) :=
      fun j => (measurable_from_nat (f := fun k : ℕ => ENNReal.ofReal (S.R j) *
        (k : ℝ≥0∞))).comp_aemeasurable (hlaw j n).aemeasurable
    have hsum : AEMeasurable (fun ω => ∑ j, ENNReal.ofReal (S.R j) *
        ((usage S sel n (stateAt S (piHat S sel) ω n) j : ℕ) : ℝ≥0∞)) (sampleMeasure S lam) :=
      Finset.aemeasurable_fun_sum _ fun j _ => hmeas j
    rw [lintegral_add_left' hsum, lintegral_finsetSum' _ fun j _ => hmeas j]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hlaw j n).lintegral_comp (f := fun k : ℕ => ENNReal.ofReal (S.R j) * (k : ℝ≥0∞))
        measurable_from_nat.aemeasurable,
      lintegral_const_mul _ measurable_from_nat, c1_poisson_mean]
  -- limits of the reservation / on-demand parts
  set a : ℝ≥0∞ := ∑ j, (ENNReal.ofReal (S.R j) * ENNReal.ofReal (e11M S sel lam j) +
      ENNReal.ofReal (S.V j) * y j) with ha
  set b : ℝ≥0∞ := ∑ j, ENNReal.ofReal (S.R j) * mu S sel lam j with hb
  have ha_ne : a ≠ ⊤ := (ENNReal.sum_lt_top.2 fun j _ => ENNReal.add_lt_top.2
    ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top,
     ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hy_ne j).lt_top⟩).ne
  have hb_ne : b ≠ ⊤ := (ENNReal.sum_lt_top.2 fun j _ =>
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hmu j).lt_top).ne
  have hAt : Tendsto A atTop (𝓝 a) := tendsto_finsetSum _ fun j _ =>
    tendsto_const_nhds.add (ENNReal.Tendsto.const_mul (hyt j) (Or.inr ENNReal.ofReal_ne_top))
  have hBt : Tendsto B atTop (𝓝 b) := tendsto_finsetSum _ fun j _ =>
    ENNReal.Tendsto.const_mul (hν j) (Or.inr ENNReal.ofReal_ne_top)
  have hA_ne : ∀ n, A n ≠ ⊤ := fun n => (ENNReal.sum_lt_top.2 fun j _ => ENNReal.add_lt_top.2
    ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top,
     ENNReal.mul_lt_top ENNReal.ofReal_lt_top (e11_pp_ne_top _ _ (hM' j)).lt_top⟩).ne
  have hB_ne : ∀ n, B n ≠ ⊤ := fun n => (ENNReal.sum_lt_top.2 fun j _ =>
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top).ne
  -- the late part: its Cesàro liminf is the late tail of (8)
  have h89 := (eq_8_9_piHat_optimal S hS sel lam hlam).2.1
  unfold avgCost at h89 ⊢
  simp only [hcS, hcH, Finset.sum_add_distrib, ENNReal.add_div] at h89 ⊢
  rw [e11_liminf _ _ b hb_ne (e11_ces B b hb_ne hBt hB_ne)] at h89
  rw [e11_liminf _ _ a ha_ne (e11_ces A a ha_ne hAt hA_ne), (ENNReal.add_right_inj hb_ne).1 h89]
  congr 1
  rw [ha, Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← ENNReal.ofReal_mul (hR j).le]
  rfl

end CloudCostOpt

open CloudCostOpt in
theorem solution (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i)
    (hR : ∀ j, 0 < S.R j) (hRV : ∀ j, S.R j < S.V j)
    (hM : ∀ j, 0 ≤ (mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal)) :
    IsStable S lam (piStar S sel lam) ∧
    avgCost S S.R S.V lam (piStar S sel lam) =
      ∑ j, ENNReal.ofReal
          (S.R j * ((mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal))) +
      ∑ j, ENNReal.ofReal (S.V j) * ∫⁻ k : ℕ,
          ENNReal.ofReal ((k : ℝ) -
            ((mu S sel lam j).toReal + zCoef S j * √((mu S sel lam j).toReal)))
          ∂(poissonMeasure (mu S sel lam j).toNNReal) +
      ∑ i, ∑' k : ℕ, ∑ l ∈ Finset.range (S.L i),
        ENNReal.ofReal (S.W i) * (rateX S sel lam i (S.δ i + k) l : ℝ≥0∞) := by
  exact CloudCostOpt.e11_main S hS sel lam hlam hR hM
