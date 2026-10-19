-- Prove2me | solution 1 for BenfordLaw.digitAt_prob_of_uniform_log_mantissa
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:46:18.025306+00:00
-- url     : https://prove2.me/submissions/6d7781b8-fc0f-40bb-8e1e-27be85d3b18e

import Mathlib
import Definitions.Def_BenfordLaw_Defs
open BenfordLaw

lemma leadingDigits_eq_iff_aux (k n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    leadingDigits 10 k x = n ↔
      Int.fract (Real.logb 10 x) ∈
        Set.Ico (Real.logb 10 n - ((k : ℝ) - 1)) (Real.logb 10 (n + 1) - ((k : ℝ) - 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  unfold leadingDigits
  rw [Nat.floor_eq_iff (by positivity), Set.mem_Ico, sub_le_iff_le_add,
    lt_sub_iff_add_lt]
  push_cast
  rw [Real.logb_le_iff_le_rpow (by norm_num) hn0, Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity)]

lemma leadingDigits_prob_aux {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (X : Ω → ℝ) (hX : HasUniformLogMantissa 10 P X)
    (k n : ℕ) (hk : 1 ≤ k) (hn1 : 10 ^ (k - 1) ≤ n) (hn2 : n < 10 ^ k) :
    P {ω | leadingDigits 10 k (X ω) = n} = ENNReal.ofReal (Real.logb 10 (1 + 1 / (n : ℝ))) := by
  obtain ⟨hXm, -, hmap⟩ := hX
  simp only [Nat.cast_ofNat] at hmap
  have hn : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by norm_num)) hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set g : Ω → ℝ := fun ω => Int.fract (Real.logb 10 (X ω)) with hg
  have hgm : Measurable g := by
    have : Measurable fun x : ℝ => Int.fract (Real.logb 10 x) :=
      (measurable_fract (R := ℝ)).comp (Real.measurable_log.div_const _)
    exact this.comp hXm
  have hset : {ω | leadingDigits 10 k (X ω) = n} =
      g ⁻¹' Set.Ico (Real.logb 10 n - ((k : ℝ) - 1)) (Real.logb 10 (n + 1) - ((k : ℝ) - 1)) := by
    ext ω
    exact leadingDigits_eq_iff_aux k n hn (X ω)
  have hkc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by push_cast [Nat.cast_sub hk]; ring
  have hlo : 0 ≤ Real.logb 10 n - ((k : ℝ) - 1) := by
    rw [sub_nonneg, ← hkc, Real.le_logb_iff_rpow_le (by norm_num) hn0, Real.rpow_natCast]
    exact_mod_cast hn1
  have hhi : Real.logb 10 (n + 1) - ((k : ℝ) - 1) ≤ 1 := by
    rw [sub_le_iff_le_add, show (1 : ℝ) + ((k : ℝ) - 1) = (k : ℝ) by ring,
      Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_natCast]
    exact_mod_cast hn2
  have hlt : Real.logb 10 n ≤ Real.logb 10 (n + 1) :=
    Real.logb_le_logb_of_le (by norm_num) hn0 (by linarith)
  rw [hset, ← MeasureTheory.Measure.map_apply hgm measurableSet_Ico, hmap,
    MeasureTheory.Measure.restrict_apply measurableSet_Ico,
    Set.inter_eq_left.mpr (Set.Ico_subset_Ico hlo hhi), Real.volume_Ico]
  congr 1
  rw [show Real.logb 10 (↑n + 1) - (↑k - 1) - (Real.logb 10 ↑n - (↑k - 1)) =
    Real.logb 10 (↑n + 1) - Real.logb 10 ↑n by ring, ← Real.logb_div (by positivity) hn0.ne']
  congr 1
  field_simp
  

lemma leadingDigits_measurableSet {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (hXm : Measurable X)
    (k m : ℕ) (hm : 1 ≤ m) : MeasurableSet {ω | leadingDigits 10 k (X ω) = m} := by
  have : {ω | leadingDigits 10 k (X ω) = m} = (fun ω => Int.fract (Real.logb 10 (X ω))) ⁻¹'
      Set.Ico (Real.logb 10 m - ((k : ℝ) - 1)) (Real.logb 10 (m + 1) - ((k : ℝ) - 1)) := by
    ext ω
    exact leadingDigits_eq_iff_aux k m hm (X ω)
  rw [this]
  have : Measurable fun x : ℝ => Int.fract (Real.logb 10 x) :=
    (measurable_fract (R := ℝ)).comp (Real.measurable_log.div_const _)
  exact (this.comp hXm) measurableSet_Ico

lemma leadingDigits_range (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    10 ^ (n - 1) ≤ leadingDigits 10 n x ∧ leadingDigits 10 n x < 10 ^ n := by
  unfold leadingDigits
  have h0 := Int.fract_nonneg (Real.logb ((10 : ℕ) : ℝ) x)
  have h1 := Int.fract_lt_one (Real.logb ((10 : ℕ) : ℝ) x)
  have hnc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by push_cast [Nat.cast_sub hn]; ring
  set f := Int.fract (Real.logb ((10 : ℕ) : ℝ) x)
  constructor
  · apply Nat.le_floor
    push_cast
    rw [← hnc, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  · rw [Nat.floor_lt (by positivity)]
    push_cast
    rw [← Real.rpow_natCast]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    linarith

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (X : Ω → ℝ) (hX : HasUniformLogMantissa 10 P X)
    (n : ℕ) (hn : 2 ≤ n) (d : ℕ) (hd : d ≤ 9) :
    (P {ω | digitAt 10 n (X ω) = d}).toReal =
      ∑ k ∈ Finset.Ico (10 ^ (n - 2) : ℕ) (10 ^ (n - 1)),
        Real.logb 10 (1 + 1 / (10 * (k : ℝ) + d)) := by
  have hpow : 10 ^ (n - 1) = 10 * 10 ^ (n - 2) := by
    rw [← pow_succ']; congr 1; omega
  have hpow' : 10 ^ n = 10 * 10 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hset : {ω | digitAt 10 n (X ω) = d} =
      ⋃ k ∈ Finset.Ico (10 ^ (n - 2) : ℕ) (10 ^ (n - 1)),
        {ω | leadingDigits 10 n (X ω) = 10 * k + d} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_Ico, digitAt, exists_prop]
    obtain ⟨hr1, hr2⟩ := leadingDigits_range n (by omega) (X ω)
    constructor
    · intro h
      refine ⟨leadingDigits 10 n (X ω) / 10, ⟨?_, ?_⟩, ?_⟩
      · rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
      · rw [Nat.div_lt_iff_lt_mul (by norm_num)]; omega
      · omega
    · rintro ⟨k, -, hk⟩
      rw [hk]; omega
  rw [hset, MeasureTheory.measure_biUnion_finset]
  · rw [ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Ico] at hk
      rw [leadingDigits_prob_aux P X hX n (10 * k + d) (by omega) (by omega) (by omega),
        ENNReal.toReal_ofReal]
      · push_cast; rfl
      · apply Real.logb_nonneg (by norm_num)
        have : (0 : ℝ) ≤ 1 / ((10 * k + d : ℕ) : ℝ) := by positivity
        linarith
    · intro k _
      rw [leadingDigits_prob_aux P X hX n (10 * k + d) (by omega) (by
        rw [Finset.mem_Ico] at *; omega) (by rw [Finset.mem_Ico] at *; omega)]
      exact ENNReal.ofReal_ne_top
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro ω hi hj
    simp only [Set.mem_ofPred_eq] at hi hj
    omega
  · intro k hk
    rw [Finset.mem_Ico] at hk
    exact leadingDigits_measurableSet X hX.1 n _ (by omega)
