-- Prove2me | solution 1 for BenfordLaw.leadingDigits_prob_of_uniform_log_mantissa
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:46:09.683763+00:00
-- url     : https://prove2.me/submissions/78f4998e-f12f-4450-9dbe-98eb900bc88c

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
  
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (X : Ω → ℝ) (hX : HasUniformLogMantissa 10 P X)
    (k n : ℕ) (hk : 1 ≤ k) (hn1 : 10 ^ (k - 1) ≤ n) (hn2 : n < 10 ^ k) :
    (P {ω | leadingDigits 10 k (X ω) = n}).toReal = Real.logb 10 (1 + 1 / (n : ℝ)) := by
  rw [leadingDigits_prob_aux P X hX k n hk hn1 hn2, ENNReal.toReal_ofReal]
  apply Real.logb_nonneg (by norm_num)
  have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  linarith
