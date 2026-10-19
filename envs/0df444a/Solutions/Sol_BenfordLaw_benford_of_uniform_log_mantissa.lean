-- Prove2me | solution 1 for BenfordLaw.benford_of_uniform_log_mantissa
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:44:16.956338+00:00
-- url     : https://prove2.me/submissions/f949d307-c216-4df4-957a-09f18318fb6c

import Mathlib
import Definitions.Def_BenfordLaw_Defs
open BenfordLaw

lemma leadingDigit_eq_iff_aux (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (d : ℕ) (hd1 : 1 ≤ d) :
    leadingDigit b x = d ↔
      Int.fract (Real.logb b x) ∈ Set.Ico (Real.logb b d) (Real.logb b (d + 1)) := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold leadingDigit
  rw [Nat.floor_eq_iff (by positivity), Set.mem_Ico, Real.logb_le_iff_le_rpow hb1 hd0,
    Real.lt_logb_iff_rpow_lt hb1 (by positivity)]

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (b : ℕ) (hb : 2 ≤ b) (P : MeasureTheory.Measure Ω) (X : Ω → ℝ)
    (hX : HasUniformLogMantissa b P X) (d : ℕ) (hd1 : 1 ≤ d) (hdb : d < b) :
    (P {ω | leadingDigit b (X ω) = d}).toReal = benfordProb b d := by
  obtain ⟨hXm, -, hmap⟩ := hX
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  set g : Ω → ℝ := fun ω => Int.fract (Real.logb b (X ω)) with hg
  have hgm : Measurable g := by
    have : Measurable fun x : ℝ => Int.fract (Real.logb b x) :=
      (measurable_fract (R := ℝ)).comp (Real.measurable_log.div_const _)
    exact this.comp hXm
  have hset : {ω | leadingDigit b (X ω) = d} =
      g ⁻¹' Set.Ico (Real.logb b d) (Real.logb b (d + 1)) := by
    ext ω
    exact leadingDigit_eq_iff_aux b hb (X ω) d hd1
  have hlo : 0 ≤ Real.logb b d := Real.logb_nonneg hb1 (by exact_mod_cast hd1)
  have hhi : Real.logb b (d + 1) ≤ 1 := by
    rw [Real.logb_le_iff_le_rpow hb1 (by positivity), Real.rpow_one]
    exact_mod_cast (by omega : d + 1 ≤ b)
  have hlt : Real.logb b d ≤ Real.logb b (d + 1) :=
    Real.logb_le_logb_of_le hb1 hd0 (by linarith)
  rw [hset, ← MeasureTheory.Measure.map_apply hgm measurableSet_Ico, hmap,
    MeasureTheory.Measure.restrict_apply measurableSet_Ico,
    Set.inter_eq_left.mpr (Set.Ico_subset_Ico hlo hhi), Real.volume_Ico,
    ENNReal.toReal_ofReal (by linarith), benfordProb, ← Real.logb_div (by positivity) hd0.ne']
  congr 1
  field_simp
