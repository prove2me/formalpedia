-- Prove2me | solution 1 for BenfordLaw.benford_of_scale_invariant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:03:15.797998+00:00
-- url     : https://prove2.me/submissions/0172987e-e16e-4751-99ed-a065c79ede9d

import Mathlib
import Definitions.Def_BenfordLaw_Defs
open BenfordLaw MeasureTheory

namespace BenfordScaleInv

/-- Leading digit in base 10 via the fractional part of the logarithm. -/
lemma leadingDigit_eq_iff (x : ℝ) (d : ℕ) (hd1 : 1 ≤ d) :
    leadingDigit 10 x = d ↔
      Real.logb 10 d ≤ Int.fract (Real.logb 10 x) ∧
        Int.fract (Real.logb 10 x) < Real.logb 10 (d + 1) := by
  have hb1 : (1 : ℝ) < ((10 : ℕ) : ℝ) := by norm_num
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold leadingDigit
  rw [Nat.floor_eq_iff (by positivity)]
  push_cast at hb1 ⊢
  rw [Real.logb_le_iff_le_rpow hb1 hd0, Real.lt_logb_iff_rpow_lt hb1 (by positivity)]

/-- Indicator of `fract z ∈ [a0, a0 + a)` as a difference of floors. -/
lemma ind_eq (z a0 a : ℝ) (h0 : 0 ≤ a0) (ha : 0 ≤ a) (h1 : a0 + a ≤ 1) :
    (if a0 ≤ Int.fract z ∧ Int.fract z < a0 + a then (1 : ℝ) else 0) =
      ((⌊z - a0⌋ - ⌊z - a0 - a⌋ : ℤ) : ℝ) := by
  have hz : z = Int.fract z + (⌊z⌋ : ℝ) := by rw [Int.fract]; ring
  have e1 : z - a0 = (Int.fract z - a0) + (⌊z⌋ : ℝ) := by linarith
  have e2 : z - a0 - a = (Int.fract z - a0 - a) + (⌊z⌋ : ℝ) := by linarith
  rw [e2, e1, Int.floor_add_intCast, Int.floor_add_intCast]
  have f0 := Int.fract_nonneg z
  have f1 := Int.fract_lt_one z
  by_cases hA : a0 ≤ Int.fract z
  · have k1 : ⌊Int.fract z - a0⌋ = 0 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    rw [k1]
    by_cases hB : Int.fract z < a0 + a
    · have k2 : ⌊Int.fract z - a0 - a⌋ = -1 := by
        rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      rw [if_pos ⟨hA, hB⟩, k2]; norm_num
    · have k2 : ⌊Int.fract z - a0 - a⌋ = 0 := by
        rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      rw [if_neg (fun h => hB h.2), k2]; norm_num
  · have k1 : ⌊Int.fract z - a0⌋ = -1 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    have k2 : ⌊Int.fract z - a0 - a⌋ = -1 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    rw [if_neg (fun h => hA h.1), k1, k2]; norm_num

lemma telescope (w a : ℝ) (q : ℕ) :
    ∑ j ∈ Finset.range q, ((⌊w - j * a⌋ - ⌊w - j * a - a⌋ : ℤ) : ℝ) =
      ((⌊w⌋ - ⌊w - q * a⌋ : ℤ) : ℝ) := by
  have := Finset.sum_range_sub' (fun j : ℕ => ((⌊w - j * a⌋ : ℤ) : ℝ)) q
  simp only [Nat.cast_zero, zero_mul, sub_zero] at this
  push_cast
  rw [← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  congr 3
  ring

lemma floor_diff_bounds (w b : ℝ) :
    b - 1 ≤ ((⌊w⌋ - ⌊w - b⌋ : ℤ) : ℝ) ∧ ((⌊w⌋ - ⌊w - b⌋ : ℤ) : ℝ) ≤ b + 1 := by
  have h1 := Int.floor_le w
  have h2 := Int.lt_floor_add_one w
  have h3 := Int.floor_le (w - b)
  have h4 := Int.lt_floor_add_one (w - b)
  push_cast
  constructor <;> linarith

lemma measurable_ld : Measurable (fun x : ℝ => leadingDigit 10 x) := by
  unfold leadingDigit
  refine Measurable.nat_floor ?_
  refine Measurable.pow measurable_const ?_
  exact measurable_fract.comp (Real.measurable_log.div_const _)

end BenfordScaleInv

open BenfordScaleInv in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (X : Ω → ℝ) (hXm : Measurable X) (hXpos : ∀ᵐ ω ∂P, 0 < X ω)
    (hinv : ∀ c : ℝ, 0 < c → ∀ d : ℕ,
      P {ω | leadingDigit 10 (c * X ω) = d} = P {ω | leadingDigit 10 (X ω) = d})
    (d : ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) :
    (P {ω | leadingDigit 10 (X ω) = d}).toReal = benfordProb 10 d := by
  set m := (P {ω | leadingDigit 10 (X ω) = d}).toReal with hm
  set a0 := Real.logb 10 d with ha0
  set a := benfordProb 10 d with ha
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd9' : (d : ℝ) + 1 ≤ 10 := by exact_mod_cast (by omega : d + 1 ≤ 10)
  have ha_eq : a = Real.logb 10 (d + 1) - a0 := by
    rw [ha, benfordProb, ha0, ← Real.logb_div (by positivity) hd0.ne']
    congr 1; field_simp
  have h0 : 0 ≤ a0 := Real.logb_nonneg (by norm_num) (by exact_mod_cast hd1)
  have haa : 0 ≤ a := by
    rw [ha_eq]; linarith [Real.logb_le_logb_of_le (b := 10) (by norm_num) hd0
      (by linarith : (d : ℝ) ≤ d + 1)]
  have h1 : a0 + a ≤ 1 := by
    rw [ha_eq]; ring_nf
    calc Real.logb 10 (1 + d) ≤ Real.logb 10 10 :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
      _ = 1 := Real.logb_self_eq_one (by norm_num)
  -- the sets S_j
  let c : ℕ → ℝ := fun j => (10 : ℝ) ^ (-(j * a))
  have hc : ∀ j, 0 < c j := fun j => by positivity
  let S : ℕ → Set Ω := fun j => {ω | leadingDigit 10 (c j * X ω) = d}
  have hS : ∀ j, MeasurableSet (S j) := fun j =>
    (measurable_ld.comp (hXm.const_mul (c j))) (measurableSet_singleton d)
  have hPS : ∀ j, P.real (S j) = m := fun j => by
    rw [measureReal_def, hm]; exact congrArg ENNReal.toReal (hinv (c j) (hc j) d)
  -- key bound for each q
  have key : ∀ q : ℕ, |(q : ℝ) * m - q * a| ≤ 1 := by
    intro q
    let g : Ω → ℝ := fun ω => ∑ j ∈ Finset.range q, (S j).indicator 1 ω
    have hint : ∀ j, Integrable ((S j).indicator (1 : Ω → ℝ)) P := fun j =>
      (integrable_const (1 : ℝ)).indicator (hS j)
    have hg : Integrable g P := integrable_finsetSum _ fun j _ => hint j
    have hgint : ∫ ω, g ω ∂P = q * m := by
      simp only [g]
      rw [integral_finsetSum _ fun j _ => hint j]
      simp [integral_indicator_one (hS _), hPS]
    have hpt : ∀ᵐ ω ∂P, q * a - 1 ≤ g ω ∧ g ω ≤ q * a + 1 := by
      filter_upwards [hXpos] with ω hω
      have : g ω = ((⌊Real.logb 10 (X ω) - a0⌋ -
          ⌊Real.logb 10 (X ω) - a0 - q * a⌋ : ℤ) : ℝ) := by
        rw [← telescope]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hcx : 0 < c j * X ω := mul_pos (hc j) hω
        have hlog : Real.logb 10 (c j * X ω) = Real.logb 10 (X ω) - j * a := by
          rw [Real.logb_mul (hc j).ne' hω.ne']
          simp only [c]
          rw [Real.logb_rpow (by norm_num) (by norm_num)]; ring
        have e := ind_eq (Real.logb 10 (c j * X ω)) a0 a h0 haa h1
        rw [hlog] at e
        rw [show Real.logb 10 (X ω) - a0 - j * a = Real.logb 10 (X ω) - j * a - a0 by ring,
          ← e]
        simp only [Set.indicator, S, Set.mem_ofPred_eq, Pi.one_apply]
        have haa0 : a0 + a = Real.logb 10 (d + 1) := by rw [ha_eq]; ring
        refine if_congr ?_ rfl rfl
        rw [leadingDigit_eq_iff _ d hd1, hlog, haa0]
      rw [this]
      exact floor_diff_bounds _ _
    have lo : q * a - 1 ≤ ∫ ω, g ω ∂P := by
      have := integral_mono_ae (integrable_const (q * a - 1)) hg
        (hpt.mono fun ω h => h.1)
      simpa using this
    have hi : ∫ ω, g ω ∂P ≤ q * a + 1 := by
      have := integral_mono_ae hg (integrable_const (q * a + 1))
        (hpt.mono fun ω h => h.2)
      simpa using this
    rw [hgint] at lo hi
    rw [abs_le]; constructor <;> linarith
  by_contra hne
  have hpos : 0 < |m - a| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨q, hq⟩ := exists_nat_gt (1 / |m - a|)
  have := key q
  rw [← mul_sub, abs_mul, Nat.abs_cast] at this
  rw [div_lt_iff₀ hpos] at hq
  linarith
