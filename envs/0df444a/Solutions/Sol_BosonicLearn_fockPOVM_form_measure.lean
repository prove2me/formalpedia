-- Prove2me | solution 1 for BosonicLearn.fockPOVM_form_measure
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T05:06:10.238663+00:00
-- url     : https://prove2.me/submissions/055695c3-7484-4d45-bc78-bcf8762d43f6

import Mathlib
import Definitions.Def_BosonicLearn_FockPOVM

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity IsTraceClass NuclearExpansion)
open QAlgorithms.RealRegisters (Hilbert)
open MeasureTheory
open scoped ENNReal

open BosonicLearn

noncomputable section

/-! ### Rank-one densities with finite support -/

private def finVec {I : Type} [DecidableEq I] (s : Finset I) (g : I → ℂ) : Hilbert I :=
  ∑ i ∈ s, lp.single 2 i (g i)

private lemma finVec_apply {I : Type} [DecidableEq I] (s : Finset I) (g : I → ℂ) (j : I) :
    finVec s g j = if j ∈ s then g j else 0 := by
  unfold finVec
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply]
  exact Finset.sum_pi_single j (fun i => g i) s

/-- The normalized rank-one matrix of the vector equal to `z` on `s` and `0` elsewhere. -/
private def rankOneMat {I : Type} [DecidableEq I] (s : Finset I) (z : I → ℂ) : Matrix I I ℂ :=
  fun i j => (if i ∈ s then z i else 0) * star (if j ∈ s then z j else 0) *
    (((∑ k ∈ s, ‖z k‖ ^ 2 : ℝ) : ℂ))⁻¹

private lemma rankOneMat_isDensity {I : Type} [DecidableEq I] (s : Finset I) (z : I → ℂ)
    (hN : 0 < ∑ k ∈ s, ‖z k‖ ^ 2) : IsDensity (rankOneMat s z) := by
  set N : ℝ := ∑ k ∈ s, ‖z k‖ ^ 2 with hNdef
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨⟨{
    left := fun n => if n = 0 then ((N : ℂ)⁻¹) • finVec s z else 0
    right := fun n => if n = 0 then finVec s z else 0
    summable := summable_of_ne_finset_zero (s := {0}) fun n hn => by
      have : n ≠ 0 := by simpa using hn
      simp [this]
    coefficients := ?_ }⟩, ?_, ?_⟩
  · intro i j
    rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
    simp only [if_true, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, finVec_apply, rankOneMat]
    ring
  · intro t x
    have key : ∑ i ∈ t, ∑ j ∈ t, star (x i) * rankOneMat s z i j * x j =
        ((‖∑ i ∈ t, star (x i) * (if i ∈ s then z i else 0)‖ ^ 2 * N⁻¹ : ℝ) : ℂ) := by
      set c : ℂ := ∑ i ∈ t, star (x i) * (if i ∈ s then z i else 0) with hc
      have h1 : c * star c = (‖c‖ : ℂ) ^ 2 := by
        rw [Complex.star_def, Complex.mul_conj']
      push_cast
      rw [← h1, hc, star_sum, Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [rankOneMat, star_mul', star_star]
      ring
    rw [key]
    refine ⟨Complex.ofReal_im _, ?_⟩
    rw [Complex.ofReal_re]
    positivity
  · have hdiag : ∀ i, (rankOneMat s z i i).re = if i ∈ s then ‖z i‖ ^ 2 * N⁻¹ else 0 := by
      intro i
      by_cases hi : i ∈ s
      · simp only [rankOneMat, hi, if_true]
        rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_inv,
          ← Complex.ofReal_mul, Complex.ofReal_re]
      · simp [rankOneMat, hi]
    have hsum : HasSum (fun i => (rankOneMat s z i i).re) (∑ i ∈ s, (rankOneMat s z i i).re) :=
      hasSum_sum_of_ne_finset_zero fun i hi => by rw [hdiag, if_neg hi]
    have hval : ∑ i ∈ s, (rankOneMat s z i i).re = 1 := by
      have : ∑ i ∈ s, (rankOneMat s z i i).re = ∑ i ∈ s, ‖z i‖ ^ 2 * N⁻¹ :=
        Finset.sum_congr rfl fun i hi => by rw [hdiag, if_pos hi]
      rw [this, ← Finset.sum_mul, ← hNdef, mul_inv_cancel₀ hN.ne']
    exact ⟨hsum.summable, hsum.tsum_eq.trans hval⟩

/-- The Born sum of a matrix against the rank-one density is its quadratic form divided by the squared norm. -/
private lemma born_rankOne {I : Type} [DecidableEq I] (E : Matrix I I ℂ) (s : Finset I) (z : I → ℂ) :
    ∑' i, ∑' j, E i j * rankOneMat s z j i =
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j) * (((∑ k ∈ s, ‖z k‖ ^ 2 : ℝ) : ℂ))⁻¹ := by
  have hinner : ∀ i, ∑' j, E i j * rankOneMat s z j i = ∑ j ∈ s, E i j * rankOneMat s z j i := by
    intro i
    exact tsum_eq_sum fun j hj => by simp [rankOneMat, hj]
  have houter : ∑' i, ∑ j ∈ s, E i j * rankOneMat s z j i =
      ∑ i ∈ s, ∑ j ∈ s, E i j * rankOneMat s z j i := by
    refine tsum_eq_sum fun i hi => ?_
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [rankOneMat, hi]
  rw [tsum_congr hinner, houter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [rankOneMat, hi, hj, if_true]
  ring

/-! ### Quadratic forms of the effects are finite measures -/

private lemma form_measure {I Ω : Type} [DecidableEq I] [MeasurableSpace Ω] (P : FockPOVM I Ω)
    (s : Finset I) (z : I → ℂ) :
    ∃ m : Measure Ω, IsFiniteMeasure m ∧ ∀ B, MeasurableSet B →
      ∑ i ∈ s, ∑ j ∈ s, star (z i) * P.effect B i j * z j = ((m B).toReal : ℂ) := by
  set N : ℝ := ∑ k ∈ s, ‖z k‖ ^ 2 with hNdef
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => by positivity
  rcases hN0.eq_or_lt with h0 | hpos
  · refine ⟨0, inferInstance, fun B _ => ?_⟩
    have hz : ∀ i ∈ s, z i = 0 := by
      intro i hi
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp h0.symm i hi
      simpa using h
    simp only [Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero, Complex.ofReal_zero]
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j _ => ?_
    rw [hz i hi]
    simp
  · have hτ := rankOneMat_isDensity s z hpos
    have hprob := P.law_prob _ hτ
    refine ⟨ENNReal.ofReal N • P.law (rankOneMat s z), Measure.smul_finite _ ENNReal.ofReal_ne_top,
      fun B hB => ?_⟩
    have hborn := P.law_born _ hτ B hB
    rw [born_rankOne] at hborn
    have hq := P.effect_form B hB s z
    set q : ℂ := ∑ i ∈ s, ∑ j ∈ s, star (z i) * P.effect B i j * z j with hqdef
    have hqre : q = (q.re : ℂ) := Complex.ext (by simp) (by simp [hq.1])
    have hre : (q * ((N : ℂ))⁻¹).re = q.re * N⁻¹ := by
      rw [← Complex.ofReal_inv, Complex.re_mul_ofReal]
    rw [hre] at hborn
    have hm : ((ENNReal.ofReal N • P.law (rankOneMat s z)) B).toReal = q.re := by
      rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hN0, hborn,
        ENNReal.toReal_ofReal (mul_nonneg hq.2.1 (inv_nonneg.mpr hN0))]
      field_simp
    rw [hm]
    exact hqre

/-! ### Matrix entries by polarization -/

private lemma form_pair {I : Type} [DecidableEq I] (E : Matrix I I ℂ) (i j : I) (c : ℂ) :
    ∑ a ∈ ({i, j} : Finset I), ∑ b ∈ ({i, j} : Finset I),
        star ((if a = i then (1 : ℂ) else 0) + c * (if a = j then 1 else 0)) * E a b *
          ((if b = i then (1 : ℂ) else 0) + c * (if b = j then 1 else 0)) =
      E i i + c * E i j + star c * E j i + star c * c * E j j := by
  by_cases hij : i = j
  · subst hij
    simp
    ring
  · have hji : j ≠ i := fun h => hij h.symm
    simp [Finset.sum_pair hij, hij, hji]
    ring

private lemma entry_measures {I Ω : Type} [DecidableEq I] [MeasurableSpace Ω] (P : FockPOVM I Ω)
    (i j : I) :
    ∃ m : Fin 4 → Measure Ω, (∀ k, IsFiniteMeasure (m k)) ∧ ∀ B, MeasurableSet B →
      P.effect B i j = (1 / 4 : ℂ) * ((((m 0 B).toReal - (m 1 B).toReal : ℝ) : ℂ) -
        Complex.I * (((m 2 B).toReal - (m 3 B).toReal : ℝ) : ℂ)) := by
  choose m hm using fun c : ℂ => form_measure P {i, j}
    (fun a => (if a = i then (1 : ℂ) else 0) + c * (if a = j then 1 else 0))
  refine ⟨![m 1, m (-1), m Complex.I, m (-Complex.I)], ?_, fun B hB => ?_⟩
  · intro k
    fin_cases k <;> exact (hm _).1
  · have h1 := (hm 1).2 B hB
    have h2 := (hm (-1)).2 B hB
    have h3 := (hm Complex.I).2 B hB
    have h4 := (hm (-Complex.I)).2 B hB
    rw [form_pair] at h1 h2 h3 h4
    show P.effect B i j = (1 / 4 : ℂ) * ((((m 1 B).toReal - (m (-1) B).toReal : ℝ) : ℂ) -
      Complex.I * (((m Complex.I B).toReal - (m (-Complex.I) B).toReal : ℝ) : ℂ))
    push_cast
    rw [← h1, ← h2, ← h3, ← h4]
    simp only [star_one, star_neg, Complex.star_def, Complex.conj_I]
    linear_combination (1 / 2 : ℂ) * (P.effect B i j - P.effect B j i) * Complex.I_mul_I

/-! ### The statement -/

theorem solution {I Ω : Type} [DecidableEq I] [MeasurableSpace Ω] (P : FockPOVM I Ω) :
    (∀ (s : Finset I) (z : I → ℂ), ∃ m : Measure Ω, IsFiniteMeasure m ∧ ∀ B, MeasurableSet B →
      ∑ i ∈ s, ∑ j ∈ s, star (z i) * P.effect B i j * z j = ((m B).toReal : ℂ)) ∧
    (∀ i j : I, ∃ m : Fin 4 → Measure Ω, (∀ k, IsFiniteMeasure (m k)) ∧ ∀ B, MeasurableSet B →
      P.effect B i j = (1 / 4 : ℂ) * ((((m 0 B).toReal - (m 1 B).toReal : ℝ) : ℂ) -
        Complex.I * (((m 2 B).toReal - (m 3 B).toReal : ℝ) : ℂ))) :=
  ⟨form_measure P, entry_measures P⟩
