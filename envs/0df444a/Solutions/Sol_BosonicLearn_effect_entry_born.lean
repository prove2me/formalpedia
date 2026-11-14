-- Prove2me | solution 1 for BosonicLearn.effect_entry_born
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T06:16:22.441538+00:00
-- url     : https://prove2.me/submissions/f13d5940-83a5-4f60-80d5-760d9bd670ca

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

/-! ### Born probabilities of rank-one states -/

/-- The quadratic form of an effect is the squared norm times the Born probability of the normalized
rank-one state. -/
private lemma law_rankOne {I O : Type} [DecidableEq I] [MeasurableSpace O] (P : FockPOVM I O)
    (s : Finset I) (z : I → ℂ) (hN : 0 < ∑ k ∈ s, ‖z k‖ ^ 2) {B : Set O} (hB : MeasurableSet B) :
    ∑ i ∈ s, ∑ j ∈ s, star (z i) * P.effect B i j * z j =
      ((∑ k ∈ s, ‖z k‖ ^ 2 : ℝ) : ℂ) * (((P.law (rankOneMat s z) B).toReal : ℝ) : ℂ) := by
  set N : ℝ := ∑ k ∈ s, ‖z k‖ ^ 2 with hNdef
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hτ := rankOneMat_isDensity s z hN
  have hborn := P.law_born _ hτ B hB
  rw [born_rankOne] at hborn
  have hq := P.effect_form B hB s z
  set q : ℂ := ∑ i ∈ s, ∑ j ∈ s, star (z i) * P.effect B i j * z j with hqdef
  have hqre : q = (q.re : ℂ) := Complex.ext (by simp) (by simp [hq.1])
  have hre : (q * ((N : ℂ))⁻¹).re = q.re * N⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.re_mul_ofReal]
  rw [hre] at hborn
  rw [hborn, ENNReal.toReal_ofReal (mul_nonneg hq.2.1 (inv_nonneg.mpr hN.le)), Complex.ofReal_mul,
    Complex.ofReal_inv, ← hqre, mul_comm q, ← mul_assoc, mul_inv_cancel₀ hNc, one_mul]

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

private def om : Fin 4 → ℂ
  | 0 => 1
  | 1 => -1
  | 2 => Complex.I
  | 3 => -Complex.I

private def cf : Fin 4 → ℂ
  | 0 => 1 / 2
  | 1 => -1 / 2
  | 2 => -Complex.I / 2
  | 3 => Complex.I / 2

private lemma norm_om (c : Fin 4) : ‖om c‖ = 1 := by
  fin_cases c <;> simp [om]

/-- The vector `e_a + ω e_b`. -/
private def pv {I : Type} [DecidableEq I] (a b : I) (ω : ℂ) : I → ℂ :=
  fun k => (if k = a then (1 : ℂ) else 0) + ω * (if k = b then 1 else 0)

private lemma pv_norm {I : Type} [DecidableEq I] {a b : I} (hab : a ≠ b) (ω : ℂ) (hω : ‖ω‖ = 1) :
    ∑ k ∈ ({a, b} : Finset I), ‖pv a b ω k‖ ^ 2 = 2 := by
  have hba : b ≠ a := fun h => hab h.symm
  rw [Finset.sum_pair hab]
  simp [pv, hab, hba, hω]
  norm_num

theorem solution {I : Type} [DecidableEq I] (a b : I) :
    ∃ (τ : Fin 4 → Matrix I I ℂ) (coef : Fin 4 → ℂ), (∀ c, IsDensity (τ c)) ∧
      (∑ c, coef c = (1 : Matrix I I ℂ) a b) ∧
      ∀ (O : Type) [MeasurableSpace O] (P : FockPOVM I O) (B : Set O), MeasurableSet B →
        P.effect B a b = ∑ c, coef c * (((P.law (τ c) B).toReal : ℝ) : ℂ) := by
  by_cases hab : a = b
  · subst hab
    have hN : ∑ k ∈ ({a} : Finset I), ‖(fun _ : I => (1 : ℂ)) k‖ ^ 2 = 1 := by simp
    refine ⟨fun _ => rankOneMat {a} (fun _ => 1), fun c => if c = 0 then 1 else 0,
      fun _ => rankOneMat_isDensity _ _ (by rw [hN]; norm_num), by simp, fun O _ P B hB => ?_⟩
    have h := law_rankOne P {a} (fun _ => 1) (by rw [hN]; norm_num) hB
    rw [hN] at h
    simp only [Finset.sum_singleton, star_one, one_mul, mul_one, Complex.ofReal_one] at h
    rw [h]
    simp
  · have hpos : ∀ c : Fin 4, 0 < ∑ k ∈ ({a, b} : Finset I), ‖pv a b (om c) k‖ ^ 2 := by
      intro c
      rw [pv_norm hab _ (norm_om c)]
      norm_num
    refine ⟨fun c => rankOneMat {a, b} (pv a b (om c)), cf,
      fun c => rankOneMat_isDensity _ _ (hpos c), ?_, fun O _ P B hB => ?_⟩
    · rw [Fin.sum_univ_four, Matrix.one_apply_ne hab]
      simp only [cf]
      ring
    · have h : ∀ c : Fin 4, P.effect B a a + om c * P.effect B a b + star (om c) * P.effect B b a +
          star (om c) * om c * P.effect B b b =
          (2 : ℂ) * (((P.law (rankOneMat {a, b} (pv a b (om c))) B).toReal : ℝ) : ℂ) := by
        intro c
        have h1 := law_rankOne P {a, b} (pv a b (om c)) (hpos c) hB
        rw [pv_norm hab _ (norm_om c)] at h1
        have h2 := form_pair (P.effect B) a b (om c)
        simp only [pv] at h1
        rw [h2] at h1
        rw [h1]
        norm_num
      have h0 := h 0
      have h1 := h 1
      have h2 := h 2
      have h3 := h 3
      simp only [om, star_one, star_neg, Complex.star_def, Complex.conj_I] at h0 h1 h2 h3
      rw [Fin.sum_univ_four]
      simp only [cf, om]
      linear_combination (1 / 4 : ℂ) * h0 - (1 / 4 : ℂ) * h1 - (Complex.I / 4) * h2 +
        (Complex.I / 4) * h3 + (1 / 2 : ℂ) * (P.effect B a b - P.effect B b a) * Complex.I_mul_I
