-- Prove2me | solution 1 for BurkholderDFI.Gundy.eq_1_5
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:52:11.180303+00:00
-- url     : https://prove2.me/submissions/37f087ff-7cb5-484d-a664-8d80e8c2e6a9

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal


namespace BurkholderDFI.Gundy
open BurkholderDFI.SquareFnLp

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}

/-- `|f_n|` with the convention `f_0 = 0`. -/
noncomputable def absZ (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun n ω => if n = 0 then 0 else |f n ω|

lemma absZ_nonneg (f : ℕ → Ω → ℝ) : 0 ≤ absZ f := by
  intro n ω
  simp only [absZ, Pi.zero_apply]
  split_ifs <;> simp [abs_nonneg]

lemma absZ_pos (f : ℕ → Ω → ℝ) {n : ℕ} (hn : 1 ≤ n) : absZ f n = fun ω => |f n ω| := by
  funext ω; simp [absZ, Nat.one_le_iff_ne_zero.mp hn]

lemma absZ_zero (f : ℕ → Ω → ℝ) : absZ f 0 = 0 := by
  funext ω; simp [absZ]

lemma absZ_submartingale [IsFiniteMeasure P]
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n)) :
    Submartingale (absZ f) ℱ P := by
  have hsub : Submartingale f ℱ P := hf.elim (fun h => h.submartingale) (fun h => h.1)
  have hadp : StronglyAdapted ℱ (absZ f) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [absZ_zero]; exact stronglyMeasurable_const
    · rw [absZ_pos f hn]
      have := (hsub.stronglyAdapted n).norm
      simpa [Real.norm_eq_abs] using this
  have hint : ∀ n, Integrable (absZ f n) P := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [absZ_zero]; exact integrable_zero _ _ _
    · rw [absZ_pos f hn]; exact (hsub.integrable n).abs
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [absZ_zero]
    exact condExp_nonneg (Eventually.of_forall (absZ_nonneg f j))
  · have hj : 1 ≤ j := le_trans hi hij
    rw [absZ_pos f hi, absZ_pos f hj]
    rcases hf with hm | ⟨hs, hnn⟩
    · have h := (hm.submartingale.sup hm.neg.submartingale).2.1 i j hij
      have e : ∀ k, (f ⊔ -f) k = fun ω => |f k ω| := by
        intro k; funext ω; simp [abs_eq_max_neg]
      simpa [e] using h
    · have h1 := hs.2.1 i j hij
      have e1 : f i =ᵐ[P] fun ω => |f i ω| := by
        filter_upwards [hnn i hi] with ω hω; simp [abs_of_nonneg hω]
      have e2 : f j =ᵐ[P] fun ω => |f j ω| := by
        filter_upwards [hnn j hj] with ω hω; simp [abs_of_nonneg hω]
      have h2 : P[f j | ℱ i] =ᵐ[P] P[fun ω => |f j ω| | ℱ i] := condExp_congr_ae e2
      filter_upwards [h1, e1, h2] with ω h1 e1 h2
      rw [← e1, ← h2]; exact h1


/-- Abstract Hölder step: from `c * P A ≤ ∫_A F` deduce `c^p * P A ≤ ∫ F^p`. -/
lemma holder_step [IsFiniteMeasure P] (F : Ω → ℝ≥0∞) (hF : AEMeasurable F P) {A : Set Ω}
    (hA : MeasurableSet A) (c : ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p)
    (h : c * P A ≤ ∫⁻ ω in A, F ω ∂P) :
    c ^ p * P A ≤ ∫⁻ ω, F ω ^ p ∂P := by
  rcases eq_or_lt_of_le hp with rfl | hp1
  · simp only [ENNReal.rpow_one]
    exact h.trans (setLIntegral_le_lintegral _ _)
  have hp0 : 0 < p := by linarith
  set q := Real.conjExponent p with hq
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
  have hq0 : 0 < q := hpq.symm.pos
  have hsum : 1 / p + 1 / q = 1 := by
    have := hpq.inv_add_inv_eq_one; simpa [one_div] using this
  set N := (∫⁻ ω, F ω ^ p ∂P) ^ (1 / p) with hN
  have hhold : ∫⁻ ω in A, F ω ∂P ≤ N * (P A) ^ (1 / q) := by
    set g : Ω → ℝ≥0∞ := A.indicator (fun _ => 1) with hg
    have hgm : AEMeasurable g P := aemeasurable_const.indicator hA
    have h1 : ∫⁻ ω in A, F ω ∂P = ∫⁻ ω, (F * g) ω ∂P := by
      rw [← lintegral_indicator hA]
      congr 1; funext ω
      by_cases hω : ω ∈ A <;> simp [hg, Set.indicator_of_mem, Set.indicator_of_notMem, hω]
    have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq hF hgm
    have h3 : ∫⁻ ω, g ω ^ q ∂P = P A := by
      rw [← lintegral_indicator_one hA]
      congr 1; funext ω
      by_cases hω : ω ∈ A <;> simp [hg, Set.indicator_of_mem, Set.indicator_of_notMem, hω, ENNReal.zero_rpow_of_pos hq0]
    rw [h1]; rw [h3] at h2; exact h2
  have hmain : c * P A ≤ N * (P A) ^ (1 / q) := h.trans hhold
  by_cases hPA : P A = 0
  · rw [hPA]; simp
  have hPAt : P A ≠ ⊤ := measure_ne_top _ _
  have hsplit : P A = (P A) ^ (1 / p) * (P A) ^ (1 / q) := by
    rw [← ENNReal.rpow_add _ _ hPA hPAt, hsum, ENNReal.rpow_one]
  have hq_ne0 : (P A) ^ (1 / q) ≠ 0 := by
    intro h0; rw [ENNReal.rpow_eq_zero_iff] at h0
    rcases h0 with ⟨h0, _⟩ | ⟨h0, _⟩
    · exact hPA h0
    · exact hPAt h0
  have hq_net : (P A) ^ (1 / q) ≠ ⊤ := by
    intro h0; rw [ENNReal.rpow_eq_top_iff] at h0
    rcases h0 with ⟨h0, _⟩ | ⟨h0, _⟩
    · exact hPA h0
    · exact hPAt h0
  have hcan : c * (P A) ^ (1 / p) ≤ N := by
    have hmain' : c * (P A) ^ (1 / p) * (P A) ^ (1 / q) ≤ N * (P A) ^ (1 / q) := by
      rw [mul_assoc, ← hsplit]; exact hmain
    have := (ENNReal.le_div_iff_mul_le (Or.inl hq_ne0) (Or.inl hq_net)).mpr hmain'
    rwa [ENNReal.mul_div_cancel_right hq_ne0 hq_net] at this
  have hpow := ENNReal.rpow_le_rpow hcan hp0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne',
    ENNReal.rpow_one] at hpow
  rw [hN, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one] at hpow
  exact hpow

lemma maxFnN_subset (f : ℕ → Ω → ℝ) (l : ℝ) (n : ℕ) :
    {ω | ENNReal.ofReal l < maxFnN f n ω} ⊆
      {ω | ((l.toNNReal : ℝ≥0) : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => absZ f k ω} := by
  intro ω hω
  simp only [Set.mem_setOf_eq, maxFnN] at hω
  rw [lt_iSup_iff] at hω
  obtain ⟨k, hk⟩ := hω
  rw [lt_iSup_iff] at hk
  obtain ⟨hkmem, hk⟩ := hk
  rw [Finset.mem_Icc] at hkmem
  have hpos : 0 < |f k ω| := by
    have : 0 < ENNReal.ofReal |f k ω| := lt_of_le_of_lt bot_le hk
    exact ENNReal.ofReal_pos.mp this
  rw [ENNReal.ofReal_lt_ofReal_iff hpos] at hk
  show ((l.toNNReal : ℝ≥0) : ℝ) ≤ _
  rw [Real.coe_toNNReal']
  have hle : absZ f k ω ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => absZ f k ω :=
    Finset.le_sup' (fun k => absZ f k ω) (Finset.mem_range.mpr (by omega))
  rw [absZ_pos f hkmem.1] at hle
  exact le_trans (max_le hk.le (abs_nonneg _)) hle


lemma lpNormE_le_pNorm (P : Measure Ω) (p : ℝ) (f : ℕ → Ω → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    lpNormE P p (fun ω => ENNReal.ofReal |f n ω|) ≤ pNorm P p f :=
  le_iSup₂ (f := fun n (_ : n ∈ Set.Ici 1) => lpNormE P p (fun ω => ENNReal.ofReal |f n ω|)) n hn

lemma eq_1_5_step [IsProbabilityMeasure P]
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (p : ℝ) (hp : 1 ≤ p) (l : ℝ) (hl : 0 < l) {n : ℕ} (hn : 1 ≤ n) :
    ENNReal.ofReal (l ^ p) * P {ω | ENNReal.ofReal l < maxFnN f n ω} ≤ pNorm P p f ^ p := by
  have hG := absZ_submartingale hf
  set ε : ℝ≥0 := l.toNNReal with hε
  set A := {ω | (ε : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    fun k => absZ f k ω} with hAdef
  have hA : MeasurableSet A :=
    measurableSet_le measurable_const (Finset.measurable_range_sup'' fun k _ =>
      (hG.stronglyMeasurable k).measurable.le (ℱ.le k))
  have h1 := maximal_ineq hG (absZ_nonneg f) (ε := ε) n
  have h2 : ENNReal.ofReal (∫ ω in A, absZ f n ω ∂P) = ∫⁻ ω in A, ENNReal.ofReal (absZ f n ω) ∂P :=
    ofReal_integral_eq_lintegral_ofReal (hG.integrable n).integrableOn
      (Eventually.of_forall (absZ_nonneg f n))
  rw [h2] at h1
  have h3 := holder_step (fun ω => ENNReal.ofReal (absZ f n ω))
    (ENNReal.measurable_ofReal.comp_aemeasurable (hG.integrable n).aemeasurable) hA (ε : ℝ≥0∞) hp h1
  have h4 : (∫⁻ ω, ENNReal.ofReal (absZ f n ω) ^ p ∂P) ≤ pNorm P p f ^ p := by
    have := ENNReal.rpow_le_rpow (lpNormE_le_pNorm P p f hn) (le_trans zero_le_one hp)
    rw [lpNormE, ← ENNReal.rpow_mul, one_div_mul_cancel (by linarith), ENNReal.rpow_one] at this
    rw [absZ_pos f hn]; exact this
  have h5 : ENNReal.ofReal (l ^ p) = (ε : ℝ≥0∞) ^ p := by
    have := ENNReal.ofReal_rpow_of_nonneg hl.le (by linarith : (0:ℝ) ≤ p)
    show ENNReal.ofReal (l ^ p) = ENNReal.ofReal l ^ p
    first | exact this | exact this.symm
  rw [h5]
  calc (ε : ℝ≥0∞) ^ p * P {ω | ENNReal.ofReal l < maxFnN f n ω}
      ≤ (ε : ℝ≥0∞) ^ p * P A := by gcongr; exact maxFnN_subset f l n
    _ ≤ _ := h3.trans h4

lemma maxFnN_mono (f : ℕ → Ω → ℝ) (ω : Ω) : Monotone (fun n => maxFnN f n ω) := by
  intro n m hnm
  simp only [maxFnN]
  exact biSup_mono fun k hk => by rw [Finset.mem_Icc] at hk ⊢; omega

theorem eq_1_5_core {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (p : ℝ) (hp : 1 ≤ p) (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal (l ^ p) * P {ω | ENNReal.ofReal l < BurkholderDFI.SquareFnLp.maxFn f ω} ≤ BurkholderDFI.SquareFnLp.pNorm P p f ^ p := by
  have hset : {ω | ENNReal.ofReal l < maxFn f ω} = ⋃ n, {ω | ENNReal.ofReal l < maxFnN f n ω} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion, maxFn, lt_iSup_iff]
  have hmono : Monotone fun n => {ω | ENNReal.ofReal l < maxFnN f n ω} := by
    intro n m hnm ω hω
    exact lt_of_lt_of_le hω (maxFnN_mono f ω hnm)
  rw [hset, hmono.measure_iUnion, ENNReal.mul_iSup]
  refine iSup_le fun n => ?_
  calc ENNReal.ofReal (l ^ p) * P {ω | ENNReal.ofReal l < maxFnN f n ω}
      ≤ ENNReal.ofReal (l ^ p) * P {ω | ENNReal.ofReal l < maxFnN f (n + 1) ω} := by
        exact mul_le_mul_right (measure_mono (μ := P) (hmono (Nat.le_succ n))) _
    _ ≤ _ := eq_1_5_step hf p hp l hl (Nat.succ_pos n)

end BurkholderDFI.Gundy

open BurkholderDFI.Gundy


theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (p : ℝ) (hp : 1 ≤ p) (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal (l ^ p) * P {ω | ENNReal.ofReal l < BurkholderDFI.SquareFnLp.maxFn f ω} ≤ BurkholderDFI.SquareFnLp.pNorm P p f ^ p := by
  exact eq_1_5_core hf p hp l hl
