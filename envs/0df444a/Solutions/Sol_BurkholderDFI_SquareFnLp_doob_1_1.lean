-- Prove2me | solution 1 for BurkholderDFI.SquareFnLp.doob_1_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:51:18.458722+00:00
-- url     : https://prove2.me/submissions/1cb2dd77-1527-4b6e-b4d3-1bce36db407f

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.SquareFnLp

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

/-- The level set of `maxFnN` for the real threshold `l + 1/(k+1)` written through `absZ`. -/
noncomputable def levelSet (f : ℕ → Ω → ℝ) (n : ℕ) (c : ℝ) : Set Ω :=
  {ω | ((c.toNNReal : ℝ≥0) : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => absZ f k ω}

lemma levelSet_subset (f : ℕ → Ω → ℝ) (n : ℕ) {l c : ℝ} (hl : 0 < l) (hc : l < c) :
    levelSet f n c ⊆ {ω | ENNReal.ofReal l < maxFnN f n ω} := by
  intro ω hω
  simp only [levelSet, Set.mem_setOf_eq] at hω
  rw [Real.coe_toNNReal _ (by linarith)] at hω
  obtain ⟨j, hj, hjle⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
    (fun k => absZ f k ω)
  rw [hjle] at hω
  have hj0 : j ≠ 0 := by
    rintro rfl
    simp [absZ] at hω; linarith
  have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
  rw [absZ_pos f hj1] at hω
  simp only [Set.mem_setOf_eq, maxFnN]
  have hjn : j ∈ Finset.Icc 1 n := by
    rw [Finset.mem_Icc]; rw [Finset.mem_range] at hj; omega
  calc ENNReal.ofReal l < ENNReal.ofReal |f j ω| := by
        rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]; linarith
    _ ≤ _ := le_iSup₂ (f := fun k (_ : k ∈ Finset.Icc 1 n) => ENNReal.ofReal |f k ω|) j hjn

lemma subset_iUnion_levelSet (f : ℕ → Ω → ℝ) (n : ℕ) {l : ℝ} (hl : 0 < l) :
    {ω | ENNReal.ofReal l < maxFnN f n ω} ⊆ ⋃ k : ℕ, levelSet f n (l + 1 / (k + 1)) := by
  intro ω hω
  simp only [Set.mem_setOf_eq, maxFnN] at hω
  rw [lt_iSup_iff] at hω
  obtain ⟨j, hj⟩ := hω
  rw [lt_iSup_iff] at hj
  obtain ⟨hjmem, hj⟩ := hj
  rw [Finset.mem_Icc] at hjmem
  have hpos : 0 < |f j ω| := by
    have : 0 < ENNReal.ofReal |f j ω| := lt_of_le_of_lt bot_le hj
    exact ENNReal.ofReal_pos.mp this
  rw [ENNReal.ofReal_lt_ofReal_iff hpos] at hj
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hj)
  simp only [Set.mem_iUnion]
  refine ⟨k, ?_⟩
  simp only [levelSet, Set.mem_setOf_eq]
  rw [Real.coe_toNNReal _ (by positivity)]
  have hle : absZ f j ω ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => absZ f k ω :=
    Finset.le_sup' (fun k => absZ f k ω) (Finset.mem_range.mpr (by omega))
  rw [absZ_pos f hjmem.1] at hle
  linarith

lemma levelSet_mono (f : ℕ → Ω → ℝ) (n : ℕ) {l : ℝ} (hl : 0 < l) :
    Monotone fun k : ℕ => levelSet f n (l + 1 / (k + 1)) := by
  intro a b hab ω hω
  simp only [levelSet, Set.mem_setOf_eq] at hω ⊢
  rw [Real.coe_toNNReal _ (by positivity)] at hω ⊢
  have : (1 : ℝ) / (b + 1) ≤ 1 / (a + 1) := by
    apply one_div_le_one_div_of_le (by positivity); exact_mod_cast Nat.succ_le_succ hab
  linarith

lemma measurableSet_levelSet [IsFiniteMeasure P]
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (n : ℕ) (c : ℝ) : MeasurableSet (levelSet f n c) := by
  have hG := absZ_submartingale hf
  exact measurableSet_le measurable_const (Finset.measurable_range_sup'' fun k _ =>
      (hG.stronglyMeasurable k).measurable.le (ℱ.le k))

lemma lpNormE_le_pNorm (P : Measure Ω) (p : ℝ) (f : ℕ → Ω → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    lpNormE P p (fun ω => ENNReal.ofReal |f n ω|) ≤ pNorm P p f :=
  le_iSup₂ (f := fun n (_ : n ∈ Set.Ici 1) => lpNormE P p (fun ω => ENNReal.ofReal |f n ω|)) n hn

theorem doob_1_1_core {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (n : ℕ) (hn : 1 ≤ n) (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal l * P {ω | ENNReal.ofReal l < maxFnN f n ω}
        ≤ ∫⁻ ω in {ω | ENNReal.ofReal l < maxFnN f n ω}, ENNReal.ofReal |f n ω| ∂P ∧
      ∫⁻ ω in {ω | ENNReal.ofReal l < maxFnN f n ω}, ENNReal.ofReal |f n ω| ∂P ≤ pNorm P 1 f := by
  have hG := absZ_submartingale hf
  set B := {ω | ENNReal.ofReal l < maxFnN f n ω} with hB
  constructor
  · have hBeq : B = ⋃ k : ℕ, levelSet f n (l + 1 / (k + 1)) := by
      apply Set.Subset.antisymm (subset_iUnion_levelSet f n hl)
      exact Set.iUnion_subset fun k => levelSet_subset f n hl (by
        have : (0:ℝ) < 1 / ((k:ℝ) + 1) := by positivity
        linarith)
    have hstep : ∀ k : ℕ, ENNReal.ofReal l * P (levelSet f n (l + 1 / (k + 1)))
        ≤ ∫⁻ ω in B, ENNReal.ofReal |f n ω| ∂P := by
      intro k
      set c : ℝ := l + 1 / (k + 1) with hc
      have hlc : l < c := by
        have : (0:ℝ) < 1 / ((k:ℝ) + 1) := by positivity
        linarith
      set ε : ℝ≥0 := c.toNNReal with hε
      have h1 := maximal_ineq hG (absZ_nonneg f) (ε := ε) n
      have hA : MeasurableSet (levelSet f n c) := measurableSet_levelSet hf n c
      have h2 : ENNReal.ofReal (∫ ω in levelSet f n c, absZ f n ω ∂P)
          = ∫⁻ ω in levelSet f n c, ENNReal.ofReal (absZ f n ω) ∂P :=
        ofReal_integral_eq_lintegral_ofReal (hG.integrable n).integrableOn
          (Eventually.of_forall (absZ_nonneg f n))
      have h1' : (ε : ℝ≥0∞) * P (levelSet f n c)
          ≤ ∫⁻ ω in levelSet f n c, ENNReal.ofReal (absZ f n ω) ∂P := by
        rw [← h2]; exact h1
      have hεl : ENNReal.ofReal l ≤ (ε : ℝ≥0∞) := by
        rw [hε, ENNReal.ofReal]; exact_mod_cast Real.toNNReal_le_toNNReal hlc.le
      calc ENNReal.ofReal l * P (levelSet f n c) ≤ (ε : ℝ≥0∞) * P (levelSet f n c) := by gcongr
        _ ≤ ∫⁻ ω in levelSet f n c, ENNReal.ofReal (absZ f n ω) ∂P := h1'
        _ ≤ ∫⁻ ω in B, ENNReal.ofReal (absZ f n ω) ∂P :=
            lintegral_mono_set (levelSet_subset f n hl hlc)
        _ = ∫⁻ ω in B, ENNReal.ofReal |f n ω| ∂P := by rw [absZ_pos f hn]
    have hPB : P B = ⨆ k : ℕ, P (levelSet f n (l + 1 / (k + 1))) := by
      rw [hBeq, (levelSet_mono f n hl).measure_iUnion]
    rw [hPB, ENNReal.mul_iSup]
    exact iSup_le hstep
  · calc ∫⁻ ω in B, ENNReal.ofReal |f n ω| ∂P ≤ ∫⁻ ω, ENNReal.ofReal |f n ω| ∂P :=
          setLIntegral_le_lintegral _ _
      _ = lpNormE P 1 (fun ω => ENNReal.ofReal |f n ω|) := by
          simp [lpNormE]
      _ ≤ pNorm P 1 f := lpNormE_le_pNorm P 1 f hn

end BurkholderDFI.SquareFnLp

open BurkholderDFI.SquareFnLp


theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (n : ℕ) (hn : 1 ≤ n) (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal l * P {ω | ENNReal.ofReal l < maxFnN f n ω}
        ≤ ∫⁻ ω in {ω | ENNReal.ofReal l < maxFnN f n ω}, ENNReal.ofReal |f n ω| ∂P ∧
      ∫⁻ ω in {ω | ENNReal.ofReal l < maxFnN f n ω}, ENNReal.ofReal |f n ω| ∂P ≤ pNorm P 1 f := by
  exact doob_1_1_core hf n hn l hl
