-- Prove2me | solution 1 for BurkholderDFI.BMO.tail_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:10:56.624137+00:00
-- url     : https://prove2.me/submissions/a57774e5-4f07-4dab-9159-75c3f4f92a8f

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
import Definitions.Def_BurkholderDFI_BMO_Condition



namespace BurkholderDFI.BMO

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

section Tail

open BurkholderDFI.SquareFnLp

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {ℱ : Filtration ℕ mΩ}
  {f : ℕ → Ω → ℝ}

lemma sqFnN_sq (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    sqFnN f n ω ^ 2 = ∑ k ∈ Finset.Icc 1 n, ENNReal.ofReal (dseq f k ω ^ 2) := by
  unfold sqFnN
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _),
    ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]

lemma Icc_sum_eq_range (g : ℕ → ℝ≥0∞) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, g k = ∑ k ∈ Finset.range n, g (k + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

lemma sqFn_sq_eq_tsum (f : ℕ → Ω → ℝ) (ω : Ω) :
    sqFn f ω ^ 2 = ∑' k : ℕ, ENNReal.ofReal (dseq f (k + 1) ω ^ 2) := by
  unfold sqFn
  rw [ENNReal.iSup_pow, ENNReal.tsum_eq_iSup_nat]
  congr 1
  ext n
  rw [sqFnN_sq, Icc_sum_eq_range]

lemma sqFn_sq_split (f : ℕ → Ω → ℝ) (ω : Ω) (m : ℕ) :
    sqFn f ω ^ 2 = sqFnN f m ω ^ 2 + ∑' j : ℕ, ENNReal.ofReal (dseq f (m + 1 + j) ω ^ 2) := by
  rw [sqFn_sq_eq_tsum, sqFnN_sq, Icc_sum_eq_range,
    ← Summable.sum_add_tsum_nat_add' (k := m) ENNReal.summable]
  congr 1
  apply tsum_congr
  intro j
  rw [show j + m + 1 = m + 1 + j by omega]

lemma measurable_f_filt (hf : Martingale f ℱ P) (n : ℕ) : Measurable[ℱ n] (f n) :=
  (hf.stronglyMeasurable n).measurable

lemma measurable_dseq_filt (hf : Martingale f ℱ P) {k n : ℕ} (hkn : k ≤ n) :
    Measurable[ℱ n] (dseq f k) := by
  by_cases h0 : k = 0
  · subst h0
    have : dseq f 0 = fun _ => (0:ℝ) := by ext ω; simp [dseq]
    rw [this]; exact measurable_const
  by_cases h1 : k = 1
  · subst h1
    have : dseq f 1 = f 1 := by ext ω; simp [dseq]
    rw [this]; exact (measurable_f_filt hf 1).mono (ℱ.mono hkn) le_rfl
  have : dseq f k = fun ω => f k ω - f (k - 1) ω := by ext ω; simp [dseq, h0, h1]
  rw [this]
  exact ((measurable_f_filt hf k).mono (ℱ.mono hkn) le_rfl).sub
    ((measurable_f_filt hf (k - 1)).mono (ℱ.mono (by omega)) le_rfl)

lemma measurable_sqFnN_filt (hf : Martingale f ℱ P) (n : ℕ) : Measurable[ℱ n] (sqFnN f n) := by
  unfold sqFnN
  exact (Finset.measurable_sum _ (fun k hk =>
    (measurable_dseq_filt hf (Finset.mem_Icc.mp hk).2).pow_const 2)).sqrt.ennreal_ofReal

lemma measurable_sqFnN (hf : Martingale f ℱ P) (n : ℕ) : Measurable (sqFnN f n) :=
  (measurable_sqFnN_filt hf n).mono (ℱ.le n) le_rfl

lemma measurable_sqFn (hf : Martingale f ℱ P) : Measurable (sqFn f) :=
  Measurable.iSup (fun n => measurable_sqFnN hf n)

lemma measurable_dseq (hf : Martingale f ℱ P) (k : ℕ) : Measurable (dseq f k) :=
  (measurable_dseq_filt hf le_rfl).mono (ℱ.le k) le_rfl

lemma measurable_tailSum (hf : Martingale f ℱ P) (n : ℕ) :
    Measurable (fun ω => ∑' j : ℕ, ENNReal.ofReal (dseq f (n + j) ω ^ 2)) :=
  Measurable.ennreal_tsum fun j => ((measurable_dseq hf (n + j)).pow_const 2).ennreal_ofReal

/-- first hitting event: `S_n² > a` and `S_k² ≤ a` for all `k < n`. -/
def hitSet (f : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) : Set Ω :=
  {ω | ENNReal.ofReal a < sqFnN f n ω ^ 2 ∧ ∀ k < n, sqFnN f k ω ^ 2 ≤ ENNReal.ofReal a}

lemma measurableSet_hitSet (hf : Martingale f ℱ P) (a : ℝ) (n : ℕ) :
    MeasurableSet[ℱ n] (hitSet f a n) := by
  have hT : ∀ k ≤ n, Measurable[ℱ n] (fun ω => sqFnN f k ω ^ 2) := fun k hk =>
    ((measurable_sqFnN_filt hf k).mono (ℱ.mono hk) le_rfl).pow_const 2
  unfold hitSet
  rw [Set.setOf_and, Set.setOf_forall]
  refine MeasurableSet.inter (measurableSet_lt measurable_const (hT n le_rfl))
    (MeasurableSet.iInter fun k => ?_)
  by_cases hk : k < n
  · simp only [hk, true_implies]
    exact measurableSet_le (hT k hk.le) measurable_const
  · simp only [hk, false_implies, Set.setOf_true]
    exact MeasurableSet.univ

lemma hitSet_disjoint (f : ℕ → Ω → ℝ) (a : ℝ) : Pairwise (fun m n => Disjoint (hitSet f a m) (hitSet f a n)) := by
  intro m n hmn
  rw [Set.disjoint_left]
  intro ω hm hn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact absurd (hn.2 m h) (not_le.mpr hm.1)
  · exact absurd (hm.2 n h) (not_le.mpr hn.1)

lemma iUnion_hitSet (f : ℕ → Ω → ℝ) (a : ℝ) :
    (⋃ n, hitSet f a n) = {ω | ENNReal.ofReal a < sqFn f ω ^ 2} := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, hitSet]
  constructor
  · rintro ⟨n, hn, -⟩
    refine lt_of_lt_of_le hn (pow_le_pow_left' ?_ 2)
    exact le_iSup (fun n => sqFnN f n ω) n
  · intro h
    have hex : ∃ n, ENNReal.ofReal a < sqFnN f n ω ^ 2 := by
      unfold sqFn at h
      rw [ENNReal.iSup_pow] at h
      exact lt_iSup_iff.mp h
    classical
    refine ⟨Nat.find hex, Nat.find_spec hex, fun k hk => ?_⟩
    exact not_lt.mp (Nat.find_min hex hk)

lemma hitSet_zero (f : ℕ → Ω → ℝ) (a : ℝ) (ha : 0 < a) : hitSet f a 0 = ∅ := by
  ext ω
  simp only [hitSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro h
  exfalso
  have : sqFnN f 0 ω = 0 := by simp [sqFnN]
  rw [this] at h
  simp at h

lemma volume_set_le (a : ℝ) (ha : 0 ≤ a) (c : ℝ≥0∞) :
    volume ({x : ℝ | ENNReal.ofReal x < ENNReal.ofReal a + c} ∩ Set.Ioi a) ≤ c := by
  by_cases hc : c = ⊤
  · rw [hc]; exact le_top
  · calc volume ({x : ℝ | ENNReal.ofReal x < ENNReal.ofReal a + c} ∩ Set.Ioi a)
        ≤ volume (Set.Ioo a (a + c.toReal)) := by
          apply measure_mono
          rintro x ⟨hx1, hx2⟩
          refine ⟨hx2, ?_⟩
          simp only [Set.mem_ofPred_eq] at hx1
          have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt ha hx2)
          rw [← ENNReal.ofReal_toReal hc, ← ENNReal.ofReal_add ha ENNReal.toReal_nonneg,
            ENNReal.ofReal_lt_ofReal_iff_of_nonneg hx0] at hx1
          exact hx1
      _ = c := by rw [Real.volume_Ioo, add_sub_cancel_left, ENNReal.ofReal_toReal hc]

lemma pointwise_bound (f : ℕ → Ω → ℝ) (a : ℝ) (ha : 0 < a) (ω : Ω) :
    volume ({x : ℝ | ENNReal.ofReal x < sqFn f ω ^ 2} ∩ Set.Ioi a)
      ≤ ∑' n : ℕ, (hitSet f a n).indicator
          (fun ω => ∑' j : ℕ, ENNReal.ofReal (dseq f (n + j) ω ^ 2)) ω := by
  by_cases hω : ω ∈ ⋃ n, hitSet f a n
  · rw [Set.mem_iUnion] at hω
    obtain ⟨n, hn⟩ := hω
    refine le_trans ?_ (ENNReal.le_tsum n)
    rw [Set.indicator_of_mem hn]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
      rcases n with _ | m
      · exfalso
        have := hn
        rw [hitSet_zero f a ha] at this
        exact this
      · exact ⟨m, rfl⟩
    have hle : sqFn f ω ^ 2
        ≤ ENNReal.ofReal a + ∑' j, ENNReal.ofReal (dseq f (m + 1 + j) ω ^ 2) := by
      rw [sqFn_sq_split f ω m]
      gcongr
      exact hn.2 m (Nat.lt_succ_self m)
    calc volume ({x : ℝ | ENNReal.ofReal x < sqFn f ω ^ 2} ∩ Set.Ioi a)
        ≤ volume ({x : ℝ | ENNReal.ofReal x
            < ENNReal.ofReal a + ∑' j, ENNReal.ofReal (dseq f (m + 1 + j) ω ^ 2)} ∩ Set.Ioi a) := by
          apply measure_mono
          rintro x ⟨hx1, hx2⟩
          exact ⟨lt_of_lt_of_le hx1 hle, hx2⟩
      _ ≤ _ := volume_set_le a ha.le _
  · rw [iUnion_hitSet] at hω
    simp only [Set.mem_ofPred_eq, not_lt] at hω
    have : {x : ℝ | ENNReal.ofReal x < sqFn f ω ^ 2} ∩ Set.Ioi a = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioi, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro hx hax
      exact absurd (lt_of_lt_of_le hx hω) (not_lt.mpr (ENNReal.ofReal_le_ofReal hax.le))
    rw [this, measure_empty]
    exact zero_le

theorem tail_integral_bound_core [IsProbabilityMeasure P]
    (hf : Martingale f ℱ P) (h191 : BMOCondition ℱ P f) :
    ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < sqFn f ω ^ 2}
        ≤ P {ω | ENNReal.ofReal a < sqFn f ω ^ 2} := by
  intro a ha
  have hT : Measurable (fun ω => sqFn f ω ^ 2) := (measurable_sqFn hf).pow_const 2
  set R : ℕ → Ω → ℝ≥0∞ := fun n ω => ∑' j : ℕ, ENNReal.ofReal (dseq f (n + j) ω ^ 2) with hR
  have hRm : ∀ n, Measurable (R n) := fun n => measurable_tailSum hf n
  have hE : ∀ n, MeasurableSet (hitSet f a n) := fun n => ℱ.le n _ (measurableSet_hitSet hf a n)
  -- Step 1: Tonelli
  set S : Set (ℝ × Ω) := {p | ENNReal.ofReal p.1 < sqFn f p.2 ^ 2} with hSdef
  have hS : MeasurableSet S :=
    measurableSet_lt (measurable_fst.ennreal_ofReal) (hT.comp measurable_snd)
  have hswap := lintegral_lintegral_swap (μ := volume.restrict (Set.Ioi a)) (ν := P)
    (f := fun x ω => S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω))
    (measurable_const.indicator hS).aemeasurable
  have h1 : ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < sqFn f ω ^ 2}
      = ∫⁻ ω, volume ({x : ℝ | ENNReal.ofReal x < sqFn f ω ^ 2} ∩ Set.Ioi a) ∂P := by
    have hl : ∀ x : ℝ, ∫⁻ ω, S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω) ∂P
        = P {ω | ENNReal.ofReal x < sqFn f ω ^ 2} := by
      intro x
      have : (fun ω => S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω))
          = {ω | ENNReal.ofReal x < sqFn f ω ^ 2}.indicator 1 := by
        ext ω
        simp [S, Set.indicator_apply]
      rw [this, lintegral_indicator_one (measurableSet_lt measurable_const hT)]
    have hr : ∀ ω : Ω, ∫⁻ x in Set.Ioi a, S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω)
        = volume ({x : ℝ | ENNReal.ofReal x < sqFn f ω ^ 2} ∩ Set.Ioi a) := by
      intro ω
      have : (fun x => S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω))
          = {x : ℝ | ENNReal.ofReal x < sqFn f ω ^ 2}.indicator 1 := by
        ext x
        simp [S, Set.indicator_apply]
      rw [this, lintegral_indicator_one (measurableSet_lt ENNReal.measurable_ofReal measurable_const),
        Measure.restrict_apply (measurableSet_lt ENNReal.measurable_ofReal measurable_const)]
    simp_rw [hl, hr] at hswap
    exact hswap
  rw [h1]
  calc ∫⁻ ω, volume ({x : ℝ | ENNReal.ofReal x < sqFn f ω ^ 2} ∩ Set.Ioi a) ∂P
      ≤ ∫⁻ ω, ∑' n : ℕ, (hitSet f a n).indicator (R n) ω ∂P :=
        lintegral_mono (fun ω => pointwise_bound f a ha ω)
    _ = ∑' n : ℕ, ∫⁻ ω, (hitSet f a n).indicator (R n) ω ∂P :=
        lintegral_tsum (fun n => ((hRm n).indicator (hE n)).aemeasurable)
    _ = ∑' n : ℕ, ∫⁻ ω in hitSet f a n, R n ω ∂P := by
        congr 1; ext n; exact lintegral_indicator (hE n) _
    _ = ∑' n : ℕ, ∫⁻ ω in hitSet f a n, condLExp (ℱ n) P (R n) ω ∂P := by
        congr 1; ext n
        exact (setLIntegral_condLExp (ℱ.le n) P (R n) (measurableSet_hitSet hf a n)).symm
    _ ≤ ∑' n : ℕ, ∫⁻ _ in hitSet f a n, (1 : ℝ≥0∞) ∂P := by
        apply ENNReal.tsum_le_tsum
        intro n
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn
          rw [hitSet_zero f a ha, Measure.restrict_empty, lintegral_zero_measure]
          exact zero_le
        · apply lintegral_mono_ae
          apply ae_restrict_of_ae
          exact h191 n hn
    _ = ∑' n : ℕ, P (hitSet f a n) := by
        congr 1; ext n; exact setLIntegral_one _
    _ = P (⋃ n, hitSet f a n) := (measure_iUnion (hitSet_disjoint f a) hE).symm
    _ = P {ω | ENNReal.ofReal a < sqFn f ω ^ 2} := by rw [iUnion_hitSet]

end Tail

end BurkholderDFI.BMO

open BurkholderDFI.BMO
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (h191 : BMOCondition ℱ P f) :
    ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < BurkholderDFI.SquareFnLp.sqFn f ω ^ 2}
        ≤ P {ω | ENNReal.ofReal a < BurkholderDFI.SquareFnLp.sqFn f ω ^ 2} := by
  exact tail_integral_bound_core hf h191
