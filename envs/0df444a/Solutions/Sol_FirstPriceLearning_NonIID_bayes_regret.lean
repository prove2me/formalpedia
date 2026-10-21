-- Prove2me | solution 1 for FirstPriceLearning.NonIID.bayes_regret
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:59:18.911771+00:00
-- url     : https://prove2.me/submissions/463c6b26-aa4b-43ba-895e-69d441c40070

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_Auction
import Definitions.Def_FirstPriceLearning_NonIID_ThresholdModel
import Definitions.Def_FirstPriceLearning_NonIID_HardInstance

set_option autoImplicit false
open MeasureTheory FirstPriceLearning.NonIID

namespace FNI

noncomputable def ue {T : ℕ} (u : Fin T → ℝ) (n : ℕ) : ℝ := if h : n < T then u ⟨n, h⟩ else 0

lemma ue_abs {T : ℕ} (u : Fin T → ℝ) (hu : ∀ s, u s = 1 ∨ u s = -1) (n : ℕ) : |ue u n| ≤ 1 := by
  unfold ue
  split_ifs with h
  · rcases hu ⟨n, h⟩ with h | h <;> simp [h]
  · simp

lemma ue_lt {T : ℕ} (u : Fin T → ℝ) (t : Fin T) : ue u t.val = u t := by
  unfold ue
  simp [t.2]

lemma valueAux_eq {T : ℕ} (u : Fin T → ℝ) (n : ℕ) :
    valueAux u n = 1 / 2 + ∑ s ∈ Finset.range n, ue u s / 2 ^ (s + 3) := by
  induction n with
  | zero => simp [valueAux]
  | succ n ih =>
    rw [valueAux, ih, Finset.sum_range_succ]
    unfold ue
    ring

lemma valueSeq_eq {T : ℕ} (u : Fin T → ℝ) (t : Fin T) :
    valueSeq u t = 1 / 2 + ∑ s ∈ Finset.range t.val, ue u s / 2 ^ (s + 3) := by
  unfold valueSeq
  exact valueAux_eq u t.val

lemma fval_eq {T : ℕ} (u : Fin T → ℝ) :
    fval u = 1 / 2 + ∑ s ∈ Finset.range T, ue u s / 2 ^ (s + 3) := by
  unfold fval
  rw [← Fin.sum_univ_eq_sum_range (fun s => ue u s / 2 ^ (s + 3)) T, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [ue_lt]
  rw [pow_add 2 (t.val) 3, pow_add 2 (t.val) 1]
  field_simp
  ring

lemma tail_bound (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) (a N : ℕ) (h : a ≤ N) :
    |∑ s ∈ Finset.Ico a N, c s / 2 ^ (s + 3)| ≤ 1 / 2 ^ (a + 2) - 1 / 2 ^ (N + 2) := by
  induction N, h using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN]
    have h1 : |c N / 2 ^ (N + 3)| ≤ 1 / 2 ^ (N + 3) := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (N + 3))]
      exact div_le_div_of_nonneg_right (hc N) (by positivity)
    have h2 : (1 : ℝ) / 2 ^ (N + 2) = 2 * (1 / 2 ^ (N + 3)) := by
      rw [pow_succ 2 (N + 2)]
      field_simp
    have h3 : (1 : ℝ) / 2 ^ (N + 1 + 2) = 1 / 2 ^ (N + 3) := by
      rfl
    calc _ ≤ |∑ s ∈ Finset.Ico a N, c s / 2 ^ (s + 3)| + |c N / 2 ^ (N + 3)| := abs_add_le _ _
      _ ≤ _ := by rw [h3]; rw [h2] at ih; linarith

lemma tail_lt (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) (a N : ℕ) (h : a ≤ N) :
    |∑ s ∈ Finset.Ico a N, c s / 2 ^ (s + 3)| < 1 / 2 ^ (a + 2) := by
  have := tail_bound c hc a N h
  have : (0 : ℝ) < 1 / 2 ^ (N + 2) := by positivity
  linarith

lemma diff_decomp {T : ℕ} (u : Fin T → ℝ) (t : Fin T) :
    fval u - valueSeq u t = ue u t.val / 2 ^ (t.val + 3) +
      ∑ s ∈ Finset.Ico (t.val + 1) T, ue u s / 2 ^ (s + 3) := by
  rw [fval_eq, valueSeq_eq, ← Finset.sum_range_add_sum_Ico _ (le_of_lt t.2),
    Finset.sum_eq_sum_Ico_succ_bot t.2]
  ring

lemma diff_tail {T : ℕ} (u : Fin T → ℝ) (hu : ∀ s, u s = 1 ∨ u s = -1) (t : Fin T) :
    |∑ s ∈ Finset.Ico (t.val + 1) T, ue u s / 2 ^ (s + 3)| < 1 / 2 ^ (t.val + 3) := by
  have := tail_lt (ue u) (ue_abs u hu) (t.val + 1) T t.2
  simpa using this

lemma f_gt_v {T : ℕ} (u : Fin T → ℝ) (hu : ∀ s, u s = 1 ∨ u s = -1) (t : Fin T) (h : u t = 1) :
    valueSeq u t < fval u := by
  have h1 := diff_decomp u t
  have h2 := diff_tail u hu t
  rw [ue_lt, h] at h1
  have h3 := (abs_lt.mp h2).1
  have h4 : (0 : ℝ) < 1 / 2 ^ (t.val + 3) := by positivity
  linarith

lemma f_lt_v {T : ℕ} (u : Fin T → ℝ) (hu : ∀ s, u s = 1 ∨ u s = -1) (t : Fin T) (h : u t = -1) :
    fval u < valueSeq u t := by
  have h1 := diff_decomp u t
  have h2 := diff_tail u hu t
  rw [ue_lt, h, neg_div] at h1
  have h3 := (abs_lt.mp h2).2
  linarith

lemma valueSeq_mem {T : ℕ} (u : Fin T → ℝ) (hu : ∀ s, u s = 1 ∨ u s = -1) (t : Fin T) :
    valueSeq u t ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) := by
  rw [valueSeq_eq]
  have := tail_bound (ue u) (ue_abs u hu) 0 t.val (Nat.zero_le _)
  rw [← Finset.range_eq_Ico] at this
  have e : (1 : ℝ) / 2 ^ (0 + 2) = 1 / 4 := by norm_num
  rw [e] at this
  have h5 : (0 : ℝ) < 1 / 2 ^ (t.val + 2) := by positivity
  obtain ⟨h6, h7⟩ := abs_le.mp this
  constructor <;> linarith

lemma fval_mem {T : ℕ} (u : Fin T → ℝ) (hu : ∀ s, u s = 1 ∨ u s = -1) :
    fval u ∈ Set.Icc (0 : ℝ) 1 := by
  rw [fval_eq]
  have := tail_bound (ue u) (ue_abs u hu) 0 T (Nat.zero_le _)
  rw [← Finset.range_eq_Ico] at this
  have e : (1 : ℝ) / 2 ^ (0 + 2) = 1 / 4 := by norm_num
  rw [e] at this
  have h5 : (0 : ℝ) < 1 / 2 ^ (T + 2) := by positivity
  obtain ⟨h6, h7⟩ := abs_le.mp this
  constructor <;> linarith

lemma valueSeq_congr {T : ℕ} (u u' : Fin T → ℝ) (s : Fin T)
    (h : ∀ r : Fin T, r < s → u r = u' r) : valueSeq u s = valueSeq u' s := by
  rw [valueSeq_eq, valueSeq_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_range] at hr
  have hrT : r < T := lt_trans hr s.2
  have := h ⟨r, hrT⟩ (by exact hr)
  unfold ue
  simp [hrT, this]

lemma prefix_sum {T : ℕ} (u : Fin T → ℝ) (t : Fin T) :
    (1 / 2 + 1 / 4 * ∑ s ∈ Finset.univ.filter (fun s : Fin T => s < t),
            u s / 2 ^ (s.val + 1)) = valueSeq u t := by
  rw [valueSeq_eq, Finset.sum_filter]
  have e1 : ∑ s : Fin T, (if s < t then u s / 2 ^ (s.val + 1) else 0) =
      ∑ s ∈ Finset.range T, (if s < t.val then ue u s / 2 ^ (s + 1) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun s => if s < t.val then ue u s / 2 ^ (s + 1) else 0) T]
    apply Finset.sum_congr rfl
    intro s _
    rw [ue_lt]
    rfl
  rw [e1, ← Finset.sum_range_add_sum_Ico _ (le_of_lt t.2)]
  have e2 : ∑ s ∈ Finset.Ico t.val T, (if s < t.val then ue u s / 2 ^ (s + 1) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    rw [Finset.mem_Ico] at hs
    simp [not_lt.mpr hs.1]
  rw [e2, add_zero, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mem_range] at hs
  rw [if_pos hs, pow_add 2 s 3, pow_add 2 s 1]
  field_simp
  ring

end FNI

namespace FNI

open FirstPriceLearning.Stochastic

lemma cdf_dirac (a x : ℝ) : cdf (Measure.dirac a) x = if a ≤ x then 1 else 0 := by
  unfold cdf
  rw [Measure.dirac_apply' _ measurableSet_Iic]
  by_cases h : a ≤ x <;> simp [Set.indicator, h]

lemma expReward_dirac (a v b : ℝ) :
    expReward (Measure.dirac a) v b = if a ≤ b then v - b else 0 := by
  unfold expReward
  rw [cdf_dirac]
  split_ifs <;> simp

lemma oracle_dirac (a v : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (hv : a ≤ v) :
    oracle (Measure.dirac a) v = v - a := by
  unfold oracle
  apply le_antisymm
  · apply ciSup_le
    intro b
    rw [expReward_dirac]
    have := b.2.1
    split_ifs with h <;> linarith
  · have hbdd : BddAbove (Set.range fun b : Set.Icc (0 : ℝ) 1 => expReward (Measure.dirac a) v b) := by
      refine ⟨|v| + 1, ?_⟩
      rintro _ ⟨b, rfl⟩
      beta_reduce
      rw [expReward_dirac]
      have := b.2.1
      have := le_abs_self v
      have := abs_nonneg v
      split_ifs <;> linarith
    refine le_trans ?_ (le_ciSup hbdd ⟨a, ha⟩)
    rw [expReward_dirac, if_pos le_rfl]

lemma law_eq_dirac {T : ℕ} (u : Fin T → ℝ) (t : Fin T) :
    hobLaw (Measure.dirac 0) (Measure.dirac (1 / 8 : ℝ)) (fval u) (valueSeq u t) =
      Measure.dirac (1 / 8 * (if fval u ≤ valueSeq u t then 1 else 0) : ℝ) := by
  unfold hobLaw
  by_cases h : fval u ≤ valueSeq u t
  · rw [if_neg (not_lt.mpr h), if_pos h]; norm_num
  · rw [if_pos (not_le.mp h), if_neg h]; norm_num

lemma m_mem {T : ℕ} (u : Fin T → ℝ) (t : Fin T) :
    (1 / 8 * (if fval u ≤ valueSeq u t then 1 else 0) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  split_ifs <;> constructor <;> norm_num

end FNI

namespace FNI

open FirstPriceLearning.Stochastic

noncomputable def uu {T : ℕ} (σ : Fin T → Bool) : Fin T → ℝ := fun t => pm (σ t)

noncomputable def mseq {T : ℕ} (σ : Fin T → Bool) (t : Fin T) : ℝ := if σ t then 0 else 1 / 8

lemma uu_pm {T : ℕ} (σ : Fin T → Bool) : ∀ s, uu σ s = 1 ∨ uu σ s = -1 := by
  intro s
  unfold uu pm
  split_ifs <;> simp

lemma law_mseq {T : ℕ} (σ : Fin T → Bool) (t : Fin T) :
    hobLaw (Measure.dirac 0) (Measure.dirac (1 / 8 : ℝ)) (fval (uu σ)) (valueSeq (uu σ) t) =
      Measure.dirac (mseq σ t) := by
  unfold hobLaw
  cases hσ : σ t
  · have h : uu σ t = -1 := by simp [uu, pm, hσ]
    have := f_lt_v (uu σ) (uu_pm σ) t h
    rw [if_neg (not_lt.mpr this.le)]
    simp [mseq, hσ]
  · have h : uu σ t = 1 := by simp [uu, pm, hσ]
    have := f_gt_v (uu σ) (uu_pm σ) t h
    rw [if_pos this]
    simp [mseq, hσ]

lemma pi_dirac_eq {T : ℕ} (x : Fin T → ℝ) :
    Measure.pi (fun t => Measure.dirac (x t)) = Measure.dirac x := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  by_cases h : ∀ i, x i ∈ s i
  · have h' : x ∈ Set.pi Set.univ s := fun i _ => h i
    rw [Set.indicator_of_mem h']
    simp [Measure.dirac_apply' _ (hs _), Set.indicator_of_mem (h _)]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have h' : x ∉ Set.pi Set.univ s := fun hh => hi (hh i (Set.mem_univ i))
    rw [Set.indicator_of_notMem h']
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [Measure.dirac_apply' _ (hs i), Set.indicator_of_notMem hi]

noncomputable def gfun {T : ℕ} (π : FullInfoPolicy T) (σ : Fin T → Bool) (t : Fin T) (ω : π.U) : ℝ :=
  payoff (valueSeq (uu σ) t) (π.bidAt (valueSeq (uu σ)) t ω (mseq σ)) (mseq σ t)

lemma integral_eq {T : ℕ} (π : FullInfoPolicy T) (σ : Fin T → Bool) (t : Fin T) :
    ∫ p : π.U × (Fin T → ℝ), payoff (valueSeq (uu σ) t) (π.bidAt (valueSeq (uu σ)) t p.1 p.2) (p.2 t)
      ∂(π.μU.prod (hobSeqLaw (Measure.dirac 0) (Measure.dirac (1 / 8 : ℝ)) (fval (uu σ)) (valueSeq (uu σ))))
      = ∫ ω, gfun π σ t ω ∂π.μU := by
  have h : hobSeqLaw (Measure.dirac 0) (Measure.dirac (1 / 8 : ℝ)) (fval (uu σ)) (valueSeq (uu σ)) =
      Measure.dirac (mseq σ) := by
    unfold hobSeqLaw
    simp_rw [law_mseq]
    exact pi_dirac_eq _
  rw [h, Measure.prod_dirac, (measurableEmbedding_prod_mk_right (mseq σ)).integral_map]
  rfl

lemma oracle_eq {T : ℕ} (σ : Fin T → Bool) (t : Fin T) :
    oracle (hobLaw (Measure.dirac 0) (Measure.dirac (1 / 8 : ℝ)) (fval (uu σ)) (valueSeq (uu σ) t))
      (valueSeq (uu σ) t) = valueSeq (uu σ) t - mseq σ t := by
  rw [law_mseq]
  have hv := (valueSeq_mem (uu σ) (uu_pm σ) t).1
  have hm : mseq σ t ∈ Set.Icc (0 : ℝ) 1 := by
    unfold mseq; split_ifs <;> constructor <;> norm_num
  apply oracle_dirac _ _ hm
  unfold mseq; split_ifs <;> linarith

lemma gfun_meas {T : ℕ} (π : FullInfoPolicy T) (σ : Fin T → Bool) (t : Fin T) :
    Measurable (gfun π σ t) := by
  unfold gfun payoff
  have hb : Measurable (fun ω : π.U => π.bidAt (valueSeq (uu σ)) t ω (mseq σ)) :=
    (π.measurable_bid t).comp (measurable_id.prodMk (measurable_const.prodMk measurable_const))
  exact (measurable_const.sub hb).mul
    (Measurable.ite (measurableSet_le measurable_const hb) measurable_const measurable_const)

lemma gfun_abs {T : ℕ} (π : FullInfoPolicy T) (σ : Fin T → Bool) (t : Fin T) (ω : π.U) :
    |gfun π σ t ω| ≤ 1 := by
  unfold gfun payoff
  have hv := valueSeq_mem (uu σ) (uu_pm σ) t
  have hb := π.bid_mem t ω (fun s => valueSeq (uu σ) ⟨s.val, by omega⟩) (fun s => mseq σ ⟨s.val, by omega⟩)
  have hb' : π.bidAt (valueSeq (uu σ)) t ω (mseq σ) ∈ Set.Icc (0 : ℝ) 1 := hb
  obtain ⟨hb1, hb2⟩ := hb'
  obtain ⟨hv1, hv2⟩ := hv
  split_ifs
  · rw [mul_one, abs_le]; constructor <;> linarith
  · simp

lemma gfun_int {T : ℕ} (π : FullInfoPolicy T) (σ : Fin T → Bool) (t : Fin T) :
    Integrable (gfun π σ t) π.μU :=
  Integrable.of_bound (gfun_meas π σ t).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun ω => by simpa using gfun_abs π σ t ω))

lemma pair_bound (v b : ℝ) (hv : 1 / 4 ≤ v) (hb : 0 ≤ b) :
    payoff v b 0 + payoff v b (1 / 8) ≤ 2 * (v - 1 / 8) := by
  unfold payoff
  rw [if_pos hb]
  by_cases h : (1 / 8 : ℝ) ≤ b
  · rw [if_pos h]; linarith
  · rw [if_neg h]; linarith

noncomputable def flipEquiv {T : ℕ} (t : Fin T) : Equiv.Perm (Fin T → Bool) :=
  Function.Involutive.toPerm (fun σ => Function.update σ t (!σ t)) (by
    intro σ
    funext r
    by_cases h : r = t
    · subst h; simp
    · simp [Function.update_of_ne h])

lemma flip_apply_self {T : ℕ} (t : Fin T) (σ : Fin T → Bool) : flipEquiv t σ t = !σ t := by
  show Function.update σ t (!σ t) t = !σ t
  simp

lemma flip_apply_ne {T : ℕ} (t : Fin T) (σ : Fin T → Bool) (r : Fin T) (h : r ≠ t) :
    flipEquiv t σ r = σ r := by
  show Function.update σ t (!σ t) r = σ r
  simp [Function.update_of_ne h]

lemma value_flip {T : ℕ} (t s : Fin T) (hs : s ≤ t) (σ : Fin T → Bool) :
    valueSeq (uu (flipEquiv t σ)) s = valueSeq (uu σ) s := by
  apply valueSeq_congr
  intro r hr
  have : r ≠ t := fun h => by subst h; exact absurd (lt_of_lt_of_le hr hs) (lt_irrefl _)
  simp [uu, flip_apply_ne t σ r this]

lemma mseq_flip {T : ℕ} (t s : Fin T) (hs : s < t) (σ : Fin T → Bool) :
    mseq (flipEquiv t σ) s = mseq σ s := by
  have : s ≠ t := ne_of_lt hs
  simp [mseq, flip_apply_ne t σ s this]

lemma bid_flip {T : ℕ} (π : FullInfoPolicy T) (t : Fin T) (σ : Fin T → Bool) (ω : π.U) :
    π.bidAt (valueSeq (uu (flipEquiv t σ))) t ω (mseq (flipEquiv t σ)) =
      π.bidAt (valueSeq (uu σ)) t ω (mseq σ) := by
  unfold FullInfoPolicy.bidAt
  congr 1
  · funext s
    exact value_flip t _ (by simp [Fin.le_def]; omega) σ
  · funext s
    exact mseq_flip t _ (by simp [Fin.lt_def]) σ

lemma pair_g {T : ℕ} (π : FullInfoPolicy T) (t : Fin T) (σ : Fin T → Bool) (ω : π.U) :
    gfun π σ t ω + gfun π (flipEquiv t σ) t ω ≤ 2 * (valueSeq (uu σ) t - 1 / 8) := by
  have hv := (valueSeq_mem (uu σ) (uu_pm σ) t).1
  have hb := π.bid_mem t ω (fun s => valueSeq (uu σ) ⟨s.val, by omega⟩) (fun s => mseq σ ⟨s.val, by omega⟩)
  have hb' : π.bidAt (valueSeq (uu σ)) t ω (mseq σ) ∈ Set.Icc (0 : ℝ) 1 := hb
  unfold gfun
  rw [bid_flip, value_flip t t le_rfl]
  have hm : mseq (flipEquiv t σ) t = if σ t then 1 / 8 else 0 := by
    cases hσ : σ t <;> simp [mseq, flip_apply_self, hσ]
  rw [hm]
  unfold mseq
  cases hσ : σ t
  · simp only [Bool.false_eq_true, if_false]
    rw [add_comm]
    exact pair_bound _ _ hv hb'.1
  · simp only [if_true]
    exact pair_bound _ _ hv hb'.1

lemma sum_pair_le {α : Type*} [Fintype α] (e : Equiv.Perm α) (g h : α → ℝ)
    (H : ∀ x, g x + g (e x) ≤ h x + h (e x)) : ∑ x, g x ≤ ∑ x, h x := by
  have h1 : ∑ x, (g x + g (e x)) ≤ ∑ x, (h x + h (e x)) := Finset.sum_le_sum (fun x _ => H x)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Equiv.sum_comp e g, Equiv.sum_comp e h] at h1
  linarith

lemma sum_pair_eq {α : Type*} [Fintype α] (e : Equiv.Perm α) (g : α → ℝ) (c : ℝ)
    (H : ∀ x, g x + g (e x) = c) : 2 * ∑ x, g x = Fintype.card α * c := by
  have h1 : ∑ x, (g x + g (e x)) = ∑ x, c := Finset.sum_congr rfl (fun x _ => H x)
  rw [Finset.sum_add_distrib, Equiv.sum_comp e g] at h1
  simp at h1
  linarith

lemma sum_mseq {T : ℕ} (t : Fin T) : ∑ σ : Fin T → Bool, mseq σ t = 2 ^ T / 16 := by
  have := sum_pair_eq (flipEquiv t) (fun σ => mseq σ t) (1 / 8) (by
    intro σ
    simp only [mseq, flip_apply_self]
    cases σ t <;> simp)
  simp at this
  linarith

lemma sum_g_le {T : ℕ} (π : FullInfoPolicy T) (t : Fin T) (ω : π.U) :
    ∑ σ : Fin T → Bool, gfun π σ t ω ≤ ∑ σ : Fin T → Bool, (valueSeq (uu σ) t - 1 / 8) := by
  apply sum_pair_le (flipEquiv t) (fun σ => gfun π σ t ω) (fun σ => valueSeq (uu σ) t - 1 / 8)
  intro σ
  have := pair_g π t σ ω
  rw [value_flip t t le_rfl]
  linarith

theorem bayes_main {T : ℕ} (π : FullInfoPolicy T) :
    (T : ℝ) / 16 ≤
      (1 / 2 ^ T : ℝ) * ∑ σ : Fin T → Bool,
        expectedRegret π (Measure.dirac 0) (Measure.dirac (1 / 8))
          (fval (fun t => pm (σ t))) (valueSeq (fun t => pm (σ t))) := by
  have hreg : ∀ σ : Fin T → Bool,
      expectedRegret π (Measure.dirac 0) (Measure.dirac (1 / 8))
          (fval (fun t => pm (σ t))) (valueSeq (fun t => pm (σ t))) =
        ∑ t : Fin T, ((valueSeq (uu σ) t - mseq σ t) - ∫ ω, gfun π σ t ω ∂π.μU) := by
    intro σ
    unfold expectedRegret
    apply Finset.sum_congr rfl
    intro t _
    rw [← integral_eq, ← oracle_eq σ t]
    rfl
  simp_rw [hreg]
  rw [Finset.sum_comm]
  have hper : ∀ t : Fin T, (2 : ℝ) ^ T / 16 ≤
      ∑ σ : Fin T → Bool, ((valueSeq (uu σ) t - mseq σ t) - ∫ ω, gfun π σ t ω ∂π.μU) := by
    intro t
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← integral_finset_sum _ (fun σ _ => gfun_int π σ t)]
    have h1 : ∫ ω, ∑ σ : Fin T → Bool, gfun π σ t ω ∂π.μU ≤
        ∑ σ : Fin T → Bool, (valueSeq (uu σ) t - 1 / 8) := by
      have : ∫ ω, ∑ σ : Fin T → Bool, gfun π σ t ω ∂π.μU ≤
          ∫ _ω, ∑ σ : Fin T → Bool, (valueSeq (uu σ) t - 1 / 8) ∂π.μU :=
        integral_mono (integrable_finset_sum _ (fun σ _ => gfun_int π σ t)) (integrable_const _)
          (fun ω => sum_g_le π t ω)
      simpa using this
    have h2 : ∑ σ : Fin T → Bool, (valueSeq (uu σ) t - 1 / 8) =
        ∑ σ : Fin T → Bool, valueSeq (uu σ) t - 2 ^ T / 8 := by
      rw [Finset.sum_sub_distrib]; simp
      ring
    rw [h2] at h1
    have h3 : (2 : ℝ) ^ T / 16 = 2 ^ T / 8 - 2 ^ T / 16 := by ring
    rw [sum_mseq t]
    linarith
  have hsum : (T : ℝ) * (2 ^ T / 16) ≤ ∑ t : Fin T, ∑ σ : Fin T → Bool,
      ((valueSeq (uu σ) t - mseq σ t) - ∫ ω, gfun π σ t ω ∂π.μU) := by
    calc (T : ℝ) * (2 ^ T / 16) = ∑ _t : Fin T, (2 : ℝ) ^ T / 16 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun t _ => hper t)
  have hpos : (0 : ℝ) < 2 ^ T := by positivity
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
  linarith

end FNI

theorem solution (T : ℕ) (π : FullInfoPolicy T) :
    (T : ℝ) / 16 ≤
      (1 / 2 ^ T : ℝ) * ∑ σ : Fin T → Bool,
        expectedRegret π (Measure.dirac 0) (Measure.dirac (1 / 8))
          (fval (fun t => pm (σ t))) (valueSeq (fun t => pm (σ t))) :=
  FNI.bayes_main π
