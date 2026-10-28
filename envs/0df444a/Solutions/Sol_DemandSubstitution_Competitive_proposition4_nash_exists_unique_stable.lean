-- Prove2me | solution 1 for DemandSubstitution.Competitive.proposition4_nash_exists_unique_stable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T07:24:03.851644+00:00
-- url     : https://prove2.me/submissions/d1d46e85-b9f2-4172-b456-cd74cbc3a3c1

import Mathlib
import Definitions.Def_DemandSubstitution_Competitive_Setting

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace P2M19701DD7

open DemandSubstitution.Competitive

/-- A level set `{x | x i + H x = t}` with `H` independent of `x i` is Lebesgue-null. -/
lemma volume_level_null {n : ℕ} (i : Fin n) (H : (Fin n → ℝ) → ℝ) (hH : Measurable H)
    (hinv : ∀ x c, H (Function.update x i c) = H x) (t : ℝ) :
    volume {x : Fin n → ℝ | x i + H x = t} = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i with he
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
  set S : Set (Fin (m + 1) → ℝ) := {x | x i + H x = t} with hS
  have hSm : MeasurableSet S := measurableSet_eq_fun ((measurable_pi_apply i).add hH)
    measurable_const
  have hpre : e ⁻¹' (e.symm ⁻¹' S) = S := by
    ext x; simp
  rw [← hpre, hmp.measure_preimage_equiv]
  have hTm : MeasurableSet (e.symm ⁻¹' S) := e.symm.measurable hSm
  rw [show (volume : Measure (ℝ × (Fin m → ℝ))) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_apply_symm hTm]
  have : ∀ y : Fin m → ℝ, (volume : Measure ℝ) ((fun a => (a, y)) ⁻¹' (e.symm ⁻¹' S)) = 0 := by
    intro y
    refine measure_mono_null (t := {t - H (Fin.insertNth i 0 y)}) ?_ (measure_singleton _)
    intro a ha
    have hval : e.symm (a, y) = Fin.insertNth (α := fun _ => ℝ) i a y := rfl
    simp only [Set.mem_preimage, hS, Set.mem_setOf_eq, hval] at ha
    have h1 : H (Fin.insertNth (α := fun _ => ℝ) i a y) =
        H (Fin.insertNth (α := fun _ => ℝ) i 0 y) := by
      rw [← Fin.update_insertNth (α := fun _ => ℝ) i (0 : ℝ) a y, hinv]
    simp only [Set.mem_singleton_iff]
    simp only [Fin.insertNth_apply_same] at ha
    rw [h1] at ha
    linarith
  simp [this]

/-- Real-valued measure along an antitone family converges to the measure of the intersection. -/
lemma tendsto_real_iInter {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (s : ℕ → Set α) (hs : ∀ k, MeasurableSet (s k)) (hm : Antitone s) :
    Tendsto (fun k => μ.real (s k)) atTop (𝓝 (μ.real (⋂ k, s k))) := by
  have h := tendsto_measure_iInter_atTop (μ := μ) (fun k => (hs k).nullMeasurableSet) hm
    ⟨0, measure_ne_top μ _⟩
  exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp h

lemma tendsto_real_iUnion {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (s : ℕ → Set α) (hm : Monotone s) :
    Tendsto (fun k => μ.real (s k)) atTop (𝓝 (μ.real (⋃ k, s k))) := by
  have h := tendsto_measure_iUnion_atTop (μ := μ) hm
  exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp h

lemma inv_succ_anti : Antitone (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
  intro k k' hk
  have : (k : ℝ) ≤ k' := by exact_mod_cast hk
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

lemma lim_right {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (Y : α → ℝ) (hY : Measurable Y) (q : ℝ) :
    Tendsto (fun k : ℕ => μ.real {x | Y x < q + 1 / ((k : ℝ) + 1)}) atTop
      (𝓝 (μ.real {x | Y x ≤ q})) := by
  have hI : (⋂ k : ℕ, {x | Y x < q + 1 / ((k : ℝ) + 1)}) = {x | Y x ≤ q} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h
      by_contra hc
      push_neg at hc
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hc)
      have := h k
      linarith
    · intro h k
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  rw [← hI]
  refine tendsto_real_iInter μ _ (fun k => measurableSet_lt hY measurable_const) ?_
  intro k k' hk x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  linarith [inv_succ_anti hk]

lemma lim_left {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (Y : α → ℝ) (q : ℝ) :
    Tendsto (fun k : ℕ => μ.real {x | Y x ≤ q - 1 / ((k : ℝ) + 1)}) atTop
      (𝓝 (μ.real {x | Y x < q})) := by
  have hU : (⋃ k : ℕ, {x | Y x ≤ q - 1 / ((k : ℝ) + 1)}) = {x | Y x < q} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk⟩
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    · intro h
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 h)
      exact ⟨k, by linarith⟩
  rw [← hU]
  refine tendsto_real_iUnion μ _ ?_
  intro k k' hk x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  linarith [inv_succ_anti hk]

lemma lim_top {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (Y : α → ℝ) :
    Tendsto (fun k : ℕ => μ.real {x | Y x ≤ k}) atTop (𝓝 1) := by
  have hU : (⋃ k : ℕ, {x | Y x ≤ k}) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    obtain ⟨k, hk⟩ := exists_nat_ge (Y x)
    exact ⟨k, hk⟩
  have h := tendsto_real_iUnion μ (fun k : ℕ => {x | Y x ≤ k}) ?_
  · rw [hU, probReal_univ] at h
    exact h
  intro k k' hk x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  have : (k : ℝ) ≤ k' := by exact_mod_cast hk
  linarith


section Model

variable {n : ℕ} (M : Model n)

lemma u_pos (i : Fin n) : 0 < M.u i := by unfold Model.u; linarith [M.c_lt_r i]

lemma o_pos (i : Fin n) : 0 < M.o i := by unfold Model.o; linarith [M.s_lt_c i]

lemma ds_update (Q x : Fin n → ℝ) (i : Fin n) (q : ℝ) :
    Ds M (Function.update Q i q) x i = Ds M Q x i := by
  unfold Ds
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma ds_ge (Q x : Fin n → ℝ) (k : Fin n) : x k ≤ Ds M Q x k := by
  unfold Ds
  have : 0 ≤ ∑ j ∈ Finset.univ.erase k, M.a j k * max (x j - Q j) 0 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (M.a_nonneg j k) (le_max_right _ _)
  linarith

lemma ds_continuous (Q : Fin n → ℝ) (k : Fin n) : Continuous fun x => Ds M Q x k := by
  unfold Ds
  exact (continuous_apply k).add (continuous_finsetSum _ fun j _ =>
    continuous_const.mul (((continuous_apply j).sub continuous_const).max continuous_const))

lemma ds_meas (Q : Fin n → ℝ) (k : Fin n) : Measurable fun x => Ds M Q x k :=
  (ds_continuous M Q k).measurable

/-- `Ds` moves by at most `L = ∑_{j ≠ i} a_ji |Q_j - Q'_j|` when `Q` changes to `Q'`. -/
lemma ds_lip (Q Q' x : Fin n → ℝ) (i : Fin n) :
    Ds M Q' x i ≤ Ds M Q x i + ∑ j ∈ Finset.univ.erase i, M.a j i * |Q j - Q' j| := by
  unfold Ds
  have : ∑ j ∈ Finset.univ.erase i, M.a j i * max (x j - Q' j) 0 ≤
      ∑ j ∈ Finset.univ.erase i, M.a j i * max (x j - Q j) 0 +
        ∑ j ∈ Finset.univ.erase i, M.a j i * |Q j - Q' j| := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 := abs_max_sub_max_le_abs (x j - Q' j) (x j - Q j) 0
    have h2 : max (x j - Q' j) 0 - max (x j - Q j) 0 ≤ |Q j - Q' j| := by
      have h3 : (x j - Q' j) - (x j - Q j) = Q j - Q' j := by ring
      rw [h3] at h1
      exact le_trans (le_abs_self _) h1
    have := mul_le_mul_of_nonneg_left h2 (M.a_nonneg j i)
    nlinarith
  linarith

variable (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]

/-- Expected sales `E[min(D^s_i, q)]`. -/
noncomputable def Ex (Q : Fin n → ℝ) (i : Fin n) (q : ℝ) : ℝ :=
  ∫ x, min (Ds M Q x i) q ∂μ

lemma min_integrable (hμ : IsDemandLaw μ) (Q : Fin n → ℝ) (i : Fin n) (q : ℝ) :
    Integrable (fun x => min (Ds M Q x i) q) μ := by
  refine Integrable.mono' ((hμ.2.2 i).abs.add (integrable_const |q|)) ?_ ?_
  · exact ((ds_continuous M Q i).min continuous_const).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    have h1 := ds_ge M Q x i
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_le]
    constructor
    · have := le_min (show -(|x i| + |q|) ≤ Ds M Q x i by
          linarith [neg_abs_le (x i), abs_nonneg q])
        (show -(|x i| + |q|) ≤ q by linarith [neg_abs_le q, abs_nonneg (x i)])
      exact this
    · linarith [min_le_right (Ds M Q x i) q, le_abs_self q, abs_nonneg (x i)]

lemma integrand_eq (u o D q : ℝ) :
    u * D - u * max (D - q) 0 - o * max (q - D) 0 = (u + o) * min D q - o * q := by
  rcases le_total D q with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith), min_eq_left h]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith), min_eq_right h]; ring

lemma profit_eq (hμ : IsDemandLaw μ) (Q : Fin n → ℝ) (i : Fin n) (q : ℝ) :
    firmProfit M μ (Function.update Q i q) i = (M.u i + M.o i) * Ex M μ Q i q - M.o i * q := by
  unfold firmProfit Ex
  have : (fun x => M.u i * Ds M (Function.update Q i q) x i
      - M.u i * max (Ds M (Function.update Q i q) x i - Function.update Q i q i) 0
      - M.o i * max (Function.update Q i q i - Ds M (Function.update Q i q) x i) 0) =
      fun x => (M.u i + M.o i) * min (Ds M Q x i) q - M.o i * q := by
    funext x
    rw [Function.update_self, ds_update, integrand_eq]
  rw [this, integral_sub ((min_integrable M μ hμ Q i q).const_mul _) (integrable_const _),
    integral_const_mul, integral_const]
  simp

lemma ediff_le (hμ : IsDemandLaw μ) (Q : Fin n → ℝ) (i : Fin n) {q1 q2 : ℝ} (hq : q1 ≤ q2) :
    Ex M μ Q i q2 - Ex M μ Q i q1 ≤ (q2 - q1) * μ.real {x | q1 < Ds M Q x i} := by
  have hs : MeasurableSet {x | q1 < Ds M Q x i} := measurableSet_lt measurable_const (ds_meas M Q i)
  unfold Ex
  rw [← integral_sub (min_integrable M μ hμ Q i q2) (min_integrable M μ hμ Q i q1)]
  calc ∫ x, (min (Ds M Q x i) q2 - min (Ds M Q x i) q1) ∂μ
      ≤ ∫ x, {x | q1 < Ds M Q x i}.indicator (fun _ => q2 - q1) x ∂μ := by
        refine integral_mono ((min_integrable M μ hμ Q i q2).sub (min_integrable M μ hμ Q i q1))
          ((integrable_const _).indicator hs) fun x => ?_
        simp only [Set.indicator_apply, Set.mem_setOf_eq]
        split_ifs with h
        · simp only [min_def]; split_ifs <;> linarith
        · simp only [min_def]; split_ifs <;> linarith
    _ = (q2 - q1) * μ.real {x | q1 < Ds M Q x i} := by
        rw [integral_indicator_const _ hs, smul_eq_mul, mul_comm]

lemma ediff_ge (hμ : IsDemandLaw μ) (Q : Fin n → ℝ) (i : Fin n) {q1 q2 : ℝ} (hq : q1 ≤ q2) :
    (q2 - q1) * μ.real {x | q2 ≤ Ds M Q x i} ≤ Ex M μ Q i q2 - Ex M μ Q i q1 := by
  have hs : MeasurableSet {x | q2 ≤ Ds M Q x i} := measurableSet_le measurable_const (ds_meas M Q i)
  unfold Ex
  rw [← integral_sub (min_integrable M μ hμ Q i q2) (min_integrable M μ hμ Q i q1)]
  calc (q2 - q1) * μ.real {x | q2 ≤ Ds M Q x i}
      = ∫ x, {x | q2 ≤ Ds M Q x i}.indicator (fun _ => q2 - q1) x ∂μ := by
        rw [integral_indicator_const _ hs, smul_eq_mul, mul_comm]
    _ ≤ ∫ x, (min (Ds M Q x i) q2 - min (Ds M Q x i) q1) ∂μ := by
        refine integral_mono ((integrable_const _).indicator hs)
          ((min_integrable M μ hμ Q i q2).sub (min_integrable M μ hμ Q i q1)) fun x => ?_
        simp only [Set.indicator_apply, Set.mem_setOf_eq]
        split_ifs with h
        · simp only [min_def]; split_ifs <;> linarith
        · simp only [min_def]; split_ifs <;> linarith

lemma gt_eq (Q : Fin n → ℝ) (i : Fin n) (q : ℝ) :
    μ.real {x | q < Ds M Q x i} = 1 - μ.real {x | Ds M Q x i ≤ q} := by
  have : {x | q < Ds M Q x i} = {x | Ds M Q x i ≤ q}ᶜ := by ext x; simp [not_le]
  rw [this, probReal_compl_eq_one_sub (measurableSet_le (ds_meas M Q i) measurable_const)]

lemma ge_eq (Q : Fin n → ℝ) (i : Fin n) (q : ℝ) :
    μ.real {x | q ≤ Ds M Q x i} = 1 - μ.real {x | Ds M Q x i < q} := by
  have : {x | q ≤ Ds M Q x i} = {x | Ds M Q x i < q}ᶜ := by ext x; simp [not_lt]
  rw [this, probReal_compl_eq_one_sub (measurableSet_lt (ds_meas M Q i) measurable_const)]

lemma le_zero_null (hμ : IsDemandLaw μ) (Q : Fin n → ℝ) (i : Fin n) :
    μ.real {x | Ds M Q x i ≤ 0} = 0 := by
  have h : μ {x | Ds M Q x i ≤ 0} = 0 := by
    refine measure_mono_null (t := {x | ¬ ∀ j, 0 < x j}) ?_ (ae_iff.1 hμ.2.1)
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    intro h
    linarith [h i, ds_ge M Q x i]
  simp [Measure.real, h]

lemma br_of (hμ : IsDemandLaw μ) (Q : Fin n → ℝ) (i : Fin n) (q : ℝ) (h0 : 0 ≤ q)
    (h1 : (M.u i + M.o i) * μ.real {x | Ds M Q x i < q} ≤ M.u i)
    (h2 : M.u i ≤ (M.u i + M.o i) * μ.real {x | Ds M Q x i ≤ q}) :
    IsBestResponse M μ Q i q := by
  refine ⟨h0, fun q' _ => ?_⟩
  rw [profit_eq M μ hμ, profit_eq M μ hμ]
  have hw : 0 < M.u i + M.o i := by linarith [u_pos M i, o_pos M i]
  rcases le_total q q' with h | h
  · have e1 := ediff_le M μ hμ Q i h
    rw [gt_eq] at e1
    have hA := mul_le_mul_of_nonneg_left e1 hw.le
    have hB : (q' - q) * ((M.u i + M.o i) * (1 - μ.real {x | Ds M Q x i ≤ q})) ≤
        (q' - q) * M.o i := mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.2 h)
    nlinarith
  · have e2 := ediff_ge M μ hμ Q i h
    rw [ge_eq] at e2
    have hA := mul_le_mul_of_nonneg_left e2 hw.le
    have hB : (q - q') * M.o i ≤
        (q - q') * ((M.u i + M.o i) * (1 - μ.real {x | Ds M Q x i < q})) :=
      mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.2 h)
    nlinarith

lemma of_br (hμ : IsDemandLaw μ) (Q : Fin n → ℝ) (i : Fin n) (q : ℝ)
    (hbr : IsBestResponse M μ Q i q) :
    (M.u i + M.o i) * μ.real {x | Ds M Q x i < q} ≤ M.u i ∧
      M.u i ≤ (M.u i + M.o i) * μ.real {x | Ds M Q x i ≤ q} := by
  have hw : 0 < M.u i + M.o i := by linarith [u_pos M i, o_pos M i]
  have hq0 := hbr.1
  constructor
  · rcases eq_or_lt_of_le hq0 with hq | hq
    · subst hq
      have : μ.real {x | Ds M Q x i < 0} ≤ μ.real {x | Ds M Q x i ≤ 0} :=
        measureReal_mono fun x hx => by simp only [Set.mem_setOf_eq] at hx ⊢; linarith
      rw [le_zero_null M μ hμ] at this
      have h0 : μ.real {x | Ds M Q x i < 0} = 0 := le_antisymm this measureReal_nonneg
      rw [h0, mul_zero]; exact (u_pos M i).le
    · obtain ⟨N, hN⟩ := exists_nat_one_div_lt hq
      have hlim : Tendsto (fun k : ℕ => (M.u i + M.o i) *
          μ.real {x | Ds M Q x i ≤ q - 1 / ((k : ℝ) + 1)}) atTop
          (𝓝 ((M.u i + M.o i) * μ.real {x | Ds M Q x i < q})) :=
        (lim_left μ (fun x => Ds M Q x i) q).const_mul _
      refine le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨N, fun k hk => ?_⟩)
      have hkN : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := inv_succ_anti hk
      have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
      set q'' := q - 1 / ((k : ℝ) + 1) with hq''
      have hb := hbr.2 q'' (by linarith)
      rw [profit_eq M μ hμ, profit_eq M μ hμ] at hb
      have e1 := ediff_le M μ hμ Q i (show q'' ≤ q by linarith)
      rw [gt_eq] at e1
      have hA := mul_le_mul_of_nonneg_left e1 hw.le
      have hd : 0 < q - q'' := by linarith
      have h3 : (q - q'') * M.o i ≤
          (q - q'') * ((M.u i + M.o i) * (1 - μ.real {x | Ds M Q x i ≤ q''})) := by nlinarith
      have h4 := le_of_mul_le_mul_left h3 hd
      linarith
  · have hk : ∀ k : ℕ, M.u i ≤ (M.u i + M.o i) *
        μ.real {x | Ds M Q x i < q + 1 / ((k : ℝ) + 1)} := by
      intro k
      have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
      set q'' := q + 1 / ((k : ℝ) + 1) with hq''
      have hb := hbr.2 q'' (by linarith)
      rw [profit_eq M μ hμ, profit_eq M μ hμ] at hb
      have e2 := ediff_ge M μ hμ Q i (show q ≤ q'' by linarith)
      rw [ge_eq] at e2
      have hA := mul_le_mul_of_nonneg_left e2 hw.le
      have hd : 0 < q'' - q := by linarith
      have h3 : (q'' - q) * ((M.u i + M.o i) * (1 - μ.real {x | Ds M Q x i < q''})) ≤
          (q'' - q) * M.o i := by nlinarith
      have h4 := le_of_mul_le_mul_left h3 hd
      linarith
    exact ge_of_tendsto' ((lim_right μ (fun x => Ds M Q x i) (ds_meas M Q i) q).const_mul _) hk

lemma br_exists (hμ : IsDemandLaw μ) (Q : Fin n → ℝ) (i : Fin n) :
    ∃ q, IsBestResponse M μ Q i q := by
  have hw : 0 < M.u i + M.o i := by linarith [u_pos M i, o_pos M i]
  have hu := u_pos M i
  set S : Set ℝ := {q | 0 ≤ q ∧ M.u i ≤ (M.u i + M.o i) * μ.real {x | Ds M Q x i ≤ q}} with hS
  have hne : S.Nonempty := by
    have hlim := (lim_top μ (fun x => Ds M Q x i)).const_mul (M.u i + M.o i)
    rw [mul_one] at hlim
    have hlt : M.u i < M.u i + M.o i := by linarith [o_pos M i]
    obtain ⟨k, hk⟩ := (hlim.eventually (lt_mem_nhds hlt)).exists
    exact ⟨k, Nat.cast_nonneg k, hk.le⟩
  have hbdd : BddBelow S := ⟨0, fun q hq => hq.1⟩
  set qs := sInf S with hqs
  have h0 : 0 ≤ qs := le_csInf hne fun q hq => hq.1
  refine ⟨qs, br_of M μ hμ Q i qs h0 ?_ ?_⟩
  · by_contra hc
    push_neg at hc
    have hlim := (lim_left μ (fun x => Ds M Q x i) qs).const_mul (M.u i + M.o i)
    obtain ⟨k, hk⟩ := (hlim.eventually (lt_mem_nhds hc)).exists
    have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
    rcases le_or_gt 0 (qs - 1 / ((k : ℝ) + 1)) with hq | hq
    · have hmem : qs - 1 / ((k : ℝ) + 1) ∈ S := ⟨hq, hk.le⟩
      have := csInf_le hbdd hmem
      linarith
    · have hsub : μ.real {x | Ds M Q x i ≤ qs - 1 / ((k : ℝ) + 1)} ≤
          μ.real {x | Ds M Q x i ≤ 0} :=
        measureReal_mono fun x hx => by simp only [Set.mem_setOf_eq] at hx ⊢; linarith
      rw [le_zero_null M μ hμ] at hsub
      have : (M.u i + M.o i) * μ.real {x | Ds M Q x i ≤ qs - 1 / ((k : ℝ) + 1)} ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hw.le hsub
      linarith
  · by_contra hc
    push_neg at hc
    have hlim := (lim_right μ (fun x => Ds M Q x i) (ds_meas M Q i) qs).const_mul
      (M.u i + M.o i)
    obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hc)).exists
    have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨s, hsS, hslt⟩ := exists_lt_of_csInf_lt hne (show sInf S < qs + 1 / ((k : ℝ) + 1) by
      rw [← hqs]; linarith)
    have hmono : μ.real {x | Ds M Q x i ≤ s} ≤
        μ.real {x | Ds M Q x i < qs + 1 / ((k : ℝ) + 1)} :=
      measureReal_mono fun x hx => by simp only [Set.mem_setOf_eq] at hx ⊢; linarith
    have := mul_le_mul_of_nonneg_left hmono hw.le
    linarith [hsS.2]

/-- Positive mass in every interval `(a, b)` with `0 ≤ a`. -/
lemma interval_pos (hf : HasPositiveDensity μ) (Q : Fin n → ℝ) (hQ : ∀ j, 0 ≤ Q j)
    (i : Fin n) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    0 < μ.real {x | a < Ds M Q x i ∧ Ds M Q x i < b} := by
  have hn : (0 : ℝ) < n := by exact_mod_cast i.pos
  set δ := (b - a) / n with hδ
  have hδpos : 0 < δ := div_pos (by linarith) hn
  have hnδ : (n : ℝ) * δ = b - a := by rw [hδ]; field_simp
  set B : Set (Fin n → ℝ) :=
    Set.pi Set.univ fun j => if j = i then Set.Ioo a (a + δ) else Set.Ioo 0 δ with hB
  have hBopen : IsOpen B := isOpen_set_pi Set.finite_univ fun j _ => by
    split_ifs <;> exact isOpen_Ioo
  have hmemB : ∀ x ∈ B, ∀ j, (j = i → a < x j ∧ x j < a + δ) ∧ (j ≠ i → 0 < x j ∧ x j < δ) := by
    intro x hx j
    have := hx j (Set.mem_univ j)
    by_cases hj : j = i
    · simp only [hj, if_true, Set.mem_Ioo] at this
      exact ⟨fun _ => by subst hj; exact this, fun h => absurd hj h⟩
    · simp only [hj, if_false, Set.mem_Ioo] at this
      exact ⟨fun h => absurd h hj, fun _ => this⟩
  have hBne : B.Nonempty := by
    refine ⟨fun j => if j = i then a + δ / 2 else δ / 2, fun j _ => ?_⟩
    by_cases hj : j = i
    · simp only [hj, if_true, Set.mem_Ioo]; constructor <;> linarith
    · simp only [hj, if_false, Set.mem_Ioo]; constructor <;> linarith
  have hBsub : B ⊆ {x | a < Ds M Q x i ∧ Ds M Q x i < b} := by
    intro x hx
    have hxi := (hmemB x hx i).1 rfl
    refine ⟨lt_of_lt_of_le hxi.1 (ds_ge M Q x i), ?_⟩
    unfold Ds
    have hterm : ∀ j ∈ Finset.univ.erase i, M.a j i * max (x j - Q j) 0 ≤ δ := by
      intro j hj
      have hxj := (hmemB x hx j).2 (Finset.ne_of_mem_erase hj)
      have hm0 : 0 ≤ max (x j - Q j) 0 := le_max_right _ _
      have hm1 : max (x j - Q j) 0 ≤ x j := max_le (by linarith [hQ j]) hxj.1.le
      have := mul_le_of_le_one_left hm0 (M.a_le_one j i)
      linarith
    have hsum := Finset.sum_le_sum hterm
    have htot : ∑ j ∈ Finset.univ.erase i, δ + δ = (n : ℝ) * δ := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      simp
    linarith
  have hBpos : 0 < μ B := by
    obtain ⟨f, hfm, hμf, hfpos⟩ := hf
    rw [hμf, withDensity_apply _ hBopen.measurableSet, lintegral_pos_iff_support hfm,
      Measure.restrict_apply (measurableSet_support hfm)]
    have hsub : B ⊆ Function.support f ∩ B := by
      intro x hx
      refine ⟨(hfpos x fun j => ?_).ne', hx⟩
      by_cases hj : j = i
      · have := (hmemB x hx j).1 hj; linarith
      · exact ((hmemB x hx j).2 hj).1
    exact lt_of_lt_of_le (hBopen.measure_pos volume hBne) (measure_mono hsub)
  have hpos : 0 < μ {x | a < Ds M Q x i ∧ Ds M Q x i < b} := lt_of_lt_of_le hBpos (measure_mono hBsub)
  exact ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)

lemma lip_one (hμ : IsDemandLaw μ) (hf : HasPositiveDensity μ) (Q Q' : Fin n → ℝ)
    (hQ : ∀ j, 0 ≤ Q j) (i : Fin n) (q q' : ℝ) (hq : IsBestResponse M μ Q i q)
    (hq' : IsBestResponse M μ Q' i q') :
    q' ≤ q + ∑ j ∈ Finset.univ.erase i, M.a j i * |Q j - Q' j| := by
  set L := ∑ j ∈ Finset.univ.erase i, M.a j i * |Q j - Q' j| with hL
  have hw : 0 < M.u i + M.o i := by linarith [u_pos M i, o_pos M i]
  by_contra hc
  push_neg at hc
  have hA := (of_br M μ hμ Q' i q' hq').1
  have hB := (of_br M μ hμ Q i q hq).2
  have hD := interval_pos M μ hf Q hQ i q (q' - L) hq.1 (by linarith)
  have hdisj : Disjoint {x | Ds M Q x i ≤ q} {x | q < Ds M Q x i ∧ Ds M Q x i < q' - L} := by
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_setOf_eq] at hx hx'
    linarith [hx'.1]
  have hU := measureReal_union (μ := μ) hdisj
    ((measurableSet_lt measurable_const (ds_meas M Q i)).inter
      (measurableSet_lt (ds_meas M Q i) measurable_const))
  have hsub : {x | Ds M Q x i ≤ q} ∪ {x | q < Ds M Q x i ∧ Ds M Q x i < q' - L} ⊆
      {x | Ds M Q' x i < q'} := by
    intro x hx
    have hl := ds_lip M Q Q' x i
    rw [← hL] at hl
    simp only [Set.mem_union, Set.mem_setOf_eq] at hx ⊢
    rcases hx with hx | hx
    · linarith
    · linarith [hx.2]
  have hmono := measureReal_mono (μ := μ) hsub
  rw [hU] at hmono
  have : (M.u i + M.o i) * μ.real {x | Ds M Q x i ≤ q} <
      (M.u i + M.o i) * μ.real {x | Ds M Q' x i < q'} := by
    apply mul_lt_mul_of_pos_left _ hw
    linarith
  linarith

lemma lip (hμ : IsDemandLaw μ) (hf : HasPositiveDensity μ) (Q Q' : Fin n → ℝ)
    (hQ : ∀ j, 0 ≤ Q j) (hQ' : ∀ j, 0 ≤ Q' j) (i : Fin n) (q q' : ℝ)
    (hq : IsBestResponse M μ Q i q) (hq' : IsBestResponse M μ Q' i q') :
    |q - q'| ≤ ∑ j ∈ Finset.univ.erase i, M.a j i * |Q j - Q' j| := by
  rw [abs_sub_le_iff]
  constructor
  · have := lip_one M μ hμ hf Q' Q hQ' i q' q hq' hq
    have hs : ∑ j ∈ Finset.univ.erase i, M.a j i * |Q' j - Q j| =
        ∑ j ∈ Finset.univ.erase i, M.a j i * |Q j - Q' j| :=
      Finset.sum_congr rfl fun j _ => by rw [abs_sub_comm]
    linarith
  · have := lip_one M μ hμ hf Q Q' hQ i q q' hq hq'
    linarith

lemma exists_K : ∃ K : ℝ, 0 ≤ K ∧ K < 1 ∧ ∀ j, ∑ i, M.a j i ≤ K := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact ⟨0, le_rfl, one_pos, fun j => isEmptyElim j⟩
  · obtain ⟨j0, hj0⟩ := Finite.exists_max (fun j => ∑ i, M.a j i)
    exact ⟨∑ i, M.a j0 i, Finset.sum_nonneg fun i _ => M.a_nonneg j0 i,
      M.a_row_sum_lt_one j0, hj0⟩

/-- `L¹` distance. -/
def l1 (P R : Fin n → ℝ) : ℝ := ∑ j, |P j - R j|

lemma contr (hμ : IsDemandLaw μ) (hf : HasPositiveDensity μ) (K : ℝ)
    (hK : ∀ j, ∑ i, M.a j i ≤ K) (P R P' R' : Fin n → ℝ)
    (hP : ∀ j, 0 ≤ P j) (hR : ∀ j, 0 ≤ R j)
    (hP' : ∀ i, IsBestResponse M μ P i (P' i)) (hR' : ∀ i, IsBestResponse M μ R i (R' i)) :
    l1 P' R' ≤ K * l1 P R := by
  unfold l1
  calc ∑ i, |P' i - R' i|
      ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, M.a j i * |P j - R j| :=
        Finset.sum_le_sum fun i _ => lip M μ hμ hf P R hP hR i _ _ (hP' i) (hR' i)
    _ ≤ ∑ i, ∑ j, M.a j i * |P j - R j| :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset _ _) fun j _ _ => mul_nonneg (M.a_nonneg j i) (abs_nonneg _)
    _ = ∑ j, (∑ i, M.a j i) * |P j - R j| := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
    _ ≤ ∑ j, K * |P j - R j| :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hK j) (abs_nonneg _)
    _ = K * ∑ j, |P j - R j| := (Finset.mul_sum _ _ _).symm

lemma ds_atom (hμ : IsDemandLaw μ) (Q : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    μ {x | Ds M Q x i = t} = 0 := by
  have hH : Measurable fun x : Fin n → ℝ => ∑ j ∈ Finset.univ.erase i, M.a j i * max (x j - Q j) 0 :=
    (continuous_finsetSum _ fun j _ =>
      continuous_const.mul (((continuous_apply j).sub continuous_const).max continuous_const)).measurable
  have hinv : ∀ (x : Fin n → ℝ) (c : ℝ),
      (∑ j ∈ Finset.univ.erase i, M.a j i * max (Function.update x i c j - Q j) 0) =
        ∑ j ∈ Finset.univ.erase i, M.a j i * max (x j - Q j) 0 := by
    intro x c
    exact Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  exact hμ.1 (volume_level_null i _ hH hinv t)

lemma le_eq_lt (hμ : IsDemandLaw μ) (Q : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    μ.real {x | Ds M Q x i ≤ t} = μ.real {x | Ds M Q x i < t} := by
  apply le_antisymm
  · have hsub : {x | Ds M Q x i ≤ t} ⊆ {x | Ds M Q x i < t} ∪ {x | Ds M Q x i = t} := by
      intro x hx
      simp only [Set.mem_setOf_eq, Set.mem_union] at hx ⊢
      rcases lt_or_eq_of_le hx with h | h
      · exact Or.inl h
      · exact Or.inr h
    have h0 : μ.real {x | Ds M Q x i = t} = 0 := by simp [Measure.real, ds_atom M μ hμ Q i t]
    calc μ.real {x | Ds M Q x i ≤ t} ≤ μ.real ({x | Ds M Q x i < t} ∪ {x | Ds M Q x i = t}) :=
          measureReal_mono hsub
      _ ≤ μ.real {x | Ds M Q x i < t} + μ.real {x | Ds M Q x i = t} := measureReal_union_le _ _
      _ = μ.real {x | Ds M Q x i < t} := by rw [h0, add_zero]
  · exact measureReal_mono fun x hx => by simp only [Set.mem_setOf_eq] at hx ⊢; linarith

lemma foc_lhs (hμ : IsDemandLaw μ) (Q : Fin n → ℝ) (i : Fin n) :
    μ.real {x | x i < Q i} - μ.real {x | x i < Q i ∧ Q i < Ds M Q x i} =
      μ.real {x | Ds M Q x i ≤ Q i} := by
  have hm2 : MeasurableSet {x : Fin n → ℝ | x i < Q i ∧ Q i < Ds M Q x i} :=
    (measurableSet_lt (measurable_pi_apply i) measurable_const).inter
      (measurableSet_lt measurable_const (ds_meas M Q i))
  have hsub12 : {x : Fin n → ℝ | x i < Q i ∧ Q i < Ds M Q x i} ⊆ {x : Fin n → ℝ | x i < Q i} :=
    fun x hx => hx.1
  rw [← measureReal_diff hsub12 hm2]
  apply le_antisymm
  · refine measureReal_mono fun x hx => ?_
    simp only [Set.mem_diff, Set.mem_setOf_eq, not_and, not_lt] at hx ⊢
    exact hx.2 hx.1
  · have hnull : μ {x : Fin n → ℝ | x i + (fun _ => (0 : ℝ)) x = Q i} = 0 :=
      hμ.1 (volume_level_null i (fun _ => (0 : ℝ)) measurable_const (fun _ _ => rfl) (Q i))
    have h0 : μ.real {x : Fin n → ℝ | x i + (fun _ => (0 : ℝ)) x = Q i} = 0 := by
      simp only [Measure.real, hnull, ENNReal.toReal_zero]
    have hsub : {x | Ds M Q x i ≤ Q i} ⊆
        ({x | x i < Q i} \ {x | x i < Q i ∧ Q i < Ds M Q x i}) ∪
          {x : Fin n → ℝ | x i + (fun _ => (0 : ℝ)) x = Q i} := by
      intro x hx
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_diff, not_and, not_lt] at hx ⊢
      rcases lt_or_ge (x i) (Q i) with h | h
      · exact Or.inl ⟨h, fun _ => hx⟩
      · right; linarith [ds_ge M Q x i]
    calc μ.real {x | Ds M Q x i ≤ Q i}
        ≤ μ.real (({x | x i < Q i} \ {x | x i < Q i ∧ Q i < Ds M Q x i}) ∪
          {x : Fin n → ℝ | x i + (fun _ => (0 : ℝ)) x = Q i}) := measureReal_mono hsub
      _ ≤ _ := measureReal_union_le _ _
      _ = _ := by rw [h0, add_zero]

theorem main (hμ : IsDemandLaw μ) (hf : HasPositiveDensity μ) :
    (∃ Q, IsNash M μ Q) ∧
      (∀ Q : Fin n → ℝ, (∀ i, 0 ≤ Q i) → (IsNash M μ Q ↔ ∀ i, FOC10 M μ Q i)) ∧
      (((∀ j, ∑ i, M.a i j < 1) ∨ (∀ i, ∑ j, M.a i j < 1)) →
        ∃ Qd : Fin n → ℝ, IsNash M μ Qd ∧ (∀ Q, IsNash M μ Q → Q = Qd) ∧
          ∀ seq : ℕ → Fin n → ℝ, (∀ i, 0 ≤ seq 0 i) →
            (∀ k i, IsBestResponse M μ (seq k) i (seq (k + 1) i)) →
            Filter.Tendsto seq Filter.atTop (nhds Qd)) := by
  obtain ⟨K, hK0, hK1, hK⟩ := exists_K M
  have hex : ∀ (Q : Fin n → ℝ) (i : Fin n), ∃ q, IsBestResponse M μ Q i q :=
    fun Q i => br_exists M μ hμ Q i
  choose b hb using hex
  -- iterates of the best-response map from `0`
  set z : ℕ → Fin n → ℝ := fun k => b^[k] 0 with hz
  have hz_succ : ∀ k, z (k + 1) = b (z k) := fun k => Function.iterate_succ_apply' b k 0
  have hz_nn : ∀ k j, 0 ≤ z k j := by
    intro k j
    cases k with
    | zero => simp [hz]
    | succ k => rw [hz_succ]; exact (hb _ j).1
  have hzd : ∀ k, l1 (z (k + 1)) (z k) ≤ K ^ k * l1 (z 1) (z 0) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := contr M μ hμ hf K hK (z (k + 1)) (z k) (z (k + 2)) (z (k + 1))
        (hz_nn _) (hz_nn _) (fun i => by rw [hz_succ (k + 1)]; exact hb _ i)
        (fun i => by rw [hz_succ k]; exact hb _ i)
      calc l1 (z (k + 1 + 1)) (z (k + 1)) ≤ K * l1 (z (k + 1)) (z k) := h
        _ ≤ K * (K ^ k * l1 (z 1) (z 0)) := mul_le_mul_of_nonneg_left ih hK0
        _ = K ^ (k + 1) * l1 (z 1) (z 0) := by ring
  have hcoord_le : ∀ (P R : Fin n → ℝ) (j : Fin n), |P j - R j| ≤ l1 P R := fun P R j =>
    Finset.single_le_sum (f := fun j => |P j - R j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
  have hl1_nn : ∀ P R : Fin n → ℝ, 0 ≤ l1 P R := fun P R =>
    Finset.sum_nonneg fun j _ => abs_nonneg _
  have hcs : CauchySeq z := by
    refine cauchySeq_of_le_geometric K (l1 (z 1) (z 0)) hK1 fun k => ?_
    rw [dist_pi_le_iff (mul_nonneg (hl1_nn _ _) (pow_nonneg hK0 _))]
    intro j
    rw [Real.dist_eq, abs_sub_comm]
    calc |z (k + 1) j - z k j| ≤ l1 (z (k + 1)) (z k) := hcoord_le _ _ j
      _ ≤ K ^ k * l1 (z 1) (z 0) := hzd k
      _ = l1 (z 1) (z 0) * K ^ k := mul_comm _ _
  obtain ⟨Qd, hQd⟩ := cauchySeq_tendsto_of_complete hcs
  have hcoord : ∀ j, Tendsto (fun k => z k j) atTop (𝓝 (Qd j)) := fun j =>
    tendsto_pi_nhds.1 hQd j
  have hQd0 : ∀ j, 0 ≤ Qd j := fun j => ge_of_tendsto' (hcoord j) fun k => hz_nn k j
  have hdz : Tendsto (fun k => l1 (z k) Qd) atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset (Fin n))
      fun j _ => ((hcoord j).sub_const (Qd j)).abs
    simpa [l1] using this
  have hfix : b Qd = Qd := by
    have h1 : Tendsto (fun k => z (k + 1)) atTop (𝓝 (b Qd)) := by
      refine tendsto_pi_nhds.2 fun j => tendsto_iff_dist_tendsto_zero.2 ?_
      have hlim : Tendsto (fun k => K * l1 (z k) Qd) atTop (𝓝 0) := by
        simpa using hdz.const_mul K
      refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) hlim
      rw [Real.dist_eq, hz_succ]
      calc |b (z k) j - b Qd j| ≤ l1 (b (z k)) (b Qd) := hcoord_le _ _ j
        _ ≤ K * l1 (z k) Qd :=
          contr M μ hμ hf K hK _ _ _ _ (hz_nn k) hQd0 (hb _) (hb _)
    have h2 : Tendsto (fun k => z (k + 1)) atTop (𝓝 Qd) := hQd.comp (tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique h1 h2
  have hNd : IsNash M μ Qd := by
    refine (isNash_iff M μ Qd).2 ⟨hQd0, fun i => ?_⟩
    have := hb Qd i
    rw [hfix] at this
    exact this
  obtain ⟨hd0, hdbr⟩ := (isNash_iff M μ Qd).1 hNd
  refine ⟨⟨Qd, hNd⟩, ?_, fun _ => ⟨Qd, hNd, ?_, ?_⟩⟩
  · intro Q hQ
    constructor
    · intro hN i
      have hw : 0 < M.u i + M.o i := by linarith [u_pos M i, o_pos M i]
      obtain ⟨h1, h2⟩ := of_br M μ hμ Q i (Q i) (((isNash_iff M μ Q).1 hN).2 i)
      rw [← le_eq_lt M μ hμ] at h1
      unfold FOC10
      rw [foc_lhs M μ hμ, eq_div_iff hw.ne']
      linarith
    · intro hF
      refine (isNash_iff M μ Q).2 ⟨hQ, fun i => ?_⟩
      have hw : 0 < M.u i + M.o i := by linarith [u_pos M i, o_pos M i]
      have hFi := hF i
      unfold FOC10 at hFi
      rw [foc_lhs M μ hμ, eq_div_iff hw.ne'] at hFi
      refine br_of M μ hμ Q i (Q i) (hQ i) ?_ ?_
      · rw [← le_eq_lt M μ hμ]; linarith
      · linarith
  · intro Q hN
    obtain ⟨hQ0, hQbr⟩ := (isNash_iff M μ Q).1 hN
    have h := contr M μ hμ hf K hK Q Qd Q Qd hQ0 hd0 hQbr hdbr
    have hz0 : l1 Q Qd = 0 := by
      have := hl1_nn Q Qd
      nlinarith
    funext j
    have := hcoord_le Q Qd j
    rw [hz0] at this
    have : |Q j - Qd j| = 0 := le_antisymm this (abs_nonneg _)
    linarith [abs_eq_zero.1 this]
  · intro seq h0 hseq
    have hs_nn : ∀ k j, 0 ≤ seq k j := by
      intro k j
      cases k with
      | zero => exact h0 j
      | succ k => exact (hseq k j).1
    have hdk : ∀ k, l1 (seq k) Qd ≤ K ^ k * l1 (seq 0) Qd := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have h := contr M μ hμ hf K hK (seq k) Qd (seq (k + 1)) Qd (hs_nn k) hd0
          (fun i => hseq k i) hdbr
        calc l1 (seq (k + 1)) Qd ≤ K * l1 (seq k) Qd := h
          _ ≤ K * (K ^ k * l1 (seq 0) Qd) := mul_le_mul_of_nonneg_left ih hK0
          _ = K ^ (k + 1) * l1 (seq 0) Qd := by ring
    have hlim : Tendsto (fun k => K ^ k * l1 (seq 0) Qd) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK1).mul_const (l1 (seq 0) Qd)
    refine tendsto_pi_nhds.2 fun j => tendsto_iff_dist_tendsto_zero.2 ?_
    refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) hlim
    rw [Real.dist_eq]
    exact le_trans (hcoord_le _ _ j) (hdk k)

end Model

end P2M19701DD7

open MeasureTheory DemandSubstitution.Competitive in
theorem solution {n : ℕ} (M : Model n)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] (hμ : IsDemandLaw μ)
    (hf : HasPositiveDensity μ) :
    (∃ Q, IsNash M μ Q) ∧
      (∀ Q : Fin n → ℝ, (∀ i, 0 ≤ Q i) → (IsNash M μ Q ↔ ∀ i, FOC10 M μ Q i)) ∧
      (((∀ j, ∑ i, M.a i j < 1) ∨ (∀ i, ∑ j, M.a i j < 1)) →
        ∃ Qd : Fin n → ℝ, IsNash M μ Qd ∧ (∀ Q, IsNash M μ Q → Q = Qd) ∧
          ∀ seq : ℕ → Fin n → ℝ, (∀ i, 0 ≤ seq 0 i) →
            (∀ k i, IsBestResponse M μ (seq k) i (seq (k + 1) i)) →
            Filter.Tendsto seq Filter.atTop (nhds Qd)) := by
  exact P2M19701DD7.main M μ hμ hf
