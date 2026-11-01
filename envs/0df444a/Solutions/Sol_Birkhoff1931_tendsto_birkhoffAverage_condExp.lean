-- Prove2me | solution 1 for Birkhoff1931.tendsto_birkhoffAverage_condExp
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T16:55:13.002641+00:00
-- url     : https://prove2.me/submissions/dbb8d832-3cd2-4ae6-a040-e38df23a3262

import Mathlib

set_option autoImplicit false
set_option linter.all false

namespace Birkhoff1931Aux

open MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X]

/-- Running maximum `max (S_0 g, ..., S_N g)` of Birkhoff sums (with `S_0 g = 0`). -/
noncomputable def runMax (T : X → X) (g : X → ℝ) : ℕ → X → ℝ
  | 0, _ => 0
  | N + 1, x => max (runMax T g N x) (birkhoffSum T g (N + 1) x)

lemma runMax_zero (T : X → X) (g : X → ℝ) (x : X) : runMax T g 0 x = 0 := rfl

lemma runMax_succ (T : X → X) (g : X → ℝ) (N : ℕ) (x : X) :
    runMax T g (N + 1) x = max (runMax T g N x) (birkhoffSum T g (N + 1) x) := rfl

lemma runMax_nonneg (T : X → X) (g : X → ℝ) (N : ℕ) (x : X) : 0 ≤ runMax T g N x := by
  induction N with
  | zero => rw [runMax_zero]
  | succ N ih => rw [runMax_succ]; exact le_trans ih (le_max_left _ _)

lemma le_runMax (T : X → X) (g : X → ℝ) {N k : ℕ} (hk : k ≤ N) (x : X) :
    birkhoffSum T g k x ≤ runMax T g N x := by
  induction N with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    rw [runMax_zero, birkhoffSum_zero]
  | succ N ih =>
    rw [runMax_succ]
    rcases Nat.lt_or_ge k (N + 1) with h | h
    · exact le_trans (ih (by omega)) (le_max_left _ _)
    · have hk' : k = N + 1 := by omega
      subst hk'
      exact le_max_right _ _

lemma runMax_eq (T : X → X) (g : X → ℝ) (N : ℕ) (x : X) :
    ∃ k ≤ N, runMax T g N x = birkhoffSum T g k x := by
  induction N with
  | zero => exact ⟨0, le_refl _, by rw [runMax_zero, birkhoffSum_zero]⟩
  | succ N ih =>
    obtain ⟨k, hk, he⟩ := ih
    rw [runMax_succ]
    rcases le_total (runMax T g N x) (birkhoffSum T g (N + 1) x) with h | h
    · exact ⟨N + 1, le_refl _, max_eq_right h⟩
    · exact ⟨k, by omega, by rw [max_eq_left h, he]⟩

lemma runMax_le (T : X → X) (g : X → ℝ) (N : ℕ) (x : X) (hpos : 0 < runMax T g N x) :
    runMax T g N x ≤ g x + runMax T g N (T x) := by
  obtain ⟨k, hk, he⟩ := runMax_eq T g N x
  rcases k with _ | j
  · rw [he, birkhoffSum_zero] at hpos
    exact absurd hpos (lt_irrefl 0)
  · rw [he, birkhoffSum_succ']
    have := le_runMax T g (show j ≤ N by omega) (T x)
    linarith

lemma measurable_birkhoffSum' {T : X → X} {g : X → ℝ} (hT : Measurable T) (hg : Measurable g)
    (n : ℕ) : Measurable (birkhoffSum T g n) := by
  have e : birkhoffSum T g n = fun x => ∑ k ∈ Finset.range n, g (T^[k] x) := rfl
  rw [e]
  exact Finset.measurable_sum _ (fun k _ => hg.comp (hT.iterate k))

lemma integrable_birkhoffSum' {μ : Measure X} {T : X → X} {g : X → ℝ}
    (hT : MeasurePreserving T μ μ) (hg : Integrable g μ) (n : ℕ) :
    Integrable (birkhoffSum T g n) μ := by
  have e : birkhoffSum T g n = fun x => ∑ k ∈ Finset.range n, g (T^[k] x) := rfl
  rw [e]
  exact integrable_finset_sum _ (fun k _ => (hT.iterate k).integrable_comp_of_integrable hg)

lemma measurable_runMax {T : X → X} {g : X → ℝ} (hT : Measurable T) (hg : Measurable g)
    (N : ℕ) : Measurable (runMax T g N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
    have e : runMax T g (N + 1) = fun x => max (runMax T g N x) (birkhoffSum T g (N + 1) x) :=
      rfl
    rw [e]
    exact ih.max (measurable_birkhoffSum' hT hg (N + 1))

lemma integrable_runMax {μ : Measure X} {T : X → X} {g : X → ℝ}
    (hT : MeasurePreserving T μ μ) (hgm : Measurable g) (hg : Integrable g μ) (N : ℕ) :
    Integrable (runMax T g N) μ := by
  induction N with
  | zero =>
    have e : runMax T g 0 = fun _ => (0 : ℝ) := rfl
    rw [e]
    exact integrable_zero _ _ _
  | succ N ih =>
    have hS := integrable_birkhoffSum' hT hg (N + 1)
    refine Integrable.mono' (ih.abs.add hS.abs)
      (measurable_runMax hT.measurable hgm (N + 1)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, runMax_succ, abs_le]
    have a1 := le_abs_self (runMax T g N x)
    have a2 := neg_abs_le (runMax T g N x)
    have b1 := le_abs_self (birkhoffSum T g (N + 1) x)
    have b2 := neg_abs_le (birkhoffSum T g (N + 1) x)
    have a0 := abs_nonneg (runMax T g N x)
    have b0 := abs_nonneg (birkhoffSum T g (N + 1) x)
    constructor
    · exact le_max_of_le_left (by linarith)
    · exact max_le (by linarith) (by linarith)

/-- **Maximal ergodic theorem** (Garsia's proof). -/
theorem maximal_ergodic (μ : Measure X) [IsFiniteMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hgm : Measurable g) (hg : Integrable g μ) :
    0 ≤ ∫ x in {x | ∃ n, 0 < birkhoffSum T g n x}, g x ∂μ := by
  let F : ℕ → Set X := fun N => {x | 0 < runMax T g N x}
  have hFm : ∀ N, MeasurableSet (F N) := fun N =>
    measurableSet_lt measurable_const (measurable_runMax hT.measurable hgm N)
  have hmono : Monotone F := by
    apply monotone_nat_of_le_succ
    intro N x hx
    show 0 < runMax T g (N + 1) x
    rw [runMax_succ]
    exact lt_max_of_lt_left hx
  have hU : (⋃ N, F N) = {x | ∃ n, 0 < birkhoffSum T g n x} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, F]
    constructor
    · rintro ⟨N, hN⟩
      obtain ⟨k, -, he⟩ := runMax_eq T g N x
      exact ⟨k, he ▸ hN⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, lt_of_lt_of_le hn (le_runMax T g le_rfl x)⟩
  have hNonneg : ∀ N, 0 ≤ ∫ x in F N, g x ∂μ := by
    intro N
    have hMm := measurable_runMax hT.measurable hgm N
    have hMi := integrable_runMax hT hgm hg N
    have hMTi : Integrable (fun x => runMax T g N (T x)) μ :=
      hT.integrable_comp_of_integrable hMi
    have h1 : ∫ x in F N, (runMax T g N x - runMax T g N (T x)) ∂μ ≤ ∫ x in F N, g x ∂μ := by
      apply setIntegral_mono_on (hMi.sub hMTi).integrableOn hg.integrableOn (hFm N)
      intro x hx
      have := runMax_le T g N x hx
      show runMax T g N x - runMax T g N (T x) ≤ g x
      linarith
    have h2 : ∫ x in F N, (runMax T g N x - runMax T g N (T x)) ∂μ
        = ∫ x in F N, runMax T g N x ∂μ - ∫ x in F N, runMax T g N (T x) ∂μ :=
      integral_sub hMi.integrableOn hMTi.integrableOn
    have h3 : ∫ x in F N, runMax T g N x ∂μ = ∫ x, runMax T g N x ∂μ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hx' : ¬ (0 < runMax T g N x) := hx
      exact le_antisymm (not_lt.1 hx') (runMax_nonneg T g N x)
    have h4 : ∫ x in F N, runMax T g N (T x) ∂μ ≤ ∫ x, runMax T g N (T x) ∂μ :=
      setIntegral_le_integral hMTi (Eventually.of_forall fun x => runMax_nonneg T g N (T x))
    have h5 : ∫ x, runMax T g N (T x) ∂μ = ∫ x, runMax T g N x ∂μ := by
      have hfm : AEStronglyMeasurable (runMax T g N) (Measure.map T μ) := by
        rw [hT.map_eq]; exact hMm.aestronglyMeasurable
      have := integral_map hT.measurable.aemeasurable hfm
      rw [hT.map_eq] at this
      exact this.symm
    linarith
  have ht := tendsto_setIntegral_of_monotone hFm hmono (hg.integrableOn)
  rw [hU] at ht
  exact ge_of_tendsto' ht hNonneg

lemma iterate_mem_iff {T : X → X} {D : Set X} (hD : T ⁻¹' D = D) (k : ℕ) (x : X) :
    T^[k] x ∈ D ↔ x ∈ D := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change T^[k] x ∈ T ⁻¹' D ↔ _
    rw [hD, ih]

lemma birkhoffSum_indicator {T : X → X} {D : Set X} (hD : T ⁻¹' D = D) (h : X → ℝ) (n : ℕ)
    (x : X) : birkhoffSum T (D.indicator h) n x = D.indicator (birkhoffSum T h n) x := by
  by_cases hx : x ∈ D
  · rw [Set.indicator_of_mem hx]
    simp only [birkhoffSum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Set.indicator_of_mem ((iterate_mem_iff hD k x).2 hx)]
  · rw [Set.indicator_of_notMem hx]
    simp only [birkhoffSum]
    apply Finset.sum_eq_zero
    intro k _
    rw [Set.indicator_of_notMem (mt (iterate_mem_iff hD k x).1 hx)]

/-- Points where the Birkhoff sums of `h` are unbounded above. -/
def unbSet (T : X → X) (h : X → ℝ) : Set X :=
  {x | ∀ M : ℕ, ∃ n, (M : ℝ) < birkhoffSum T h n x}

lemma mem_unbSet (T : X → X) (h : X → ℝ) (x : X) :
    x ∈ unbSet T h ↔ ∀ M : ℕ, ∃ n, (M : ℝ) < birkhoffSum T h n x := Iff.rfl

lemma unbSet_invariant (T : X → X) (h : X → ℝ) : T ⁻¹' unbSet T h = unbSet T h := by
  ext x
  rw [Set.mem_preimage, mem_unbSet, mem_unbSet]
  constructor
  · intro H M
    obtain ⟨M', hM'⟩ := exists_nat_gt ((M : ℝ) - h x)
    obtain ⟨n, hn⟩ := H M'
    refine ⟨n + 1, ?_⟩
    rw [birkhoffSum_succ']
    linarith
  · intro H M
    obtain ⟨M', hM'⟩ := exists_nat_gt ((M : ℝ) + |h x|)
    obtain ⟨n', hn'⟩ := H M'
    rcases n' with _ | n
    · rw [birkhoffSum_zero] at hn'
      exact absurd hn' (not_lt.2 (Nat.cast_nonneg _))
    · refine ⟨n, ?_⟩
      rw [birkhoffSum_succ'] at hn'
      linarith [le_abs_self (h x)]

lemma measurableSet_unbSet {T : X → X} {h : X → ℝ} (hT : Measurable T) (hh : Measurable h) :
    MeasurableSet (unbSet T h) := by
  have e : unbSet T h = ⋂ M : ℕ, ⋃ n : ℕ, {x | (M : ℝ) < birkhoffSum T h n x} := by
    ext x; simp [unbSet]
  rw [e]
  exact MeasurableSet.iInter fun M => MeasurableSet.iUnion fun n =>
    measurableSet_lt measurable_const (measurable_birkhoffSum' hT hh n)

lemma upper_bound (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hgm : Measurable g) (hg : Integrable g μ)
    (hzero : ∀ s, MeasurableSet[MeasurableSpace.invariants T] s → ∫ x in s, g x ∂μ = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ x ∂μ, ∃ M : ℕ, ∀ n : ℕ, birkhoffSum T g n x - n * ε ≤ M := by
  let h : X → ℝ := fun x => g x - ε
  have hhm : Measurable h := hgm.sub measurable_const
  have hhi : Integrable h μ := hg.sub (integrable_const ε)
  have hDm : MeasurableSet (unbSet T h) := measurableSet_unbSet hT.measurable hhm
  have hDinv := unbSet_invariant T h
  have hDI : MeasurableSet[MeasurableSpace.invariants T] (unbSet T h) := ⟨hDm, hDinv⟩
  have hmax := maximal_ergodic μ hT (hhm.indicator hDm) (hhi.indicator hDm)
  have hset : {x | ∃ n, 0 < birkhoffSum T ((unbSet T h).indicator h) n x} = unbSet T h := by
    ext x
    constructor
    · rintro ⟨n, hn⟩
      rw [birkhoffSum_indicator hDinv] at hn
      by_contra hx
      rw [Set.indicator_of_notMem hx] at hn
      exact lt_irrefl _ hn
    · intro hx
      obtain ⟨n, hn⟩ := (mem_unbSet T h x).1 hx 0
      refine ⟨n, ?_⟩
      rw [birkhoffSum_indicator hDinv, Set.indicator_of_mem hx]
      exact_mod_cast hn
  rw [hset, setIntegral_indicator hDm, Set.inter_self] at hmax
  have e2 : ∫ x in unbSet T h, h x ∂μ = ∫ x in unbSet T h, g x ∂μ - μ.real (unbSet T h) * ε := by
    rw [integral_sub hg.integrableOn (integrable_const ε).integrableOn, setIntegral_const,
      smul_eq_mul]
  rw [e2, hzero _ hDI] at hmax
  have hr : μ.real (unbSet T h) = 0 := by
    have h0 : 0 ≤ μ.real (unbSet T h) := measureReal_nonneg
    have h1 : μ.real (unbSet T h) * ε ≤ 0 := by linarith
    by_contra hne
    have : 0 < μ.real (unbSet T h) * ε := mul_pos (lt_of_le_of_ne h0 (Ne.symm hne)) hε
    linarith
  have hμD : μ (unbSet T h) = 0 := (measureReal_eq_zero_iff (measure_ne_top μ _)).1 hr
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμD] with x hx
  rw [mem_unbSet] at hx
  push Not at hx
  obtain ⟨M, hM⟩ := hx
  refine ⟨M, fun n => ?_⟩
  have h1 := hM n
  have hs : birkhoffSum T h n x = birkhoffSum T g n x - n * ε := by
    simp [h, birkhoffSum, Finset.sum_sub_distrib]
  linarith

lemma eventually_le_of_bound {T : X → X} {g : X → ℝ} {x : X} {ε : ℝ} (hε : 0 < ε)
    (hb : ∃ M : ℕ, ∀ n : ℕ, birkhoffSum T g n x - n * ε ≤ M) :
    ∀ᶠ n in atTop, birkhoffAverage ℝ T g n x ≤ 2 * ε := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨N, hN⟩ := exists_nat_gt ((M : ℝ) / ε)
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnN : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have h1 : (M : ℝ) < N * ε := by rwa [div_lt_iff₀ hε] at hN
  have h2 : (N : ℝ) * ε ≤ n * ε := mul_le_mul_of_nonneg_right (by linarith) hε.le
  have h3 := hM n
  show (n : ℝ)⁻¹ • birkhoffSum T g n x ≤ 2 * ε
  rw [smul_eq_mul, inv_mul_le_iff₀ hnpos]
  linarith

lemma tendsto_zero (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hgm : Measurable g) (hg : Integrable g μ)
    (hzero : ∀ s, MeasurableSet[MeasurableSpace.invariants T] s → ∫ x in s, g x ∂μ = 0) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ T g n x) atTop (𝓝 0) := by
  have hzero' : ∀ s, MeasurableSet[MeasurableSpace.invariants T] s →
      ∫ x in s, (-g) x ∂μ = 0 := by
    intro s hs
    simp only [Pi.neg_apply]
    rw [integral_neg, hzero s hs, neg_zero]
  have hup : ∀ k : ℕ, ∀ᵐ x ∂μ, ∃ M : ℕ, ∀ n : ℕ,
      birkhoffSum T g n x - n * (1 / ((k : ℝ) + 1)) ≤ M :=
    fun k => upper_bound μ hT hgm hg hzero _ (by positivity)
  have hlo : ∀ k : ℕ, ∀ᵐ x ∂μ, ∃ M : ℕ, ∀ n : ℕ,
      birkhoffSum T (-g) n x - n * (1 / ((k : ℝ) + 1)) ≤ M :=
    fun k => upper_bound μ hT hgm.neg hg.neg hzero' _ (by positivity)
  rw [← ae_all_iff] at hup hlo
  filter_upwards [hup, hlo] with x hu hl
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < -a / 2 by linarith)
    filter_upwards [eventually_le_of_bound (by positivity) (hl k)] with n hn
    have hneg : birkhoffAverage ℝ T (-g) n x = -birkhoffAverage ℝ T g n x := by
      rw [birkhoffAverage_neg, Pi.neg_apply, Pi.neg_apply]
    rw [hneg] at hn
    linarith
  · intro b hb
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < b / 2 by linarith)
    filter_upwards [eventually_le_of_bound (by positivity) (hu k)] with n hn
    linarith

end Birkhoff1931Aux

open MeasureTheory Filter Topology in
theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (T : X → X) (hT : MeasurePreserving T μ μ) (f : X → ℝ)
    (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ T f n x) atTop
      (𝓝 (condExp (MeasurableSpace.invariants T) μ f x)) := by
  have hf'm : StronglyMeasurable (hf.1.mk f) := hf.1.stronglyMeasurable_mk
  have hff' : f =ᵐ[μ] hf.1.mk f := hf.1.ae_eq_mk
  have hf'i : Integrable (hf.1.mk f) μ := hf.congr hff'
  have hm : MeasurableSpace.invariants T ≤ ‹MeasurableSpace X› := MeasurableSpace.invariants_le T
  have hcm : StronglyMeasurable[MeasurableSpace.invariants T]
      (condExp (MeasurableSpace.invariants T) μ (hf.1.mk f)) := stronglyMeasurable_condExp
  have hcinv : condExp (MeasurableSpace.invariants T) μ (hf.1.mk f) ∘ T
      = condExp (MeasurableSpace.invariants T) μ (hf.1.mk f) :=
    MeasurableSpace.comp_eq_of_measurable_invariants hcm.measurable
  have hcM : Measurable (condExp (MeasurableSpace.invariants T) μ (hf.1.mk f)) :=
    (hcm.mono hm).measurable
  have hci : Integrable (condExp (MeasurableSpace.invariants T) μ (hf.1.mk f)) μ :=
    integrable_condExp
  have hgm : Measurable (hf.1.mk f - condExp (MeasurableSpace.invariants T) μ (hf.1.mk f)) :=
    hf'm.measurable.sub hcM
  have hgi : Integrable (hf.1.mk f - condExp (MeasurableSpace.invariants T) μ (hf.1.mk f)) μ :=
    hf'i.sub hci
  have hzero : ∀ s, MeasurableSet[MeasurableSpace.invariants T] s →
      ∫ x in s, (hf.1.mk f - condExp (MeasurableSpace.invariants T) μ (hf.1.mk f)) x ∂μ = 0 := by
    intro s hs
    simp only [Pi.sub_apply]
    rw [integral_sub hf'i.integrableOn hci.integrableOn, setIntegral_condExp hm hf'i hs, sub_self]
  have key := Birkhoff1931Aux.tendsto_zero μ hT hgm hgi hzero
  have hcc : condExp (MeasurableSpace.invariants T) μ f
      =ᵐ[μ] condExp (MeasurableSpace.invariants T) μ (hf.1.mk f) := condExp_congr_ae hff'
  have hA : ∀ᵐ x ∂μ, ∀ n : ℕ, birkhoffAverage ℝ T f n x = birkhoffAverage ℝ T (hf.1.mk f) n x := by
    rw [ae_all_iff]
    intro n
    exact hT.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ hff' n
  filter_upwards [key, hcc, hA] with x hx hcx hAx
  rw [hcx]
  have hev : ∀ᶠ n in atTop,
      birkhoffAverage ℝ T (hf.1.mk f - condExp (MeasurableSpace.invariants T) μ (hf.1.mk f)) n x
        + condExp (MeasurableSpace.invariants T) μ (hf.1.mk f) x
        = birkhoffAverage ℝ T f n x := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [hAx n, birkhoffAverage_sub, Pi.sub_apply, Pi.sub_apply,
      birkhoffAverage_of_comp_eq ℝ hcinv hn']
    ring
  have ht := hx.add (tendsto_const_nhds (x := condExp (MeasurableSpace.invariants T) μ (hf.1.mk f) x))
  rw [zero_add] at ht
  exact ht.congr' hev
