-- Prove2me | solution 1 for FastFashion.Structure.delta_hA_integral_formula
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:31:19.882991+00:00
-- url     : https://prove2.me/submissions/ed71eb95-4415-4ef7-a4df-89fc145f9728

import Mathlib
import Definitions.Def_FastFashion_Structure_Model

open MeasureTheory ProbabilityTheory

namespace Aux_FF_dhA_formula

open FastFashion.Structure

lemma hit {S Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam : S → ℝ}
    {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (s : S) (ω : Ω) (q q' : ℕ)
    (hqq : q ≤ q') (t' : ℝ) (ht0 : 0 ≤ t') (ht' : N s t' ω = q') :
    ∃ ts : ℝ, 0 ≤ ts ∧ N s ts ω = q ∧ ∀ t, 0 ≤ t → q ≤ N s t ω → ts ≤ t := by
  set U : Set ℝ := {t | 0 ≤ t ∧ q ≤ N s t ω} with hU
  have hne : U.Nonempty := ⟨t', ht0, ht' ▸ hqq⟩
  have hbdd : BddBelow U := ⟨0, fun t ht => ht.1⟩
  have h0 : 0 ≤ sInf U := le_csInf hne (fun t ht => ht.1)
  have hlow : ∀ t, 0 ≤ t → q ≤ N s t ω → sInf U ≤ t := fun t h1 h2 => csInf_le hbdd ⟨h1, h2⟩
  refine ⟨sInf U, h0, le_antisymm ?_ ?_, hlow⟩
  · -- upper bound via unit jumps
    rcases eq_or_lt_of_le h0 with h | h
    · rw [← h, hN.zero]; exact Nat.zero_le _
    · obtain ⟨u, hu, hj⟩ := hN.unitJumps s ω (sInf U) h
      set v := (max u 0 + sInf U) / 2
      have hv1 : u < v := by
        have := le_max_left u 0
        have : max u 0 < sInf U := max_lt hu h
        simp only [v]; linarith
      have hv2 : v < sInf U := by
        have : max u 0 < sInf U := max_lt hu h
        simp only [v]; linarith
      have hv0 : 0 ≤ v := by
        have := le_max_right u 0
        simp only [v]; linarith
      have hlt : N s v ω < q := by
        by_contra hc
        push_neg at hc
        have := hlow v hv0 hc
        linarith
      have := hj v hv1 hv2
      omega
  · -- lower bound via right continuity
    have hc := hN.rightContinuous s ω (sInf U) h0
    have hev : ∀ᶠ u in nhdsWithin (sInf U) (Set.Ici (sInf U)), N s u ω = N s (sInf U) ω := by
      have := hc.tendsto
      rw [nhds_discrete, Filter.tendsto_pure] at this
      exact this
    obtain ⟨ε, hε, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).1 hev
    obtain ⟨u, ⟨hu0, huq⟩, hult⟩ := exists_lt_of_csInf_lt hne (Set.mem_Ioi.1 hε)
    have hge : sInf U ≤ u := csInf_le hbdd ⟨hu0, huq⟩
    have := hsub ⟨hge, hult⟩
    simp only [Set.mem_setOf_eq] at this
    omega

lemma stock_mono {S Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam : S → ℝ}
    {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (s : S) (ω : Ω) :
    Monotone (fun n : ℕ => stockoutTime N s (fun _ => n) ω) := by
  intro q q' hqq
  simp only [stockoutTime]
  split_ifs with h1 h2 h2
  · obtain ⟨t', ht0, ht'⟩ := h2
    obtain ⟨ts, hts0, htsq, hts⟩ := hit hN s ω q q' hqq t' ht0 ht'
    have hb1 : BddBelow {t : ℝ | 0 ≤ t ∧ N s t ω = q} := ⟨0, fun t ht => ht.1⟩
    apply WithTop.coe_le_coe.2
    calc sInf {t : ℝ | 0 ≤ t ∧ N s t ω = q} ≤ ts := csInf_le hb1 ⟨hts0, htsq⟩
      _ ≤ sInf {t : ℝ | 0 ≤ t ∧ N s t ω = q'} :=
          le_csInf ⟨t', ht0, ht'⟩ (fun t ht => hts t ht.1 (ht.2 ▸ hqq))
  · exact le_top
  · exfalso
    obtain ⟨t', ht0, ht'⟩ := h2
    obtain ⟨ts, hts0, htsq, _⟩ := hit hN s ω q q' hqq t' ht0 ht'
    exact h1 ⟨ts, hts0, htsq⟩
  · exact le_top

lemma stock_eq {S Ω : Type*} (N : S → ℝ → Ω → ℕ) (s : S) (q : S → ℕ) (ω : Ω) :
    stockoutTime N s q ω = stockoutTime N s (fun _ => q s) ω := rfl

lemma stop_coe {S Ω : Type*} (N : S → ℝ → Ω → ℕ) (A : Finset S) (q : S → ℕ) (T : ℝ) (ω : Ω) :
    ((stopMin N A q T ω : ℝ) : WithTop ℝ) = min (tauMin N A q ω) (T : WithTop ℝ) := by
  unfold stopMin
  cases h : tauMin N A q ω with
  | top => simp
  | coe t => simp [WithTop.coe_min]


lemma stock_mono' {S Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam : S → ℝ}
    {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (s : S) (ω : Ω) {q q' : S → ℕ}
    (h : q s ≤ q' s) : stockoutTime N s q ω ≤ stockoutTime N s q' ω := by
  rw [stock_eq N s q, stock_eq N s q']
  exact stock_mono hN s ω h

lemma stock_nonneg {S Ω : Type*} (N : S → ℝ → Ω → ℕ) (s : S) (q : S → ℕ) (ω : Ω) :
    (0 : WithTop ℝ) ≤ stockoutTime N s q ω := by
  unfold stockoutTime
  split_ifs with h
  · exact WithTop.coe_le_coe.2 (le_csInf h (fun t ht => ht.1))
  · exact le_top

lemma tau_nonneg {S Ω : Type*} (N : S → ℝ → Ω → ℕ) (A : Finset S) (q : S → ℕ) (ω : Ω) :
    (0 : WithTop ℝ) ≤ tauMin N A q ω :=
  Finset.le_inf (fun s _ => stock_nonneg N s q ω)

lemma tau_mono {S Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam : S → ℝ}
    {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (A : Finset S) (ω : Ω) {q q' : S → ℕ}
    (h : q ≤ q') : tauMin N A q ω ≤ tauMin N A q' ω :=
  Finset.inf_mono_fun (fun s _ => stock_mono' hN s ω (h s))

lemma stop_mono {S Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam : S → ℝ}
    {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (A : Finset S) (T : ℝ) (ω : Ω)
    {q q' : S → ℕ} (h : q ≤ q') : stopMin N A q T ω ≤ stopMin N A q' T ω := by
  have : ((stopMin N A q T ω : ℝ) : WithTop ℝ) ≤ ((stopMin N A q' T ω : ℝ) : WithTop ℝ) := by
    rw [stop_coe, stop_coe]
    exact min_le_min_right _ (tau_mono hN A ω h)
  exact WithTop.coe_le_coe.1 this

lemma stop_nonneg {S Ω : Type*} (N : S → ℝ → Ω → ℕ) (A : Finset S) (q : S → ℕ) (T : ℝ)
    (ω : Ω) (hT : 0 ≤ T) : 0 ≤ stopMin N A q T ω := by
  have : ((0 : ℝ) : WithTop ℝ) ≤ ((stopMin N A q T ω : ℝ) : WithTop ℝ) := by
    rw [stop_coe]
    exact le_min (tau_nonneg N A q ω) (WithTop.coe_le_coe.2 hT)
  exact WithTop.coe_le_coe.1 this

lemma stop_le {S Ω : Type*} (N : S → ℝ → Ω → ℕ) (A : Finset S) (q : S → ℕ) (T : ℝ)
    (ω : Ω) : stopMin N A q T ω ≤ T := by
  have : ((stopMin N A q T ω : ℝ) : WithTop ℝ) ≤ ((T : ℝ) : WithTop ℝ) := by
    rw [stop_coe]; exact min_le_right _ _
  exact WithTop.coe_le_coe.1 this

lemma stop_neg {S Ω : Type*} (N : S → ℝ → Ω → ℕ) (A : Finset S) (q : S → ℕ) (T : ℝ)
    (ω : Ω) (hT : T < 0) : stopMin N A q T ω = T := by
  have : ((stopMin N A q T ω : ℝ) : WithTop ℝ) = ((T : ℝ) : WithTop ℝ) := by
    rw [stop_coe]
    apply min_eq_right
    exact le_trans (WithTop.coe_le_coe.2 hT.le) (tau_nonneg N A q ω)
  exact WithTop.coe_injective this

lemma N_stop_mono {S Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam : S → ℝ}
    {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (A : Finset S) (T : ℝ) (ω : Ω)
    (s : S) {q q' : S → ℕ} (h : q ≤ q') :
    N s (stopMin N A q T ω) ω ≤ N s (stopMin N A q' T ω) ω := by
  rcases lt_or_ge T 0 with hT | hT
  · rw [stop_neg N A q T ω hT, stop_neg N A q' T ω hT]
  · exact hN.mono s ω (stop_nonneg N A q T ω hT) (stop_mono hN A T ω h)

lemma stock_le_iff {S Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam : S → ℝ}
    {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (s : S) (q : S → ℕ) (ω : Ω) (x : ℝ) :
    stockoutTime N s q ω ≤ ((x : ℝ) : WithTop ℝ) ↔ (0 ≤ x ∧ q s ≤ N s x ω) := by
  have hbdd : BddBelow {t : ℝ | 0 ≤ t ∧ N s t ω = q s} := ⟨0, fun t ht => ht.1⟩
  constructor
  · intro h
    have hx : 0 ≤ x := WithTop.coe_le_coe.1 ((stock_nonneg N s q ω).trans h)
    refine ⟨hx, ?_⟩
    unfold stockoutTime at h
    split_ifs at h with hne
    · obtain ⟨t', ht0, ht'⟩ := hne
      obtain ⟨ts, hts0, htsq, hts⟩ := hit hN s ω (q s) (q s) le_rfl t' ht0 ht'
      have h1 : ts ≤ sInf {t : ℝ | 0 ≤ t ∧ N s t ω = q s} :=
        le_csInf ⟨t', ht0, ht'⟩ (fun t ht => hts t ht.1 ht.2.ge)
      have h2 : sInf {t : ℝ | 0 ≤ t ∧ N s t ω = q s} ≤ x := WithTop.coe_le_coe.1 h
      have := hN.mono s ω hts0 (h1.trans h2)
      omega
    · exact absurd h (by simp)
  · rintro ⟨hx, hq⟩
    obtain ⟨ts, hts0, htsq, hts⟩ := hit hN s ω (q s) (N s x ω) hq x hx rfl
    have hne : {t : ℝ | 0 ≤ t ∧ N s t ω = q s}.Nonempty := ⟨ts, hts0, htsq⟩
    unfold stockoutTime
    rw [if_pos hne]
    exact WithTop.coe_le_coe.2 ((csInf_le hbdd ⟨hts0, htsq⟩).trans (hts x hx hq))

lemma stop_le_iff {S Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam : S → ℝ}
    {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (A : Finset S) (q : S → ℕ) (T : ℝ)
    (ω : Ω) (x : ℝ) :
    stopMin N A q T ω ≤ x ↔ (T ≤ x ∨ ∃ s ∈ A, (0 ≤ x ∧ q s ≤ N s x ω)) := by
  rw [← WithTop.coe_le_coe, stop_coe, min_le_iff, WithTop.coe_le_coe, or_comm]
  apply or_congr_right
  unfold tauMin
  rw [Finset.inf_le_iff (WithTop.coe_lt_top x)]
  simp only [stock_le_iff hN]

lemma stop_measurable {S Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam : S → ℝ}
    {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (A : Finset S) (q : S → ℕ) (T : ℝ) :
    Measurable (fun ω => stopMin N A q T ω) := by
  apply measurable_of_Iic
  intro x
  have : (fun ω => stopMin N A q T ω) ⁻¹' Set.Iic x =
      {ω | T ≤ x} ∪ ⋃ s ∈ A, {ω | 0 ≤ x ∧ q s ≤ N s x ω} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion,
      exists_prop]
    exact stop_le_iff hN A q T ω x
  rw [this]
  apply MeasurableSet.union (MeasurableSet.const _)
  apply Finset.measurableSet_biUnion
  intro s _
  by_cases hx : 0 ≤ x
  · simp only [hx, true_and]
    exact (hN.measurable s x hx) (measurableSet_Ici (a := q s))
  · simp only [hx, false_and, Set.setOf_false, MeasurableSet.empty]

lemma stop_integrable {S Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {lam : S → ℝ} {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (A : Finset S)
    (q : S → ℕ) (T : ℝ) (hT : 0 ≤ T) : Integrable (fun ω => stopMin N A q T ω) P := by
  apply Integrable.of_bound (stop_measurable hN A q T).aestronglyMeasurable T
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [stop_nonneg N A q T ω hT], stop_le N A q T ω⟩

lemma stock_congr {S Ω : Type*} (N : S → ℝ → Ω → ℕ) (s : S) {q q' : S → ℕ} (ω : Ω)
    (h : q s = q' s) : stockoutTime N s q ω = stockoutTime N s q' ω := by
  rw [stock_eq N s q, stock_eq N s q', h]

lemma tau_congr {S Ω : Type*} (N : S → ℝ → Ω → ℕ) (A : Finset S) {q q' : S → ℕ} (ω : Ω)
    (h : ∀ s ∈ A, q s = q' s) : tauMin N A q ω = tauMin N A q' ω :=
  Finset.inf_congr rfl (fun s hs => stock_congr N s ω (h s hs))

lemma hA_congr {S Ω : Type*} [MeasurableSpace Ω] (N : S → ℝ → Ω → ℕ) (P : Measure Ω) (T : ℝ)
    (A : Finset S) {q q' : S → ℕ} (h : ∀ s ∈ A, q s = q' s) : hA N P T A q = hA N P T A q' := by
  unfold hA
  congr 1
  funext ω
  unfold stopMin
  rw [tau_congr N A ω h]

lemma delta_zero {S Ω : Type*} [DecidableEq S] [MeasurableSpace Ω] (N : S → ℝ → Ω → ℕ)
    (P : Measure Ω) (T : ℝ) (A : Finset S) (q : S → ℕ) (s : S) (hs : s ∉ A) :
    delta (hA N P T A) s q = 0 := by
  unfold delta
  rw [hA_congr N P T A (q := q + Pi.single s 1) (q' := q)]
  · ring
  · intro s' hs'
    have : s' ≠ s := fun h => hs (h ▸ hs')
    simp [Pi.single_apply, this]

lemma lt_stock_iff {S Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam : S → ℝ}
    {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (s : S) (q : S → ℕ) (ω : Ω) {t : ℝ}
    (ht : 0 ≤ t) : ((t : ℝ) : WithTop ℝ) < stockoutTime N s q ω ↔ N s t ω < q s := by
  rw [← not_le, stock_le_iff hN]
  simp [ht]

lemma comap_le_M {S Ω : Type*} [MeasurableSpace Ω] (N : S → ℝ → Ω → ℕ) (s : S) {t : ℝ}
    (ht : 0 ≤ t) : MeasurableSpace.comap (N s t) inferInstance ≤
      ⨆ (t : ℝ) (_ : 0 ≤ t), MeasurableSpace.comap (N s t) inferInstance :=
  le_iSup₂ (f := fun (t : ℝ) (_ : 0 ≤ t) => MeasurableSpace.comap (N s t) inferInstance) t ht

lemma measM {S Ω : Type*} [MeasurableSpace Ω] (N : S → ℝ → Ω → ℕ) (s : S) {t : ℝ}
    (ht : 0 ≤ t) (B : Set ℕ) :
    MeasurableSet[⨆ (t : ℝ) (_ : 0 ≤ t), MeasurableSpace.comap (N s t) inferInstance]
      {ω | N s t ω ∈ B} :=
  comap_le_M N s ht _ ⟨B, (Set.to_countable B).measurableSet, rfl⟩

lemma M_le {S Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam : S → ℝ}
    {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (s : S) :
    (⨆ (t : ℝ) (_ : 0 ≤ t), MeasurableSpace.comap (N s t) inferInstance) ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun t ht => (hN.measurable s t ht).comap_le

lemma prob_tau_gt {S Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam : S → ℝ}
    {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (B : Finset S) (q : S → ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    (P {ω | ((t : ℝ) : WithTop ℝ) < tauMin N B q ω}).toReal =
      ∏ s' ∈ B, (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s' q ω}).toReal := by
  have hset : {ω | ((t : ℝ) : WithTop ℝ) < tauMin N B q ω} =
      ⋂ s' ∈ B, {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s' q ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, tauMin]
    exact Finset.lt_inf_iff (WithTop.coe_lt_top t)
  rw [hset, hN.indepSizes.meas_biInter, ENNReal.toReal_prod]
  intro s' _
  have : {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s' q ω} = {ω | N s' t ω ∈ Set.Iio (q s')} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_Iio]
    exact lt_stock_iff hN s' q ω ht
  rw [this]
  exact measM N s' ht _

lemma antitone_prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f : Ω → WithTop ℝ) :
    Antitone (fun t : ℝ => (P {ω | ((t : ℝ) : WithTop ℝ) < f ω}).toReal) := by
  intro a b hab
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  exact lt_of_le_of_lt (WithTop.coe_le_coe.2 hab) hω

lemma hA_layer {S Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {lam : S → ℝ} {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (A : Finset S)
    (q : S → ℕ) {T : ℝ} (hT : 0 < T) :
    hA N P T A q = ∫ t in (0)..T, (P {ω | ((t : ℝ) : WithTop ℝ) < tauMin N A q ω}).toReal := by
  unfold hA
  rw [(stop_integrable hN A q T hT.le).integral_eq_integral_meas_lt
    (Filter.Eventually.of_forall (fun ω => stop_nonneg N A q T ω hT.le))]
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (t := Set.Ioi (0:ℝ)) (s := Set.Ioc 0 T)
    nullMeasurableSet_Ioi Set.Ioc_subset_Ioi_self ?_]
  · rw [intervalIntegral.integral_of_le hT.le, integral_Ioc_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    simp only [measureReal_def]
    congr 2
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [← WithTop.coe_lt_coe, stop_coe, lt_min_iff]
    simp [ht.2]
  · apply Filter.Eventually.of_forall
    intro t ht
    have htT : T < t := by
      simp only [Set.mem_diff, Set.mem_Ioi, Set.mem_Ioc, not_and, not_le] at ht
      exact ht.2 ht.1
    have : {ω | t < stopMin N A q T ω} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact (stop_le N A q T ω).trans htT.le
    rw [this, measureReal_def, measure_empty, ENNReal.toReal_zero]

lemma eq_one {S Ω : Type*} [DecidableEq S] [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {lam : S → ℝ} {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P)
    {T : ℝ} (hT : 0 < T) (A : Finset S) (q : S → ℕ) (s : S) (hs : s ∈ A) :
    delta (hA N P T A) s q =
        ∫ t in (0)..T,
          ((P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s (q + Pi.single s 1) ω}).toReal
            - (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s q ω}).toReal)
          * ∏ s' ∈ A.erase s, (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s' q ω}).toReal := by
  unfold delta
  rw [hA_layer hN A _ hT, hA_layer hN A _ hT,
    ← intervalIntegral.integral_sub ((antitone_prob P _).intervalIntegrable)
      ((antitone_prob P _).intervalIntegrable)]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hT.le] at ht
  simp only
  rw [prob_tau_gt hN A _ ht.1, prob_tau_gt hN A _ ht.1, ← Finset.mul_prod_erase A _ hs,
    ← Finset.mul_prod_erase A _ hs]
  have : ∏ s' ∈ A.erase s,
      (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s' (q + Pi.single s 1) ω}).toReal =
      ∏ s' ∈ A.erase s, (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s' q ω}).toReal := by
    apply Finset.prod_congr rfl
    intro s' hs'
    have hne := Finset.ne_of_mem_erase hs'
    congr 2
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [stock_congr N s' ω (q' := q) (by simp [Pi.single_apply, hne])]
  rw [this]
  ring

lemma eq_two {S Ω : Type*} [DecidableEq S] [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {lam : S → ℝ} {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P)
    {T : ℝ} (hT : 0 < T) (A : Finset S) (q : S → ℕ) (s : S) :
    (∫ t in (0)..T,
          ((P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s (q + Pi.single s 1) ω}).toReal
            - (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s q ω}).toReal)
          * ∏ s' ∈ A.erase s, (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s' q ω}).toReal) =
        ∫ t in (0)..T,
          (P {ω | N s t ω = q s}).toReal
          * ∏ s' ∈ A.erase s, (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s' q ω}).toReal := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hT.le] at ht
  simp only
  congr 1
  have h1 : {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s (q + Pi.single s 1) ω} =
      {ω | N s t ω < q s} ∪ {ω | N s t ω = q s} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union]
    rw [lt_stock_iff hN s _ ω ht.1]
    simp only [Pi.add_apply, Pi.single_eq_same]
    omega
  have h2 : {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s q ω} = {ω | N s t ω < q s} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    exact lt_stock_iff hN s _ ω ht.1
  have hmeas : MeasurableSet {ω | N s t ω = q s} :=
    (hN.measurable s t ht.1) (measurableSet_singleton (q s))
  rw [h1, h2, measure_union _ hmeas, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  · ring
  · rw [Set.disjoint_left]
    intro ω h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    omega

lemma pois_pt {S Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam : S → ℝ}
    {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (s : S) (hl : 0 < lam s) {t : ℝ}
    (ht : 0 ≤ t) (j : ℕ) :
    (P {ω | N s t ω = j}).toReal = Real.exp (-(lam s * t)) * (lam s * t) ^ j / (j.factorial) := by
  have hmap := hN.incrementLaw s 0 t le_rfl ht
  have hf : (fun ω => N s t ω - N s 0 ω) = N s t := funext fun ω => by simp [hN.zero]
  rw [hf, sub_zero] at hmap
  have : P {ω | N s t ω = j} = P.map (N s t) {j} := by
    rw [Measure.map_apply (hN.measurable s t ht) (measurableSet_singleton j)]; rfl
  rw [this, hmap, poissonMeasure_singleton, ENNReal.toReal_ofReal (by positivity),
    Real.coe_toNNReal _ (by positivity)]

/-- Poisson probability term. -/
noncomputable def pterm (l : ℝ) (j : ℕ) (x : ℝ) : ℝ := Real.exp (-(l * x)) * (l * x) ^ j / (j.factorial)

lemma pterm_cont (l : ℝ) (j : ℕ) : Continuous (pterm l j) := by
  unfold pterm; fun_prop

lemma hasDerivAt_psum (l : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y => ∑ j ∈ Finset.range (k + 1), pterm l j y) (-(l * pterm l k x)) x := by
  have h0 : HasDerivAt (fun y => l * y) l x := by simpa using (hasDerivAt_id x).const_mul l
  have h1 : HasDerivAt (fun y => -(l * y)) (-l) x := h0.neg
  have he := h1.exp
  induction k with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pterm, pow_zero, mul_one,
      Nat.factorial_zero, Nat.cast_one, div_one]
    convert he using 1
    ring
  | succ k ih =>
    have hsum : (fun y => ∑ j ∈ Finset.range (k + 1 + 1), pterm l j y) =
        fun y => (∑ j ∈ Finset.range (k + 1), pterm l j y) + pterm l (k + 1) y := by
      funext y; rw [Finset.sum_range_succ]
    rw [hsum]
    have h2 : HasDerivAt (pterm l (k + 1))
        (-(l * pterm l (k + 1) x) + l * pterm l k x) x := by
      have hp := h0.pow (k + 1)
      have h3 : HasDerivAt (pterm l (k + 1)) _ x :=
        (he.mul hp).div_const (((k + 1).factorial : ℕ) : ℝ)
      refine h3.congr_deriv ?_
      simp only [Pi.pow_apply, Nat.add_sub_cancel, pterm, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_succ]
      have : (k.factorial : ℝ) ≠ 0 := by positivity
      field_simp
    exact (ih.add h2).congr_deriv (by ring)

lemma one_sub_psum (l : ℝ) (k : ℕ) {y : ℝ} :
    1 - ∑ j ∈ Finset.range (k + 1), pterm l j y = ∫ t in (0)..y, l * pterm l k t := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y => -∑ j ∈ Finset.range (k + 1), pterm l j y) (f' := fun t => l * pterm l k t)
    (fun x _ => by have := (hasDerivAt_psum l k x).neg; rw [neg_neg] at this; exact this)
    ((continuous_const.mul (pterm_cont l k)).intervalIntegrable _ _)]
  have h0 : ∑ j ∈ Finset.range (k + 1), pterm l j 0 = 1 := by
    rw [Finset.sum_range_succ']
    simp [pterm]
  simp only [h0]
  ring

lemma cdf_stock {S Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {lam : S → ℝ} {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (s : S) (hl : 0 < lam s)
    (q : S → ℕ) (k : ℕ) (hk : q s = k + 1) {y : ℝ} (hy : 0 ≤ y) :
    (P {ω | stockoutTime N s q ω ≤ ((y : ℝ) : WithTop ℝ)}).toReal =
      ∫ t in (0)..y, lam s * pterm (lam s) k t := by
  rw [← one_sub_psum]
  have hset : {ω | stockoutTime N s q ω ≤ ((y : ℝ) : WithTop ℝ)} =
      (⋃ j ∈ Finset.range (k + 1), {ω | N s y ω = j})ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, Finset.mem_range,
      exists_prop, not_exists, not_and]
    rw [stock_le_iff hN, hk]
    constructor
    · rintro ⟨_, h⟩ j hj hj'; omega
    · intro h; refine ⟨hy, ?_⟩
      by_contra hc; exact h _ (by omega) rfl
  have hm : ∀ j ∈ Finset.range (k + 1), MeasurableSet {ω | N s y ω = j} :=
    fun j _ => (hN.measurable s y hy) (measurableSet_singleton j)
  have hd : (↑(Finset.range (k + 1)) : Set ℕ).PairwiseDisjoint fun b => {ω | N s y ω = b} := by
    intro i _ j _ hij
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro ω h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    exact hij (h1.symm.trans h2)
  rw [hset, prob_compl_eq_one_sub (Finset.measurableSet_biUnion _ hm),
    measure_biUnion_finset hd hm, ENNReal.toReal_sub_of_le, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_one]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [pois_pt hN s hl hy j]; rfl
  · intro j _; exact measure_ne_top _ _
  · rw [← measure_biUnion_finset hd hm]; exact prob_le_one
  · exact ENNReal.one_ne_top

lemma stop_meas_sup {S Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam : S → ℝ}
    {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (B : Finset S) (q : S → ℕ) (T' : ℝ) :
    Measurable[⨆ i ∈ (B : Set S), ⨆ (t : ℝ) (_ : 0 ≤ t),
      MeasurableSpace.comap (N i t) inferInstance] (fun ω => stopMin N B q T' ω) := by
  apply measurable_of_Iic
  intro x
  have : (fun ω => stopMin N B q T' ω) ⁻¹' Set.Iic x =
      {ω | T' ≤ x} ∪ ⋃ s ∈ B, {ω | 0 ≤ x ∧ q s ≤ N s x ω} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion,
      exists_prop]
    exact stop_le_iff hN B q T' ω x
  rw [this]
  apply MeasurableSet.union (MeasurableSet.const _)
  apply Finset.measurableSet_biUnion
  intro s hs
  by_cases hx : 0 ≤ x
  · simp only [hx, true_and]
    have h := measM N s hx (Set.Ici (q s))
    exact (le_iSup₂ (f := fun i (_ : i ∈ (B : Set S)) => ⨆ (t : ℝ) (_ : 0 ≤ t),
      MeasurableSpace.comap (N i t) inferInstance) s (Finset.mem_coe.2 hs)) _ h
  · simp only [hx, false_and, Set.setOf_false, MeasurableSet.empty]

lemma eq_three {S Ω : Type*} [DecidableEq S] [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {lam : S → ℝ} {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P)
    (hlam : ∀ s, 0 < lam s) {T : ℝ} (hT : 0 < T) (A : Finset S) (q : S → ℕ) (s : S) :
    (∫ t in (0)..T,
          (P {ω | N s t ω = q s}).toReal
          * ∏ s' ∈ A.erase s, (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s' q ω}).toReal) =
        (1 / lam s) *
          (P {ω | stockoutTime N s (q + Pi.single s 1) ω
                    ≤ min (tauMin N (A.erase s) q ω) ((T : ℝ) : WithTop ℝ)}).toReal := by
  have hl : 0 < lam s := hlam s
  have hq1 : (q + Pi.single s 1 : S → ℕ) s = q s + 1 := by simp
  set X : Ω → ℝ := fun ω => stopMin N {s} (q + Pi.single s 1) (T + 1) ω with hX_def
  set Y : Ω → ℝ := fun ω => stopMin N (A.erase s) q T ω with hY_def
  set G : ℝ → ℝ := fun t => (P {ω | ((t : ℝ) : WithTop ℝ) < tauMin N (A.erase s) q ω}).toReal
    with hG_def
  set f : ℝ → ℝ := fun t => lam s * pterm (lam s) (q s) t with hf_def
  have hXm : Measurable X := stop_measurable hN _ _ _
  have hYm : Measurable Y := stop_measurable hN _ _ _
  have hfc : Continuous f := continuous_const.mul (pterm_cont _ _)
  have hf0 : ∀ x, 0 < x → 0 ≤ f x := by
    intro x hx
    have := mul_pos hl hx
    simp only [f, pterm]
    exact mul_nonneg hl.le (div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg this.le _))
      (Nat.cast_nonneg _))
  -- the event
  have hE : {ω | stockoutTime N s (q + Pi.single s 1) ω
      ≤ min (tauMin N (A.erase s) q ω) ((T : ℝ) : WithTop ℝ)} = {ω | X ω ≤ Y ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, X, Y]
    have e : stopMin N {s} (q + Pi.single s 1) (T + 1) ω ≤ stopMin N (A.erase s) q T ω ↔
        ((stopMin N {s} (q + Pi.single s 1) (T + 1) ω : ℝ) : WithTop ℝ) ≤
          ((stopMin N (A.erase s) q T ω : ℝ) : WithTop ℝ) := WithTop.coe_le_coe.symm
    rw [e, stop_coe, stop_coe]
    have hsing : tauMin N {s} (q + Pi.single s 1) ω = stockoutTime N s (q + Pi.single s 1) ω := by
      simp [tauMin]
    rw [hsing]
    have hTT : min (tauMin N (A.erase s) q ω) ((T : ℝ) : WithTop ℝ) < ((T + 1 : ℝ) : WithTop ℝ) :=
      lt_of_le_of_lt (min_le_right _ _) (WithTop.coe_lt_coe.2 (by linarith))
    constructor
    · intro h; exact (min_le_left _ _).trans h
    · intro h
      rcases le_total (stockoutTime N s (q + Pi.single s 1) ω) ((T + 1 : ℝ) : WithTop ℝ) with h1 | h1
      · rwa [min_eq_left h1] at h
      · rw [min_eq_right h1] at h; exact absurd (lt_of_le_of_lt h hTT) (lt_irrefl _)
  -- independence
  have hind : IndepFun X Y P := by
    rw [IndepFun_iff_Indep]
    have h := indep_iSup_of_disjoint (fun i => M_le hN i) hN.indepSizes
      (S := (({s} : Finset S) : Set S)) (T := (((A.erase s) : Finset S) : Set S))
      (Finset.disjoint_coe.2 (Finset.disjoint_singleton_left.2 (Finset.notMem_erase s A)))
    exact indep_of_indep_of_le_right
      (indep_of_indep_of_le_left h (stop_meas_sup hN _ _ _).comap_le)
      (stop_meas_sup hN _ _ _).comap_le
  -- product formula
  have hprod : P {ω | X ω ≤ Y ω} = ∫⁻ x, (P.map Y) (Set.Ici x) ∂(P.map X) := by
    have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
      measurableSet_le measurable_fst measurable_snd
    have : P {ω | X ω ≤ Y ω} = P.map (fun ω => (X ω, Y ω)) {p : ℝ × ℝ | p.1 ≤ p.2} := by
      rw [Measure.map_apply (hXm.prodMk hYm) hmeas]; rfl
    rw [this, (indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable hYm.aemeasurable).1 hind,
      Measure.prod_apply hmeas]
    rfl
  have hh : ∀ x, (P.map Y) (Set.Ici x) = P {ω | x ≤ Y ω} := fun x => by
    rw [Measure.map_apply hYm measurableSet_Ici]; rfl
  have hhm : Measurable (fun x => (P.map Y) (Set.Ici x)) :=
    Antitone.measurable (fun a b hab => measure_mono (Set.Ici_subset_Ici.2 hab))
  have hres : ∫⁻ x, (P.map Y) (Set.Ici x) ∂(P.map X) =
      ∫⁻ x in Set.Iic T, (P.map Y) (Set.Ici x) ∂(P.map X) := by
    rw [← lintegral_add_compl _ (measurableSet_Iic (a := T))]
    have : ∫⁻ x in (Set.Iic T)ᶜ, (P.map Y) (Set.Ici x) ∂(P.map X) = 0 := by
      rw [setLIntegral_congr_fun measurableSet_Iic.compl (g := fun _ => 0) ?_]
      · simp
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_Iic, not_le] at hx
      show (P.map Y) (Set.Ici x) = 0
      rw [hh]
      have : {ω | x ≤ Y ω} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
        exact lt_of_le_of_lt (stop_le N (A.erase s) q T ω) hx
      rw [this, measure_empty]
    rw [this, add_zero]
  -- density measure
  set dens : ℝ → ENNReal := fun t => ENNReal.ofReal ((Set.Ioi (0 : ℝ)).indicator f t) with hdens
  have hdm : Measurable dens :=
    ENNReal.measurable_ofReal.comp (hfc.measurable.indicator measurableSet_Ioi)
  have hdensind : ∀ b, (Set.Iic b).indicator dens =
      (Set.Ioc 0 b).indicator (fun x => ENNReal.ofReal (f x)) := by
    intro b
    funext x
    by_cases h1 : 0 < x
    · by_cases h2 : x ≤ b
      · simp [Set.indicator_apply, dens, h1, h2]
      · simp [Set.indicator_apply, dens, h1, h2]
    · simp [Set.indicator_apply, dens, h1]
  have hfint : ∀ b, IntegrableOn f (Set.Ioc 0 b) :=
    fun b => (hfc.integrableOn_Icc (a := 0) (b := b)).mono_set Set.Ioc_subset_Icc_self
  have hext : (P.map X).restrict (Set.Iic T) = (volume.withDensity dens).restrict (Set.Iic T) := by
    apply Measure.ext_of_Iic
    intro a
    rw [Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply measurableSet_Iic,
      Set.Iic_inter_Iic, withDensity_apply _ measurableSet_Iic,
      Measure.map_apply hXm measurableSet_Iic, ← lintegral_indicator measurableSet_Iic,
      hdensind, lintegral_indicator measurableSet_Ioc,
      ← ofReal_integral_eq_lintegral_ofReal (hfint _)
        (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => hf0 x hx.1))]
    have hbT : a ⊓ T ≤ T := inf_le_right
    rcases lt_or_ge (a ⊓ T) 0 with hb | hb
    · have : X ⁻¹' Set.Iic (a ⊓ T) = ∅ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_le, X]
        exact lt_of_lt_of_le hb (stop_nonneg N _ _ _ ω (by linarith))
      rw [this, measure_empty, Set.Ioc_eq_empty (by linarith), Measure.restrict_empty,
        integral_zero_measure, ENNReal.ofReal_zero]
    · have : X ⁻¹' Set.Iic (a ⊓ T) =
          {ω | stockoutTime N s (q + Pi.single s 1) ω ≤ ((a ⊓ T : ℝ) : WithTop ℝ)} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq, X]
        rw [← WithTop.coe_le_coe, stop_coe, min_le_iff, WithTop.coe_le_coe]
        have hsing : tauMin N {s} (q + Pi.single s 1) ω =
            stockoutTime N s (q + Pi.single s 1) ω := by simp [tauMin]
        rw [hsing]
        have : ¬ (T + 1 ≤ a ⊓ T) := by linarith
        simp [this]
      rw [this, ← ENNReal.ofReal_toReal (measure_ne_top _ _),
        cdf_stock hN s hl (q + Pi.single s 1) (q s) hq1 hb, intervalIntegral.integral_of_le hb]
  have hden : ∫⁻ x in Set.Iic T, (P.map Y) (Set.Ici x) ∂(P.map X) =
      ∫⁻ x in Set.Iic T, dens x * (P.map Y) (Set.Ici x) := by
    rw [hext, restrict_withDensity measurableSet_Iic,
      lintegral_withDensity_eq_lintegral_mul _ hdm hhm]
    rfl
  have hioo : ∫⁻ x in Set.Iic T, dens x * (P.map Y) (Set.Ici x) =
      ∫⁻ x in Set.Ioo 0 T, ENNReal.ofReal (f x * G x) := by
    rw [← lintegral_indicator measurableSet_Iic]
    have : (Set.Iic T).indicator (fun x => dens x * (P.map Y) (Set.Ici x)) =
        (Set.Ioc 0 T).indicator (fun x => dens x * (P.map Y) (Set.Ici x)) := by
      funext x
      by_cases h1 : 0 < x
      · by_cases h2 : x ≤ T
        · simp [Set.indicator_apply, h1, h2]
        · simp [Set.indicator_apply, h1, h2]
      · simp [Set.indicator_apply, dens, h1]
    rw [this, lintegral_indicator measurableSet_Ioc, setLIntegral_congr Ioo_ae_eq_Ioc.symm]
    apply setLIntegral_congr_fun_ae measurableSet_Ioo
    filter_upwards [meas_le_ae_eq_meas_lt P volume Y] with x hx hxI
    rw [hh x]
    have hdx : dens x = ENNReal.ofReal (f x) := by
      simp [dens, Set.indicator_of_mem (show x ∈ Set.Ioi 0 from hxI.1)]
    rw [hdx]
    rw [hx]
    have hset : {ω | x < Y ω} = {ω | ((x : ℝ) : WithTop ℝ) < tauMin N (A.erase s) q ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, Y]
      rw [← WithTop.coe_lt_coe, stop_coe, lt_min_iff]
      simp [hxI.2]
    rw [hset, ← ENNReal.ofReal_toReal (measure_ne_top P _), ← ENNReal.ofReal_mul (hf0 x hxI.1)]
  have hGm : Measurable G := (antitone_prob P _).measurable
  have hint : IntegrableOn (fun x => f x * G x) (Set.Ioo 0 T) := by
    refine Integrable.mul_bdd ((hfc.integrableOn_Icc (a := 0) (b := T)).mono_set
      Set.Ioo_subset_Icc_self) hGm.aestronglyMeasurable (c := 1) ?_
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    rw [← measureReal_def]
    exact measureReal_le_one
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo 0 T)] fun x => f x * G x :=
    ae_restrict_of_forall_mem measurableSet_Ioo
      (fun x hx => mul_nonneg (hf0 x hx.1) ENNReal.toReal_nonneg)
  have hmain : P {ω | X ω ≤ Y ω} = ENNReal.ofReal (∫ x in Set.Ioo 0 T, f x * G x) := by
    rw [hprod, hres, hden, hioo, ofReal_integral_eq_lintegral_ofReal hint hnn]
  rw [hE, hmain, ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioo
    (fun x hx => mul_nonneg (hf0 x hx.1) ENNReal.toReal_nonneg))]
  rw [intervalIntegral.integral_of_le hT.le, integral_Ioc_eq_integral_Ioo,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  simp only [f, G]
  rw [pois_pt hN s hl hx.1.le, prob_tau_gt hN (A.erase s) q hx.1.le]
  unfold pterm
  field_simp

end Aux_FF_dhA_formula

open Aux_FF_dhA_formula in
open FastFashion.Structure in
theorem solution {S Ω : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ) (T : ℝ)
    (hN : IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (hT : 0 < T)
    (A : Finset S) (q : S → ℕ) (s : S) (hs : s ∈ A) :
    delta (hA N P T A) s q =
        ∫ t in (0)..T,
          ((P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s (q + Pi.single s 1) ω}).toReal
            - (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s q ω}).toReal)
          * ∏ s' ∈ A.erase s, (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s' q ω}).toReal ∧
    (∫ t in (0)..T,
          ((P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s (q + Pi.single s 1) ω}).toReal
            - (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s q ω}).toReal)
          * ∏ s' ∈ A.erase s, (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s' q ω}).toReal) =
        ∫ t in (0)..T,
          (P {ω | N s t ω = q s}).toReal
          * ∏ s' ∈ A.erase s, (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s' q ω}).toReal ∧
    (∫ t in (0)..T,
          (P {ω | N s t ω = q s}).toReal
          * ∏ s' ∈ A.erase s, (P {ω | ((t : ℝ) : WithTop ℝ) < stockoutTime N s' q ω}).toReal) =
        (1 / lam s) *
          (P {ω | stockoutTime N s (q + Pi.single s 1) ω
                    ≤ min (tauMin N (A.erase s) q ω) ((T : ℝ) : WithTop ℝ)}).toReal :=
  ⟨eq_one hN hT A q s hs, eq_two hN hT A q s, eq_three hN hlam hT A q s⟩
