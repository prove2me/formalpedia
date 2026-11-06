-- Prove2me | solution 1 for FastFashion.Structure.eq_2_optional_sampling
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:19:42.794213+00:00
-- url     : https://prove2.me/submissions/30ec57c8-7dec-4b9c-8454-131a949e86d8

import Mathlib
import Definitions.Def_FastFashion_Structure_Model
import Theorems.Thm_FastFashion_Structure_delta_hA_integral_formula

open MeasureTheory ProbabilityTheory

namespace Aux_FF_eq_2

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

lemma N_stop_le {S Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam : S → ℝ}
    {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (A : Finset S) (q : S → ℕ) (T : ℝ)
    (hT : 0 ≤ T) (ω : Ω) (s : S) (hs : s ∈ A) :
    N s (stopMin N A q T ω) ω ≤ q s := by
  by_contra hc
  push_neg at hc
  have h0 := stop_nonneg N A q T ω hT
  obtain ⟨ts, hts0, htsq, _⟩ := hit hN s ω (q s) _ hc.le _ h0 rfl
  have h1 : stockoutTime N s q ω ≤ ((ts : ℝ) : WithTop ℝ) :=
    (stock_le_iff hN s q ω ts).2 ⟨hts0, htsq.ge⟩
  have h2 : ((stopMin N A q T ω : ℝ) : WithTop ℝ) ≤ stockoutTime N s q ω := by
    rw [stop_coe]
    exact (min_le_left _ _).trans (Finset.inf_le hs)
  have h3 : stopMin N A q T ω ≤ ts := WithTop.coe_le_coe.1 (h2.trans h1)
  have := hN.mono s ω h0 h3
  omega

/-- The event `E_k = {τ_s(k+1) ≤ τ_{A∖{s}} ∧ T}`. -/
def Ev {S Ω : Type*} [DecidableEq S] (N : S → ℝ → Ω → ℕ) (A : Finset S) (q : S → ℕ) (T : ℝ)
    (s : S) (k : ℕ) : Set Ω :=
  {ω | stockoutTime N s (Function.update q s (k + 1)) ω
        ≤ min (tauMin N (A.erase s) q ω) ((T : ℝ) : WithTop ℝ)}

lemma mem_Ev_iff {S Ω : Type*} [DecidableEq S] [MeasurableSpace Ω] {P : Measure Ω} {lam : S → ℝ}
    {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (A : Finset S) (q : S → ℕ) (T : ℝ)
    (hT : 0 ≤ T) (ω : Ω) (s : S) (hs : s ∈ A) (k : ℕ) (hk : k + 1 ≤ q s) :
    ω ∈ Ev N A q T s k ↔ k + 1 ≤ N s (stopMin N A q T ω) ω := by
  have hA : tauMin N A q ω = min (stockoutTime N s q ω) (tauMin N (A.erase s) q ω) := by
    unfold tauMin
    conv_lhs => rw [← Finset.insert_erase hs]
    rw [Finset.inf_insert]
  have hm : ((stopMin N A q T ω : ℝ) : WithTop ℝ) =
      min (min (stockoutTime N s q ω) (tauMin N (A.erase s) q ω)) ((T : ℝ) : WithTop ℝ) := by
    rw [stop_coe, hA]
  have hupd : (Function.update q s (k + 1)) s = k + 1 := by simp
  have hmono : stockoutTime N s (Function.update q s (k + 1)) ω ≤ stockoutTime N s q ω :=
    stock_mono' hN s ω (by rw [hupd]; exact hk)
  constructor
  · intro h
    simp only [Ev, Set.mem_setOf_eq] at h
    have : stockoutTime N s (Function.update q s (k + 1)) ω ≤
        ((stopMin N A q T ω : ℝ) : WithTop ℝ) := by
      rw [hm]
      exact le_min (le_min hmono (h.trans (min_le_left _ _))) (h.trans (min_le_right _ _))
    have := ((stock_le_iff hN s _ ω _).1 this).2
    rw [hupd] at this
    exact this
  · intro h
    have h' : stockoutTime N s (Function.update q s (k + 1)) ω ≤
        ((stopMin N A q T ω : ℝ) : WithTop ℝ) :=
      (stock_le_iff hN s _ ω _).2 ⟨stop_nonneg N A q T ω hT, by rw [hupd]; exact h⟩
    simp only [Ev, Set.mem_setOf_eq]
    rw [hm] at h'
    exact h'.trans (min_le_min_right _ (min_le_right _ _))

lemma Ev_measurable {S Ω : Type*} [DecidableEq S] [MeasurableSpace Ω] {P : Measure Ω}
    {lam : S → ℝ} {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (A : Finset S)
    (q : S → ℕ) (T : ℝ) (hT : 0 ≤ T) (s : S) (k : ℕ) : MeasurableSet (Ev N A q T s k) := by
  have : Ev N A q T s k =
      {ω | stopMin N {s} (Function.update q s (k + 1)) T ω ≤ stopMin N (A.erase s) q T ω} ∩
      {ω | k + 1 ≤ N s T ω} := by
    ext ω
    simp only [Ev, Set.mem_setOf_eq, Set.mem_inter_iff]
    have e : stopMin N {s} (Function.update q s (k + 1)) T ω ≤ stopMin N (A.erase s) q T ω ↔
        ((stopMin N {s} (Function.update q s (k + 1)) T ω : ℝ) : WithTop ℝ) ≤
          ((stopMin N (A.erase s) q T ω : ℝ) : WithTop ℝ) := WithTop.coe_le_coe.symm
    rw [e, stop_coe, stop_coe]
    have hsing : tauMin N {s} (Function.update q s (k + 1)) ω =
        stockoutTime N s (Function.update q s (k + 1)) ω := by
      simp [tauMin]
    rw [hsing]
    have hT' : stockoutTime N s (Function.update q s (k + 1)) ω ≤ ((T : ℝ) : WithTop ℝ) ↔
        k + 1 ≤ N s T ω := by
      rw [stock_le_iff hN]; simp [hT]
    rw [← hT']
    set σ := stockoutTime N s (Function.update q s (k + 1)) ω
    set τ := tauMin N (A.erase s) q ω
    constructor
    · intro h
      have hσ : σ ≤ ((T : ℝ) : WithTop ℝ) := h.trans (min_le_right _ _)
      refine ⟨?_, hσ⟩
      rw [min_eq_left hσ]; exact h
    · rintro ⟨h1, h2⟩
      rw [min_eq_left h2] at h1; exact h1
  rw [this]
  apply MeasurableSet.inter
  · exact measurableSet_le (stop_measurable hN _ _ T) (stop_measurable hN _ _ T)
  · exact (hN.measurable s T hT) (measurableSet_Ici (a := k + 1))

lemma N_stop_eq_sum {S Ω : Type*} [DecidableEq S] [MeasurableSpace Ω] {P : Measure Ω}
    {lam : S → ℝ} {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (A : Finset S)
    (q : S → ℕ) (T : ℝ) (hT : 0 ≤ T) (s : S) (hs : s ∈ A) :
    (fun ω => (N s (stopMin N A q T ω) ω : ℝ)) =
      fun ω => ∑ k ∈ Finset.range (q s), (Ev N A q T s k).indicator (1 : Ω → ℝ) ω := by
  classical
  funext ω
  have hle := N_stop_le hN A q T hT ω s hs
  have : ∀ k ∈ Finset.range (q s), (Ev N A q T s k).indicator (1 : Ω → ℝ) ω =
      if k + 1 ≤ N s (stopMin N A q T ω) ω then 1 else 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Set.indicator_apply, Pi.one_apply]
    congr 1
    exact propext (mem_Ev_iff hN A q T hT ω s hs k hk)
  rw [Finset.sum_congr rfl this, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  have hf : (Finset.range (q s)).filter (fun k => k + 1 ≤ N s (stopMin N A q T ω) ω) =
      Finset.range (N s (stopMin N A q T ω) ω) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hf, Finset.card_range]

lemma hA_zero {S Ω : Type*} [DecidableEq S] [MeasurableSpace Ω] {P : Measure Ω}
    {lam : S → ℝ} {N : S → ℝ → Ω → ℕ} (hN : IsPoissonFamily lam N P) (A : Finset S)
    (q : S → ℕ) (T : ℝ) (hT : 0 ≤ T) (s : S) (hs : s ∈ A) :
    hA N P T A (Function.update q s 0) = 0 := by
  unfold hA
  have : ∀ ω, stopMin N A (Function.update q s 0) T ω = 0 := by
    intro ω
    apply le_antisymm _ (stop_nonneg N A _ T ω hT)
    rw [stop_le_iff hN]
    right
    exact ⟨s, hs, le_rfl, by simp⟩
  simp [this]

lemma term_eq {S Ω : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ) (T : ℝ)
    (hN : IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (hT : 0 < T)
    (A : Finset S) (q : S → ℕ) (s : S) (hs : s ∈ A) :
    Integrable (fun ω => (N s (stopMin N A q T ω) ω : ℝ)) P ∧
    ∫ ω, (N s (stopMin N A q T ω) ω : ℝ) ∂P = lam s * hA N P T A q := by
  rw [N_stop_eq_sum hN A q T hT.le s hs]
  have hE := fun k => Ev_measurable hN A q T hT.le s k
  have hI : ∀ k ∈ Finset.range (q s),
      Integrable (fun ω => (Ev N A q T s k).indicator (1 : Ω → ℝ) ω) P :=
    fun k _ => (integrable_const (1 : ℝ)).indicator (hE k)
  refine ⟨integrable_finsetSum _ hI, ?_⟩
  rw [integral_finsetSum _ hI]
  simp only [integral_indicator_one (hE _)]
  -- each probability is `lam s * Δ_s h^A`
  have hd : ∀ k ∈ Finset.range (q s), P.real (Ev N A q T s k) =
      lam s * (hA N P T A (Function.update q s (k + 1)) - hA N P T A (Function.update q s k)) := by
    intro k _
    obtain ⟨h1, h2, h3⟩ :=
      delta_hA_integral_formula P lam N T hN hlam hT A (Function.update q s k) s hs
    have hdel := h1.trans (h2.trans h3)
    have hupd : Function.update q s k + Pi.single s 1 = Function.update q s (k + 1) := by
      funext t
      by_cases hts : t = s
      · subst hts; simp
      · simp [Function.update, hts, Pi.single_apply]
    have htau : ∀ ω, tauMin N (A.erase s) (Function.update q s k) ω = tauMin N (A.erase s) q ω := by
      intro ω
      apply tau_congr
      intro t ht
      simp [Function.update, Finset.ne_of_mem_erase ht]
    simp only [delta, hupd, htau] at hdel
    rw [hdel, measureReal_def]
    have := (hlam s).ne'
    unfold Ev
    field_simp
  rw [Finset.sum_congr rfl hd, ← Finset.mul_sum,
    Finset.sum_range_sub (fun k => hA N P T A (Function.update q s k)),
    Function.update_eq_self, hA_zero hN A q T hT.le s hs, sub_zero]

end Aux_FF_eq_2

open Aux_FF_eq_2 in
open FastFashion.Structure in
theorem solution {S Ω : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ) (T : ℝ)
    (hN : IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (hT : 0 < T)
    (Sp : Finset S) :
    ∀ q : S → ℕ, expectedSales N P Sp T q =
      (∑ s ∈ Sp, lam s) * hA N P T Sp q + ∑ s ∈ Spᶜ, lam s * hA N P T (insert s Sp) q := by
  intro q
  have h1 := fun s (hs : s ∈ Sp) => term_eq P lam N T hN hlam hT Sp q s hs
  have h2 := fun s (_ : s ∈ Spᶜ) =>
    term_eq P lam N T hN hlam hT (insert s Sp) q s (Finset.mem_insert_self s Sp)
  unfold expectedSales sales
  simp only [Nat.cast_add, Nat.cast_sum]
  rw [integral_add (integrable_finsetSum _ (fun s hs => (h1 s hs).1))
      (integrable_finsetSum _ (fun s hs => (h2 s hs).1)),
    integral_finsetSum _ (fun s hs => (h1 s hs).1),
    integral_finsetSum _ (fun s hs => (h2 s hs).1),
    Finset.sum_congr rfl (fun s hs => (h1 s hs).2),
    Finset.sum_congr rfl (fun s hs => (h2 s hs).2), Finset.sum_mul]
