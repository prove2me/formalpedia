-- Prove2me | solution 1 for FastFashion.Structure.hA_supermodular
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:14:09.08076+00:00
-- url     : https://prove2.me/submissions/7b94bf07-ec04-4a6e-b503-f8fe8319d156

import Mathlib
import Definitions.Def_FastFashion_Structure_Model
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Theorems.Thm_FastFashion_Structure_stopMin_supermodular_pathwise

open MeasureTheory ProbabilityTheory

namespace Aux_FF_hA_supermodular

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

end Aux_FF_hA_supermodular

open Aux_FF_hA_supermodular in
open FastFashion.Structure in
theorem solution {S Ω : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ) (T : ℝ)
    (hN : IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (hT : 0 < T) :
    ∀ A : Finset S, Supermodularity.Monotonicity.SupermodularOn (hA N P T A) Set.univ := by
  intro A x _ y _
  have hI := fun q => stop_integrable hN A q T hT.le
  have hpw := stopMin_supermodular_pathwise P lam N T hN A
  simp only [hA]
  rw [← integral_add (hI x) (hI y), ← integral_add (hI _) (hI _)]
  exact integral_mono ((hI x).add (hI y)) ((hI _).add (hI _))
    (fun ω => hpw ω (Set.mem_univ x) (Set.mem_univ y))
