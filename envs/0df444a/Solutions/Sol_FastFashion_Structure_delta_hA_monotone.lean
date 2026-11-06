-- Prove2me | solution 1 for FastFashion.Structure.delta_hA_monotone
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:15:12.366942+00:00
-- url     : https://prove2.me/submissions/32d42577-ca31-4818-9a9b-c056fef46d05

import Mathlib
import Definitions.Def_FastFashion_Structure_Model
import Theorems.Thm_FastFashion_Structure_delta_hA_integral_formula

open MeasureTheory ProbabilityTheory

namespace Aux_FF_delta_hA_monotone

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

end Aux_FF_delta_hA_monotone

open Aux_FF_delta_hA_monotone in
open FastFashion.Structure in
theorem solution {S Ω : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ) (T : ℝ)
    (hN : IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (hT : 0 < T)
    (A : Finset S) :
    (∀ (q : S → ℕ) (s : S),
      delta (hA N P T A) s (q + Pi.single s 1) ≤ delta (hA N P T A) s q) ∧
    (∀ (q : S → ℕ) (s s' : S), s ≠ s' →
      delta (hA N P T A) s q ≤ delta (hA N P T A) s (q + Pi.single s' 1)) := by
  have key : ∀ (q : S → ℕ) (s : S), s ∈ A → delta (hA N P T A) s q =
      (1 / lam s) * (P {ω | stockoutTime N s (q + Pi.single s 1) ω
                    ≤ min (tauMin N (A.erase s) q ω) ((T : ℝ) : WithTop ℝ)}).toReal := by
    intro q s hs
    obtain ⟨h1, h2, h3⟩ := delta_hA_integral_formula P lam N T hN hlam hT A q s hs
    exact h1.trans (h2.trans h3)
  have hpos : ∀ s, 0 ≤ 1 / lam s := fun s => (one_div_pos.2 (hlam s)).le
  refine ⟨fun q s => ?_, fun q s s' hss' => ?_⟩
  · by_cases hs : s ∈ A
    · rw [key q s hs, key _ s hs]
      apply mul_le_mul_of_nonneg_left _ (hpos s)
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      have ht : tauMin N (A.erase s) (q + Pi.single s 1) ω = tauMin N (A.erase s) q ω := by
        apply tau_congr
        intro s₀ hs₀
        simp [Pi.single_apply, Finset.ne_of_mem_erase hs₀]
      rw [ht] at hω
      refine le_trans ?_ hω
      apply stock_mono' hN s ω
      simp
    · rw [delta_zero N P T A _ s hs, delta_zero N P T A _ s hs]
  · by_cases hs : s ∈ A
    · rw [key q s hs, key _ s hs]
      apply mul_le_mul_of_nonneg_left _ (hpos s)
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      have he : stockoutTime N s (q + Pi.single s' 1 + Pi.single s 1) ω =
          stockoutTime N s (q + Pi.single s 1) ω := by
        apply stock_congr
        simp [Pi.single_apply, hss']
      rw [he]
      refine le_trans hω (min_le_min_right _ ?_)
      apply tau_mono hN
      intro x
      simp
    · rw [delta_zero N P T A _ s hs, delta_zero N P T A _ s hs]
