-- Prove2me | solution 1 for FastFashion.Structure.stopMin_supermodular_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:10:45.047195+00:00
-- url     : https://prove2.me/submissions/a9333f1a-1262-4e2e-bf9c-fc1be36544ae

import Mathlib
import Definitions.Def_FastFashion_Structure_Model
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

open MeasureTheory ProbabilityTheory

namespace Aux_FastFashion_Structure_stopMin_supermodular_pathwise

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

end Aux_FastFashion_Structure_stopMin_supermodular_pathwise

open Aux_FastFashion_Structure_stopMin_supermodular_pathwise in
open FastFashion.Structure in
theorem solution {S Ω : Type*} [Fintype S] [DecidableEq S]
    [MeasurableSpace Ω] (P : Measure Ω) (lam : S → ℝ) (N : S → ℝ → Ω → ℕ) (T : ℝ)
    (hN : IsPoissonFamily lam N P) :
    ∀ (A : Finset S) (ω : Ω),
      Supermodularity.Monotonicity.SupermodularOn (fun q : S → ℕ => stopMin N A q T ω)
        Set.univ := by
  intro A ω x _ y _
  simp only
  set h : S → ℕ → WithTop ℝ :=
    fun s n => stockoutTime N s (fun _ => n) ω with hh
  have hm : ∀ s, Monotone (h s) := fun s => stock_mono hN s ω
  have htau : ∀ q, tauMin N A q ω = A.inf (fun s => h s (q s)) := by
    intro q
    unfold tauMin
    exact Finset.inf_congr rfl (fun s _ => stock_eq N s q ω)
  have hinf : ((stopMin N A (x ⊓ y) T ω : ℝ) : WithTop ℝ) =
      ((min (stopMin N A x T ω) (stopMin N A y T ω) : ℝ) : WithTop ℝ) := by
    rw [WithTop.coe_min, stop_coe, stop_coe, stop_coe, htau, htau, htau]
    have : A.inf (fun s => h s ((x ⊓ y) s)) =
        A.inf (fun s => h s (x s)) ⊓ A.inf (fun s => h s (y s)) := by
      rw [← Finset.inf_inf]
      exact Finset.inf_congr rfl (fun s _ => by
        simp only [Pi.inf_apply]
        exact (hm s).map_min)
    rw [this]
    exact inf_inf_distrib_right _ _ _
  have hsup : ((max (stopMin N A x T ω) (stopMin N A y T ω) : ℝ) : WithTop ℝ) ≤
      ((stopMin N A (x ⊔ y) T ω : ℝ) : WithTop ℝ) := by
    rw [WithTop.coe_max, stop_coe, stop_coe, stop_coe, htau, htau, htau]
    apply max_le
    · apply min_le_min_right
      apply Finset.le_inf
      intro s hs
      exact (Finset.inf_le hs).trans ((hm s) (by simp [Pi.sup_apply]))
    · apply min_le_min_right
      apply Finset.le_inf
      intro s hs
      exact (Finset.inf_le hs).trans ((hm s) (by simp [Pi.sup_apply]))
  have h1 := WithTop.coe_injective hinf
  have h2 := WithTop.coe_le_coe.1 hsup
  have := min_add_max (stopMin N A x T ω) (stopMin N A y T ω)
  linarith
