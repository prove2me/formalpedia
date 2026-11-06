-- Prove2me | solution 1 for FastFashion.Structure.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:16:49.285587+00:00
-- url     : https://prove2.me/submissions/a0c6cd57-224a-403c-9d0e-191b2d211d48

import Mathlib
import Definitions.Def_FastFashion_Structure_Model
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Theorems.Thm_FastFashion_Structure_eq_2_optional_sampling
import Theorems.Thm_FastFashion_Structure_delta_hA_integral_formula
import Theorems.Thm_FastFashion_Structure_delta_hA_monotone
import Theorems.Thm_FastFashion_Structure_hA_supermodular

open MeasureTheory ProbabilityTheory

namespace Aux_FF_proposition_1

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

lemma step_mono {S : Type*} [Fintype S] [DecidableEq S] (f : (S → ℕ) → ℝ)
    (hf : ∀ q s, f q ≤ f (q + Pi.single s 1)) : Monotone f := by
  have hk : ∀ (a : S) (k : ℕ) (x : S → ℕ), f x ≤ f (x + Pi.single a k) := by
    intro a k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      have : x + Pi.single a (k + 1) = (x + Pi.single a k) + Pi.single a 1 := by
        rw [Pi.single_add, add_assoc]
      rw [this]
      exact (ih x).trans (hf _ a)
  intro q q' hqq
  let r : Finset S → S → ℕ := fun A t => if t ∈ A then q' t else q t
  have hr : ∀ A : Finset S, f q ≤ f (r A) := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp [r]
    | insert a A ha ih =>
      have : r (insert a A) = r A + Pi.single a (q' a - q a) := by
        funext t
        by_cases hta : t = a
        · subst hta
          have hle : q t ≤ q' t := hqq t
          simp only [r, Finset.mem_insert, true_or, if_true, ha, if_false, Pi.add_apply,
            Pi.single_eq_same]
          omega
        · simp [r, Pi.single_apply, hta]
      rw [this]
      exact ih.trans (hk a _ _)
  have : r Finset.univ = q' := by funext t; simp [r]
  rw [← this]
  exact hr _

lemma delta_comb {S ι : Type*} [DecidableEq S] (I : Finset ι) (c : ℝ) (a : ι → ℝ)
    (h0 : (S → ℕ) → ℝ) (h : ι → (S → ℕ) → ℝ) (s : S) (q : S → ℕ) :
    delta (fun x => c * h0 x + ∑ i ∈ I, a i * h i x) s q =
      c * delta h0 s q + ∑ i ∈ I, a i * delta (h i) s q := by
  simp only [delta, mul_sub, Finset.sum_sub_distrib]
  ring

end Aux_FF_proposition_1

open Aux_FF_proposition_1 in
open FastFashion.Structure in
theorem solution {S Ω : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ) (T : ℝ)
    (hN : IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (hT : 0 < T)
    (Sp : Finset S) :
    Monotone (expectedSales N P Sp T) ∧
    (∀ (q : S → ℕ) (s : S),
      delta (expectedSales N P Sp T) s (q + Pi.single s 1)
        ≤ delta (expectedSales N P Sp T) s q) ∧
    (∀ (q : S → ℕ) (s s' : S), s ≠ s' →
      delta (expectedSales N P Sp T) s q
        ≤ delta (expectedSales N P Sp T) s (q + Pi.single s' 1)) ∧
    Supermodularity.Monotonicity.SupermodularOn (expectedSales N P Sp T) Set.univ := by
  set c : ℝ := ∑ s ∈ Sp, lam s with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg (fun s _ => (hlam s).le)
  have hg : expectedSales N P Sp T =
      fun x => c * hA N P T Sp x + ∑ s ∈ Spᶜ, lam s * hA N P T (insert s Sp) x :=
    funext (eq_2_optional_sampling P lam N T hN hlam hT Sp)
  have hdpos : ∀ (A : Finset S) (q : S → ℕ) (s : S), 0 ≤ delta (hA N P T A) s q := by
    intro A q s
    by_cases hs : s ∈ A
    · obtain ⟨h1, h2, h3⟩ := delta_hA_integral_formula P lam N T hN hlam hT A q s hs
      rw [h1.trans (h2.trans h3)]
      exact mul_nonneg (one_div_pos.2 (hlam s)).le ENNReal.toReal_nonneg
    · rw [delta_zero N P T A q s hs]
  have hmono := fun A => delta_hA_monotone P lam N T hN hlam hT A
  have hsup := hA_supermodular P lam N T hN hlam hT
  rw [hg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply step_mono
    intro q s
    have := delta_comb (S := S) Spᶜ c lam (hA N P T Sp) (fun s => hA N P T (insert s Sp)) s q
    have hnn : 0 ≤ c * delta (hA N P T Sp) s q +
        ∑ i ∈ Spᶜ, lam i * delta (hA N P T (insert i Sp)) s q :=
      add_nonneg (mul_nonneg hc0 (hdpos _ _ _))
        (Finset.sum_nonneg (fun i _ => mul_nonneg (hlam i).le (hdpos _ _ _)))
    rw [← this] at hnn
    unfold delta at hnn
    linarith
  · intro q s
    rw [delta_comb, delta_comb]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left ((hmono Sp).1 q s) hc0
    · exact Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left ((hmono (insert i Sp)).1 q s) (hlam i).le)
  · intro q s s' hss'
    rw [delta_comb, delta_comb]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left ((hmono Sp).2 q s s' hss') hc0
    · exact Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left ((hmono (insert i Sp)).2 q s s' hss') (hlam i).le)
  · intro x _ y _
    have h0 := hsup Sp (Set.mem_univ x) (Set.mem_univ y)
    have hi : ∀ i ∈ Spᶜ, lam i * hA N P T (insert i Sp) x + lam i * hA N P T (insert i Sp) y ≤
        lam i * hA N P T (insert i Sp) (x ⊔ y) + lam i * hA N P T (insert i Sp) (x ⊓ y) := by
      intro i _
      have := hsup (insert i Sp) (Set.mem_univ x) (Set.mem_univ y)
      rw [← mul_add, ← mul_add]
      exact mul_le_mul_of_nonneg_left this (hlam i).le
    have hs := Finset.sum_le_sum hi
    simp only [Finset.sum_add_distrib] at hs
    have := mul_le_mul_of_nonneg_left h0 hc0
    simp only
    linarith
