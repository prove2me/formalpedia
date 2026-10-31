-- Prove2me | solution 1 for FBMSP.remark2_submodular_greedy
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T12:36:46.524526+00:00
-- url     : https://prove2.me/submissions/33339181-fdde-467e-ae52-39f54024f33d

import Definitions.Def_FBMSP_Model
import Theorems.Thm_CustAssort_AugGreedy_greedy_approximation

open MeasureTheory Set FBMSP
open scoped BigOperators

private lemma menu_nonneg (η : Measure ℝ) (x : ℝ) (P : Finset ℝ) :
    0 ≤ menuAt η x P := by
  classical
  unfold menuAt
  split_ifs <;> simp_all only [le_max_iff, le_refl, true_or]

private lemma menu_le (η : Measure ℝ) (x : ℝ) (P : Finset ℝ) (b : ℝ)
    (hb : 0 ≤ b) (h : ∀ p ∈ P, postedRevenue η x p ≤ b) : menuAt η x P ≤ b := by
  classical
  unfold menuAt
  split_ifs with hP
  · exact max_le hb (Finset.sup'_le _ _ h)
  · exact hb

private lemma le_menu (η : Measure ℝ) (x : ℝ) (P : Finset ℝ) (p : ℝ)
    (hp : p ∈ P) : postedRevenue η x p ≤ menuAt η x P := by
  classical
  have hP : P.Nonempty := ⟨p, hp⟩
  rw [menuAt, dif_pos hP]
  exact (Finset.le_sup' (fun q => postedRevenue η x q) hp).trans (le_max_right _ _)

private lemma menu_mono (η : Measure ℝ) (x : ℝ) : Monotone (menuAt η x) := by
  intro A B hAB
  exact menu_le η x A _ (menu_nonneg η x B) (fun p hp => le_menu η x B p (hAB hp))

private lemma menu_insert (η : Measure ℝ) (x p : ℝ) (P : Finset ℝ) :
    menuAt η x (insert p P) = max (menuAt η x P) (postedRevenue η x p) := by
  classical
  apply le_antisymm
  · apply menu_le η x _ _ ((menu_nonneg η x P).trans (le_max_left _ _))
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact le_max_right _ _
    · exact (le_menu η x P q hq).trans (le_max_left _ _)
  · exact max_le (menu_mono η x (Finset.subset_insert p P))
      (le_menu η x _ p (Finset.mem_insert_self p P))

private lemma menu_union (η : Measure ℝ) (x : ℝ) (A B : Finset ℝ) :
    menuAt η x (A ∪ B) = max (menuAt η x A) (menuAt η x B) := by
  classical
  apply le_antisymm
  · apply menu_le η x _ _ ((menu_nonneg η x A).trans (le_max_left _ _))
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (le_menu η x A p hp).trans (le_max_left _ _)
    · exact (le_menu η x B p hp).trans (le_max_right _ _)
  · exact max_le (menu_mono η x Finset.subset_union_left)
      (menu_mono η x Finset.subset_union_right)

private lemma menu_submodular (η : Measure ℝ) (x : ℝ) :
    IsSubmodular (menuAt η x) := by
  intro A B
  have h : menuAt η x (A ∩ B) ≤ min (menuAt η x A) (menuAt η x B) :=
    le_min (menu_mono η x Finset.inter_subset_left)
      (menu_mono η x Finset.inter_subset_right)
  rw [menu_union]
  calc
    menuAt η x (A ∩ B) + max (menuAt η x A) (menuAt η x B) ≤
        min (menuAt η x A) (menuAt η x B) + max (menuAt η x A) (menuAt η x B) :=
      by linarith
    _ = menuAt η x A + menuAt η x B := min_add_max _ _

private lemma posted_integrable (ν η : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η] (p : ℝ) :
    Integrable (fun x => postedRevenue η x p) ν := by
  have hs : Antitone (survival η) := by
    intro a b hab
    exact ENNReal.toReal_mono (measure_ne_top η (Ici a))
      (measure_mono (Ici_subset_Ici.mpr hab))
  have hm : Measurable (fun x => postedRevenue η x p) :=
    measurable_const.mul (hs.measurable.comp (measurable_const.sub measurable_id))
  apply (integrable_const (|p| : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  have hS : survival η (p - x) ≤ 1 := measureReal_le_one
  have hS0 : 0 ≤ survival η (p - x) := ENNReal.toReal_nonneg
  simp only [postedRevenue, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hS0]
  simpa using mul_le_mul_of_nonneg_left hS (abs_nonneg p)

private lemma menu_integrable (ν η : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η] (P : Finset ℝ) :
    Integrable (fun x => menuAt η x P) ν := by
  classical
  induction P using Finset.induction_on with
  | empty => simpa [menuAt] using (integrable_const (0 : ℝ) : Integrable (fun _ : ℝ => 0) ν)
  | @insert p P hp ih =>
    simpa only [menu_insert, Pi.sup_def] using ih.sup (posted_integrable ν η p)

private lemma revenue_properties (ν η : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η] :
    menuRevenue ν η ∅ = 0 ∧ (∀ P, 0 ≤ menuRevenue ν η P) ∧
      Monotone (menuRevenue ν η) ∧ IsSubmodular (menuRevenue ν η) := by
  refine ⟨by simp [menuRevenue, menuAt], ?_, ?_, ?_⟩
  · intro P
    exact integral_nonneg (fun x => menu_nonneg η x P)
  · intro A B hAB
    exact integral_mono (menu_integrable ν η A) (menu_integrable ν η B)
      (fun x => menu_mono η x hAB)
  · intro A B
    have h := integral_mono
      ((menu_integrable ν η (A ∩ B)).add (menu_integrable ν η (A ∪ B)))
      ((menu_integrable ν η A).add (menu_integrable ν η B))
      (fun x => menu_submodular η x A B)
    simp only [Pi.add_apply] at h
    simpa only [integral_add (menu_integrable ν η (A ∩ B))
      (menu_integrable ν η (A ∪ B)),
      integral_add (menu_integrable ν η A) (menu_integrable ν η B), menuRevenue] using h

private lemma submodular_marginal (F : Finset ℝ → ℝ) (hF : IsSubmodular F)
    (P : Finset ℝ) : CustAssort.AugGreedy.SubmodularOn F P := by
  classical
  intro A B hAB hBP p hp
  have hpB : p ∉ B := (Finset.mem_sdiff.mp hp).2
  have hi : insert p A ∩ B = A := by
    ext q
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hq, hqB⟩
      · exact (hpB hqB).elim
      · exact hq
    · intro hq
      exact ⟨Or.inr hq, hAB hq⟩
  have hu : insert p A ∪ B = insert p B := by
    ext q
    simp only [Finset.mem_union, Finset.mem_insert]
    aesop
  have hs := hF (insert p A) B
  rw [hi, hu] at hs
  linarith

private lemma exists_greedy_chain (F : Finset ℝ → ℝ) (P : Finset ℝ)
    (k : ℕ) (hk : k ≤ P.card) : ∃ A, IsGreedyChain F P k A := by
  classical
  let chooseP (B : Finset ℝ) : ℝ :=
    if h : (P \ B).Nonempty then
      (Finset.exists_max_image (P \ B) (fun p => F (insert p B)) h).choose else 0
  have hchoose (B : Finset ℝ) (h : (P \ B).Nonempty) :
      chooseP B ∈ P \ B ∧ ∀ q ∈ P \ B, F (insert q B) ≤ F (insert (chooseP B) B) := by
    simp only [chooseP, dif_pos h]
    exact (Finset.exists_max_image (P \ B) (fun p => F (insert p B)) h).choose_spec
  let A : ℕ → Finset ℝ := Nat.rec ∅ (fun _ B => insert (chooseP B) B)
  have hA0 : A 0 = ∅ := rfl
  have hAs (t : ℕ) : A (t + 1) = insert (chooseP (A t)) (A t) := rfl
  have hinv : ∀ t, t ≤ k → A t ⊆ P ∧ (A t).card = t := by
    intro t
    induction t with
    | zero => simp [hA0]
    | succ t ih =>
      intro htk
      obtain ⟨hsub, hcard⟩ := ih (by omega)
      have hne : (P \ A t).Nonempty := Finset.sdiff_nonempty_of_card_lt_card (by omega)
      have hc := hchoose (A t) hne
      rw [hAs]
      exact ⟨Finset.insert_subset (Finset.mem_sdiff.mp hc.1).1 hsub,
        by rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hc.1).2, hcard]⟩
  refine ⟨A, hA0, ?_⟩
  intro t ht
  obtain ⟨hsub, hcard⟩ := hinv t (le_of_lt ht)
  have hne : (P \ A t).Nonempty := Finset.sdiff_nonempty_of_card_lt_card (by omega)
  obtain ⟨hp, hmax⟩ := hchoose (A t) hne
  exact ⟨hsub, chooseP (A t), hp, hAs t, fun q hq => sub_le_sub_right (hmax q hq) _⟩

private lemma greedy_chain_output (F : Finset ℝ → ℝ) (P : Finset ℝ)
    (k : ℕ) (A : ℕ → Finset ℝ) (hA : IsGreedyChain F P k A) :
    A k ⊆ P ∧ (A k).card = k ∧ CustAssort.AugGreedy.IsGreedyOutput F P k (A k) := by
  classical
  have hinv : ∀ t, t ≤ k → A t ⊆ P ∧ (A t).card = t ∧
      CustAssort.AugGreedy.GreedyReach F P k (A t) := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [hA.1]
      exact ⟨Finset.empty_subset P, Finset.card_empty, .nil⟩
    | succ t ih =>
      intro htk
      obtain ⟨hsub, hcard, hreach⟩ := ih (by omega)
      obtain ⟨_, p, hp, hnext, hmax⟩ := hA.2 t (by omega)
      rw [hnext]
      refine ⟨Finset.insert_subset (Finset.mem_sdiff.mp hp).1 hsub,
        by rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hp).2, hcard], ?_⟩
      exact .step hreach (by omega) hp (fun q hq => by linarith [hmax q hq])
  obtain ⟨hsub, hcard, hreach⟩ := hinv k le_rfl
  exact ⟨hsub, hcard, hreach, by simp [hcard]⟩

private lemma candidate_attains (F : Finset ℝ → ℝ) (P : Finset ℝ) (k : ℕ) :
    ∃ S : Finset ℝ, S ⊆ P ∧ S.card ≤ k ∧ candidateOptimum F P k = F S := by
  classical
  let C := P.powerset.filter (fun S => S.card ≤ k)
  have hC : C.Nonempty := ⟨∅, by simp [C]⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image C F hC
  have hS' : S ⊆ P ∧ S.card ≤ k := by simpa [C] using hS
  refine ⟨S, hS'.1, hS'.2, ?_⟩
  have hgreat : IsGreatest {r : ℝ | ∃ A : Finset ℝ, A ⊆ P ∧ A.card ≤ k ∧ r = F A} (F S) := by
    refine ⟨⟨S, hS'.1, hS'.2, rfl⟩, ?_⟩
    rintro r ⟨A, hAP, hAk, rfl⟩
    exact hmax A (by simp [C, hAP, hAk])
  exact hgreat.csSup_eq

theorem solution (ν η : MeasureTheory.Measure ℝ)
    (hpred : ValidPredictions ν) (hnoise : ValidNoise η) :
    menuRevenue ν η ∅ = 0 ∧
    (∀ P : Finset ℝ, 0 ≤ menuRevenue ν η P) ∧
    Monotone (menuRevenue ν η) ∧
    IsSubmodular (menuRevenue ν η) ∧
    ∀ (P : Finset ℝ) (k : ℕ), k ≤ P.card → (∀ p ∈ P, 0 ≤ p) →
      (∃ A : ℕ → Finset ℝ, IsGreedyChain (menuRevenue ν η) P k A) ∧
      ∀ A : ℕ → Finset ℝ, IsGreedyChain (menuRevenue ν η) P k A →
        A k ⊆ P ∧ (A k).card = k ∧
          (1 - Real.exp (-1)) * candidateOptimum (menuRevenue ν η) P k ≤
            menuRevenue ν η (A k) := by
  classical
  letI : IsProbabilityMeasure ν := hpred.1
  letI : IsProbabilityMeasure η := hnoise.1
  obtain ⟨hz, hn, hm, hs⟩ := revenue_properties ν η
  refine ⟨hz, hn, hm, hs, ?_⟩
  intro P k hk hp
  refine ⟨exists_greedy_chain _ P k hk, ?_⟩
  intro A hA
  obtain ⟨hsub, hcard, hout⟩ := greedy_chain_output _ P k A hA
  refine ⟨hsub, hcard, ?_⟩
  obtain ⟨S, hSP, hSk, hopt⟩ := candidate_attains (menuRevenue ν η) P k
  rw [hopt]
  exact CustAssort.AugGreedy.greedy_approximation _ P k (A k)
    (fun B C hBC _ => hm hBC) (submodular_marginal _ hs P) (by linarith)
    hout S hSP hSk
