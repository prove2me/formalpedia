-- Prove2me | solution 1 for CommitteeVoting.SingleVoter.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T14:25:12.963606+00:00
-- url     : https://prove2.me/submissions/2571c884-22f1-42b9-913b-5008433279c0

import Mathlib
import Definitions.Def_CommitteeVoting_SingleVoter_PoissonBinomial
import Definitions.Def_CommitteeVoting_SingleVoter_Committee
import Definitions.Def_CommitteeVoting_SingleVoter_SuccessProb

open CommitteeVoting.SingleVoter CommitteeVoting.ExpConv

namespace CVProp2Aux

lemma weight_nonneg {ι : Type*} [DecidableEq ι] (s : ι → ℝ) (hs : ∀ j, 0 ≤ s j ∧ s j ≤ 1)
    (S A : Finset ι) : 0 ≤ pbWeight s S A := by
  unfold pbWeight
  apply mul_nonneg
  · exact Finset.prod_nonneg fun i _ => (hs i).1
  · exact Finset.prod_nonneg fun i _ => by linarith [(hs i).2]

/-- Conditioning on one coordinate `b ∈ S`. -/
lemma decomp {ι : Type*} [DecidableEq ι] (s : ι → ℝ) (S : Finset ι) (b : ι) (hb : b ∈ S)
    (F : Finset ι → ℝ) :
    ∑ H ∈ S.powerset, pbWeight s S H * F H =
      ∑ t ∈ (S.erase b).powerset,
        pbWeight s (S.erase b) t * (s b * F (insert b t) + (1 - s b) * F t) := by
  set R := S.erase b with hR
  have hbR : b ∉ R := Finset.notMem_erase b S
  have hS : S = insert b R := (Finset.insert_erase hb).symm
  rw [hS, Finset.sum_powerset_insert hbR, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have htR : t ⊆ R := Finset.mem_powerset.mp ht
  have hbt : b ∉ t := fun h => hbR (htR h)
  have w1 : pbWeight s (insert b R) t = (1 - s b) * pbWeight s R t := by
    unfold pbWeight
    rw [Finset.insert_sdiff_of_notMem _ hbt, Finset.prod_insert (fun h => hbR (Finset.sdiff_subset h))]
    ring
  have w2 : pbWeight s (insert b R) (insert b t) = s b * pbWeight s R t := by
    unfold pbWeight
    rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem hbR, Finset.prod_insert hbt]
    ring
  rw [w1, w2]
  ring

/-- Probability that the fixed committee `T` has at least `r` honest members. -/
noncomputable def Q {m : ℕ} (s : Fin m → ℝ) (r : ℤ) (T : Finset (Fin m)) : ℝ :=
  ∑ H ∈ (Finset.univ : Finset (Fin m)).powerset,
    pbWeight s Finset.univ H * (if r ≤ ((T ∩ H).card : ℤ) then 1 else 0)

lemma exchange {m : ℕ} (s : Fin m → ℝ) (hs : ∀ j, 0 ≤ s j ∧ s j ≤ 1) (r : ℤ)
    (T : Finset (Fin m)) (a b : Fin m) (ha : a ∉ T) (hb : b ∈ T) (hab : s b ≤ s a) :
    Q s r T ≤ Q s r (insert a (T.erase b)) := by
  have hne : a ≠ b := fun h => ha (h ▸ hb)
  unfold Q
  rw [decomp s _ b (Finset.mem_univ b), decomp s _ b (Finset.mem_univ b),
    decomp s _ a (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ a⟩),
    decomp s _ a (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ a⟩)]
  apply Finset.sum_le_sum
  intro t ht
  have htR := Finset.mem_powerset.mp ht
  have hat : a ∉ t := fun h => by
    have := htR h; simp at this
  have hbt : b ∉ t := fun h => by
    have := htR h; simp at this
  apply mul_le_mul_of_nonneg_left _ (weight_nonneg s hs _ _)
  set T' := insert a (T.erase b)
  have hbT' : b ∉ T' := by simp [T', hne.symm]
  have hT't : T' ∩ t = T ∩ t := by
    ext x; simp only [T', Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨h1 | ⟨_, h1⟩, h2⟩
      · exact absurd (h1 ▸ h2) hat
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr ⟨fun h => hbt (h ▸ h2), h1⟩, h2⟩
  have hnot : a ∉ T ∩ t := fun h => hat (Finset.mem_inter.mp h).2
  have hnotb : b ∉ T ∩ t := fun h => hbt (Finset.mem_inter.mp h).2
  have e1 : ∀ X, T ∩ insert a X = T ∩ X := fun X => Finset.inter_insert_of_notMem ha
  have e2 : ∀ X, T ∩ insert b X = insert b (T ∩ X) := fun X => Finset.inter_insert_of_mem hb
  have e3 : ∀ X, T' ∩ insert b X = T' ∩ X := fun X => Finset.inter_insert_of_notMem hbT'
  have e4 : ∀ X, T' ∩ insert a X = insert a (T' ∩ X) := fun X =>
    Finset.inter_insert_of_mem (Finset.mem_insert_self _ _)
  simp only [e1, e2, e3, e4, hT't]
  rw [Finset.card_insert_of_notMem hnot, Finset.card_insert_of_notMem hnotb]
  set u := (T ∩ t).card
  push_cast
  have h0a := (hs a).1; have h1a := (hs a).2; have h0b := (hs b).1; have h1b := (hs b).2
  split_ifs <;> first | omega | nlinarith

lemma topk {m : ℕ} (s : Fin m → ℝ) (hs : ∀ j, 0 ≤ s j ∧ s j ≤ 1) (r : ℤ)
    (Cstar : Finset (Fin m)) (htop : ∀ a ∈ Cstar, ∀ b ∉ Cstar, s b ≤ s a) :
    ∀ n : ℕ, ∀ T : Finset (Fin m), T.card = Cstar.card → (T \ Cstar).card = n →
      Q s r T ≤ Q s r Cstar := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hT hn
    by_cases hsub : T ⊆ Cstar
    · rw [Finset.eq_of_subset_of_card_le hsub (le_of_eq hT.symm)]
    · obtain ⟨b, hbT, hbC⟩ := Finset.not_subset.mp hsub
      have hsub2 : ¬ Cstar ⊆ T := fun h => hbC (by
        rw [← Finset.eq_of_subset_of_card_le h (le_of_eq hT)] at hbT; exact hbT)
      obtain ⟨a, haC, haT⟩ := Finset.not_subset.mp hsub2
      have hne : a ≠ b := fun h => haT (h ▸ hbT)
      have h1 := exchange s hs r T a b haT hbT (htop a haC b hbC)
      refine le_trans h1 (ih _ ?_ _ ?_ rfl)
      · rw [← hn]
        apply Finset.card_lt_card
        refine ⟨?_, ?_⟩
        · intro x hx
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨h | ⟨_, h⟩, h2⟩
          · exact absurd (h ▸ haC) h2
          · exact ⟨h, h2⟩
        · intro h
          have := h (Finset.mem_sdiff.mpr ⟨hbT, hbC⟩)
          simp at this
          exact hne this.1.symm
      · rw [Finset.card_insert_of_notMem (fun h => haT (Finset.mem_of_mem_erase h)),
          Finset.card_erase_of_mem hbT, hT]
        have : 0 < Cstar.card := Finset.card_pos.mpr ⟨a, haC⟩
        omega

lemma singleScore_eq {m : ℕ} (C : Finset (Fin m)) (j : Fin m) :
    singleScore C j = if j ∈ C then 1 else 0 := by
  unfold singleScore CommitteeVoting.SingleVoter.score
  split_ifs with h <;> simp [h]

lemma admissible_exists {m k : ℕ} (hkm : k ≤ m) (C : Finset (Fin m)) :
    ∃ T, Admissible k (singleScore C) T := by
  by_cases hk : k ≤ C.card
  · obtain ⟨T, hTC, hT⟩ := Finset.exists_subset_card_eq hk
    refine ⟨T, hT, fun a ha b _ => ?_⟩
    rw [singleScore_eq, singleScore_eq, if_pos (hTC ha)]
    split_ifs <;> omega
  · have hc : k - C.card ≤ Cᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin]; omega
    obtain ⟨D, hD, hDc⟩ := Finset.exists_subset_card_eq hc
    have hdisj : Disjoint C D := by
      rw [Finset.disjoint_left]; intro x hx hxD
      have := hD hxD; simp [hx] at this
    refine ⟨C ∪ D, ?_, fun a _ b hb => ?_⟩
    · rw [Finset.card_union_of_disjoint hdisj, hDc]; omega
    · have hbC : b ∉ C := fun h => hb (Finset.mem_union_left _ h)
      rw [singleScore_eq, if_neg hbC]; omega

lemma admissible_self {m k : ℕ} (Cstar : Finset (Fin m)) (hcard : Cstar.card = k)
    (T : Finset (Fin m)) : Admissible k (singleScore Cstar) T ↔ T = Cstar := by
  constructor
  · rintro ⟨hT, hadm⟩
    have hsub : T ⊆ Cstar := by
      intro a ha
      by_contra haC
      have hCT : Cstar ⊆ T := by
        intro b hb
        by_contra hbT
        have := hadm a ha b hbT
        rw [singleScore_eq, singleScore_eq, if_pos hb, if_neg haC] at this
        omega
      exact haC (by
        rw [Finset.eq_of_subset_of_card_le hCT (by omega)] ; exact ha)
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  · rintro rfl
    refine ⟨hcard, fun a ha b hb => ?_⟩
    rw [singleScore_eq, singleScore_eq, if_pos ha, if_neg hb]; omega

end CVProp2Aux

open CVProp2Aux in
theorem solution {m k : ℕ} (hkm : k ≤ m) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Fin m → ℝ) (hs : ∀ j, 0 ≤ s j ∧ s j ≤ 1)
    (Cstar : Finset (Fin m)) (hcard : Cstar.card = k)
    (htop : ∀ a ∈ Cstar, ∀ b ∉ Cstar, s b ≤ s a)
    (C : Finset (Fin m)) :
    successProb k p s C ≤ successProb k p s Cstar := by
  set r : ℤ := ⌈(1 - p) * (k : ℝ)⌉ with hr
  obtain ⟨T0, hT0⟩ := admissible_exists hkm C
  have step1 : successProb k p s C ≤ Q s r T0 := by
    unfold successProb Q
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro H _
    have hw := weight_nonneg s hs Finset.univ H
    split_ifs with h1 h2
    · simp
    · exact absurd (h1 T0 hT0) h2
    · simpa using hw
    · simp
  have step3 : successProb k p s Cstar = Q s r Cstar := by
    unfold successProb Q
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro H _
    have hiff : IsHonestOutcome k p H (singleScore Cstar) ↔ r ≤ ((Cstar ∩ H).card : ℤ) := by
      constructor
      · intro h; exact h Cstar ((admissible_self Cstar hcard Cstar).mpr rfl)
      · intro h T hT
        rw [(admissible_self Cstar hcard T).mp hT]; exact h
    by_cases h : r ≤ ((Cstar ∩ H).card : ℤ)
    · rw [if_pos (hiff.mpr h), if_pos h]; ring
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]; ring
  have step2 : Q s r T0 ≤ Q s r Cstar :=
    topk s hs r Cstar htop _ T0 (by rw [hT0.1, hcard]) rfl
  linarith
