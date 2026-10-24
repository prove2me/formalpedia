-- Prove2me | solution 1 for CommitteeVoting.SingleVoter.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T14:26:10.55247+00:00
-- url     : https://prove2.me/submissions/982d6491-711f-4f2f-8675-c88f749a9aa6

import Mathlib
import Definitions.Def_CommitteeVoting_SingleVoter_PoissonBinomial

open CommitteeVoting.SingleVoter

namespace CVLemma1Aux

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

/-- Marginalisation: a function of `S ∩ H` averaged over `H ⊆ U` equals its average over the
Poisson binomial outcomes of `S`. -/
lemma marginal {m : ℕ} (s : Fin m → ℝ) (S : Finset (Fin m)) (g : Finset (Fin m) → ℝ) :
    ∀ n : ℕ, ∀ U : Finset (Fin m), S ⊆ U → (U \ S).card = n →
      ∑ H ∈ U.powerset, pbWeight s U H * g (S ∩ H) = ∑ A ∈ S.powerset, pbWeight s S A * g A := by
  intro n
  induction n with
  | zero =>
    intro U hSU hn
    have hUS : U = S := by
      apply le_antisymm _ hSU
      intro x hx; by_contra hxS
      have : x ∈ U \ S := Finset.mem_sdiff.mpr ⟨hx, hxS⟩
      rw [Finset.card_eq_zero.mp hn] at this; simp at this
    subst hUS
    apply Finset.sum_congr rfl
    intro H hH
    rw [Finset.inter_eq_right.mpr (Finset.mem_powerset.mp hH)]
  | succ n ih =>
    intro U hSU hn
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (U \ S).card)
    obtain ⟨hbU, hbS⟩ := Finset.mem_sdiff.mp hb
    rw [decomp s U b hbU]
    have e : ∀ t, S ∩ insert b t = S ∩ t := fun t => Finset.inter_insert_of_notMem hbS
    simp only [e]
    have : ∀ t ∈ (U.erase b).powerset, pbWeight s (U.erase b) t * (s b * g (S ∩ t) + (1 - s b) * g (S ∩ t))
        = pbWeight s (U.erase b) t * g (S ∩ t) := fun t _ => by ring
    rw [Finset.sum_congr rfl this]
    apply ih
    · intro x hx; exact Finset.mem_erase.mpr ⟨fun h => hbS (h ▸ hx), hSU hx⟩
    · have : U.erase b \ S = (U \ S).erase b := by
        ext x; simp [Finset.mem_sdiff, Finset.mem_erase]; tauto
      rw [this, Finset.card_erase_of_mem hb, hn]; rfl

end CVLemma1Aux

open CVLemma1Aux in
theorem solution {m k : ℕ} (hkm : k ≤ m) (p : Fin m → ℝ) (hanti : Antitone p)
    (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) (x : ℕ) (hx : 0 < x)
    (S : Finset (Fin m)) (hS : S.card = k) :
    pbTail p S x ≤ pbTail p (Finset.univ.filter fun j : Fin m => j.val < k) x := by
  have key : ∀ T : Finset (Fin m), pbTail p T x = Q p ((x : ℤ) + 1) T := by
    intro T
    unfold pbTail Q
    rw [Finset.sum_filter]
    rw [marginal p T (fun A => if ((x : ℤ) + 1) ≤ (A.card : ℤ) then 1 else 0) _ Finset.univ
      (Finset.subset_univ T) rfl]
    apply Finset.sum_congr rfl
    intro A _
    by_cases h : x < A.card
    · rw [if_pos h, if_pos (by omega)]; ring
    · rw [if_neg h, if_neg (by omega)]; ring
  set Cstar := (Finset.univ.filter fun j : Fin m => j.val < k)
  have hC : Cstar.card = k := by
    rw [Fin.card_filter_val_lt]; omega
  have htop : ∀ a ∈ Cstar, ∀ b ∉ Cstar, p b ≤ p a := by
    intro a ha b hb
    simp only [Cstar, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at ha hb
    exact hanti (Fin.le_def.mpr (by omega))
  rw [key, key]
  exact topk p hp _ Cstar htop _ S (by rw [hS, hC]) rfl
