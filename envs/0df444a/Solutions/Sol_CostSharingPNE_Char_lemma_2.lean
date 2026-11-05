-- Prove2me | solution 1 for CostSharingPNE.Char.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:22:14.932634+00:00
-- url     : https://prove2.me/submissions/ce67ed89-efe4-40c2-8793-400d2861c45f

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Definitions.Def_CostSharingPNE_Char_Basis

open CostSharingPNE.Char

namespace CSPLemma2Aux

variable {n : ℕ}

/-- Möbius inversion on the Boolean lattice: `W(S) = ∑_{T ⊆ S} q^W_T`. -/
lemma sum_mobius (S : Finset (Fin n)) : ∀ W : Welfare n, ∑ T ∈ S.powerset, mobius W T = W S := by
  induction S using Finset.induction_on with
  | empty => intro W; simp [mobius]
  | insert a S ha ih =>
    intro W
    rw [Finset.sum_powerset_insert ha]
    have key : ∀ T ∈ S.powerset, mobius W (insert a T) =
        - mobius W T + mobius (fun R => W (insert a R)) T := by
      intro T hT
      have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
      unfold mobius
      rw [Finset.sum_powerset_insert haT, Finset.card_insert_of_notMem haT, ← Finset.sum_neg_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro R hR
        have hRT := Finset.card_le_card (Finset.mem_powerset.mp hR)
        rw [show T.card + 1 - R.card = (T.card - R.card) + 1 by omega, pow_succ]
        ring
      · apply Finset.sum_congr rfl
        intro R hR
        have haR : a ∉ R := fun h => haT (Finset.mem_powerset.mp hR h)
        rw [Finset.card_insert_of_notMem haR]
        congr 2
        omega
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_neg_distrib, ih W,
      ih (fun R => W (insert a R))]
    ring

lemma mem_contributing (W : Welfare n) (S : Finset (Fin n)) (i : Fin n) :
    i ∈ contributing W S ↔ ∃ T ∈ coalitions W, T ⊆ S ∧ i ∈ T := by
  unfold contributing coalitionsIn
  simp only [Finset.mem_biUnion, Finset.mem_filter, id]
  constructor
  · rintro ⟨T, ⟨h1, h2⟩, h3⟩; exact ⟨T, h1, h2, h3⟩
  · rintro ⟨T, h1, h2, h3⟩; exact ⟨T, ⟨h1, h2⟩, h3⟩

lemma W_erase (W : Welfare n) (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S)
    (hic : i ∉ contributing W S) : W S = W (S.erase i) := by
  rw [← sum_mobius S W, ← sum_mobius (S.erase i) W]
  conv_lhs => rw [← Finset.insert_erase hi]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase i S)]
  rw [add_eq_left]
  apply Finset.sum_eq_zero
  intro t ht
  by_contra hne
  apply hic
  rw [mem_contributing]
  refine ⟨insert i t, ?_, ?_, Finset.mem_insert_self _ _⟩
  · unfold coalitions
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Finset.insert_nonempty _ _, hne⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; exact hi
    · exact Finset.mem_of_mem_erase (Finset.mem_powerset.mp ht h)

/-- Counterexample 1 (p. 20): a two-resource game between `p` and `q`. -/
lemma cx1 (W : Welfare n) (f : Welfare n → Rule n) (hpne : GuaranteesPNE {W} f)
    (S : Finset (Fin n)) (p q : Fin n) (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    ¬ (f W p S < f W p (S.erase q) ∧ f W q (S.erase p) < f W q S) := by
  classical
  rintro ⟨h1, h2⟩
  let A : Fin n → Finset (Finset (Fin 2)) := fun k =>
    if k = p ∨ k = q then {{0}, {1}} else if k ∈ S then {Finset.univ} else {∅}
  have hA : ∀ k, (A k).Nonempty := by
    intro k; simp only [A]; split_ifs <;> simp
  obtain ⟨a, ha, hN⟩ := hpne 2 (by norm_num) (fun _ => W) (fun _ => rfl) A hA
  have hother : ∀ (b : Fin n → Finset (Fin 2)), (∀ k, k ≠ p → k ≠ q → b k = a k) →
      ∀ r, players b r = S.filter (fun k => (k = p → r ∈ b p) ∧ (k = q → r ∈ b q)) := by
    intro b hb r
    ext k
    simp only [players, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hkp : k = p
    · subst hkp; simp [hp, hpq]
    by_cases hkq : k = q
    · subst hkq; simp [hq, hkp]
    have hak := ha k
    rw [hb k hkp hkq]
    simp only [A, hkp, hkq, or_self, if_false] at hak
    by_cases hkS : k ∈ S
    · rw [if_pos hkS, Finset.mem_singleton] at hak
      simp [hak, hkS, hkp, hkq]
    · rw [if_neg hkS, Finset.mem_singleton] at hak
      simp [hak, hkS]
  have hap := ha p
  have haq := ha q
  simp only [A, true_or, or_true, if_true, Finset.mem_insert, Finset.mem_singleton] at hap haq
  have hut : ∀ (b : Fin n → Finset (Fin 2)) (k : Fin n) (x : Fin 2),
      b k = {x} → utility (fun _ => W) f b k = f W k (players b x) := by
    intro b k x hx; unfold utility; rw [hx, Finset.sum_singleton]
  obtain ⟨x, hx⟩ : ∃ x : Fin 2, a p = {x} := by rcases hap with h | h <;> exact ⟨_, h⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin 2, a q = {y} := by rcases haq with h | h <;> exact ⟨_, h⟩
  have hfin : ∀ z : Fin 2, z = 0 ∨ z = 1 := by intro z; fin_cases z <;> simp
  have hrefl : ∀ k, k ≠ p → k ≠ q → a k = a k := fun _ _ _ => rfl
  by_cases hxy : x = y
  · -- together: p deviates to the other resource
    subst hxy
    set x' : Fin 2 := if x = 0 then 1 else 0 with hx'
    have hxx' : x' ≠ x := by
      rcases hfin x with h | h <;> simp [hx', h]
    have hmem : ({x'} : Finset (Fin 2)) ∈ A p := by
      simp only [A, true_or, if_true]
      rcases hfin x' with h | h <;> simp [h]
    have hdev := hN p {x'} hmem
    set b := Function.update a p {x'} with hb
    have hbo : ∀ k, k ≠ p → k ≠ q → b k = a k := fun k hk _ => by
      rw [hb, Function.update_of_ne hk]
    have hbp : b p = {x'} := by simp [hb]
    have hbq : b q = {x} := by rw [hb, Function.update_of_ne (Ne.symm hpq), hy]
    rw [hut b p x' hbp, hut a p x hx] at hdev
    have e1 : players a x = S := by
      rw [hother a hrefl x]
      ext k; simp [hx, hy]
    have e2 : players b x' = S.erase q := by
      rw [hother b hbo x']
      ext k
      simp only [Finset.mem_filter, hbp, hbq, Finset.mem_singleton, Finset.mem_erase]
      constructor
      · rintro ⟨hk, -, h⟩
        exact ⟨fun hkq => hxx' (h hkq), hk⟩
      · rintro ⟨hkq, hk⟩
        exact ⟨hk, fun _ => trivial, fun h => absurd h hkq⟩
    rw [e1, e2] at hdev
    linarith
  · -- apart: q deviates to p's resource
    have hmem : ({x} : Finset (Fin 2)) ∈ A q := by
      simp only [A, or_true, if_true]
      rcases hfin x with h | h <;> simp [h]
    have hdev := hN q {x} hmem
    set b := Function.update a q {x} with hb
    have hbo : ∀ k, k ≠ p → k ≠ q → b k = a k := fun k _ hk => by
      rw [hb, Function.update_of_ne hk]
    have hbq : b q = {x} := by simp [hb]
    have hbp : b p = {x} := by rw [hb, Function.update_of_ne hpq, hx]
    rw [hut b q x hbq, hut a q y hy] at hdev
    have e1 : players b x = S := by
      rw [hother b hbo x]
      ext k; simp [hbp, hbq]
    have e2 : players a y = S.erase p := by
      rw [hother a hrefl y]
      ext k
      simp only [Finset.mem_filter, hx, hy, Finset.mem_singleton, Finset.mem_erase]
      constructor
      · rintro ⟨hk, h, -⟩
        exact ⟨fun hkp => hxy (h hkp).symm, hk⟩
      · rintro ⟨hkp, hk⟩
        exact ⟨hk, fun h => absurd h hkp, fun _ => trivial⟩
    rw [e1, e2] at hdev
    linarith

end CSPLemma2Aux

open CSPLemma2Aux in
theorem solution (n : ℕ) (hn : 1 < n) (W : Welfare n) (f : Welfare n → Rule n)
    (hbb : IsBudgetBalanced (f W) W) (hpne : GuaranteesPNE {W} f) :
    ∀ S : Finset (Fin n), ∀ i ∈ S \ contributing W S, f W i S = 0 := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro i hi
    rw [Finset.mem_sdiff] at hi
    obtain ⟨hiS, hic⟩ := hi
    by_contra hne
    have hW := W_erase W S i hiS hic
    have b1 := hbb S
    have b2 := hbb (S.erase i)
    rw [← Finset.add_sum_erase S _ hiS] at b1
    have hfi : f W i S = ∑ k ∈ S.erase i, (f W k (S.erase i) - f W k S) := by
      rw [Finset.sum_sub_distrib]; linarith
    obtain ⟨j, hj, hpos⟩ : ∃ j ∈ S.erase i, 0 < f W i S * (f W j (S.erase i) - f W j S) := by
      by_contra hcon
      push Not at hcon
      have : f W i S * f W i S ≤ 0 := by
        rw [hfi, Finset.mul_sum]
        rw [← hfi]
        exact Finset.sum_nonpos hcon
      have := mul_self_pos.mpr hne
      linarith
    have hjS : j ∈ S := Finset.mem_of_mem_erase hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hsub : S.erase j ⊂ S := Finset.erase_ssubset hjS
    have hzero : f W i (S.erase j) = 0 := by
      apply ih _ hsub
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_erase.mpr ⟨Ne.symm hji, hiS⟩, fun hc => hic ?_⟩
      rw [mem_contributing] at hc ⊢
      obtain ⟨T, hT, hTS, hiT⟩ := hc
      exact ⟨T, hT, hTS.trans (Finset.erase_subset _ _), hiT⟩
    rcases lt_or_gt_of_ne hne with hneg | hposi
    · have h2 : f W j (S.erase i) - f W j S < 0 := by
        by_contra h; push Not at h; nlinarith
      exact cx1 W f hpne S i j hiS hjS (Ne.symm hji) ⟨by linarith, by linarith⟩
    · have h2 : 0 < f W j (S.erase i) - f W j S := by
        by_contra h; push Not at h; nlinarith
      exact cx1 W f hpne S j i hjS hiS hji ⟨by linarith, by linarith⟩
