-- Prove2me | solution 1 for DoubleGreedyUSM.Randomized.lemma_III_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:37:33.80995+00:00
-- url     : https://prove2.me/submissions/303860c7-ed70-4cce-8e8d-fb78060203e2

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_DoubleGreedyUSM_Randomized_Algorithm2

set_option autoImplicit false

namespace P1d081209

open DoubleGreedyUSM.Randomized

def Inv {X : Type} (q : List X) (S : Finset X × Finset X) : Prop :=
  ∀ v, (v ∈ q → (v ∈ S.1 ↔ v ∈ S.2)) ∧ (v ∉ q → v ∉ S.1 ∧ v ∈ S.2)

def Good {X : Type} (q : List X) (μ : (Finset X × Finset X) → ℝ) : Prop :=
  ∀ t, 0 ≤ μ t ∧ (μ t ≠ 0 → Inv q t)

lemma addProb_bounds {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (s : Finset X × Finset X) (u : X) : 0 ≤ addProb f s u ∧ addProb f s u ≤ 1 := by
  unfold addProb
  simp only
  have ha : 0 ≤ max (f (insert u s.1) - f s.1) 0 := le_max_right _ _
  have hb : 0 ≤ max (f (s.2.erase u) - f s.2) 0 := le_max_right _ _
  split_ifs with h
  · exact ⟨zero_le_one, le_rfl⟩
  · have hpos : 0 < max (f (insert u s.1) - f s.1) 0 + max (f (s.2.erase u) - f s.2) 0 :=
      lt_of_le_of_ne (by linarith) (Ne.symm h)
    refine ⟨div_nonneg ha hpos.le, ?_⟩
    rw [div_le_one hpos]; linarith

lemma nextMass_nonneg {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (s : Finset X × Finset X) (u : X) (t : Finset X × Finset X) : 0 ≤ nextMass f s u t := by
  have h := addProb_bounds f s u
  unfold nextMass
  have h1 : 0 ≤ (if t = (insert u s.1, s.2) then addProb f s u else 0) := by
    split_ifs <;> linarith
  have h2 : 0 ≤ (if t = (s.1, s.2.erase u) then 1 - addProb f s u else 0) := by
    split_ifs <;> linarith
  linarith

lemma good_step {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (q : List X)
    (μ : (Finset X × Finset X) → ℝ) (u : X) (hu : u ∉ q) (h : Good q μ) :
    Good (q ++ [u]) (advance f μ u) := by
  intro t
  constructor
  · unfold advance
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (h s).1 (nextMass_nonneg f s u t))
  · intro ht
    unfold advance at ht
    obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
    have hμ : μ s ≠ 0 := left_ne_zero_of_mul hs
    have hn : nextMass f s u t ≠ 0 := right_ne_zero_of_mul hs
    have hinv := (h s).2 hμ
    have hu' := (hinv u).2 hu
    have ht' : t = (insert u s.1, s.2) ∨ t = (s.1, s.2.erase u) := by
      by_contra hc
      push Not at hc
      apply hn
      simp [nextMass, hc.1, hc.2]
    intro v
    have hv := hinv v
    rcases ht' with rfl | rfl
    · by_cases hvu : v = u
      · subst hvu
        simp [hu'.2]
      · simpa [List.mem_append, List.mem_singleton, hvu, Finset.mem_insert] using hv
    · by_cases hvu : v = u
      · subst hvu
        simp [hu'.1]
      · simpa [List.mem_append, List.mem_singleton, hvu, Finset.mem_erase] using hv

lemma fold_good {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) :
    ∀ (p q : List X) (μ : (Finset X × Finset X) → ℝ), p.Nodup → (∀ u ∈ p, u ∉ q) → Good q μ →
      Good (q ++ p) (p.foldl (advance f) μ) := by
  intro p
  induction p with
  | nil => intro q μ _ _ h; simpa using h
  | cons u p ih =>
    intro q μ hnd hdis h
    rw [List.nodup_cons] at hnd
    rw [List.foldl_cons]
    have h1 := good_step f q μ u (hdis u List.mem_cons_self) h
    have h2 : ∀ w ∈ p, w ∉ q ++ [u] := by
      intro w hw hwq
      rcases List.mem_append.mp hwq with h' | h'
      · exact hdis w (List.mem_cons_of_mem u hw) h'
      · rw [List.mem_singleton] at h'
        exact hnd.1 (h' ▸ hw)
    have := ih (q ++ [u]) (advance f μ u) hnd.2 h2 h1
    simpa using this

lemma state_good {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (l : List X)
    (hl : l.Nodup) (i : ℕ) : Good (l.take i) (state f l i) := by
  have h0 : Good ([] : List X) (fun s => if s = ((∅ : Finset X), (Finset.univ : Finset X)) then 1 else 0) := by
    intro t
    constructor
    · dsimp only
      split_ifs <;> norm_num
    · intro ht v
      dsimp only at ht
      split_ifs at ht with h
      · subst h; simp
      · exact absurd rfl ht
  have := fold_good f (l.take i) [] _ (hl.sublist (List.take_sublist _ _)) (by simp) h0
  simpa [state] using this

lemma state_succ {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (l : List X)
    (k : ℕ) (hk : k < l.length) : state f l (k + 1) = advance f (state f l k) (l[k]) := by
  unfold state
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hk]
  simp

lemma expect_advance {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (μ : (Finset X × Finset X) → ℝ) (u : X) (g : Finset X × Finset X → ℝ) :
    expect (advance f μ u) g = ∑ s : Finset X × Finset X, μ s *
      (addProb f s u * g (insert u s.1, s.2) + (1 - addProb f s u) * g (s.1, s.2.erase u)) := by
  unfold expect advance
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp [nextMass, add_mul, Finset.sum_add_distrib, ite_mul]

lemma core (a b L1 L2 : ℝ) (hab : 0 ≤ a + b)
    (h : (L1 = 0 ∧ L2 ≤ a) ∨ (L2 = 0 ∧ L1 ≤ b)) :
    (if max a 0 + max b 0 = 0 then 1 else max a 0 / (max a 0 + max b 0)) * L1 +
      (1 - (if max a 0 + max b 0 = 0 then 1 else max a 0 / (max a 0 + max b 0))) * L2 ≤
    1 / 2 * ((if max a 0 + max b 0 = 0 then 1 else max a 0 / (max a 0 + max b 0)) * a +
      (1 - (if max a 0 + max b 0 = 0 then 1 else max a 0 / (max a 0 + max b 0))) * b) := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0; subst hb0
    simp
    rcases h with h | h <;> linarith [h.1, h.2]
  · rw [max_eq_right ha, max_eq_left hb]
    rcases eq_or_lt_of_le hb with hb0 | hbp
    · subst hb0
      have ha0 : a = 0 := by linarith
      subst ha0
      simp
      rcases h with h | h <;> linarith [h.1, h.2]
    · rw [if_neg (by linarith)]
      simp
      rcases h with h | h <;> linarith [h.1, h.2]
  · rw [max_eq_left ha, max_eq_right hb]
    rcases eq_or_lt_of_le ha with ha0 | hap
    · subst ha0
      have hb0 : b = 0 := by linarith
      subst hb0
      simp
      rcases h with h | h <;> linarith [h.1, h.2]
    · rw [if_neg (by linarith), add_zero, div_self (ne_of_gt hap)]
      simp
      rcases h with h | h <;> linarith [h.1, h.2]
  · rw [max_eq_left ha, max_eq_left hb]
    rcases eq_or_lt_of_le (add_nonneg ha hb) with h0 | hpos
    · have ha0 : a = 0 := by linarith
      have hb0 : b = 0 := by linarith
      subst ha0; subst hb0
      simp
      rcases h with h | h <;> linarith [h.1, h.2]
    · rw [if_neg (ne_of_gt hpos)]
      have hq : 1 - a / (a + b) = b / (a + b) := by
        field_simp; ring
      rw [hq]
      have hpa : a / (a + b) * (a + b) = a := div_mul_cancel₀ _ (ne_of_gt hpos)
      have hqb : b / (a + b) * (a + b) = b := div_mul_cancel₀ _ (ne_of_gt hpos)
      have hp0 : 0 ≤ a / (a + b) := div_nonneg ha hpos.le
      have hq0 : 0 ≤ b / (a + b) := div_nonneg hb hpos.le
      have pq : a / (a + b) * b = b / (a + b) * a := by ring
      have hd : (a / (a + b) - b / (a + b)) * (a + b) = a - b := by rw [sub_mul, hpa, hqb]
      have e : (a / (a + b) - b / (a + b)) * (a - b) =
          (a / (a + b) - b / (a + b)) ^ 2 * (a + b) := by
        rw [← hd]; ring
      have hnn : 0 ≤ (a / (a + b) - b / (a + b)) ^ 2 * (a + b) :=
        mul_nonneg (sq_nonneg _) hpos.le
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1
        nlinarith [mul_le_mul_of_nonneg_left h2 hq0]
      · subst h1
        nlinarith [mul_le_mul_of_nonneg_left h2 hp0]

lemma pointwise {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (O : Finset X) (s : Finset X × Finset X) (u : X)
    (hXY : s.1 ⊆ s.2) (huX : u ∉ s.1) (huY : u ∈ s.2) :
    f (DoubleGreedyUSM.Deterministic.optI O s) -
      (addProb f s u * f (DoubleGreedyUSM.Deterministic.optI O (insert u s.1, s.2)) +
        (1 - addProb f s u) * f (DoubleGreedyUSM.Deterministic.optI O (s.1, s.2.erase u))) ≤
    1 / 2 * ((addProb f s u * (f (insert u s.1) + f s.2) +
        (1 - addProb f s u) * (f s.1 + f (s.2.erase u))) - (f s.1 + f s.2)) := by
  obtain ⟨Xs, Ys⟩ := s
  simp only at hXY huX huY ⊢
  set P := (O ∪ Xs) ∩ Ys with hP
  have hPY : P ⊆ Ys := Finset.inter_subset_right
  have hXP : Xs ⊆ P := fun v hv => Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hv, hXY hv⟩
  have hab : 0 ≤ (f (insert u Xs) - f Xs) + (f (Ys.erase u) - f Ys) := by
    have h := hf (insert u Xs) (Ys.erase u)
    have e1 : insert u Xs ∪ Ys.erase u = Ys := by
      ext v
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ((rfl | hv) | ⟨_, hv⟩)
        · exact huY
        · exact hXY hv
        · exact hv
      · intro hv
        by_cases hvu : v = u
        · exact Or.inl (Or.inl hvu)
        · exact Or.inr ⟨hvu, hv⟩
    have e2 : insert u Xs ∩ Ys.erase u = Xs := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨rfl | hv, hvu, _⟩
        · exact absurd rfl hvu
        · exact hv
      · intro hv
        exact ⟨Or.inr hv, fun h => huX (h ▸ hv), hXY hv⟩
    rw [e1, e2] at h
    linarith
  have key : ∀ L1 L2 : ℝ, (L1 = 0 ∧ L2 ≤ f (insert u Xs) - f Xs) ∨
      (L2 = 0 ∧ L1 ≤ f (Ys.erase u) - f Ys) →
      f (DoubleGreedyUSM.Deterministic.optI O (insert u Xs, Ys)) = f P - L1 →
      f (DoubleGreedyUSM.Deterministic.optI O (Xs, Ys.erase u)) = f P - L2 →
      f (DoubleGreedyUSM.Deterministic.optI O (Xs, Ys)) -
        (addProb f (Xs, Ys) u * f (DoubleGreedyUSM.Deterministic.optI O (insert u Xs, Ys)) +
          (1 - addProb f (Xs, Ys) u) * f (DoubleGreedyUSM.Deterministic.optI O (Xs, Ys.erase u))) ≤
      1 / 2 * ((addProb f (Xs, Ys) u * (f (insert u Xs) + f Ys) +
          (1 - addProb f (Xs, Ys) u) * (f Xs + f (Ys.erase u))) - (f Xs + f Ys)) := by
    intro L1 L2 hc e1 e2
    rw [e1, e2]
    have h0 : DoubleGreedyUSM.Deterministic.optI O (Xs, Ys) = P := rfl
    rw [h0]
    have hc' := core _ _ L1 L2 hab hc
    unfold addProb
    simp only
    nlinarith [hc']
  by_cases huO : u ∈ O
  · have huP : u ∈ P := Finset.mem_inter.mpr ⟨Finset.mem_union_left _ huO, huY⟩
    apply key 0 (f P - f (P.erase u)) (Or.inl ⟨rfl, ?_⟩)
    · have : DoubleGreedyUSM.Deterministic.optI O (insert u Xs, Ys) = P := by
        unfold DoubleGreedyUSM.Deterministic.optI
        ext v
        simp only [hP, Finset.mem_inter, Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro ⟨(h | rfl | h), hv⟩
          · exact ⟨Or.inl h, hv⟩
          · exact ⟨Or.inl huO, hv⟩
          · exact ⟨Or.inr h, hv⟩
        · rintro ⟨(h | h), hv⟩
          · exact ⟨Or.inl h, hv⟩
          · exact ⟨Or.inr (Or.inr h), hv⟩
      rw [this]; ring
    · have : DoubleGreedyUSM.Deterministic.optI O (Xs, Ys.erase u) = P.erase u := by
        unfold DoubleGreedyUSM.Deterministic.optI
        ext v
        simp only [hP, Finset.mem_inter, Finset.mem_erase]
        tauto
      rw [this]; ring
    · -- f P - f (P.erase u) ≤ f (insert u Xs) - f Xs
      have h := hf (insert u Xs) (P.erase u)
      have e1 : insert u Xs ∪ P.erase u = P := by
        ext v
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ((rfl | hv) | ⟨_, hv⟩)
          · exact huP
          · exact hXP hv
          · exact hv
        · intro hv
          by_cases hvu : v = u
          · exact Or.inl (Or.inl hvu)
          · exact Or.inr ⟨hvu, hv⟩
      have e2 : insert u Xs ∩ P.erase u = Xs := by
        ext v
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨rfl | hv, hvu, _⟩
          · exact absurd rfl hvu
          · exact hv
        · intro hv
          exact ⟨Or.inr hv, fun h => huX (h ▸ hv), hXP hv⟩
      rw [e1, e2] at h
      linarith
  · have huP : u ∉ P := fun h => huO (by
      rcases (Finset.mem_union.mp (Finset.mem_inter.mp h).1) with h' | h'
      · exact h'
      · exact absurd h' huX)
    apply key (f P - f (insert u P)) 0 (Or.inr ⟨rfl, ?_⟩)
    · have : DoubleGreedyUSM.Deterministic.optI O (insert u Xs, Ys) = insert u P := by
        unfold DoubleGreedyUSM.Deterministic.optI
        ext v
        simp only [hP, Finset.mem_inter, Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro ⟨(h | rfl | h), hv⟩
          · exact Or.inr ⟨Or.inl h, hv⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨Or.inr h, hv⟩
        · rintro (rfl | ⟨(h | h), hv⟩)
          · exact ⟨Or.inr (Or.inl rfl), huY⟩
          · exact ⟨Or.inl h, hv⟩
          · exact ⟨Or.inr (Or.inr h), hv⟩
      rw [this]; ring
    · have : DoubleGreedyUSM.Deterministic.optI O (Xs, Ys.erase u) = P := by
        unfold DoubleGreedyUSM.Deterministic.optI
        ext v
        simp only [hP, Finset.mem_inter, Finset.mem_erase]
        constructor
        · rintro ⟨h, _, hv⟩; exact ⟨h, hv⟩
        · rintro ⟨h, hv⟩
          refine ⟨h, ?_, hv⟩
          rintro rfl
          exact huP (Finset.mem_inter.mpr ⟨h, hv⟩)
      rw [this]; ring
    · -- f P - f (insert u P) ≤ f (Ys.erase u) - f Ys
      have h := hf (insert u P) (Ys.erase u)
      have e1 : insert u P ∪ Ys.erase u = Ys := by
        ext v
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ((rfl | hv) | ⟨_, hv⟩)
          · exact huY
          · exact hPY hv
          · exact hv
        · intro hv
          by_cases hvu : v = u
          · exact Or.inl (Or.inl hvu)
          · exact Or.inr ⟨hvu, hv⟩
      have e2 : insert u P ∩ Ys.erase u = P := by
        ext v
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨rfl | hv, hvu, _⟩
          · exact absurd rfl hvu
          · exact hv
        · intro hv
          exact ⟨Or.inr hv, fun h => huP (h ▸ hv), hPY hv⟩
      rw [e1, e2] at h
      linarith

lemma step_ineq {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (O : Finset X) (q : List X)
    (μ : (Finset X × Finset X) → ℝ) (hG : Good q μ) (u : X) (hu : u ∉ q) :
    expect μ (fun s => f (DoubleGreedyUSM.Deterministic.optI O s)) -
        expect (advance f μ u) (fun s => f (DoubleGreedyUSM.Deterministic.optI O s)) ≤
      (1 / 2 : ℝ) * (expect (advance f μ u) (fun s => f s.1 + f s.2) -
        expect μ (fun s => f s.1 + f s.2)) := by
  rw [expect_advance, expect_advance]
  unfold expect
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : μ s = 0
  · simp [hs]
  · have hinv := (hG s).2 hs
    have h0 := (hG s).1
    have hu' := (hinv u).2 hu
    have hXY : s.1 ⊆ s.2 := by
      intro v hv
      by_cases hvq : v ∈ q
      · exact ((hinv v).1 hvq).mp hv
      · exact absurd hv ((hinv v).2 hvq).1
    have pw := pointwise f hf O s u hXY hu'.1 hu'.2
    have := mul_le_mul_of_nonneg_left pw h0
    simp only at this ⊢
    linarith [this]

end P1d081209

open DoubleGreedyUSM.Randomized in
theorem solution {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (hf0 : ∀ S : Finset X, 0 ≤ f S)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x : X, x ∈ l)
    (O : Finset X) (hO : ∀ S : Finset X, f S ≤ f O) :
    ∀ i (hi : 1 ≤ i) (hin : i ≤ l.length),
      expect (state f l (i - 1)) (fun s => f (DoubleGreedyUSM.Deterministic.optI O s)) -
        expect (state f l i) (fun s => f (DoubleGreedyUSM.Deterministic.optI O s)) ≤
      (1 / 2 : ℝ) *
        (expect (state f l i) (fun s => f s.1 + f s.2) -
          expect (state f l (i - 1)) (fun s => f s.1 + f s.2)) := by
  intro i hi hin
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk' : k < l.length := by omega
  have hu : l[k] ∉ l.take k := by
    intro hm
    rw [List.mem_iff_getElem] at hm
    obtain ⟨j, hj, hjk⟩ := hm
    rw [List.getElem_take] at hjk
    have hj' : j < k := by simp at hj; omega
    have := (List.Nodup.getElem_inj_iff hl).mp hjk
    omega
  have st := P1d081209.step_ineq f hf O (l.take k) (state f l k)
    (P1d081209.state_good f l hl k) (l[k]) hu
  simp only [Nat.add_sub_cancel]
  rw [P1d081209.state_succ f l k hk']
  exact st
