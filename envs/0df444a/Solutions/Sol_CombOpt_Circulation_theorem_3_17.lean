-- Prove2me | solution 1 for CombOpt.Circulation.theorem_3_17
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T14:28:33.804776+00:00
-- url     : https://prove2.me/submissions/0a4ccb54-6503-49cc-8b6f-c69d67f12099

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph
import Definitions.Def_CombOpt_Circulation_delta
import Definitions.Def_CombOpt_Circulation_IsIntegralVector
import Definitions.Def_CombOpt_Circulation_IsIntegralBound
import Definitions.Def_CombOpt_Circulation_IsCirculation

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Hoff61
open CombOpt.Circulation

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

noncomputable def Z : AddSubgroup ℝ := (Int.castAddHom ℝ).range

lemma mem_Z {r : ℝ} : r ∈ Z ↔ ∃ n : ℤ, r = n := by
  unfold Z
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa using hn.symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by simp⟩

/-- Per-arc cut contribution `u_e [e enters A] - l_e [e leaves A]`. -/
noncomputable def c (G : MultiDigraph V E) (l u : E → ℝ) (e : E) (A : Finset V) : ℝ :=
  (if G.tail e ∉ A ∧ G.head e ∈ A then u e else 0) -
    (if G.tail e ∈ A ∧ G.head e ∉ A then l e else 0)

/-- Slack of the Hoffman–Gale condition for the arc set `F` and demands `b`. -/
noncomputable def f (G : MultiDigraph V E) (l u : E → ℝ) (F : Finset E) (b : V → ℝ)
    (A : Finset V) : ℝ :=
  ∑ e ∈ F, c G l u e A - ∑ v ∈ A, b v

/-- Net inflow at `v` using only arcs of `F`. -/
noncomputable def exF (G : MultiDigraph V E) (F : Finset E) (x : E → ℝ) (v : V) : ℝ :=
  ∑ e ∈ F, ((if G.head e = v then x e else 0) - (if G.tail e = v then x e else 0))

lemma c_submod (G : MultiDigraph V E) (l u : E → ℝ) (e : E) (hle : l e ≤ u e)
    (A B : Finset V) :
    c G l u e (A ∩ B) + c G l u e (A ∪ B) ≤ c G l u e A + c G l u e B := by
  unfold c
  by_cases h1 : G.tail e ∈ A <;> by_cases h2 : G.tail e ∈ B <;>
    by_cases h3 : G.head e ∈ A <;> by_cases h4 : G.head e ∈ B <;>
    simp [h1, h2, h3, h4, Finset.mem_inter, Finset.mem_union] <;> linarith

lemma sum_b' (b : V → ℝ) (p q : V) (t : ℝ) (A : Finset V) :
    ∑ v ∈ A, (b v - (if v = q then t else 0) + (if v = p then t else 0)) =
      ∑ v ∈ A, b v - (if q ∈ A then t else 0) + (if p ∈ A then t else 0) := by
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']

lemma base_b (b : V → ℝ) (hsum : ∑ v, b v = 0)
    (h : ∀ A : Finset V, 0 ≤ -∑ v ∈ A, b v) : ∀ v, b v = 0 := by
  intro v
  have h1 := h {v}
  have h2 := h (Finset.univ.erase v)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)] at hsum
  simp only [Finset.sum_singleton] at h1
  linarith

lemma c_mem_Z (G : MultiDigraph V E) (l u : E → ℝ) (hlZ : ∀ e, l e ∈ Z) (huZ : ∀ e, u e ∈ Z)
    (e : E) (A : Finset V) : c G l u e A ∈ Z := by
  unfold c
  apply Z.sub_mem <;> split_ifs <;> first | exact Z.zero_mem | exact hlZ e | exact huZ e

set_option maxHeartbeats 1000000 in
theorem main (G : MultiDigraph V E) (l u : E → ℝ) (hlu : ∀ e, l e ≤ u e) (F : Finset E) :
    ∀ b : V → ℝ, ∑ v, b v = 0 → (∀ A, 0 ≤ f G l u F b A) →
      ∃ x : E → ℝ, (∀ e ∈ F, l e ≤ x e ∧ x e ≤ u e) ∧ (∀ v, exF G F x v = b v) ∧
        ((∀ e, l e ∈ Z) → (∀ e, u e ∈ Z) → (∀ v, b v ∈ Z) → ∀ e, x e ∈ Z) := by
  classical
  refine Finset.induction_on F ?_ ?_
  · intro b hsum hf
    have hb : ∀ v, b v = 0 := base_b b hsum (fun A => by simpa [f] using hf A)
    refine ⟨0, by simp, fun v => by simp [exF, hb], fun _ _ _ e => by simp⟩
  · intro e0 F' he0 ih b hsum hf
    have hsub : ∀ A B : Finset V, G.head e0 ∈ A → G.tail e0 ∉ A → G.tail e0 ∈ B →
        G.head e0 ∉ B →
        u e0 - f G l u (insert e0 F') b A ≤ l e0 + f G l u (insert e0 F') b B := by
      intro A B h1 h2 h3 h4
      have hAB := hf (A ∩ B)
      have hAB' := hf (A ∪ B)
      have k1 : c G l u e0 A = u e0 := by simp [c, h1, h2]
      have k2 : c G l u e0 B = - l e0 := by simp [c, h3, h4]
      have k3 : c G l u e0 (A ∩ B) = 0 := by simp [c, Finset.mem_inter, h1, h2, h3, h4]
      have k4 : c G l u e0 (A ∪ B) = 0 := by simp [c, Finset.mem_union, h1, h2, h3, h4]
      have hs : ∑ e ∈ F', (c G l u e (A ∩ B) + c G l u e (A ∪ B)) ≤
          ∑ e ∈ F', (c G l u e A + c G l u e B) :=
        Finset.sum_le_sum (fun e _ => c_submod G l u e (hlu e) A B)
      have hb := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := b)
      simp only [f, Finset.sum_insert he0] at hAB hAB' ⊢
      simp only [Finset.sum_add_distrib] at hs
      rw [k1, k2]
      rw [k3] at hAB
      rw [k4] at hAB'
      linarith
    obtain ⟨t, ht_l, ht_u, ht_A, ht_B, ht_mem⟩ : ∃ t : ℝ, l e0 ≤ t ∧ t ≤ u e0 ∧
        (∀ A : Finset V, G.head e0 ∈ A → G.tail e0 ∉ A →
          u e0 - f G l u (insert e0 F') b A ≤ t) ∧
        (∀ B : Finset V, G.tail e0 ∈ B → G.head e0 ∉ B →
          t ≤ l e0 + f G l u (insert e0 F') b B) ∧
        (t = l e0 ∨ ∃ A : Finset V, t = u e0 - f G l u (insert e0 F') b A) := by
      let Lw : Finset ℝ := insert (l e0)
        ((Finset.univ.filter (fun A : Finset V => G.head e0 ∈ A ∧ G.tail e0 ∉ A)).image
          (fun A => u e0 - f G l u (insert e0 F') b A))
      have hne : Lw.Nonempty := Finset.insert_nonempty _ _
      refine ⟨Lw.max' hne, Finset.le_max' _ _ (Finset.mem_insert_self _ _), ?_, ?_, ?_, ?_⟩
      · apply Finset.max'_le
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact hlu e0
        · obtain ⟨A, _, rfl⟩ := Finset.mem_image.1 hy
          linarith [hf A]
      · intro A h1 h2
        have hmem : u e0 - f G l u (insert e0 F') b A ∈ Lw := by
          simp only [Lw, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact Or.inr ⟨A, ⟨h1, h2⟩, rfl⟩
        exact Finset.le_max' _ _ hmem
      · intro B h3 h4
        apply Finset.max'_le
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · linarith [hf B]
        · obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
          exact hsub A B hA.1 hA.2 h3 h4
      · have hm := Finset.max'_mem Lw hne
        rcases Finset.mem_insert.1 hm with h | h
        · exact Or.inl h
        · obtain ⟨A, _, hA⟩ := Finset.mem_image.1 h
          exact Or.inr ⟨A, hA.symm⟩
    obtain ⟨b', hb'⟩ : ∃ b' : V → ℝ, ∀ v,
        b' v = b v - (if v = G.head e0 then t else 0) + (if v = G.tail e0 then t else 0) :=
      ⟨_, fun v => rfl⟩
    have hsb' : ∀ A : Finset V, ∑ v ∈ A, b' v = ∑ v ∈ A, b v -
        (if G.head e0 ∈ A then t else 0) + (if G.tail e0 ∈ A then t else 0) := by
      intro A
      simp_rw [hb']
      exact sum_b' b _ _ t A
    have hsum' : ∑ v, b' v = 0 := by
      rw [hsb']
      simp [hsum]
    have hf' : ∀ A, 0 ≤ f G l u F' b' A := by
      intro A
      have h0 := hf A
      simp only [f, Finset.sum_insert he0] at h0
      simp only [f]
      rw [hsb' A]
      by_cases h1 : G.tail e0 ∈ A <;> by_cases h2 : G.head e0 ∈ A
      · have k : c G l u e0 A = 0 := by simp [c, h1, h2]
        rw [k] at h0
        rw [if_pos h1, if_pos h2]
        linarith
      · have k : c G l u e0 A = - l e0 := by simp [c, h1, h2]
        have h5 := ht_B A h1 h2
        simp only [f, Finset.sum_insert he0] at h5
        rw [k] at h0 h5
        rw [if_pos h1, if_neg h2]
        linarith
      · have k : c G l u e0 A = u e0 := by simp [c, h1, h2]
        have h5 := ht_A A h2 h1
        simp only [f, Finset.sum_insert he0] at h5
        rw [k] at h0 h5
        rw [if_neg h1, if_pos h2]
        linarith
      · have k : c G l u e0 A = 0 := by simp [c, h1, h2]
        rw [k] at h0
        rw [if_neg h1, if_neg h2]
        linarith
    obtain ⟨x', hx1, hx2, hx3⟩ := ih b' hsum' hf'
    refine ⟨Function.update x' e0 t, ?_, ?_, ?_⟩
    · intro e he
      rcases Finset.mem_insert.1 he with rfl | he'
      · simp only [Function.update_self]
        exact ⟨ht_l, ht_u⟩
      · have hne : e ≠ e0 := by rintro rfl; exact he0 he'
        rw [Function.update_of_ne hne]
        exact hx1 e he'
    · intro v
      have hF' : exF G F' (Function.update x' e0 t) v = exF G F' x' v := by
        unfold exF
        refine Finset.sum_congr rfl (fun e he => ?_)
        have hne : e ≠ e0 := by rintro rfl; exact he0 he
        rw [Function.update_of_ne hne]
      have hins : exF G (insert e0 F') (Function.update x' e0 t) v =
          ((if G.head e0 = v then t else 0) - (if G.tail e0 = v then t else 0)) +
            exF G F' (Function.update x' e0 t) v := by
        unfold exF
        rw [Finset.sum_insert he0, Function.update_self]
      rw [hins, hF', hx2 v, hb' v]
      simp only [@eq_comm _ v]
      ring
    · intro hlZ huZ hbZ e
      have htZ : t ∈ Z := by
        rcases ht_mem with h | ⟨A, h⟩
        · rw [h]; exact hlZ e0
        · rw [h]
          apply Z.sub_mem (huZ e0)
          unfold f
          exact Z.sub_mem (Z.sum_mem fun e _ => c_mem_Z G l u hlZ huZ e A)
            (Z.sum_mem fun v _ => hbZ v)
      have hb'Z : ∀ v, b' v ∈ Z := by
        intro v
        rw [hb' v]
        apply Z.add_mem
        · apply Z.sub_mem (hbZ v)
          split_ifs
          · exact htZ
          · exact Z.zero_mem
        · split_ifs
          · exact htZ
          · exact Z.zero_mem
      by_cases hee : e = e0
      · subst hee
        rw [Function.update_self]
        exact htZ
      · rw [Function.update_of_ne hee]
        exact hx3 hlZ huZ hb'Z e

lemma sum_delta_compl {M : Type*} [AddCommMonoid M] (G : MultiDigraph V E) (w : E → M)
    (A : Finset V) :
    ∑ e ∈ delta G Aᶜ, w e = ∑ e, if G.tail e ∉ A ∧ G.head e ∈ A then w e else 0 := by
  unfold delta
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  simp [Finset.mem_compl]

lemma sum_delta {M : Type*} [AddCommMonoid M] (G : MultiDigraph V E) (w : E → M)
    (A : Finset V) :
    ∑ e ∈ delta G A, w e = ∑ e, if G.tail e ∈ A ∧ G.head e ∉ A then w e else 0 := by
  unfold delta
  rw [Finset.sum_filter]

lemma exF_univ (G : MultiDigraph V E) (x : E → ℝ) (v : V) :
    exF G Finset.univ x v = excess G x v := by
  unfold exF excess
  rw [Finset.sum_sub_distrib, Finset.sum_filter, Finset.sum_filter]

lemma cut_balance (G : MultiDigraph V E) (x : E → ℝ) (hx : IsCirculation G x)
    (A : Finset V) : ∑ e ∈ delta G Aᶜ, x e = ∑ e ∈ delta G A, x e := by
  have h0 : ∑ v ∈ A, exF G Finset.univ x v = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    rw [exF_univ]
    exact hx v
  unfold exF at h0
  rw [Finset.sum_comm] at h0
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq] at h0
  have key : ∑ e, ((if G.tail e ∉ A ∧ G.head e ∈ A then x e else 0) -
      (if G.tail e ∈ A ∧ G.head e ∉ A then x e else 0)) =
      ∑ e, ((if G.head e ∈ A then x e else 0) - (if G.tail e ∈ A then x e else 0)) := by
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases h1 : G.tail e ∈ A <;> by_cases h2 : G.head e ∈ A <;> simp [h1, h2]
  simp only [Finset.sum_sub_distrib] at h0 key
  rw [sum_delta_compl, sum_delta]
  linarith

lemma real_hoffman (G : MultiDigraph V E) (l u : E → ℝ) (hlu : ∀ e, l e ≤ u e)
    (hcond : ∀ A : Finset V, ∑ e ∈ delta G Aᶜ, u e ≥ ∑ e ∈ delta G A, l e) :
    ∃ x : E → ℝ, IsCirculation G x ∧ (∀ e, l e ≤ x e ∧ x e ≤ u e) ∧
      ((∀ e, l e ∈ Z) → (∀ e, u e ∈ Z) → ∀ e, x e ∈ Z) := by
  have hf : ∀ A, 0 ≤ f G l u Finset.univ 0 A := by
    intro A
    have h := hcond A
    rw [sum_delta_compl, sum_delta] at h
    unfold f c
    simp only [Pi.zero_apply, Finset.sum_const_zero, sub_zero, Finset.sum_sub_distrib]
    linarith
  obtain ⟨x, hx1, hx2, hx3⟩ := main G l u hlu Finset.univ 0 (by simp) hf
  refine ⟨x, fun v => ?_, fun e => hx1 e (Finset.mem_univ e), fun hl hu => hx3 hl hu
    (fun _ => Z.zero_mem)⟩
  rw [← exF_univ]
  exact hx2 v

lemma coe_sum (s : Finset E) (w : E → ℝ) :
    ((∑ e ∈ s, w e : ℝ) : EReal) = ∑ e ∈ s, (w e : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

lemma necessity (G : MultiDigraph V E) (l u : E → EReal) (x : E → ℝ)
    (hx : IsCirculation G x) (hb : ∀ e, l e ≤ (x e : EReal) ∧ (x e : EReal) ≤ u e)
    (A : Finset V) : ∑ e ∈ delta G Aᶜ, u e ≥ ∑ e ∈ delta G A, l e := by
  calc ∑ e ∈ delta G A, l e ≤ ∑ e ∈ delta G A, (x e : EReal) :=
        Finset.sum_le_sum (fun e _ => (hb e).1)
    _ = ∑ e ∈ delta G Aᶜ, (x e : EReal) := by
        rw [← coe_sum, ← coe_sum, cut_balance G x hx A]
    _ ≤ ∑ e ∈ delta G Aᶜ, u e := Finset.sum_le_sum (fun e _ => (hb e).2)

lemma sufficiency (G : MultiDigraph V E) (l u : E → EReal) (hl : ∀ e, l e ≠ ⊤)
    (hu : ∀ e, u e ≠ ⊥) (hlu : ∀ e, l e ≤ u e)
    (hcond : ∀ A : Finset V, ∑ e ∈ delta G Aᶜ, u e ≥ ∑ e ∈ delta G A, l e) :
    ∃ x : E → ℝ, IsCirculation G x ∧ (∀ e, l e ≤ (x e : EReal) ∧ (x e : EReal) ≤ u e) ∧
      (IsIntegralBound l → IsIntegralBound u → IsIntegralVector x) := by
  classical
  set S : ℝ := ∑ e, (|(l e).toReal| + |(u e).toReal|) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun e _ => by positivity)
  have hlS : ∀ e, |(l e).toReal| ≤ S := fun e =>
    le_trans (le_add_of_nonneg_right (abs_nonneg _))
      (Finset.single_le_sum (f := fun e => |(l e).toReal| + |(u e).toReal|)
        (fun e _ => by positivity) (Finset.mem_univ e))
  have huS : ∀ e, |(u e).toReal| ≤ S := fun e =>
    le_trans (le_add_of_nonneg_left (abs_nonneg _))
      (Finset.single_le_sum (f := fun e => |(l e).toReal| + |(u e).toReal|)
        (fun e _ => by positivity) (Finset.mem_univ e))
  have hlS' : ∀ s : Finset E, ∑ e ∈ s, |(l e).toReal| ≤ S := fun s =>
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun _ _ _ => abs_nonneg _))
      (Finset.sum_le_sum (fun e _ => le_add_of_nonneg_right (abs_nonneg _)))
  have huS' : ∀ s : Finset E, ∑ e ∈ s, |(u e).toReal| ≤ S := fun s =>
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun _ _ _ => abs_nonneg _))
      (Finset.sum_le_sum (fun e _ => le_add_of_nonneg_left (abs_nonneg _)))
  set N : ℤ := ⌈2 * S⌉ + 1 with hN
  set M : ℝ := (N : ℝ) with hMdef
  have hM : 2 * S + 1 ≤ M := by
    rw [hMdef, hN]
    push_cast
    linarith [Int.le_ceil (2 * S)]
  set L : E → ℝ := fun e => if l e = ⊥ then -M else (l e).toReal with hL
  set U : E → ℝ := fun e => if u e = ⊤ then M else (u e).toReal with hU
  have hLl : ∀ e, l e ≤ (L e : EReal) := by
    intro e
    by_cases h : l e = ⊥
    · rw [h]; exact bot_le
    · simp only [hL, h, if_false]
      rw [EReal.coe_toReal (hl e) h]
  have hUu : ∀ e, (U e : EReal) ≤ u e := by
    intro e
    by_cases h : u e = ⊤
    · rw [h]; exact le_top
    · simp only [hU, h, if_false]
      rw [EReal.coe_toReal h (hu e)]
  have hLb : ∀ e, L e ≤ |(l e).toReal| - (if l e = ⊥ then M else 0) := by
    intro e
    by_cases h : l e = ⊥
    · simp [hL, h]
    · simp only [hL, h, if_false, sub_zero]
      exact le_abs_self _
  have hUb : ∀ e, -|(u e).toReal| + (if u e = ⊤ then M else 0) ≤ U e := by
    intro e
    by_cases h : u e = ⊤
    · simp [hU, h]
    · simp only [hU, h, if_false, add_zero]
      exact neg_abs_le _
  have hLU : ∀ e, L e ≤ U e := by
    intro e
    by_cases h1 : l e = ⊥
    · have hu1 := hUb e
      have hu2 := huS e
      have hM0 : (0:ℝ) ≤ if u e = ⊤ then M else 0 := by split_ifs <;> linarith
      simp only [hL, h1, if_true]
      linarith
    · by_cases h2 : u e = ⊤
      · have hl1 := hLb e
        have hl2 := hlS e
        simp only [hU, h2, if_true]
        rw [if_neg h1] at hl1
        linarith
      · simp only [hL, hU, h1, h2, if_false]
        exact EReal.toReal_le_toReal (hlu e) h1 h2
  have hcR : ∀ A : Finset V, ∑ e ∈ delta G Aᶜ, U e ≥ ∑ e ∈ delta G A, L e := by
    intro A
    by_cases hinf : (∃ e ∈ delta G Aᶜ, u e = ⊤) ∨ (∃ e ∈ delta G A, l e = ⊥)
    · have h1 : ∑ e ∈ delta G Aᶜ, U e ≥
          -∑ e ∈ delta G Aᶜ, |(u e).toReal| + ∑ e ∈ delta G Aᶜ, (if u e = ⊤ then M else 0) := by
        rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum (fun e _ => hUb e)
      have h2 : ∑ e ∈ delta G A, L e ≤
          ∑ e ∈ delta G A, |(l e).toReal| - ∑ e ∈ delta G A, (if l e = ⊥ then M else 0) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_le_sum (fun e _ => hLb e)
      have hM0 : 0 ≤ M := by linarith
      have hn1 : 0 ≤ ∑ e ∈ delta G Aᶜ, (if u e = ⊤ then M else 0) :=
        Finset.sum_nonneg (fun e _ => by split_ifs <;> linarith)
      have hn2 : 0 ≤ ∑ e ∈ delta G A, (if l e = ⊥ then M else 0) :=
        Finset.sum_nonneg (fun e _ => by split_ifs <;> linarith)
      have hP : M ≤ ∑ e ∈ delta G Aᶜ, (if u e = ⊤ then M else 0) +
          ∑ e ∈ delta G A, (if l e = ⊥ then M else 0) := by
        rcases hinf with ⟨e, he, h⟩ | ⟨e, he, h⟩
        · have := Finset.single_le_sum (f := fun e => if u e = ⊤ then M else 0)
            (fun e _ => by split_ifs <;> linarith) he
          simp only [h, if_true] at this
          linarith
        · have := Finset.single_le_sum (f := fun e => if l e = ⊥ then M else 0)
            (fun e _ => by split_ifs <;> linarith) he
          simp only [h, if_true] at this
          linarith
      have := hlS' (delta G A)
      have := huS' (delta G Aᶜ)
      show ∑ e ∈ delta G A, L e ≤ ∑ e ∈ delta G Aᶜ, U e
      linarith
    · push_neg at hinf
      obtain ⟨hi1, hi2⟩ := hinf
      have e1 : ∑ e ∈ delta G Aᶜ, u e = ((∑ e ∈ delta G Aᶜ, U e : ℝ) : EReal) := by
        rw [coe_sum]
        refine Finset.sum_congr rfl (fun e he => ?_)
        simp only [hU, hi1 e he, if_false]
        rw [EReal.coe_toReal (hi1 e he) (hu e)]
      have e2 : ∑ e ∈ delta G A, l e = ((∑ e ∈ delta G A, L e : ℝ) : EReal) := by
        rw [coe_sum]
        refine Finset.sum_congr rfl (fun e he => ?_)
        simp only [hL, hi2 e he, if_false]
        rw [EReal.coe_toReal (hl e) (hi2 e he)]
      have h := hcond A
      rw [e1, e2] at h
      exact EReal.coe_le_coe_iff.1 h
  obtain ⟨x, hx1, hx2, hx3⟩ := real_hoffman G L U hLU hcR
  refine ⟨x, hx1, fun e => ⟨le_trans (hLl e) (EReal.coe_le_coe_iff.2 (hx2 e).1),
    le_trans (EReal.coe_le_coe_iff.2 (hx2 e).2) (hUu e)⟩, fun hil hiu => ?_⟩
  have hMZ : M ∈ Z := mem_Z.2 ⟨N, rfl⟩
  have hLZ : ∀ e, L e ∈ Z := by
    intro e
    by_cases h : l e = ⊥
    · simp only [hL, h, if_true]
      exact Z.neg_mem hMZ
    · simp only [hL, h, if_false]
      obtain ⟨n, hn⟩ := hil e (hl e) h
      rw [hn, EReal.toReal_coe]
      exact mem_Z.2 ⟨n, rfl⟩
  have hUZ : ∀ e, U e ∈ Z := by
    intro e
    by_cases h : u e = ⊤
    · simp only [hU, h, if_true]
      exact hMZ
    · simp only [hU, h, if_false]
      obtain ⟨n, hn⟩ := hiu e h (hu e)
      rw [hn, EReal.toReal_coe]
      exact mem_Z.2 ⟨n, rfl⟩
  intro e
  exact mem_Z.1 (hx3 hLZ hUZ e)

end Hoff61

open CombOpt.Circulation in
theorem solution {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : MultiDigraph V E) (l u : E → EReal) (hl : ∀ e, l e ≠ ⊤)
    (hu : ∀ e, u e ≠ ⊥) (hlu : ∀ e, l e ≤ u e) :
    ((∃ x : E → ℝ, IsCirculation G x ∧ ∀ e, l e ≤ (x e : EReal) ∧ (x e : EReal) ≤ u e) ↔
        ∀ A : Finset V, ∑ e ∈ delta G Aᶜ, u e ≥ ∑ e ∈ delta G A, l e) ∧
      (IsIntegralBound l → IsIntegralBound u →
        ((∃ x : E → ℝ, IsIntegralVector x ∧ IsCirculation G x ∧
            ∀ e, l e ≤ (x e : EReal) ∧ (x e : EReal) ≤ u e) ↔
          ∀ A : Finset V, ∑ e ∈ delta G Aᶜ, u e ≥ ∑ e ∈ delta G A, l e)) := by
  refine ⟨⟨fun ⟨x, hx, hb⟩ => Hoff61.necessity G l u x hx hb, fun h => ?_⟩,
    fun hil hiu => ⟨fun ⟨x, _, hx, hb⟩ => Hoff61.necessity G l u x hx hb, fun h => ?_⟩⟩
  · obtain ⟨x, hx1, hx2, _⟩ := Hoff61.sufficiency G l u hl hu hlu h
    exact ⟨x, hx1, hx2⟩
  · obtain ⟨x, hx1, hx2, hx3⟩ := Hoff61.sufficiency G l u hl hu hlu h
    exact ⟨x, hx3 hil hiu, hx1, hx2⟩
