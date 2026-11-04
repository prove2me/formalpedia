-- Prove2me | solution 1 for BudgetedAffine.Disjoint.greedy_run_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T21:20:30.887896+00:00
-- url     : https://prove2.me/submissions/42565abe-31da-46d2-bf1e-4aa23d7b7485

import Mathlib
import Definitions.Def_BudgetedAffine_Disjoint_Model
import Definitions.Def_BudgetedAffine_Disjoint_OnlineCover
import Definitions.Def_BudgetedAffine_Disjoint_Construction

set_option autoImplicit false
open Matrix BudgetedAffine.Disjoint

theorem affdisj_take_ofFn_congr {α : Type} {L : ℕ} (f f' : ℕ → α) (ℓ : ℕ)
    (h : ∀ i < ℓ, f i = f' i) :
    (List.ofFn (fun i : Fin L => f i.val)).take ℓ = (List.ofFn (fun i : Fin L => f' i.val)).take ℓ := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    simp only [List.length_take, List.length_ofFn, lt_min_iff] at h1
    exact h i h1.1

theorem solution {m n L : ℕ} {M : Matrix (Fin m) (Fin n) ℝ} {d : Fin n → ℝ} {ρ : ℝ}
    (alg : OnlineCover M d ρ) (w : Fin L → Fin m → ℝ) (Shat : Fin L → Finset (Fin m)) :
    ∃ (σ : Fin L ≃ Fin L) (a : Fin L → Finset (Fin m)), IsGreedyRun alg w Shat σ a := by
  classical
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    exact ⟨Equiv.refl _, fun i => i.elim0, fun ℓ => ℓ.elim0, fun ℓ => ℓ.elim0⟩
  let pre : (ℕ → Finset (Fin m)) → ℕ → List (Finset (Fin m)) :=
    fun f ℓ => (List.ofFn (fun i : Fin L => f i.val)).take ℓ
  let Good : ℕ → (ℕ → Fin L) → (ℕ → Finset (Fin m)) → Prop := fun k σf af =>
    (∀ i j, i < k → j < k → σf i = σf j → i = j) ∧
    ∀ ℓ < k, (af ℓ ⊆ Shat (σf ℓ) ∧ ∑ i ∈ af ℓ, w (σf ℓ) i ≤ 1) ∧
      ∀ s, (∀ j < ℓ, σf j ≠ s) → ∀ b ⊆ Shat s, ∑ i ∈ b, w s i ≤ 1 →
        alg.augCost (pre af ℓ) b ≤ alg.augCost (pre af ℓ) (af ℓ)
  have step : ∀ k, k ≤ L → ∃ σf af, Good k σf af := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨fun _ => ⟨0, hL⟩, fun _ => ∅, fun i j hi _ _ => absurd hi (Nat.not_lt_zero _),
        fun ℓ hℓ => absurd hℓ (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨σf, af, hinj, hgood⟩ := ih (by omega)
      have hunused : ∃ s : Fin L, ∀ j < k, σf j ≠ s := by
        by_contra hcon
        push_neg at hcon
        choose f hf using hcon
        have hfi : Function.Injective (fun s : Fin L => (⟨f s, (hf s).1⟩ : Fin k)) := by
          intro s t hst
          simp only [Fin.mk.injEq] at hst
          rw [← (hf s).2, ← (hf t).2, hst]
        have := Fintype.card_le_of_injective _ hfi
        simp only [Fintype.card_fin] at this
        omega
      obtain ⟨s0, hs0⟩ := hunused
      set cand : Finset (Fin L × Finset (Fin m)) := (Finset.univ ×ˢ Finset.univ).filter
        (fun p => (∀ j < k, σf j ≠ p.1) ∧ p.2 ⊆ Shat p.1 ∧ ∑ i ∈ p.2, w p.1 i ≤ 1) with hcand
      have hne : cand.Nonempty := ⟨(s0, ∅), by simpa [hcand] using hs0⟩
      obtain ⟨p, hp, hpmax⟩ := Finset.exists_max_image cand
        (fun p => alg.augCost (pre af k) p.2) hne
      obtain ⟨hp1, hp2, hp3⟩ := (Finset.mem_filter.1 hp).2
      refine ⟨Function.update σf k p.1, Function.update af k p.2, ?_, ?_⟩
      · intro i j hi hj hij
        rcases (Nat.lt_succ_iff.1 hi).lt_or_eq with hi' | rfl <;>
          rcases (Nat.lt_succ_iff.1 hj).lt_or_eq with hj' | rfl
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)] at hij
          exact hinj i j hi' hj' hij
        · rw [Function.update_of_ne (by omega), Function.update_self] at hij
          exact absurd hij (hp1 i hi')
        · rw [Function.update_self, Function.update_of_ne (by omega)] at hij
          exact absurd hij.symm (hp1 j hj')
        · rfl
      · intro ℓ hℓ
        have hpre_eq : pre (Function.update af k p.2) ℓ = pre af ℓ :=
          affdisj_take_ofFn_congr _ _ ℓ (fun i hi => Function.update_of_ne (by omega) _ _)
        rw [hpre_eq]
        rcases (Nat.lt_succ_iff.1 hℓ).lt_or_eq with hlt | rfl
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          obtain ⟨h1, h2⟩ := hgood ℓ hlt
          refine ⟨h1, fun s hs b hb hbw => h2 s (fun j hj => ?_) b hb hbw⟩
          have := hs j hj
          rwa [Function.update_of_ne (by omega)] at this
        · rw [Function.update_self, Function.update_self]
          refine ⟨⟨hp2, hp3⟩, fun s hs b hb hbw => ?_⟩
          have hs' : ∀ j < ℓ, σf j ≠ s := fun j hj => by
            have := hs j hj
            rwa [Function.update_of_ne (by omega)] at this
          exact hpmax (s, b) (Finset.mem_filter.2 ⟨by simp, hs', hb, hbw⟩)
  obtain ⟨σf, af, hinj, hgood⟩ := step L le_rfl
  have hσinj : Function.Injective (fun i : Fin L => σf i.val) :=
    fun i j h => Fin.ext (hinj _ _ i.isLt j.isLt h)
  refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hσinj), fun i => af i.val, ?_, ?_⟩
  · intro ℓ
    exact (hgood ℓ.val ℓ.isLt).1
  · intro ℓ s hs b hb hbw
    exact (hgood ℓ.val ℓ.isLt).2 s (fun j hj e => hs ⟨j, by omega⟩ (show (⟨j, by omega⟩ : Fin L) < ℓ from hj)
      (by simpa using e)) b hb hbw
