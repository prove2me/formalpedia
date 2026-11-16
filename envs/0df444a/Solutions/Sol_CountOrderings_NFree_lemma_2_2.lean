-- Prove2me | solution 1 for CountOrderings.NFree.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @bersubs
-- created : 2026-11-15T17:13:48.83638+00:00
-- url     : https://prove2.me/submissions/544b93e8-694a-4d99-a675-6707a7bb8a25

import Definitions.Def_CountOrderings_NFree_Poset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Atoms.Finite
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Positivity

namespace CountOrderings.NFree

private abbrev Ranking (T : Type) [Fintype T] := T ≃ Fin (Fintype.card T)

private def Respects {T : Type} [Fintype T] [PartialOrder T]
    (s : Finset T) (e : Ranking T) : Prop :=
  ∀ v ∈ s, ∀ x : T, v ≤ x → e v ≤ e x

private abbrev ConstrainedRank {T : Type} [Fintype T] [PartialOrder T] (s : Finset T) :=
  {e : Ranking T // Respects s e}

private theorem below_comparable {T : Type} [PartialOrder T] [Fintype T]
    (hT : IsRootedTreePoset T) : ∀ x a b : T, a ≤ x → b ≤ x → a ≤ b ∨ b ≤ a := by
  obtain ⟨r, hr, hparent⟩ := hT
  intro x
  induction x using WellFoundedLT.induction with
  | ind x ih =>
    intro a b ha hb
    by_cases hax : a = x
    · subst a
      exact Or.inr hb
    by_cases hbx : b = x
    · subst b
      exact Or.inl ha
    have hltA : a < x := lt_of_le_of_ne ha hax
    have hltB : b < x := lt_of_le_of_ne hb hbx
    have hxr : x ≠ r := by
      intro hx
      subst x
      exact (not_lt_of_ge (hr a)) hltA
    obtain ⟨p, hp, huniq⟩ := hparent x hxr
    obtain ⟨u, hau, hu⟩ := hltA.exists_le_covby
    obtain ⟨v, hbv, hv⟩ := hltB.exists_le_covby
    rw [huniq u hu] at hau
    rw [huniq v hv] at hbv
    exact ih p hp.lt a b hau hbv

private theorem exists_first {T : Type} [PartialOrder T] [Fintype T]
    (v : T) (e : Ranking T) :
    ∃ u : {x : T // v ≤ x}, ∀ x : {x : T // v ≤ x}, e u ≤ e x := by
  classical
  let : Nonempty {x : T // v ≤ x} := ⟨⟨v, le_rfl⟩⟩
  obtain ⟨u, _, hu⟩ := Finset.exists_min_image Finset.univ
    (fun x : {x : T // v ≤ x} => e x) Finset.univ_nonempty
  exact ⟨u, fun x => hu x (Finset.mem_univ x)⟩

private noncomputable def firstInUpSet {T : Type} [PartialOrder T] [Fintype T]
    (v : T) (e : Ranking T) : {x : T // v ≤ x} :=
  (exists_first v e).choose

private theorem firstInUpSet_le {T : Type} [PartialOrder T] [Fintype T]
    (v : T) (e : Ranking T) (x : {x : T // v ≤ x}) : e (firstInUpSet v e) ≤ e x :=
  (exists_first v e).choose_spec x

private theorem firstInUpSet_eq {T : Type} [PartialOrder T] [Fintype T]
    (v : T) (e : Ranking T) (u : {x : T // v ≤ x})
    (hu : ∀ x : {x : T // v ≤ x}, e u ≤ e x) : firstInUpSet v e = u :=
  Subtype.ext (e.injective (le_antisymm (firstInUpSet_le v e u) (hu _)))

private theorem swap_keeps_above {T : Type} [PartialOrder T] [DecidableEq T]
    {w v u x : T} (hwv : w ≤ v ↔ w ≤ u) (h : w ≤ x) :
    w ≤ Equiv.swap v u x := by
  by_cases hxv : x = v
  · subst x
    simpa using hwv.mp h
  by_cases hxu : x = u
  · subst x
    simpa using hwv.mpr h
  simpa only [Equiv.swap_apply_of_ne_of_ne hxv hxu] using h

private def swapRanks {T : Type} [Fintype T] [DecidableEq T]
    (v u : T) (e : Ranking T) : Ranking T :=
  (Equiv.swap v u).trans e

private theorem swapRanks_twice {T : Type} [Fintype T] [DecidableEq T]
    (v u : T) (e : Ranking T) :
    swapRanks v u (swapRanks v u e) = e := by
  apply Equiv.ext
  intro x
  change e (Equiv.swap v u (Equiv.swap v u x)) = e x
  rw [Equiv.swap_apply_self]

private theorem respects_swap {T : Type} [PartialOrder T] [Fintype T] [DecidableEq T]
    (hchain : ∀ x a b : T, a ≤ x → b ≤ x → a ≤ b ∨ b ≤ a)
    (s : Finset T) (v : T) (u : {x : T // v ≤ x}) (hmax : ∀ w ∈ s, ¬ v ≤ w)
    (e : Ranking T) (he : Respects s e) : Respects s (swapRanks v u e) := by
  intro w hw x hx
  have hwv : w ≤ v ↔ w ≤ ↑u :=
    ⟨fun h => h.trans u.2, fun h => (hchain u w v h u.2).resolve_right (hmax w hw)⟩
  have hnv : w ≠ v := fun h => hmax w hw (h ▸ le_rfl)
  have hnu : w ≠ ↑u := fun h => hmax w hw (h.symm ▸ u.2)
  change e (Equiv.swap v ↑u w) ≤ e (Equiv.swap v ↑u x)
  rw [Equiv.swap_apply_of_ne_of_ne hnv hnu]
  exact he w hw _ (swap_keeps_above hwv hx)

/-- Put the minimum-ranked element of the new subtree at its root, and remember
which element held that rank. The recorded element determines the inverse swap. -/
private noncomputable def enforceRoot {T : Type} [PartialOrder T] [Fintype T] [DecidableEq T]
    (hchain : ∀ x a b : T, a ≤ x → b ≤ x → a ≤ b ∨ b ≤ a)
    (s : Finset T) (v : T) (hmax : ∀ w ∈ s, ¬ v ≤ w) :
    ConstrainedRank s ≃ ConstrainedRank (insert v s) × {x : T // v ≤ x} := by
  refine {
    toFun := fun e =>
      let u := firstInUpSet v e.1
      (⟨swapRanks v u e.1, ?_⟩, u)
    invFun := fun p => ⟨swapRanks v p.2 p.1.1, ?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro w hw x hx
    rcases Finset.mem_insert.mp hw with hwv | hws
    · subst w
      change e.1 (Equiv.swap v ↑u v) ≤ e.1 (Equiv.swap v ↑u x)
      rw [Equiv.swap_apply_left]
      exact firstInUpSet_le v e.1 ⟨_, swap_keeps_above ⟨fun _ => u.2, fun _ => le_rfl⟩ hx⟩
    · exact respects_swap hchain s v u hmax e.1 e.2 w hws x hx
  · exact respects_swap hchain s v p.2 hmax p.1.1
      (fun w hw => p.1.2 w (Finset.mem_insert_of_mem hw))
  · intro e
    exact Subtype.ext (swapRanks_twice _ _ _)
  · rintro ⟨e, u⟩
    let e' := swapRanks v u e.1
    have hfirst : firstInUpSet v e' = u := by
      apply firstInUpSet_eq
      intro x
      change e.1 (Equiv.swap v ↑u ↑u) ≤ e.1 (Equiv.swap v ↑u ↑x)
      rw [Equiv.swap_apply_right]
      exact e.2 v (Finset.mem_insert_self v s) _
        (swap_keeps_above ⟨fun _ => u.2, fun _ => le_rfl⟩ x.2)
    apply Prod.ext
    · apply Subtype.ext
      change swapRanks v (firstInUpSet v e') e' = e.1
      rw [hfirst]
      exact swapRanks_twice _ _ _
    · exact hfirst

private theorem card_upSet {T : Type} [PartialOrder T] [Fintype T] (v : T) :
    Nat.card {x : T // v ≤ x} = upSetCard v := by
  classical
  rw [Nat.card_eq_fintype_card, upSetCard]
  exact Fintype.card_of_subtype _ (by simp)

private theorem count_constraints {T : Type} [PartialOrder T] [Fintype T]
    (hchain : ∀ x a b : T, a ≤ x → b ≤ x → a ≤ b ∨ b ≤ a) (s : Finset T) :
    Nat.card (ConstrainedRank s) * ∏ v ∈ s, upSetCard v = (Fintype.card T).factorial := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨v, hv, hmax⟩ := s.exists_maximal hs
      have hprior : ∀ w ∈ s.erase v, ¬ v ≤ w := by
        intro w hw hvw
        obtain ⟨hne, hw⟩ := Finset.mem_erase.mp hw
        exact hne (le_antisymm (hmax hw hvw) hvw)
      have hrec := Nat.card_congr (enforceRoot hchain (s.erase v) v hprior)
      rw [Nat.card_prod, Finset.insert_erase hv, card_upSet] at hrec
      have hprod : (∏ w ∈ s, upSetCard w) =
          upSetCard v * ∏ w ∈ s.erase v, upSetCard w := calc
        _ = (∏ w ∈ insert v (s.erase v), upSetCard w) := by rw [Finset.insert_erase hv]
        _ = _ := Finset.prod_insert (Finset.notMem_erase v s)
      rw [hprod, ← Nat.mul_assoc, ← hrec]
      exact ih _ (Finset.erase_ssubset hv)
    · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hs
      let e : ConstrainedRank (∅ : Finset T) ≃ Ranking T := {
        toFun := Subtype.val
        invFun := fun e => ⟨e, by simp [Respects]⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
      }
      rw [Nat.card_congr e, Finset.prod_empty, Nat.mul_one, Nat.card_eq_fintype_card]
      exact Fintype.card_equiv (Fintype.equivFin T)

end CountOrderings.NFree

open CountOrderings.NFree in
theorem solution (T : Type) [PartialOrder T] [Fintype T] (hT : IsRootedTreePoset T) :
    (numLinExt T : ℚ) =
      ((Fintype.card T).factorial : ℚ) / ∏ v : T, (upSetCard v : ℚ) := by
  classical
  have h := count_constraints (below_comparable hT) Finset.univ
  have hcard : Nat.card (ConstrainedRank (Finset.univ : Finset T)) = numLinExt T := by
    rw [numLinExt, ← Nat.card_coe_set_eq]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun e => ?_)
    simp [Respects, FCP.Order.LinearExtensions]
  rw [hcard] at h
  have hden : ∏ v : T, (upSetCard v : ℚ) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    have hpos : 0 < upSetCard v := Finset.card_pos.mpr ⟨v, by simp⟩
    exact_mod_cast hpos.ne'
  apply (eq_div_iff hden).2
  rw [← Nat.cast_prod, ← Nat.cast_mul]
  exact congrArg (fun n : ℕ => (n : ℚ)) h
