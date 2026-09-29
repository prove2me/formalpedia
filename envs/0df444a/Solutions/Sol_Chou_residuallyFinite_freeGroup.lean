-- Prove2me | solution 1 for Chou.residuallyFinite_freeGroup
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-20T11:59:25.364749+00:00
-- url     : https://prove2.me/submissions/6c86760e-2a43-411c-848b-d1e66b10a4d2

import Mathlib

/-!
# Free groups are residually finite

Chou, *Elementary amenable groups*, Illinois J. Math. **24** (1980), p. 406, uses without proof
the classical fact that a free group is residually finite.

Route taken (the classical permutation route):

* Let `w ≠ 1` and let `L := w.toWord` be its reduced word, of length `n`.  The states are the
  `n + 1` positions between the letters of `L`, i.e. `Fin (n + 1)`.
* `Lib.Move L a x y` is the partial "reading" relation.  The letters are read from the right,
  so a positive letter `(a, true)` in position `i` moves the state `i + 1` to the state `i`,
  and a negative letter `(a, false)` in position `i` moves the state `i` to the state `i + 1`.
* Reducedness of `L` (`FreeGroup.IsReduced`: no `a a⁻¹` or `a⁻¹ a` in consecutive positions)
  makes `Move L a` the graph of a *partial injection* of `Fin (n + 1)`
  (`Lib.Move.right_unique`, `Lib.Move.left_unique`).
* `Equiv.extendSubtype` extends that partial injection to a permutation
  `σ a : Equiv.Perm (Fin (n + 1))` (`Lib.exists_perm`).
* `Lib.lift_drop_apply`: the homomorphism `FreeGroup.lift σ` sends the suffix `L.drop i` to a
  permutation carrying the state `n` to the state `i`; with `i = 0` this shows that
  `FreeGroup.lift σ w` carries `n` to `0`, hence is not the identity of the finite group
  `Equiv.Perm (Fin (n + 1))` as `n ≠ 0`.
* `Group.residuallyFinite_of_forall_exists_finite_monoidHom` then concludes.
-/

namespace Chou

namespace Lib

open FreeGroup

variable {α : Type*}

/-- The partial "reading" relation attached to a word `L` and a letter `a`.  The letters of `L`
are read from the right: the positive letter `(a, true)` in position `i` moves the state
`i + 1` to the state `i`, and the negative letter `(a, false)` in position `i` moves the state
`i` to the state `i + 1`.  The states are the `L.length + 1` positions between letters. -/
def Move (L : List (α × Bool)) (a : α) (x y : Fin (L.length + 1)) : Prop :=
  ∃ i : ℕ, ∃ h : i < L.length,
    (L[i]'h = (a, true) ∧ (x : ℕ) = i + 1 ∧ (y : ℕ) = i) ∨
    (L[i]'h = (a, false) ∧ (x : ℕ) = i ∧ (y : ℕ) = i + 1)

/-- A reduced word has no two consecutive letters of the form `(a, b), (a, !b)`. -/
theorem not_adjacent {L : List (α × Bool)} (hred : IsReduced L) {i : ℕ} (h : i + 1 < L.length)
    {a : α} {b : Bool} (h1 : L[i]'(by omega) = (a, b)) (h2 : L[i + 1]'h = (a, !b)) : False := by
  have hc : L.IsChain (fun p q : α × Bool ↦ p.1 = q.1 → p.2 = q.2) := hred
  have hstep := hc.getElem i h
  rw [h1, h2] at hstep
  simp at hstep

/-- For a reduced word, `Move L a` is the graph of a partial function. -/
theorem Move.right_unique {L : List (α × Bool)} (hred : IsReduced L) {a : α}
    {x y y' : Fin (L.length + 1)} (h : Move L a x y) (h' : Move L a x y') : y = y' := by
  obtain ⟨i, hi, hc⟩ := h
  obtain ⟨j, hj, hc'⟩ := h'
  apply Fin.ext
  rcases hc with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ <;> rcases hc' with ⟨f1, f2, f3⟩ | ⟨f1, f2, f3⟩
  · omega
  · have hji : j = i + 1 := by omega
    subst hji
    exact absurd (not_adjacent hred hj e1 (by simpa using f1)) (by simp)
  · have hij : i = j + 1 := by omega
    subst hij
    exact absurd (not_adjacent hred hi f1 (by simpa using e1)) (by simp)
  · omega

/-- For a reduced word, `Move L a` is the graph of an injective partial function. -/
theorem Move.left_unique {L : List (α × Bool)} (hred : IsReduced L) {a : α}
    {x x' y : Fin (L.length + 1)} (h : Move L a x y) (h' : Move L a x' y) : x = x' := by
  obtain ⟨i, hi, hc⟩ := h
  obtain ⟨j, hj, hc'⟩ := h'
  apply Fin.ext
  rcases hc with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ <;> rcases hc' with ⟨f1, f2, f3⟩ | ⟨f1, f2, f3⟩
  · omega
  · have hij : i = j + 1 := by omega
    subst hij
    exact (not_adjacent hred hi f1 (by simpa using e1)).elim
  · have hji : j = i + 1 := by omega
    subst hji
    exact (not_adjacent hred hj e1 (by simpa using f1)).elim
  · omega

/-- The partial injection `Move L a` extends to a permutation of the set of states. -/
theorem exists_perm {L : List (α × Bool)} (hred : IsReduced L) :
    ∃ σ : α → Equiv.Perm (Fin (L.length + 1)),
      ∀ (a : α) (x y : Fin (L.length + 1)), Move L a x y → σ a x = y := by
  classical
  have key : ∀ a : α, ∃ e : {x : Fin (L.length + 1) // ∃ y, Move L a x y} ≃
      {y : Fin (L.length + 1) // ∃ x, Move L a x y},
      ∀ (x : Fin (L.length + 1)) (hx : ∃ y, Move L a x y),
        Move L a x ((e ⟨x, hx⟩ : _) : Fin (L.length + 1)) := by
    intro a
    refine ⟨Equiv.ofBijective (fun x => ⟨x.2.choose, x.1, x.2.choose_spec⟩) ⟨?_, ?_⟩, ?_⟩
    · rintro ⟨x, hx⟩ ⟨x', hx'⟩ hxx'
      have h1 : Move L a x hx.choose := hx.choose_spec
      have h2 : Move L a x' hx'.choose := hx'.choose_spec
      have hval : hx.choose = hx'.choose := congrArg Subtype.val hxx'
      rw [hval] at h1
      exact Subtype.ext (Move.left_unique hred h1 h2)
    · rintro ⟨y, x, hxy⟩
      refine ⟨⟨x, y, hxy⟩, Subtype.ext ?_⟩
      exact Move.right_unique hred (Exists.choose_spec (⟨y, hxy⟩ : ∃ y, Move L a x y)) hxy
    · intro x hx
      exact hx.choose_spec
  choose e he using key
  refine ⟨fun a => (e a).extendSubtype, fun a x y h => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem _ _ ⟨y, h⟩]
  exact Move.right_unique hred (he a x ⟨y, h⟩) h

/-- Reading the suffix `L.drop i` of `L` moves the state `L.length` to the state `i`. -/
theorem lift_drop_apply {L : List (α × Bool)} (σ : α → Equiv.Perm (Fin (L.length + 1)))
    (hσ : ∀ (a : α) (x y : Fin (L.length + 1)), Move L a x y → σ a x = y) :
    ∀ k : ℕ, k ≤ L.length →
      (FreeGroup.lift σ) (FreeGroup.mk (L.drop (L.length - k)))
          ⟨L.length, Nat.lt_succ_self _⟩ = ⟨L.length - k, by omega⟩ := by
  intro k
  induction k with
  | zero => intro _; simp [← FreeGroup.one_eq_mk]
  | succ k ih =>
    intro hk
    have hk' : k ≤ L.length := by omega
    have hik : L.length - (k + 1) < L.length := by omega
    have hsucc : L.length - (k + 1) + 1 = L.length - k := by omega
    rw [show L.drop (L.length - (k + 1)) =
          [L[L.length - (k + 1)]'hik] ++ L.drop (L.length - (k + 1) + 1) from
        List.drop_eq_getElem_cons hik, ← FreeGroup.mul_mk, _root_.map_mul, Equiv.Perm.mul_apply,
      hsucc, ih hk']
    have hfin : (⟨L.length - k, by omega⟩ : Fin (L.length + 1)) =
        ⟨L.length - (k + 1) + 1, by omega⟩ := by
      simp only [Fin.mk.injEq]
      omega
    rw [hfin]
    rcases hb : (L[L.length - (k + 1)]'hik).2 with _ | _
    · have hlet : (L[L.length - (k + 1)]'hik) = ((L[L.length - (k + 1)]'hik).1, false) := by
        rw [← hb]
      have hmove : Move L (L[L.length - (k + 1)]'hik).1
          ⟨L.length - (k + 1), by omega⟩ ⟨L.length - (k + 1) + 1, by omega⟩ :=
        ⟨L.length - (k + 1), hik, Or.inr ⟨hlet, rfl, rfl⟩⟩
      have hval : (FreeGroup.lift σ) (FreeGroup.mk [L[L.length - (k + 1)]'hik]) =
          (σ (L[L.length - (k + 1)]'hik).1)⁻¹ := by
        simp [FreeGroup.lift_mk, hb]
      rw [hval, Equiv.Perm.inv_def, Equiv.symm_apply_eq]
      exact (hσ _ _ _ hmove).symm
    · have hlet : (L[L.length - (k + 1)]'hik) = ((L[L.length - (k + 1)]'hik).1, true) := by
        rw [← hb]
      have hmove : Move L (L[L.length - (k + 1)]'hik).1
          ⟨L.length - (k + 1) + 1, by omega⟩ ⟨L.length - (k + 1), by omega⟩ :=
        ⟨L.length - (k + 1), hik, Or.inl ⟨hlet, rfl, rfl⟩⟩
      have hval : (FreeGroup.lift σ) (FreeGroup.mk [L[L.length - (k + 1)]'hik]) =
          σ (L[L.length - (k + 1)]'hik).1 := by
        simp [FreeGroup.lift_mk, hb]
      rw [hval]
      exact hσ _ _ _ hmove


/-- p. 406 (external): free groups are residually finite. -/
theorem residuallyFinite_freeGroup' (α : Type*) : Group.ResiduallyFinite (FreeGroup α) := by
  classical
  refine Group.residuallyFinite_of_forall_exists_finite_monoidHom (fun w hw => ?_)
  obtain ⟨σ, hσ⟩ := Lib.exists_perm (FreeGroup.isReduced_toWord (x := w))
  refine ⟨Equiv.Perm (Fin (w.toWord.length + 1)), inferInstance, inferInstance,
    FreeGroup.lift σ, fun hcon => ?_⟩
  have h0 := Lib.lift_drop_apply σ hσ w.toWord.length le_rfl
  simp only [Nat.sub_self, List.drop_zero, FreeGroup.mk_toWord, hcon, Equiv.Perm.coe_one,
    id_eq] at h0
  have hlen : w.toWord.length = 0 := by simpa using congrArg Fin.val h0
  exact hw (FreeGroup.toWord_eq_nil_iff.mp (List.length_eq_zero_iff.mp hlen))

end Lib

end Chou

open Chou

theorem solution (α : Type*) : Group.ResiduallyFinite (FreeGroup α) :=
  Chou.Lib.residuallyFinite_freeGroup' α
