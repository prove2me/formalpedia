-- Prove2me | solution 1 for FixedMachinePrec.fill_slot_schedule_with_dummies
-- status  : ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T12:25:05.592881+00:00
-- url     : https://prove2.me/submissions/d62cb6a4-4a8c-41a3-8ffa-2ed3a05b2a02

import Definitions.Def_FixedMachinePrec_Deadline

open FixedMachinePrec

private theorem embed_jobs (G : Instance) (m T : ℕ) (τ : Fin G.n → ℕ)
    (h : IsSlotSchedule G m T τ) : ∃ f : Fin G.n ↪ Fin T × Fin m, ∀ x, (f x).1.val + 1 = τ x := by
  classical
  let fiber (t : ℕ) := Finset.univ.filter fun x => τ x = t
  have cap (t) : Fintype.card (fiber t) ≤ m := by rw [Fintype.card_coe]; exact h.2.1 t
  let label (t) : fiber t ↪ Fin m := (Fintype.equivFin (fiber t)).toEmbedding.trans (Fin.castLEEmb (cap t))
  let f (x : Fin G.n) : Fin T × Fin m :=
    (⟨τ x - 1, by have := h.1 x; omega⟩, label (τ x) ⟨x, by simp [fiber]⟩)
  have ht (x) : (f x).1.val + 1 = τ x := by dsimp [f]; have := h.1 x; omega
  refine ⟨⟨f, ?_⟩, ht⟩
  intro x y e
  have et : τ x = τ y := (ht x).symm.trans ((congrArg (fun z : Fin T × Fin m => z.1.val+1) e).trans (ht y))
  have ey : y ∈ fiber (τ x) := by simp [fiber, et]
  apply_fun Prod.snd at e
  change label (τ x) ⟨x,_⟩ = label (τ y) ⟨y,_⟩ at e
  have transport (s t : ℕ) (est : s=t) (z : Fin G.n) (hs : z ∈ fiber s) (ht : z ∈ fiber t) : label s ⟨z,hs⟩ = label t ⟨z,ht⟩ := by subst t; rfl
  have eq : label (τ x) ⟨x, by simp [fiber]⟩ = label (τ x) ⟨y,ey⟩ := e.trans (transport _ _ et.symm y _ ey)
  exact congrArg Subtype.val ((label _).injective eq)

private theorem mem_union_slots {α : Type*} [DecidableEq α] (x : α) (l : List (Finset α)) :
    x ∈ l.foldr (· ∪ ·) ∅ ↔ ∃ A ∈ l, x ∈ A := by
  induction l with
  | nil => simp
  | cons A l ih => simp [ih]

theorem solution (G : Instance) (m T : ℕ) (τ : Fin G.n → ℕ) (h : IsSlotSchedule G m T τ) :
    ∃ S : List (Finset (Fin (m*T))), IsFullSchedule (paddedPrec G (m*T)) m Finset.univ S ∧ S.length = T := by
  classical
  obtain ⟨f,hf⟩ := embed_jobs G m T τ h
  have hsize : G.n ≤ m*T := by simpa [Nat.mul_comm] using Fintype.card_le_of_embedding f
  let orig : Fin G.n → Fin (m*T) := Fin.castLE hsize
  let cells : Fin T × Fin m ≃ Fin (m*T) := finProdFinEquiv.trans (Fin.castOrderIso (Nat.mul_comm T m)).toEquiv
  obtain ⟨π,hπ⟩ := Equiv.Perm.exists_extending_pair orig (fun x => cells (f x)) (Fin.castLE_injective _) (cells.injective.comp f.injective)
  let cell := π.trans cells.symm
  have he (x : Fin G.n) : cell (orig x) = f x := by simp [cell,hπ]
  have precedes (x y) (hp : paddedPrec G (m*T) x y) : (cell x).1 < (cell y).1 := by
    obtain ⟨hx,hy,hxy⟩ := hp
    let a : Fin G.n := ⟨x.val,hx⟩
    let b : Fin G.n := ⟨y.val,hy⟩
    have ea : orig a = x := rfl
    have eb : orig b = y := rfl
    rw [← ea, ← eb, he, he]
    have hp' := h.2.2 a b hxy
    have := hf a; have := hf b
    exact (show (f a).1.val < (f b).1.val by omega)
  let slot (i : Fin T) : Finset (Fin (m*T)) := Finset.univ.image fun j : Fin m => cell.symm (i,j)
  have mem (i x) : x ∈ slot i ↔ (cell x).1 = i := by
    simp only [slot, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j,rfl⟩; simp
    · intro hx; exact ⟨(cell x).2, by rw [← hx]; simp⟩
  let S := List.ofFn slot
  refine ⟨S, ⟨?_, ?_, ?_, ?_⟩, by simp [S]⟩
  · intro A hA
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hA
    constructor
    · dsimp only [slot]
      rw [Finset.card_image_of_injective]; simp
      exact fun x y e => congrArg Prod.snd (cell.symm.injective e)
    · intro x hx y hy hp
      have := precedes x y hp
      simp_all [mem]
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [S,List.getElem_ofFn,mem] at hx hy
    exact (Nat.ne_of_lt hij) (congrArg Fin.val (hx.symm.trans hy))
  · ext x
    simp only [Finset.mem_univ, iff_true, mem_union_slots]
    exact ⟨_, List.mem_ofFn.mpr ⟨(cell x).1,rfl⟩,(mem _ _).mpr rfl⟩
  · intro i j hi hj x y hx hy hp
    simp only [S,List.getElem_ofFn,mem] at hx hy
    have ep := precedes x y hp
    rw [hx,hy] at ep
    exact ep
