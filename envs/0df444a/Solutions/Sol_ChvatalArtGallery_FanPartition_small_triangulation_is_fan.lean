-- Prove2me | solution 1 for ChvatalArtGallery.FanPartition.small_triangulation_is_fan
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:13:16.736739+00:00
-- url     : https://prove2.me/submissions/843938c5-a60f-4ef9-8286-e4a8b19cd0d4

import Mathlib
import Definitions.Def_ChvatalArtGallery_FanPartition_Triangulation



namespace ChvatalArtGallery.FanPartition
set_option maxRecDepth 100000
def prr {n : ℕ} : Sym2 (Fin n) → Fin n × Fin n :=
  Sym2.lift ⟨fun x y => (min x y, max x y), fun x y => by simp [min_comm, max_comm]⟩

theorem prr_spec {n : ℕ} (e : Sym2 (Fin n)) : e = s((prr e).1, (prr e).2) := by
  induction e using Sym2.ind with
  | _ x y =>
    simp only [prr, Sym2.lift_mk]
    rcases le_total x y with h | h
    · simp [min_eq_left h, max_eq_right h]
    · simp [min_eq_right h, max_eq_left h, Sym2.eq_swap]

def fcross {n : ℕ} (a b c d : Fin n) : Prop :=
  0 < cdist a c ∧ cdist a c < cdist a b ∧ cdist a b < cdist a d

instance {n : ℕ} (a b c d : Fin n) : Decidable (fcross a b c d) := by
  unfold fcross; infer_instance

def FC {n : ℕ} (e f : Sym2 (Fin n)) : Prop :=
  fcross (prr e).1 (prr e).2 (prr f).1 (prr f).2 ∨ fcross (prr e).1 (prr e).2 (prr f).2 (prr f).1 ∨
  fcross (prr e).2 (prr e).1 (prr f).1 (prr f).2 ∨ fcross (prr e).2 (prr e).1 (prr f).2 (prr f).1

instance {n : ℕ} (e f : Sym2 (Fin n)) : Decidable (FC e f) := by
  unfold FC; infer_instance

def FD {n : ℕ} (e : Sym2 (Fin n)) : Prop :=
  (prr e).1 ≠ (prr e).2 ∧ cdist (prr e).1 (prr e).2 ≠ 1 ∧ cdist (prr e).2 (prr e).1 ≠ 1

instance {n : ℕ} (e : Sym2 (Fin n)) : Decidable (FD e) := by
  unfold FD; infer_instance

theorem crosses_mk_iff {n : ℕ} (x y z w : Fin n) :
    Crosses s(x, y) s(z, w) ↔ fcross x y z w ∨ fcross x y w z ∨ fcross y x z w ∨ fcross y x w z := by
  unfold Crosses fcross
  constructor
  · rintro ⟨a, b, c, d, h1, h2, h3⟩
    rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases Sym2.eq_iff.1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h3
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr h3))
  · rintro (h | h | h | h)
    · exact ⟨x, y, z, w, rfl, rfl, h⟩
    · exact ⟨x, y, w, z, rfl, Sym2.eq_swap, h⟩
    · exact ⟨y, x, z, w, Sym2.eq_swap, rfl, h⟩
    · exact ⟨y, x, w, z, Sym2.eq_swap, Sym2.eq_swap, h⟩

theorem crosses_iff_FC {n : ℕ} (e f : Sym2 (Fin n)) : Crosses e f ↔ FC e f := by
  have he := prr_spec e
  have hf := prr_spec f
  unfold FC
  generalize prr e = p at he ⊢
  generalize prr f = q at hf ⊢
  subst he hf
  exact crosses_mk_iff _ _ _ _

theorem diag_mk_iff {n : ℕ} (x y : Fin n) :
    IsDiagonal s(x, y) ↔ x ≠ y ∧ cdist x y ≠ 1 ∧ cdist y x ≠ 1 := by
  unfold IsDiagonal
  constructor
  · intro h; exact h x y rfl
  · intro h a b hab
    rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact ⟨h.1.symm, h.2.2, h.2.1⟩

theorem diag_iff_FD {n : ℕ} (e : Sym2 (Fin n)) : IsDiagonal e ↔ FD e := by
  have he := prr_spec e
  unfold FD
  generalize prr e = p at he ⊢
  subst he
  exact diag_mk_iff _ _

def FT (n : ℕ) (D : Finset (Sym2 (Fin n))) : Prop :=
  3 ≤ n ∧ (∀ e ∈ D, FD e) ∧ (∀ e ∈ D, ∀ f ∈ D, ¬ FC e f) ∧
  (∀ e : Sym2 (Fin n), FD e → (∀ f ∈ D, ¬ FC e f) → e ∈ D)

instance (n : ℕ) (D : Finset (Sym2 (Fin n))) : Decidable (FT n D) := by
  unfold FT; infer_instance

theorem IsTriangulation_iff_FT (n : ℕ) (D : Finset (Sym2 (Fin n))) :
    IsTriangulation n D ↔ FT n D := by
  unfold IsTriangulation FT
  simp only [diag_iff_FD, crosses_iff_FC]

theorem exists_sublist_toFinset {α : Type*} [DecidableEq α] (D : Finset α) (L : List α)
    (hL : ∀ e ∈ D, e ∈ L) : ∃ l ∈ L.sublists, l.toFinset = D := by
  refine ⟨L.filter (fun e => decide (e ∈ D)), ?_, ?_⟩
  · rw [List.mem_sublists]; exact List.filter_sublist
  · ext e
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hL e h, h⟩⟩

theorem small_core (n : ℕ) (hn3 : 3 ≤ n) (hn5 : n ≤ 5)
    (D : Finset (Sym2 (Fin n))) (hD : IsTriangulation n D) :
    IsFan n D (triangles n D) := by
  rw [IsTriangulation_iff_FT] at hD
  have hdiag : ∀ e ∈ D, FD e := hD.2.1
  interval_cases n
  · have hL : ∀ e ∈ D, e ∈ ([] : List (Sym2 (Fin 3))) := by
      intro e he
      have h1 : ∀ e : Sym2 (Fin 3), FD e → e ∈ ([] : List (Sym2 (Fin 3))) := by decide +kernel
      exact h1 e (hdiag e he)
    obtain ⟨l, hl, rfl⟩ := exists_sublist_toFinset D _ hL
    revert l; decide +kernel
  · have hL : ∀ e ∈ D, e ∈ ([s(0,2), s(1,3)] : List (Sym2 (Fin 4))) := by
      intro e he
      have h1 : ∀ e : Sym2 (Fin 4), FD e → e ∈ ([s(0,2), s(1,3)] : List (Sym2 (Fin 4))) := by decide +kernel
      exact h1 e (hdiag e he)
    obtain ⟨l, hl, rfl⟩ := exists_sublist_toFinset D _ hL
    revert l; decide +kernel
  · have hL : ∀ e ∈ D, e ∈ ([s(0,2), s(0,3), s(1,3), s(1,4), s(2,4)] : List (Sym2 (Fin 5))) := by
      intro e he
      have h1 : ∀ e : Sym2 (Fin 5), FD e → e ∈ ([s(0,2), s(0,3), s(1,3), s(1,4), s(2,4)] : List (Sym2 (Fin 5))) := by decide +kernel
      exact h1 e (hdiag e he)
    obtain ⟨l, hl, rfl⟩ := exists_sublist_toFinset D _ hL
    revert l; decide +kernel

end ChvatalArtGallery.FanPartition

open ChvatalArtGallery.FanPartition


theorem solution (n : ℕ) (hn3 : 3 ≤ n) (hn5 : n ≤ 5)
    (D : Finset (Sym2 (Fin n))) (hD : IsTriangulation n D) :
    IsFan n D (triangles n D) := by
  exact small_core n hn3 hn5 D hD
