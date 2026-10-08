-- Prove2me | solution 1 for CorrColoring.ThreeChoosable.choosable_iff_consistent_corr_colorable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:03:52.398223+00:00
-- url     : https://prove2.me/submissions/ce6641f0-9e32-4c58-8864-7b8d5b3ecff7

import Mathlib
import Definitions.Def_CorrColoring_ThreeChoosable_IsChoosable
import Definitions.Def_CorrColoring_ThreeChoosable_KCorrAssignment
import Definitions.Def_CorrColoring_ThreeChoosable_ConsistentOn

set_option autoImplicit false

namespace P6c5a9611

open CorrColoring.ThreeChoosable

/-- one-step relation of the correspondence on `V × Fin k` -/
def R {V : Type*} {G : SimpleGraph V} {k : ℕ} (C : KCorrAssignment G k) :
    V × Fin k → V × Fin k → Prop := fun p q => C.M p.1 p.2 q.1 q.2

theorem chain {V : Type*} {G : SimpleGraph V} {k : ℕ} (C : KCorrAssignment G k)
    {p q : V × Fin k} (h : Relation.ReflTransGen (R C) p q) :
    ∃ W : G.Walk p.1 q.1, ∃ f : ℕ → Fin k, f 0 = p.2 ∧ f W.length = q.2 ∧
      ∀ i < W.length, C.M (W.getVert i) (f i) (W.getVert (i + 1)) (f (i + 1)) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨SimpleGraph.Walk.nil, fun _ => q.2, rfl, rfl, by simp⟩
  | @head a b hab _ ih =>
    obtain ⟨W, f, h0, hl, hM⟩ := ih
    refine ⟨SimpleGraph.Walk.cons (C.adj hab) W,
      fun i => match i with
        | 0 => a.2
        | j + 1 => f j, rfl, ?_, ?_⟩
    · simpa using hl
    · intro i hi
      cases i with
      | zero =>
        simp only [SimpleGraph.Walk.getVert_zero, zero_add,
          SimpleGraph.Walk.getVert_cons_succ]
        rw [h0]
        exact hab
      | succ j =>
        simp only [SimpleGraph.Walk.getVert_cons_succ]
        simp only [SimpleGraph.Walk.length_cons] at hi
        exact hM j (by omega)

theorem same_vertex {V : Type*} {G : SimpleGraph V} {k : ℕ} (C : KCorrAssignment G k)
    (hC : Consistent C) {v : V} {c d : Fin k}
    (h : Relation.ReflTransGen (R C) (v, c) (v, d)) : c = d := by
  obtain ⟨W, f, h0, hl, hM⟩ := chain C h
  by_contra hne
  exact hC v W ⟨f, hM, by rw [h0, hl]; exact hne⟩

def setoidR {V : Type*} {G : SimpleGraph V} {k : ℕ} (C : KCorrAssignment G k) :
    Setoid (V × Fin k) where
  r := Relation.ReflTransGen (R C)
  iseqv := ⟨fun _ => Relation.ReflTransGen.refl,
    fun h => by
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih => exact Relation.ReflTransGen.head (C.symm hbc) ih,
    fun h1 h2 => h1.trans h2⟩

theorem forward {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hG : IsChoosable G k) (C : KCorrAssignment G k) (hC : Consistent C) :
    ∃ φ : V → Fin k, IsCColoring C φ := by
  classical
  let S := setoidR C
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (Quotient S)
  let L : V → Finset (Fin n) := fun v =>
    Finset.univ.image (fun c : Fin k => e (Quotient.mk S (v, c)))
  have hinj : ∀ v, Function.Injective (fun c : Fin k => e (Quotient.mk S (v, c))) := by
    intro v c d hcd
    have := Quotient.exact (e.injective hcd)
    exact same_vertex C hC this
  have hL : ∀ v, (L v).card = k := by
    intro v
    simp only [L]
    rw [Finset.card_image_of_injective _ (hinj v)]
    simp
  obtain ⟨ψ, hψL, hψ⟩ := hG (Fin n) L hL
  have hmem : ∀ v, ∃ c : Fin k, e (Quotient.mk S (v, c)) = ψ v := by
    intro v
    have := hψL v
    simp only [L, Finset.mem_image, Finset.mem_univ, true_and] at this
    exact this
  choose φ hφ using hmem
  refine ⟨φ, ?_⟩
  intro u v huv hM
  apply hψ u v huv
  rw [← hφ u, ← hφ v]
  congr 1
  apply Quotient.sound
  exact Relation.ReflTransGen.single hM

theorem backward {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (h : ∀ C : KCorrAssignment G k, Consistent C → ∃ φ : V → Fin k, IsCColoring C φ) :
    IsChoosable G k := by
  classical
  intro α L hL
  let e : ∀ v, Fin k ≃ L v := fun v => ((L v).equivFin.trans (finCongr (hL v))).symm
  let C : KCorrAssignment G k :=
    { M := fun u c v d => G.Adj u v ∧ ((e u c : α) = (e v d : α))
      adj := fun h => h.1
      symm := fun h => ⟨h.1.symm, h.2.symm⟩
      unique := by
        intro u c v d d' h1 h2
        apply (e v).injective
        apply Subtype.ext
        rw [← h1.2, ← h2.2] }
  have hC : Consistent C := by
    intro v W hW
    obtain ⟨c, hM, hne⟩ := hW
    have key : ∀ i ≤ W.length, ((e (W.getVert i) (c i)) : α) = ((e (W.getVert 0) (c 0)) : α) := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        rw [← ih (by omega)]
        exact ((hM j (by omega)).2).symm
    have k1 := key W.length le_rfl
    rw [SimpleGraph.Walk.getVert_length, SimpleGraph.Walk.getVert_zero] at k1
    exact hne ((e v).injective (Subtype.ext k1)).symm
  obtain ⟨φ, hφ⟩ := h C hC
  refine ⟨fun v => (e v (φ v) : α), fun v => (e v (φ v)).2, ?_⟩
  intro u v huv heq
  exact hφ u v huv ⟨huv, heq⟩

end P6c5a9611

open CorrColoring.ThreeChoosable in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) :
    IsChoosable G k ↔
      ∀ C : KCorrAssignment G k, Consistent C → ∃ φ : V → Fin k, IsCColoring C φ := by
  exact ⟨fun h C hC => P6c5a9611.forward G k h C hC, P6c5a9611.backward G k⟩
