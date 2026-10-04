-- Prove2me | solution 1 for DiscreteConvex.MConvexSetsB.submodular_induces_mconvex
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:12:35.030861+00:00
-- url     : https://prove2.me/submissions/ac16e5a1-3432-4f03-b8c8-6a4dcd8c89ee

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSetsB_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexSetsB_BasePolyhedron
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB

open DiscreteConvex.MConvexSetsB

/-- The counterexample set function on `V = Unit`: `ρ(∅) = 0`, `ρ(V) = -1`. -/
noncomputable def cexRho : Finset Unit → WithTop ℝ :=
  fun X => if X = ∅ then 0 else (((-1 : ℝ)) : WithTop ℝ)

lemma cexRho_submod : SubmodularSetFunction cexRho := by
  refine ⟨by simp [cexRho], by simp [cexRho], ?_⟩
  intro X Y
  have hX : X = ∅ ∨ X = Finset.univ := by
    rcases Finset.eq_empty_or_nonempty X with h | h
    · exact Or.inl h
    · right; ext u; simp; obtain ⟨w, hw⟩ := h; cases u; cases w; exact hw
  have hY : Y = ∅ ∨ Y = Finset.univ := by
    rcases Finset.eq_empty_or_nonempty Y with h | h
    · exact Or.inl h
    · right; ext u; simp; obtain ⟨w, hw⟩ := h; cases u; cases w; exact hw
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;> simp [cexRho]

lemma cexRho_int : IsIntegerValued cexRho := by
  intro X
  right
  by_cases h : X = ∅
  · exact ⟨0, by simp [cexRho, h]⟩
  · exact ⟨-1, by simp [cexRho, h]⟩

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) (hInt : IsIntegerValued ρ),
    ExchangeAxiomB {x : V → ℤ | (fun v => (x v : ℝ)) ∈ BasePolyhedron ρ} ∧
      ({x : V → ℤ | (fun v => (x v : ℝ)) ∈ BasePolyhedron ρ}).Nonempty ∧
      (∀ X : Finset V, ρ X = ⨆ x ∈ BasePolyhedron ρ, (((∑ v ∈ X, x v : ℝ)) : WithTop ℝ))) := by
  intro h
  have key := (h cexRho cexRho_submod cexRho_int).2.2 Finset.univ
  have hu : cexRho Finset.univ = (((-1 : ℝ)) : WithTop ℝ) := by simp [cexRho]
  rw [hu] at key
  -- the point `x = 0` is not in the base polyhedron, so its inner supremum is `sSup ∅ = 0`
  have h0 : (0 : (Unit → ℝ)) ∉ BasePolyhedron cexRho := by
    intro hx
    have := hx.2
    simp [cexRho] at this
  have hle : (⨆ (_ : (0 : Unit → ℝ) ∈ BasePolyhedron cexRho),
      (((∑ v ∈ Finset.univ, (0 : Unit → ℝ) v : ℝ)) : WithTop ℝ)) ≤
      ⨆ x ∈ BasePolyhedron cexRho, (((∑ v ∈ Finset.univ, x v : ℝ)) : WithTop ℝ) :=
    le_ciSup (f := fun x => ⨆ (_ : x ∈ BasePolyhedron cexRho),
      (((∑ v ∈ Finset.univ, x v : ℝ)) : WithTop ℝ)) (OrderTop.bddAbove _) 0
  rw [← key] at hle
  have he : (⨆ (_ : (0 : Unit → ℝ) ∈ BasePolyhedron cexRho),
      (((∑ v ∈ Finset.univ, (0 : Unit → ℝ) v : ℝ)) : WithTop ℝ)) = 0 := by
    rw [ciSup_neg h0]; simp [sSup]
  rw [he] at hle
  have : ((0 : ℝ) : WithTop ℝ) ≤ (((-1 : ℝ)) : WithTop ℝ) := by simpa using hle
  have := WithTop.coe_le_coe.mp this
  linarith

#print axioms solution
