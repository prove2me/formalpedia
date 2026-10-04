-- Prove2me | solution 1 for DiscreteConvex.MConvexSetsB.base_polyhedron_support_function
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:09:05.230871+00:00
-- url     : https://prove2.me/submissions/35765aa0-37bd-40e4-839a-bab1b576e75c

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSetsB_BasePolyhedron
import Definitions.Def_DiscreteConvex_MConvexSetsB_LovaszExtension
import Definitions.Def_DiscreteConvex_MConvexSetsB_SortedValues
import Definitions.Def_DiscreteConvex_MConvexSetsB_LevelSet
import Definitions.Def_DiscreteConvex_MConvexSetsB_ScalarWithTop

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

lemma cex_lovasz : LovaszExtension cexRho (fun _ => (1 : ℝ)) = (((-1 : ℝ)) : WithTop ℝ) := by
  have hs : SortedValues (fun _ : Unit => (1 : ℝ)) = [1] := by
    unfold SortedValues
    have : Finset.image (fun _ : Unit => (1 : ℝ)) Finset.univ = {1} := by
      ext a; simp
    rw [this, Finset.sort_singleton]
  have hl : LevelSet (fun _ : Unit => (1 : ℝ)) 1 = Finset.univ := by
    unfold LevelSet; rw [hs]; ext u; simp
  unfold LovaszExtension
  simp only [hs, List.length_singleton, Nat.sub_self, Finset.range_zero, Finset.sum_empty,
    zero_add, hl]
  have hu : cexRho Finset.univ = (((-1 : ℝ)) : WithTop ℝ) := by simp [cexRho]
  rw [hu]
  show (((1 * (-1) : ℝ)) : WithTop ℝ) = _
  norm_num

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) (p : V → ℝ),
    (⨆ x ∈ BasePolyhedron ρ, (((∑ v, p v * x v : ℝ)) : WithTop ℝ)) = LovaszExtension ρ p) := by
  intro h
  have key := h cexRho cexRho_submod (fun _ => (1 : ℝ))
  rw [cex_lovasz] at key
  -- the point `x = 0` is not in the base polyhedron, so its inner supremum is `sSup ∅ = 0`
  have h0 : (0 : (Unit → ℝ)) ∉ BasePolyhedron cexRho := by
    intro hx
    have := hx.2
    simp [cexRho] at this
  have hle : (⨆ (_ : (0 : Unit → ℝ) ∈ BasePolyhedron cexRho),
      (((∑ v, (fun _ => (1 : ℝ)) v * (0 : Unit → ℝ) v : ℝ)) : WithTop ℝ)) ≤
      ⨆ x ∈ BasePolyhedron cexRho, (((∑ v, (fun _ => (1 : ℝ)) v * x v : ℝ)) : WithTop ℝ) :=
    le_ciSup (f := fun x => ⨆ (_ : x ∈ BasePolyhedron cexRho),
      (((∑ v, (fun _ => (1 : ℝ)) v * x v : ℝ)) : WithTop ℝ)) (OrderTop.bddAbove _) 0
  rw [key] at hle
  have he : (⨆ (_ : (0 : Unit → ℝ) ∈ BasePolyhedron cexRho),
      (((∑ v, (fun _ => (1 : ℝ)) v * (0 : Unit → ℝ) v : ℝ)) : WithTop ℝ)) = 0 := by
    rw [ciSup_neg h0]; simp [sSup]
  rw [he] at hle
  have : ((0 : ℝ) : WithTop ℝ) ≤ (((-1 : ℝ)) : WithTop ℝ) := by simpa using hle
  have := WithTop.coe_le_coe.mp this
  linarith

#print axioms solution
