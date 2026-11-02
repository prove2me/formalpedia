-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsD.polyhedral_mconvex_argmin_polyhedron
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-02T01:32:00.266625+00:00
-- url     : https://prove2.me/submissions/20a39233-6cd8-42b6-bbda-a74a948a75bc

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ArgMinOn
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MConvexPolyhedronR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_LinearWeightR

open scoped Pointwise
open Classical
open DiscreteConvex.MConvexFunctionsD

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
      (f : (V → ℝ) → WithTop ℝ)
      (_hpoly : IsPolyhedralConvex f) (_hf : MExchangeAxiomR f)
      (p : V → ℝ) (_hne : (ArgMinOn (LinearWeightR f p)).Nonempty),
      MConvexPolyhedronR (ArgMinOn (LinearWeightR f p))) := by
  intro H
  let f : (Unit → ℝ) → WithTop ℝ := fun _ => ⊤
  let p : Unit → ℝ := fun _ => 0
  have hpoly : IsPolyhedralConvex f := by
    refine ⟨1, fun _ _ => 0, fun _ => -1, ?_⟩
    ext q
    simp only [f, Set.mem_setOf_eq, top_le_iff, WithTop.coe_ne_top, false_iff, not_forall]
    exact ⟨0, by norm_num⟩
  have hf : MExchangeAxiomR f := by
    intro x hx
    simp [DomR, f] at hx
  have hmem_all : ∀ x : Unit → ℝ, x ∈ ArgMinOn (LinearWeightR f p) := by
    intro x y
    simp [LinearWeightR, f]
  have hne : (ArgMinOn (LinearWeightR f p)).Nonempty := ⟨fun _ => 0, hmem_all _⟩
  have hres := (H f hpoly hf p hne).2
  let x : Unit → ℝ := fun _ => 1
  let y : Unit → ℝ := fun _ => 0
  have hx : x ∈ DomR (fun z => if z ∈ ArgMinOn (LinearWeightR f p) then (0 : WithTop ℝ) else ⊤) := by
    simp [DomR, hmem_all x]
  have hy : y ∈ DomR (fun z => if z ∈ ArgMinOn (LinearWeightR f p) then (0 : WithTop ℝ) else ⊤) := by
    simp [DomR, hmem_all y]
  have hu : () ∈ SuppPosR x y := by
    simp [SuppPosR, x, y]
  obtain ⟨v, hv, -⟩ := hres x hx y hy () hu
  simp [SuppNegR, x, y] at hv
  norm_num at hv
