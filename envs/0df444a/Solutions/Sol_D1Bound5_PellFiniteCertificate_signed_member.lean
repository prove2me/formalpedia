-- Prove2me | solution 1 for D1Bound5.PellFiniteCertificate.signed_member
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:22:18.458241+00:00
-- url     : https://prove2.me/submissions/27f91b75-9f54-446f-8cc2-53ce888b74d3

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_PellCFPrefixCheck_Definitions
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellMatchingCheck_Definitions
import Definitions.Def_D1Bound5_UnitPairArithmeticModel_Definitions
import Definitions.Def_D1Bound5_UnitPairPellBounds_Definitions
import Theorems.Thm_D1Bound5_pellCFSolutions_complete_abs

section
open scoped NumberField
open Module

namespace D1Bound5



theorem _root_.solution {d X : ℤ}
    (C : PellFiniteCertificate d X) (hd : 7 ≤ d) (hX : 1 ≤ X)
    (u v z : ℤ) (hv : v ≠ 0) (heq : u^2-d*v^2=2)
    (hbound : u^2-1 ≤ X^2) (hz : z=d*v^2+1 ∨ z=-(d*v^2+1)) :
    PellSignedMember C.graph.magnitudes z := by
  have hsol := pellCFSolutions_complete_abs hd C.prefix_checked C.stopping hX hv heq hbound
  have hmem : |u|^2-1 ∈
      (pellCFSolutions d C.a0 X C.lastIndex).map (fun uv => uv.1^2-1) :=
    List.mem_map.mpr ⟨(|u|,|v|),hsol,rfl⟩
  rw [C.magnitudes_eq] at hmem
  rw [sq_abs] at hmem
  refine ⟨u^2-1,hmem,?_⟩
  rcases hz with hz | hz
  · exact Or.inl (by nlinarith [heq])
  · exact Or.inr (by nlinarith [heq])







end D1Bound5
end
