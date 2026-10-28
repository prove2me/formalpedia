-- Prove2me | solution 1 for D1Bound5.small_pair_graph_excludes_three_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:38:05.735955+00:00
-- url     : https://prove2.me/submissions/f8c46de7-4876-4a41-82f7-8b5ff62d175a

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions
import Theorems.Thm_D1Bound5_no_three_of_graph_certificate
import Theorems.Thm_D1Bound5_pairClosure_complete_full_ring
import Theorems.Thm_D1Bound5_pairClosure_of_checked
import Theorems.Thm_D1Bound5_pairSeedsCovered_of_checked

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt







/-- Complete finite-graph exclusion for actual full-ring common extensions.
Every input hypothesis is either mathematical anchor data or a finite,
kernel-checkable seed, closure, filtering or triangle certificate. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {tau nu : ℤ} (hd : 0 < discriminant tau nu)
    (e : QuadInt tau nu ≃+* 𝓞 K) (a b : QuadInt tau nu)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a*b+1 ≠ 0)
    (hroot : ∃ r0, r0*r0 = a*b+1) (hNa : a.norm ≤ 8) (hNb : b.norm ≤ 8)
    (bound : ℤ) (roots vertices large : List (QuadInt tau nu))
    (sieve : List (ℕ × ℕ)) (hvalid : CoordinateSquareSieveValid tau nu sieve)
    (hrootdisk : ∀ q ∈ disk tau nu 132, q ∈ roots)
    (hseeds : pairSeedsCoveredBool a b roots vertices = true)
    (hclosed : pairClosureBool a b bound vertices = true)
    (hfilter : largePairVertices a b vertices = large)
    (htriangle : pairGraphTriangleFreeBool sieve large = true)
    (t : Fin 3 → QuadInt tau nu) (ht : IsD1Tuple t)
    (hpair : ∀ i, PairExtension a b (t i))
    (hlarge : ∀ i, 9 ≤ (t i).norm)
    (hbound : ∀ i, (t i).norm ≤ bound)
    (hneA : ∀ i, t i ≠ a) (hneB : ∀ i, t i ≠ b) : False := by
  apply no_three_of_graph_certificate hd sieve hvalid large htriangle t ht
  intro i
  have hmem : t i ∈ vertices := by
    apply pairClosure_complete_full_ring hK phi hd e a b ha hb hab hroot hNa hNb
      bound vertices ?_ ?_ (t i) (hpair i) (hbound i)
    · intro z hz hNz
      exact pairSeedsCovered_of_checked hd a b ha hNa roots vertices
        hrootdisk hseeds z hz hNz
    · intro z hz w hw hNw
      exact pairClosure_of_checked a b bound vertices hclosed hz hw hNw
  rw [← hfilter]
  apply List.mem_filter.mpr
  refine ⟨hmem, ?_⟩
  simp only [decide_eq_true_eq]
  exact ⟨hlarge i, ht.2.1 i, hneA i, hneB i⟩

end D1Bound5
end
