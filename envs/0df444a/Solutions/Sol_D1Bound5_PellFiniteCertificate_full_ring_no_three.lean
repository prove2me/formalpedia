-- Prove2me | solution 1 for D1Bound5.PellFiniteCertificate.full_ring_no_three
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:27:36.976274+00:00
-- url     : https://prove2.me/submissions/e1c0fdb5-07c4-4ece-a91e-22113556652f

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
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellMatchingCheck_Definitions
import Definitions.Def_D1Bound5_UnitPairArithmeticModel_Definitions
import Definitions.Def_D1Bound5_UnitPairRealReduction_Definitions
import Theorems.Thm_D1Bound5_PellFiniteCertificate_full_ring_member
import Theorems.Thm_D1Bound5_UnitPairArithmeticModel_pellIntegerSquare
import Theorems.Thm_D1Bound5_pellMatchingCheck_no_three

section
namespace D1Bound5











































theorem PellMatchingCertificate.no_three {d : ℤ} (C : PellMatchingCertificate d)
    (hd : 0 < d) (a b c : ℤ)
    (ha : PellSignedMember C.magnitudes a) (hb : PellSignedMember C.magnitudes b)
    (hc : PellSignedMember C.magnitudes c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsab : PellIntegerSquare d (a*b+1))
    (hsac : PellIntegerSquare d (a*c+1)) : False :=
  pellMatchingCheck_no_three d hd C.masks C.masks_valid C.magnitudes C.witnesses
    C.checked C.large a b c ha hb hc hab hac hbc hsab hsac

end D1Bound5
end

section
open scoped NumberField
open Module

namespace D1Bound5









/-- The complete finite theorem in the actual full ring. Its only finite
input is a concrete kernel-checked certificate whose list is proved complete
by the ordinary continued-fraction theorem. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (M : UnitPairArithmeticModel (𝓞 K)) {X : ℤ}
    (C : PellFiniteCertificate M.d X) (hd : 7 ≤ M.d) (hX : 1 ≤ X)
    (t : Fin 3 → 𝓞 K) (ht : IsD1Tuple t)
    (hreal : ∀ i, UnitPairRealDescription M.d (t i))
    (hbound : ∀ i, ‖phi (t i : K)‖^2 ≤ (X : ℝ)^4) : False := by
  choose z hz hmem using fun i => C.full_ring_member hK phi hd hX (t i) (hreal i) (hbound i)
  have hne (i j : Fin 3) (hij : i ≠ j) : z i ≠ z j := by
    intro he
    apply hij
    apply ht.1
    rw [hz i,hz j,he]
  have hs (i j : Fin 3) (hij : i ≠ j) : PellIntegerSquare M.d (z i*z j+1) := by
    apply M.pellIntegerSquare hK
    obtain ⟨r,hr⟩ := ht.2.2 i j hij
    exact ⟨r,by simpa only [hz i,hz j,Int.cast_add,Int.cast_mul,Int.cast_one] using hr⟩
  exact C.graph.no_three M.positive (z 0) (z 1) (z 2) (hmem 0) (hmem 1) (hmem 2)
    (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 1 2 (by decide))
    (hs 0 1 (by decide)) (hs 0 2 (by decide))

end D1Bound5
end
