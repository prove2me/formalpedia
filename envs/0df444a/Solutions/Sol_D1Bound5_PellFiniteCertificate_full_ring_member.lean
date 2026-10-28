-- Prove2me | solution 1 for D1Bound5.PellFiniteCertificate.full_ring_member
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:50:44.229336+00:00
-- url     : https://prove2.me/submissions/4caf9e32-c782-42af-8df6-68a3cbece634

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
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PellCFPrefixCheck_Definitions
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellMatchingCheck_Definitions
import Definitions.Def_D1Bound5_UnitPairArithmeticModel_Definitions
import Definitions.Def_D1Bound5_UnitPairRealReduction_Definitions
import Theorems.Thm_D1Bound5_PellFiniteCertificate_signed_member
import Theorems.Thm_D1Bound5_QuadInt_norm_formula
import Theorems.Thm_D1Bound5_exists_imaginary_quadratic_ring_equiv
import Theorems.Thm_D1Bound5_norm_sq_full_ring_equiv

section
open scoped NumberField
open Module

namespace D1Bound5







/-- Closed radius X^2 is represented by squared complex norm at most X^4.
Both signs of each real Pell extension are retained. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ) {d X : ℤ}
    (C : PellFiniteCertificate d X) (hd : 7 ≤ d) (hX : 1 ≤ X)
    (z : 𝓞 K) (hreal : UnitPairRealDescription d z)
    (hbound : ‖phi (z : K)‖^2 ≤ (X : ℝ)^4) :
    ∃ m : ℤ, z=(m : 𝓞 K) ∧ PellSignedMember C.graph.magnitudes m := by
  obtain ⟨u,v,hv,heq,hz⟩ := hreal
  let m : ℤ := d*v^2+1
  have hm : 0 < m := by
    dsimp [m]
    have hp := mul_nonneg (show 0 ≤ d by omega) (sq_nonneg v)
    omega
  obtain ⟨tau,nu,_,_,⟨e⟩⟩ := exists_imaginary_quadratic_ring_equiv hK
  have hint : ‖phi ((m : 𝓞 K) : K)‖^2 = (m : ℝ)^2 := by
    have hh := norm_sq_full_ring_equiv e phi (m : QuadInt tau nu)
    simpa [QuadInt.norm_formula] using hh
  have hn : ‖phi (z : K)‖^2 = (m : ℝ)^2 := by
    rcases hz with hz | hz
    · simpa [m,hz] using hint
    · have hz' : z = -(m : 𝓞 K) := hz
      change ‖(phi.comp (algebraMap (𝓞 K) K)) z‖^2 = (m : ℝ)^2
      rw [hz', map_neg, norm_neg]
      exact hint
  have hbound' : m^2 ≤ X^4 := by
    rw [hn] at hbound
    exact_mod_cast hbound
  have hmag : u^2-1 ≤ X^2 := by
    have hrel : u^2-1=m := by dsimp [m]; nlinarith [heq]
    rw [hrel]
    by_contra h
    have hlo : 0 < m-X^2 := by omega
    have hhi : 0 < m+X^2 := by positivity
    have hp := mul_pos hlo hhi
    nlinarith
  rcases hz with hz | hz
  · exact ⟨m,hz,C.signed_member hd hX u v m hv heq hmag (Or.inl rfl)⟩
  · refine ⟨-m,by simpa only [m,Int.cast_neg] using hz,?_⟩
    exact C.signed_member hd hX u v (-m) hv heq hmag (Or.inr rfl)



end D1Bound5
end
