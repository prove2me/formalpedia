-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TA2.gram_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:21.989118+00:00
-- url     : https://prove2.me/submissions/00cbc9fc-635f-4b59-aba3-354bf83fca10

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OffDiagonalSchurComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TA2
namespace Formalism.FourierDecayAlt.P.TA2
theorem _root_.solution {α : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : Finset α) (k : α → α → ℂ) (V : α → H) (hk : PSDOn P k) :
    0 ≤ (∑ x ∈ P, ∑ y ∈ P, k x y * ⟪V x, V y⟫_ℂ).re := by
  classical
  let S : Submodule ℂ H := Submodule.span ℂ (V '' (P : Set α))
  have : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ ((P.finite_toSet).image V)
  have hmem : ∀ x ∈ P, V x ∈ S := fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩
  let v : α → S := fun x => if hx : x ∈ P then ⟨V x, hmem x hx⟩ else 0
  have hv : ∀ x ∈ P, ((v x : S) : H) = V x := fun x hx => by simp [v, hx]
  let b := stdOrthonormalBasis ℂ S
  have key : ∀ x ∈ P, ∀ y ∈ P,
      ⟪V x, V y⟫_ℂ = ∑ j, conj (⟪b j, v x⟫_ℂ) * ⟪b j, v y⟫_ℂ := by
    intro x hx y hy
    rw [← hv x hx, ← hv y hy, ← Submodule.coe_inner, ← b.sum_inner_mul_inner]
    refine sum_congr rfl fun j _ => ?_
    rw [inner_conj_symm]
  have e : ∑ x ∈ P, ∑ y ∈ P, k x y * ⟪V x, V y⟫_ℂ
      = ∑ j, ∑ x ∈ P, ∑ y ∈ P, conj (⟪b j, v x⟫_ℂ) * k x y * ⟪b j, v y⟫_ℂ := by
    symm
    rw [sum_comm]
    refine sum_congr rfl fun x hx => ?_
    rw [sum_comm]
    refine sum_congr rfl fun y hy => ?_
    rw [key x hx y hy, mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [e, Complex.re_sum]
  exact sum_nonneg fun j _ => hk.2 fun x => ⟪b j, v x⟫_ℂ
end Formalism.FourierDecayAlt.P.TA2
