-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramConjugationNorm.gram_re_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:56:49.800735+00:00
-- url     : https://prove2.me/submissions/1ae6cc0e-b929-415e-9388-978eb6e62d04

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramConjugationNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramConjugationNorm
open Finset Filter Topology Formalism.FourierDecayAlt.TA
open scoped InnerProductSpace ComplexConjugate
variable {E : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Formalism.FourierDecayAlt.P.GramConjugationNorm
theorem _root_.solution (k : Pt E → Pt E → ℂ) (V : Pt E → H) (P : Finset (Pt E))
    (hk : PSDOn P k) : 0 ≤ (gram k V P).re := by
  classical
  let S : Submodule ℂ H := Submodule.span ℂ (V '' (P : Set (Pt E)))
  have : FiniteDimensional ℂ S :=
    FiniteDimensional.span_of_finite ℂ ((P.finite_toSet).image V)
  have hex : ∀ p, p ∈ P → ∃ v : S, (v : H) = V p :=
    fun p hp => ⟨⟨V p, Submodule.subset_span ⟨p, hp, rfl⟩⟩, rfl⟩
  choose! v hv using hex
  let b := stdOrthonormalBasis ℂ S
  have key : gram k V P =
      ∑ j, ∑ p ∈ P, ∑ p' ∈ P, conj (⟪b j, v p⟫_ℂ) * k p p' * ⟪b j, v p'⟫_ℂ := by
    unfold gram
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p' hp' => ?_
    have h1 : ⟪V p, V p'⟫_ℂ = ⟪v p, v p'⟫_ℂ := by
      rw [← hv p hp, ← hv p' hp']; rfl
    rw [h1, ← b.sum_inner_mul_inner (v p) (v p'), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_conj_symm]; ring
  rw [key, Complex.re_sum]
  exact Finset.sum_nonneg fun j _ => hk.2 (fun p => ⟪b j, v p⟫_ℂ)
end Formalism.FourierDecayAlt.P.GramConjugationNorm
