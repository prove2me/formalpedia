-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.shape_minor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:29.903367+00:00
-- url     : https://prove2.me/submissions/6b5a8a5c-b9e8-4f09-99aa-b545fc1aa726

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementH
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MinorProductSupportTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {R : Type u} [CommRing R] {J : Type} [Fintype J] [DecidableEq J] {N1 p : ℕ}
    (A : Fin p → J → R) (I : Fin p → Fin N1) :
    (Matrix.of fun (r r' : Fin p) =>
      (∑ j, C (A r j) * X (j, I r') : MvPolynomial (J × Fin N1) R)).det ∈
        restrictSupport R (shapeSet A I) := by
  classical
  have hτ : ∀ τ : Fin p → J, ∑ π : Equiv.Perm (Fin p), Equiv.Perm.sign π •
      ∏ i, (C (A (π i) (τ i)) * X (τ i, I i) : MvPolynomial (J × Fin N1) R) =
      C (Matrix.of fun (r i : Fin p) => A r (τ i)).det * ∏ i, X (τ i, I i) := by
    intro τ
    rw [Matrix.det_apply, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun π _ => ?_
    simp only [Units.smul_def, map_zsmul, smul_mul_assoc, Finset.prod_mul_distrib, map_prod,
      Matrix.of_apply]
  rw [Matrix.det_apply]
  simp only [Matrix.of_apply]
  simp_rw [Finset.prod_univ_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Submodule.sum_mem _ fun τ _ => ?_
  have hX : ∏ i, (X (τ i, I i) : MvPolynomial (J × Fin N1) R) =
      monomial (∑ i, Finsupp.single (τ i, I i) 1) 1 := by
    rw [monomial_sum_one]
    rfl
  rw [hτ τ, hX, C_mul_monomial, mul_one, monomial_mem_restrictSupport]
  by_cases hinj : Function.Injective τ
  · by_cases hd : (Matrix.of fun (r i : Fin p) => A r (τ i)).det = 0
    · exact Or.inr hd
    · left
      refine ⟨τ, hinj, ?_, rfl⟩
      by_contra hno
      push_neg at hno
      apply hd
      rw [Matrix.det_apply]
      refine Finset.sum_eq_zero fun π _ => ?_
      obtain ⟨i, hi⟩ := hno π
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), smul_zero]
  · right
    simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i, i', hii, hne⟩ := hinj
    exact Matrix.det_zero_of_column_eq hne (fun k => by simp [hii])
end Formalism.DworkPowerSeriesWeights
