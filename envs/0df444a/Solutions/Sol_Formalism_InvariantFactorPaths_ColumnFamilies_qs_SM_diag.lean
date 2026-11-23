-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_SM_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:33.282403+00:00
-- url     : https://prove2.me/submissions/378a8510-cdec-4b83-81da-871e9b7ceb27

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {A : Type*} [CommRing A] (d : Fin n → A) (b : ℕ) (α β : SymIdx n b) :
    qs_SM (Matrix.diagonal d) b α β = if α = β then ∏ x, d x ^ (β.1 x : ℕ) else 0 := by
  classical
  have h1 : ∀ x : Fin n, (∑ a : Fin n, (MvPolynomial.C (Matrix.diagonal d a x) * X a : MvPolynomial (Fin n) A)) =
      MvPolynomial.monomial (Finsupp.single x 1) (d x) := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [Matrix.diagonal_apply_eq, MvPolynomial.C_mul_X_eq_monomial]
    · intro a _ ha; rw [Matrix.diagonal_apply_ne _ ha]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [qs_SM]
  simp_rw [h1, MvPolynomial.monomial_pow]
  rw [← MvPolynomial.monomial_sum_prod, MvPolynomial.coeff_monomial]
  have h3 : (∑ x : Fin n, (β.1 x : ℕ) • Finsupp.single x 1 = symMono α) ↔ α = β := by
    rw [Finsupp.ext_iff]
    constructor
    · intro h
      refine Subtype.ext (funext fun x => Fin.ext ?_)
      have := h x
      rw [Finsupp.finsetSum_apply] at this
      simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      exact this.symm
    · rintro rfl x
      rw [Finsupp.finsetSum_apply]
      simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
  simp only [h3]
end Formalism.InvariantFactorPaths.ColumnFamilies
