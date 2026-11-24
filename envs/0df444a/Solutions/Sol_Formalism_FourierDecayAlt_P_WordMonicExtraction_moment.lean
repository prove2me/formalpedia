-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordMonicExtraction.moment
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:49.549475+00:00
-- url     : https://prove2.me/submissions/fe8847bd-9371-4afb-b90f-fa44fa2c7946

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.WordMonicExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
private theorem lagsum_lemma {F : Type} [Field F] {d : ℕ} (v : Fin (d + 1) → F)
    (hv : Function.Injective v) (P : Polynomial F) (hP : P.natDegree ≤ d) :
    ∑ j, (∏ i ∈ Finset.univ.erase j, (v j - v i)⁻¹) * P.eval (v j) = P.coeff d := by
  have hdeg : P.degree < ((Finset.univ : Finset (Fin (d + 1))).card : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hP)
  have hI := Lagrange.eq_interpolate (s := Finset.univ) (v := v) hv.injOn hdeg
  conv_rhs => rw [hI]
  rw [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hb : Lagrange.basis Finset.univ v j =
      Polynomial.C (∏ i ∈ Finset.univ.erase j, (v j - v i)⁻¹) *
        Lagrange.nodal (Finset.univ.erase j) v := by
    unfold Lagrange.basis Lagrange.basisDivisor Lagrange.nodal
    rw [Finset.prod_mul_distrib, map_prod]
  have hn : (Lagrange.nodal (Finset.univ.erase j) v).natDegree = d := by
    rw [Lagrange.natDegree_nodal, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, Nat.add_sub_cancel]
  have hm := (Lagrange.nodal_monic (s := Finset.univ.erase j) (v := v)).coeff_natDegree
  rw [hn] at hm
  rw [Polynomial.coeff_C_mul, hb, Polynomial.coeff_C_mul, hm]
  ring
section
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
end
section
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
end
end Formalism.FourierDecayAlt.P.WordMonicExtraction
namespace Formalism.FourierDecayAlt.P
open Finset Polynomial Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.WordMonicExtraction
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordMonicExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.WordMonicExtraction
theorem _root_.solution (d : ℕ) (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (k : ℕ) (hk : k ≤ d) :
    ∑ j, lagCo y j * y j ^ k = if k = d then 1 else 0 := by
  have h := lagsum_lemma y hy (Polynomial.X ^ k) (by rw [Polynomial.natDegree_X_pow]; exact hk)
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.coeff_X_pow] at h
  simp only [lagCo]
  rw [h]
  exact if_congr eq_comm rfl rfl
end Formalism.FourierDecayAlt.P.WordMonicExtraction
