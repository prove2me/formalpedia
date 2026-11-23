-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx3.wExact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:50.31501+00:00
-- url     : https://prove2.me/submissions/f1a47ce6-e07f-4db9-9e7b-a5f87bf81ac2

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_nrm_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_rho_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx3
open Polynomial
namespace Formalism.FourierDecayAlt.P.Mx3
theorem _root_.solution : WExact := by
  intro P hP π
  have hmonic : (coordinatePolynomial P π).Monic := by
    unfold coordinatePolynomial
    exact monic_prod_of_monic _ _ (fun i _ => monic_X_add_C _)
  have hdvd : coordinatePolynomial P π ∣ wNum P π := by
    unfold coordinatePolynomial
    apply Finset.prod_dvd_of_coprime
    · intro i hi j hj hij
      show IsCoprime (X + C ((rho P π i : ℂ) + 1)) (X + C ((rho P π j : ℂ) + 1))
      have e : ∀ a : ℂ, (X + C a : ℂ[X]) = X - C (-a) := by intro a; simp
      rw [e, e]
      apply isCoprime_X_sub_C_of_isUnit_sub
      apply IsUnit.mk0
      intro h0
      have h1 : (rho P π i : ℂ) = rho P π j := by linear_combination -h0
      have h2 : rho P π i = rho P π j := by exact_mod_cast h1
      rcases lt_or_gt_of_ne hij with h | h
      · exact absurd h2 (ne_of_gt (rho_inj P hP π i j hi hj h))
      · exact absurd h2 (ne_of_lt (rho_inj P hP π j i hj hi h))
    · intro l hl
      have e : (X + C ((rho P π l : ℂ) + 1) : ℂ[X]) = X - C (-((rho P π l : ℂ) + 1)) := by rw [C_neg, sub_neg_eq_add]
      rw [e, dvd_iff_isRoot, IsRoot.def]
      unfold wNum
      rw [eval_add, eval_finsetSum, Finset.sum_eq_single l]
      · have hk := nrm_key P hP l hl π
        have hk' := congrArg (fun x : ℝ => (x : ℂ)) hk
        simp only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_one] at hk'
        have hq : eval (-((rho P π l : ℂ) + 1)) (qP P) = ((I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l - 1) : ℝ) : ℂ) := by
          unfold qP I.qpoly
          simp only [eval_mul, eval_C, eval_prod, eval_add, eval_X]
          push_cast
          congr 1
          refine Finset.prod_congr rfl ?_
          intro i _; ring
        rw [hq]
        simp only [eval_mul, eval_C, eval_prod, eval_add, eval_X]
        have e1 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-((rho P π l : ℂ) + 1) + (rho P π j : ℂ)) =
            ∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l - 1) :=
          Finset.prod_congr rfl (fun j _ => by ring)
        have e2 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-((rho P π l : ℂ) + 1) + ((rho P π j : ℂ) + 1)) =
            ∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l) :=
          Finset.prod_congr rfl (fun j _ => by ring)
        rw [e1, e2, mul_comm (∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l - 1)), hk']
        ring
      · intro m _ hml
        simp only [eval_mul, eval_C, eval_prod, eval_add, eval_X]
        have : ∏ j ∈ (Icc 1 (P.k - 1)).erase m, (-((rho P π l : ℂ) + 1) + ((rho P π j : ℂ) + 1)) = 0 :=
          Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨fun h => hml h.symm, hl⟩) (by ring)
        rw [this]; simp
      · intro h; exact absurd hl h
  have hmod := (modByMonic_eq_zero_iff_dvd hmonic).2 hdvd
  have := modByMonic_add_div (wNum P π) (coordinatePolynomial P π)
  rw [hmod, zero_add] at this
  exact this.symm
end Formalism.FourierDecayAlt.P.Mx3
