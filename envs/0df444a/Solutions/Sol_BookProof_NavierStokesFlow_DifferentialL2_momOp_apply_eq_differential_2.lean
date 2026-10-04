-- Prove2me | solution 2 for BookProof.NavierStokesFlow.DifferentialL2.momOp_apply_eq_differential
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T11:44:40.203227+00:00
-- url     : https://prove2.me/submissions/5dd70520-6e48-46fb-bffc-9f71eddcb527

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteProductCore

set_option autoImplicit false

namespace AF3644BA

open BookProof.HermiteProductCore

theorem hasDerivAt_update_apply {d : ℕ} (v : Fin d → ℝ) (i j : Fin d) (t0 : ℝ) :
    HasDerivAt (fun t : ℝ => Function.update v i t j) (if j = i then 1 else 0) t0 := by
  by_cases h : j = i
  · subst h
    rw [if_pos rfl]
    exact (hasDerivAt_id' t0).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by simp)
  · rw [if_neg h]
    exact (hasDerivAt_const t0 (v j)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by simp [Function.update_of_ne h])

theorem hasDerivAt_eval_update {d : ℕ} (v : Fin d → ℝ) (i : Fin d)
    (p : MvPolynomial (Fin d) ℂ) (t0 : ℝ) :
    HasDerivAt (fun t : ℝ => MvPolynomial.eval
        (fun j => ((Function.update v i t j : ℝ) : ℂ)) p)
      (MvPolynomial.eval (fun j => ((Function.update v i t0 j : ℝ) : ℂ))
        (MvPolynomial.pderiv i p)) t0 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      refine ((hasDerivAt_const t0 a).congr_deriv ?_).congr_of_eventuallyEq ?_
      · simp
      · exact Filter.Eventually.of_forall fun t => by simp
  | add p q hp hq =>
      refine ((hp.add hq).congr_deriv ?_).congr_of_eventuallyEq ?_
      · simp
      · exact Filter.Eventually.of_forall fun t => by simp
  | mul_X p j hp =>
      have hj : HasDerivAt (fun t : ℝ => ((Function.update v i t j : ℝ) : ℂ))
          (((if j = i then 1 else 0 : ℝ)) : ℂ) t0 :=
        (hasDerivAt_update_apply v i j t0).ofReal_comp
      refine ((hp.mul hj).congr_deriv ?_).congr_of_eventuallyEq ?_
      · rw [Derivation.leibniz, MvPolynomial.pderiv_X]
        by_cases h : j = i
        · subst h
          simp [smul_eq_mul]
          ring
        · simp [smul_eq_mul, h, Pi.single_apply]
          ring
      · exact Filter.Eventually.of_forall fun t => by simp

end AF3644BA

open BookProof.HermiteProductCore BookProof.NavierStokesFlow.DifferentialL2 in
theorem solution {d : ℕ} (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (momPoly i p) x
      = -Complex.I * deriv (fun t : ℝ => pgFun p (sec i x t)) (x i) := by
  -- norm squared along the line
  have hnorm : ∀ t : ℝ, ‖sec i x t‖ ^ 2
      = ∑ j, (Function.update (WithLp.ofLp x) i t j) ^ 2 := by
    intro t
    rw [EuclideanSpace.norm_sq_eq]
    simp [sec, Real.norm_eq_abs, sq_abs]
  have hN : HasDerivAt (fun t : ℝ => ‖sec i x t‖ ^ 2) (2 * x i) (x i) := by
    have hs : HasDerivAt (fun t : ℝ => ∑ j, (Function.update (WithLp.ofLp x) i t j) ^ 2)
        (∑ j, (2 * Function.update (WithLp.ofLp x) i (x i) j *
          (if j = i then 1 else 0))) (x i) := by
      apply HasDerivAt.fun_sum
      intro j _
      exact ((AF3644BA.hasDerivAt_update_apply (WithLp.ofLp x) i j (x i)).pow 2).congr_deriv
        (by norm_num)
    have hval : (∑ j, (2 * Function.update (WithLp.ofLp x) i (x i) j *
          (if j = i then (1:ℝ) else 0))) = 2 * x i := by
      simp [Finset.sum_ite_eq']
    rw [hval] at hs
    exact hs.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hnorm t)
  have hG : HasDerivAt (fun t : ℝ => ((gaussD (sec i x t) : ℝ) : ℂ))
      (((gaussD x * (-(x i) / 2) : ℝ)) : ℂ) (x i) := by
    have h1 := ((hN.neg.div_const 4).exp).ofReal_comp
    have hsx : sec i x (x i) = x := by
      ext j; simp [sec]
    refine (h1.congr_deriv ?_).congr_of_eventuallyEq ?_
    · rw [Pi.neg_apply, hsx]
      unfold gaussD
      push_cast
      ring
    · exact Filter.Eventually.of_forall fun t => by simp [gaussD]
  have hP := AF3644BA.hasDerivAt_eval_update (WithLp.ofLp x) i p (x i)
  have hF : HasDerivAt (fun t : ℝ => pgFun p (sec i x t))
      (MvPolynomial.eval (fun j => ((Function.update (WithLp.ofLp x) i (x i) j : ℝ) : ℂ))
        (MvPolynomial.pderiv i p) * ((gaussD x : ℝ) : ℂ)
        + MvPolynomial.eval (fun j => ((Function.update (WithLp.ofLp x) i (x i) j : ℝ) : ℂ)) p
          * (((gaussD x * (-(x i) / 2) : ℝ)) : ℂ)) (x i) := by
    have hsx : sec i x (x i) = x := by
      ext j; simp [sec]
    refine ((hP.mul hG).congr_deriv ?_).congr_of_eventuallyEq ?_
    · rw [hsx]
    · exact Filter.Eventually.of_forall fun t => by simp [pgFun, sec]
  rw [hF.deriv]
  simp only [pgFun, momPoly, LinearMap.coe_mk, AddHom.coe_mk, map_mul, map_sub,
    MvPolynomial.eval_C, MvPolynomial.eval_X, Function.update_eq_self]
  push_cast
  simp
  ring
