-- Prove2me | solution 2 for BookProof.ShiftedHermiteCore.deriv_pgFunT_sec
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T04:20:50.04991+00:00
-- url     : https://prove2.me/submissions/829a815d-21cf-4576-954e-9c53b20438c7

-- Generated from ChapterShiftedHermiteCore.lean — solution of BookProof.ShiftedHermiteCore.deriv_pgFunT_sec
import Mathlib
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.ShiftedHermiteCore

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

set_option maxHeartbeats 1000000

variable {d : ℕ}

/-! ### Coordinate sections (re-proved locally) -/

private theorem sol_sec_apply (i : Fin d) (x : Vd d) (t : ℝ) (j : Fin d) :
    (sec i x t) j = if j = i then t else x j := by
  simp [sec, Function.update_apply]

@[simp] private theorem sol_sec_self (i : Fin d) (x : Vd d) : sec i x (x i) = x := by
  simp [sec]

private theorem sol_norm_sq_sec (i : Fin d) (x : Vd d) (t : ℝ) :
    ‖sec i x t‖ ^ 2 = (∑ j ∈ Finset.univ.erase i, (x j) ^ 2) + t ^ 2 := by
  classical
  rw [norm_sq_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), sol_sec_apply]
  simp only []
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun j hj => by rw [sol_sec_apply, if_neg (Finset.ne_of_mem_erase hj)]

/-- A purely one-dimensional computation: the derivative of `s ↦ e^{-(S+s²)/4}`. -/
private theorem sol_hasDerivAt_exp_quad (S t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-(S + s ^ 2) / 4))
      (-(t / 2) * Real.exp (-(S + t ^ 2) / 4)) t := by
  have h1 : HasDerivAt (fun s : ℝ => -(S + s ^ 2) / 4) (-(2 * t) / 4) t := by
    have h : HasDerivAt (fun s : ℝ => -(S + s ^ 2) / 4) (-(0 + 2 * t) / 4) t := by
      have h0 : HasDerivAt (fun s : ℝ => S + s ^ 2) (0 + 2 * t) t := by
        simpa using ((hasDerivAt_pow 2 t).const_add S)
      exact h0.neg.div_const 4
    simpa using h
  have h2 := h1.exp
  have hv : -(t / 2) * Real.exp (-(S + t ^ 2) / 4)
      = Real.exp (-(S + t ^ 2) / 4) * (-(2 * t) / 4) := by ring
  rw [hv]
  exact h2

private theorem sol_hasDerivAt_gaussD_sec (i : Fin d) (x : Vd d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gaussD (sec i x s)) (-(t / 2) * gaussD (sec i x t)) t := by
  have hfun : (fun s : ℝ => gaussD (sec i x s))
      = fun s : ℝ => Real.exp (-((∑ j ∈ Finset.univ.erase i, (x j) ^ 2) + s ^ 2) / 4) := by
    funext s
    rw [gaussD, sol_norm_sq_sec]
  have hval : gaussD (sec i x t)
      = Real.exp (-((∑ j ∈ Finset.univ.erase i, (x j) ^ 2) + t ^ 2) / 4) := by
    rw [gaussD, sol_norm_sq_sec]
  rw [hfun, hval]
  exact sol_hasDerivAt_exp_quad _ t

/-- The derivative of a polynomial along one coordinate is the partial derivative. -/
private theorem sol_hasDerivAt_eval_update (i : Fin d) (p : MvPolynomial (Fin d) ℂ)
    (x : Fin d → ℂ) (t : ℂ) :
    HasDerivAt (fun s : ℂ => MvPolynomial.eval (Function.update x i s) p)
      (MvPolynomial.eval (Function.update x i t) (pderiv i p)) t := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have hfun : (fun s : ℂ => MvPolynomial.eval (Function.update x i s) (MvPolynomial.C a))
          = fun _ : ℂ => a := by
        funext s
        simp
      have hder : MvPolynomial.eval (Function.update x i t) (pderiv i (MvPolynomial.C a))
          = (0 : ℂ) := by
        simp
      rw [hfun, hder]
      exact hasDerivAt_const t a
  | add p q hp hq =>
      have h := hp.add hq
      have hfun : (fun s : ℂ => MvPolynomial.eval (Function.update x i s) (p + q))
          = (fun s : ℂ => MvPolynomial.eval (Function.update x i s) p)
            + fun s : ℂ => MvPolynomial.eval (Function.update x i s) q := by
        funext s
        simp only [Pi.add_apply, map_add]
      have hder : MvPolynomial.eval (Function.update x i t) (pderiv i (p + q))
          = MvPolynomial.eval (Function.update x i t) (pderiv i p)
            + MvPolynomial.eval (Function.update x i t) (pderiv i q) := by
        simp only [map_add]
      rw [hfun, hder]
      exact h
  | mul_X p j hp =>
      by_cases hj : j = i
      · subst hj
        have hXfun : (fun s : ℂ => MvPolynomial.eval (Function.update x j s) (MvPolynomial.X j))
            = fun s : ℂ => s := by
          funext s
          simp
        have hX : HasDerivAt
            (fun s : ℂ => MvPolynomial.eval (Function.update x j s) (MvPolynomial.X j)) 1 t := by
          rw [hXfun]
          exact hasDerivAt_id' t
        have h := hp.mul hX
        have hfun : (fun s : ℂ =>
              MvPolynomial.eval (Function.update x j s) (p * MvPolynomial.X j))
            = (fun s : ℂ => MvPolynomial.eval (Function.update x j s) p)
              * fun s : ℂ => MvPolynomial.eval (Function.update x j s) (MvPolynomial.X j) := by
          funext s
          simp only [Pi.mul_apply, map_mul]
        have hder : MvPolynomial.eval (Function.update x j t)
              (pderiv j (p * MvPolynomial.X j))
            = MvPolynomial.eval (Function.update x j t) (pderiv j p)
                * MvPolynomial.eval (Function.update x j t) (MvPolynomial.X j)
              + MvPolynomial.eval (Function.update x j t) p * 1 := by
          rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self]
          simp only [map_add, map_mul, map_one]
        rw [hfun, hder]
        exact h
      · have hXfun : (fun s : ℂ => MvPolynomial.eval (Function.update x i s) (MvPolynomial.X j))
            = fun _ : ℂ => x j := by
          funext s
          simp [MvPolynomial.eval_X, Function.update_apply, hj]
        have hX : HasDerivAt
            (fun s : ℂ => MvPolynomial.eval (Function.update x i s) (MvPolynomial.X j)) 0 t := by
          rw [hXfun]
          exact hasDerivAt_const t (x j)
        have h := hp.mul hX
        have hfun : (fun s : ℂ =>
              MvPolynomial.eval (Function.update x i s) (p * MvPolynomial.X j))
            = (fun s : ℂ => MvPolynomial.eval (Function.update x i s) p)
              * fun s : ℂ => MvPolynomial.eval (Function.update x i s) (MvPolynomial.X j) := by
          funext s
          simp only [Pi.mul_apply, map_mul]
        have hder : MvPolynomial.eval (Function.update x i t)
              (pderiv i (p * MvPolynomial.X j))
            = MvPolynomial.eval (Function.update x i t) (pderiv i p)
                * MvPolynomial.eval (Function.update x i t) (MvPolynomial.X j)
              + MvPolynomial.eval (Function.update x i t) p * 0 := by
          rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_of_ne hj]
          simp only [map_add, map_mul, map_zero]
        rw [hfun, hder]
        exact h

private theorem sol_hasDerivAt_evalSec (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    HasDerivAt (fun t : ℝ => MvPolynomial.eval (fun j => (((sec i x t) j : ℝ) : ℂ)) p)
      (MvPolynomial.eval (fun j => ((x j : ℝ) : ℂ)) (pderiv i p)) (x i) := by
  classical
  have hupd : ∀ t : ℝ, (fun j => (((sec i x t) j : ℝ) : ℂ))
      = Function.update (fun j => ((x j : ℝ) : ℂ)) i ((t : ℝ) : ℂ) := by
    intro t
    funext j
    rw [sol_sec_apply, Function.update_apply]
    by_cases hj : j = i <;> simp [hj]
  have hbase := sol_hasDerivAt_eval_update i p (fun j => ((x j : ℝ) : ℂ)) (((x i : ℝ)) : ℂ)
  have h := hbase.comp_ofReal (z := x i)
  have heq : (fun y : ℝ => MvPolynomial.eval
        (Function.update (fun j => ((x j : ℝ) : ℂ)) i ((y : ℝ) : ℂ)) p)
      = fun t : ℝ => MvPolynomial.eval (fun j => (((sec i x t) j : ℝ) : ℂ)) p := by
    funext t; rw [hupd t]
  rw [heq] at h
  have hfun : Function.update (fun j => ((x j : ℝ) : ℂ)) i (((x i : ℝ)) : ℂ)
      = fun j => ((x j : ℝ) : ℂ) := by
    funext j
    rw [Function.update_apply]
    by_cases hj : j = i <;> simp [hj]
  rwa [hfun] at h

/-- **The coordinate derivative of a Gauss–polynomial**:
`∂ᵢ(p·e^{-‖u‖²/4}) = (∂ᵢp − (uᵢ/2)p)·e^{-‖u‖²/4}`. -/
private theorem sol_hasDerivAt_pgFun_sec (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    HasDerivAt (fun t : ℝ => pgFun p (sec i x t))
      (pgFun (pderiv i p - (1/2 : ℂ) • (X i * p)) x) (x i) := by
  have hg : HasDerivAt (fun t : ℝ => ((gaussD (sec i x t) : ℝ) : ℂ))
      (((-(x i / 2) * gaussD x : ℝ)) : ℂ) (x i) := by
    have h := (sol_hasDerivAt_gaussD_sec i x (x i)).ofReal_comp
    simpa using h
  have hp := sol_hasDerivAt_evalSec i p x
  have h := hp.mul hg
  have hfun : (fun t : ℝ => pgFun p (sec i x t))
      = (fun t : ℝ => MvPolynomial.eval (fun j => (((sec i x t) j : ℝ) : ℂ)) p)
        * (fun t : ℝ => ((gaussD (sec i x t) : ℝ) : ℂ)) := by
    funext t; simp [pgFun]
  have hval : pgFun (pderiv i p - (1/2 : ℂ) • (X i * p)) x
      = MvPolynomial.eval (fun j => ((x j : ℝ) : ℂ)) (pderiv i p)
          * ((gaussD (sec i x (x i)) : ℝ) : ℂ)
        + MvPolynomial.eval (fun j => (((sec i x (x i)) j : ℝ) : ℂ)) p
          * (((-(x i / 2) * gaussD x : ℝ)) : ℂ) := by
    rw [sol_sec_self]
    simp only [pgFun, map_sub, MvPolynomial.smul_eval, map_mul, MvPolynomial.eval_X]
    push_cast
    ring
  rw [hfun, hval]
  exact h

@[simp] private theorem sol_dPoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    dPoly i p = pderiv i p - (1/2 : ℂ) • (X i * p) := rfl

/-! ### The phase along a coordinate line (re-proved locally) -/

private theorem sol_phaseArg_sec (k x : Vd d) (i : Fin d) (t : ℝ) :
    phaseArg k (sec i x t) = phaseArg k x + k i * (t - x i) := by
  classical
  have hterm : ∀ j : Fin d, k j * (sec i x t) j
      = k j * x j + (if j = i then k i * (t - x i) else 0) := by
    intro j
    rw [sol_sec_apply]
    by_cases hj : j = i
    · subst hj; simp; ring
    · simp [hj]
  rw [phaseArg, phaseArg, Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib]
  simp

private theorem sol_phaseFun_sec (k x : Vd d) (i : Fin d) (t : ℝ) :
    phaseFun k (sec i x t)
      = phaseFun k x * Complex.exp (Complex.I * (((k i * (t - x i) : ℝ)) : ℂ)) := by
  rw [phaseFun, phaseFun, sol_phaseArg_sec, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The derivative of the phase along the `i`-th coordinate line. -/
private theorem sol_hasDerivAt_phaseFun_sec (k x : Vd d) (i : Fin d) :
    HasDerivAt (fun t : ℝ => phaseFun k (sec i x t))
      (phaseFun k x * (Complex.I * ((k i : ℝ) : ℂ))) (x i) := by
  have hlin : HasDerivAt
      (fun z : ℂ => Complex.I * (((k i : ℝ) : ℂ) * (z - ((x i : ℝ) : ℂ))))
      (Complex.I * ((k i : ℝ) : ℂ)) (((x i : ℝ)) : ℂ) := by
    simpa using
      ((((hasDerivAt_id (((x i : ℝ)) : ℂ)).sub_const (((x i : ℝ)) : ℂ)).const_mul
        (((k i : ℝ) : ℂ))).const_mul Complex.I)
  have hE : HasDerivAt
      (fun z : ℂ => Complex.exp (Complex.I * (((k i : ℝ) : ℂ) * (z - ((x i : ℝ) : ℂ)))))
      (Complex.I * ((k i : ℝ) : ℂ)) (((x i : ℝ)) : ℂ) := by
    simpa using hlin.cexp
  have hR := hE.comp_ofReal (z := x i)
  have hfun : (fun t : ℝ =>
        Complex.exp (Complex.I * (((k i : ℝ) : ℂ) * (((t : ℝ) : ℂ) - ((x i : ℝ) : ℂ)))))
      = fun t : ℝ => Complex.exp (Complex.I * (((k i * (t - x i) : ℝ)) : ℂ)) := by
    funext t
    congr 2
    push_cast
    ring
  rw [hfun] at hR
  have hmul := hR.const_mul (phaseFun k x)
  have hfun2 : (fun t : ℝ =>
        phaseFun k x * Complex.exp (Complex.I * (((k i * (t - x i) : ℝ)) : ℂ)))
      = fun t : ℝ => phaseFun k (sec i x t) := by
    funext t
    rw [sol_phaseFun_sec]
  rwa [hfun2] at hmul

/-- **The derivative of a translated, modulated Gauss–polynomial along a coordinate line.** -/
private theorem sol_hasDerivAt_pgFunT_sec (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ)
    (x : Vd d) :
    HasDerivAt (fun t : ℝ => pgFunT a k p (sec i x t))
      (pgFunT a k (dPoly i p) x + (Complex.I * ((k i : ℝ) : ℂ)) * pgFunT a k p x) (x i) := by
  have hsec : ∀ t : ℝ, sec i x t - a = sec i (x - a) (t - a i) := by
    intro t
    ext j
    by_cases h : j = i <;> simp [sol_sec_apply, h]
  have h1 : HasDerivAt (fun t : ℝ => pgFun p (sec i x t - a))
      (pgFun (dPoly i p) (x - a)) (x i) := by
    have hbase := sol_hasDerivAt_pgFun_sec i p (x - a)
    have hpt : (x - a) i = x i - a i := by simp
    rw [hpt] at hbase
    have hcomp := HasDerivAt.comp_sub_const (x i) (a i) hbase
    have hfun : (fun t : ℝ => pgFun p (sec i (x - a) (t - a i)))
        = fun t : ℝ => pgFun p (sec i x t - a) := by
      funext t
      rw [hsec]
    rw [hfun] at hcomp
    simpa [sol_dPoly_apply] using hcomp
  have h2 := sol_hasDerivAt_phaseFun_sec k x i
  have hprod := h1.mul h2
  simp only [Pi.mul_def, sol_sec_self] at hprod
  have hval : (fun t : ℝ => pgFun p (sec i x t - a) * phaseFun k (sec i x t))
      = fun t : ℝ => pgFunT a k p (sec i x t) := by
    funext t
    rw [pgFunT]
  rw [hval] at hprod
  have hsimp : pgFun (dPoly i p) (x - a) * phaseFun k x
      + pgFun p (x - a) * (phaseFun k x * (Complex.I * ((k i : ℝ) : ℂ)))
      = pgFunT a k (dPoly i p) x + (Complex.I * ((k i : ℝ) : ℂ)) * pgFunT a k p x := by
    rw [pgFunT, pgFunT]
    ring
  rwa [hsimp] at hprod

theorem solution (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    deriv (fun t : ℝ => pgFunT a k p (sec i x t)) (x i)
      = pgFunT a k (dPoly i p) x + (Complex.I * ((k i : ℝ) : ℂ)) * pgFunT a k p x :=
  (sol_hasDerivAt_pgFunT_sec a k i p x).deriv
