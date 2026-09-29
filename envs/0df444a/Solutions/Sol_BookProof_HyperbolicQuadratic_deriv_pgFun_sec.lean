-- Prove2me | solution 1 for BookProof.HyperbolicQuadratic.deriv_pgFun_sec
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T04:20:59.995984+00:00
-- url     : https://prove2.me/submissions/76360498-7823-49c4-8b94-e406ac498baf

import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

/-- Coordinates of the coordinate line `sec i x s`. -/
theorem hqDps_sec_apply {d : ℕ} (i : Fin d) (x : Vd d) (s : ℝ) (j : Fin d) :
    (sec i x s) j = if j = i then s else x j := by
  by_cases h : j = i
  · subst h; simp [sec]
  · simp [sec, h]

/-- Differentiating the polynomial factor along the `i`-th coordinate line gives `pderiv i`. -/
theorem hqDps_eval_hasDerivAt {d : ℕ} (i : Fin d) (x : Vd d) (t : ℝ)
    (p : MvPolynomial (Fin d) ℂ) :
    HasDerivAt (fun s : ℝ => MvPolynomial.eval (fun k => (((sec i x s) k : ℝ) : ℂ)) p)
      (MvPolynomial.eval (fun k => (((sec i x t) k : ℝ) : ℂ)) (pderiv i p)) t := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have hfun : (fun s : ℝ => MvPolynomial.eval (fun k => (((sec i x s) k : ℝ) : ℂ)) (C a))
          = fun _ : ℝ => a := by
        funext s; simp
      rw [hfun, MvPolynomial.pderiv_C, map_zero]
      exact hasDerivAt_const t a
  | add q r hq hr =>
      have hfun : (fun s : ℝ => MvPolynomial.eval (fun k => (((sec i x s) k : ℝ) : ℂ)) (q + r))
          = fun s : ℝ => MvPolynomial.eval (fun k => (((sec i x s) k : ℝ) : ℂ)) q
              + MvPolynomial.eval (fun k => (((sec i x s) k : ℝ) : ℂ)) r := by
        funext s; simp
      rw [hfun, map_add, map_add]
      exact hq.add hr
  | mul_X q j hq =>
      have hcoord : HasDerivAt (fun s : ℝ => (((sec i x s) j : ℝ) : ℂ))
          (if j = i then (1 : ℂ) else 0) t := by
        by_cases h : j = i
        · have hfun2 : (fun s : ℝ => (((sec i x s) j : ℝ) : ℂ))
              = fun s : ℝ => ((s : ℝ) : ℂ) := by
            funext s; rw [hqDps_sec_apply, if_pos h]
          rw [hfun2, if_pos h]
          simpa using (hasDerivAt_id t).ofReal_comp
        · have hfun2 : (fun s : ℝ => (((sec i x s) j : ℝ) : ℂ))
              = fun _ : ℝ => (((x j) : ℝ) : ℂ) := by
            funext s; rw [hqDps_sec_apply, if_neg h]
          rw [hfun2, if_neg h]
          exact hasDerivAt_const t _
      have hfun : (fun s : ℝ => MvPolynomial.eval (fun k => (((sec i x s) k : ℝ) : ℂ)) (q * X j))
          = fun s : ℝ => MvPolynomial.eval (fun k => (((sec i x s) k : ℝ) : ℂ)) q
              * (((sec i x s) j : ℝ) : ℂ) := by
        funext s; simp
      rw [hfun]
      have hval : MvPolynomial.eval (fun k => (((sec i x t) k : ℝ) : ℂ)) (pderiv i (q * X j))
          = MvPolynomial.eval (fun k => (((sec i x t) k : ℝ) : ℂ)) (pderiv i q)
              * (((sec i x t) j : ℝ) : ℂ)
            + MvPolynomial.eval (fun k => (((sec i x t) k : ℝ) : ℂ)) q
              * (if j = i then (1 : ℂ) else 0) := by
        rw [MvPolynomial.pderiv_mul]
        by_cases h : j = i
        · subst h
          simp [MvPolynomial.pderiv_X_self]
        · rw [if_neg h, MvPolynomial.pderiv_X_of_ne h]
          simp
      rw [hval]
      exact hq.mul hcoord

/-- Differentiating the Gaussian factor along the `i`-th coordinate line. -/
theorem hqDps_gaussD_hasDerivAt {d : ℕ} (i : Fin d) (x : Vd d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gaussD (sec i x s)) (-(t / 2) * gaussD (sec i x t)) t := by
  set N : ℝ := ∑ j ∈ Finset.univ.erase i, (x j) ^ 2 with hNdef
  have hnorm : ∀ s : ℝ, ‖sec i x s‖ ^ 2 = s ^ 2 + N := by
    intro s
    rw [EuclideanSpace.real_norm_sq_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    · rw [hqDps_sec_apply]; simp
    · rw [hNdef]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hqDps_sec_apply, if_neg (Finset.ne_of_mem_erase hj)]
  have hgt : ∀ s : ℝ, gaussD (sec i x s) = Real.exp (-(1 / 4 : ℝ) * (s ^ 2 + N)) := by
    intro s
    unfold gaussD
    rw [hnorm s]
    congr 1
    ring
  have hu : HasDerivAt (fun s : ℝ => -(1 / 4 : ℝ) * (s ^ 2 + N)) (-(t / 2)) t := by
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h2 := (h1.add_const N).const_mul (-(1 / 4 : ℝ))
    have h3 : -(1 / 4 : ℝ) * (2 * t) = -(t / 2) := by ring
    rw [h3] at h2
    exact h2
  have hfun : (fun s : ℝ => gaussD (sec i x s))
      = fun s : ℝ => Real.exp (-(1 / 4 : ℝ) * (s ^ 2 + N)) := funext hgt
  have hD : -(t / 2) * Real.exp (-(1 / 4 : ℝ) * (t ^ 2 + N))
      = Real.exp (-(1 / 4 : ℝ) * (t ^ 2 + N)) * -(t / 2) := by ring
  rw [hfun, hgt t, hD]
  exact hu.exp

theorem solution {d : ℕ} (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) (t : ℝ) :
    deriv (fun s : ℝ => pgFun p (sec i x s)) t = pgFun (dPoly i p) (sec i x t) := by
  have hE := hqDps_eval_hasDerivAt i x t p
  have hG := (hqDps_gaussD_hasDerivAt i x t).ofReal_comp
  have hfun : (fun s : ℝ => pgFun p (sec i x s))
      = fun s : ℝ => MvPolynomial.eval (fun k => (((sec i x s) k : ℝ) : ℂ)) p
          * ((gaussD (sec i x s) : ℝ) : ℂ) := by
    funext s; rw [pgFun]
  have hXi : MvPolynomial.eval (fun k => (((sec i x t) k : ℝ) : ℂ)) (X i) = ((t : ℝ) : ℂ) := by
    rw [MvPolynomial.eval_X]
    simp [hqDps_sec_apply]
  have hval : MvPolynomial.eval (fun k => (((sec i x t) k : ℝ) : ℂ)) (pderiv i p)
        * ((gaussD (sec i x t) : ℝ) : ℂ)
      + MvPolynomial.eval (fun k => (((sec i x t) k : ℝ) : ℂ)) p
        * ((-(t / 2) * gaussD (sec i x t) : ℝ) : ℂ)
      = pgFun (dPoly i p) (sec i x t) := by
    have hdP : dPoly i p = pderiv i p - (1 / 2 : ℂ) • (X i * p) := rfl
    rw [pgFun, hdP, map_sub, MvPolynomial.smul_eq_C_mul, map_mul, map_mul,
      MvPolynomial.eval_C, hXi]
    push_cast
    ring
  rw [hfun, ← hval]
  exact (hE.mul hG).deriv