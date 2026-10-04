-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.hasDerivAt_pgFun_sec
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T12:34:49.218443+00:00
-- url     : https://prove2.me/submissions/e2939570-83a6-43a2-a203-844d95768698

import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteProductCore

set_option autoImplicit false

open BookProof.HermiteProductCore BookProof.NavierStokesFlow.DifferentialL2 in
theorem norm_sq_sec_aux_bac9 {d : ℕ} (i : Fin d) (x : Vd d) (t : ℝ) :
    ‖sec i x t‖ ^ 2 = (∑ j ∈ Finset.univ.erase i, (x j) ^ 2) + t ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [sec, Function.update_of_ne hji]
  · simp [sec]

open BookProof.HermiteProductCore BookProof.NavierStokesFlow.DifferentialL2 in
theorem gauss_deriv_bac9 {d : ℕ} (i : Fin d) (x : Vd d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gaussD (sec i x s)) (-(t / 2) * gaussD (sec i x t)) t := by
  have key : (fun s : ℝ => gaussD (sec i x s)) =
      fun s => Real.exp (-((∑ j ∈ Finset.univ.erase i, (x j) ^ 2) + s ^ 2) / 4) := by
    funext s
    show Real.exp (-‖sec i x s‖ ^ 2 / 4) = _
    rw [norm_sq_sec_aux_bac9]
  rw [key]
  have h := (((hasDerivAt_pow 2 t).const_add
    (∑ j ∈ Finset.univ.erase i, (x j) ^ 2)).neg.div_const 4).exp
  convert h using 1
  show -(t / 2) * Real.exp (-‖sec i x t‖ ^ 2 / 4) = _
  rw [norm_sq_sec_aux_bac9]
  norm_num
  ring
  rfl

open BookProof.HermiteProductCore BookProof.NavierStokesFlow.DifferentialL2 in
theorem sec_self_bac9 {d : ℕ} (i : Fin d) (x : Vd d) : sec i x (x i) = x := by
  ext j
  by_cases h : j = i
  · subst h; simp [sec]
  · simp [sec]

open BookProof.HermiteProductCore BookProof.NavierStokesFlow.DifferentialL2 in
theorem coord_deriv_bac9 {d : ℕ} (i j : Fin d) (x : Vd d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (((sec i x s) j : ℝ) : ℂ)) (if j = i then 1 else 0 : ℂ) t := by
  by_cases h : j = i
  · subst h
    have e : (fun s : ℝ => (((sec j x s) j : ℝ) : ℂ)) = fun s : ℝ => (s : ℂ) := by
      funext s; simp [sec]
    rw [e, if_pos rfl]
    simpa using (hasDerivAt_id t).ofReal_comp
  · have e : (fun s : ℝ => (((sec i x s) j : ℝ) : ℂ)) = fun _ : ℝ => ((x j : ℝ) : ℂ) := by
      funext s; simp [sec, h]
    rw [e, if_neg h]
    exact hasDerivAt_const t _

open BookProof.HermiteProductCore BookProof.NavierStokesFlow.DifferentialL2 MvPolynomial in
theorem poly_deriv_bac9 {d : ℕ} (i : Fin d) (x : Vd d) (t : ℝ) (p : MvPolynomial (Fin d) ℂ) :
    HasDerivAt (fun s : ℝ => MvPolynomial.eval (fun j => (((sec i x s) j : ℝ) : ℂ)) p)
      (MvPolynomial.eval (fun j => (((sec i x t) j : ℝ) : ℂ)) (pderiv i p)) t := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t a
  | add p q hp hq =>
    have h := hp.add hq
    refine HasDerivAt.congr_deriv (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)) ?_
    · simp
    · simp
  | mul_X p j hp =>
    have hc := coord_deriv_bac9 i j x t
    have h := hp.mul hc
    refine HasDerivAt.congr_deriv (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)) ?_
    · simp
    · rw [Derivation.leibniz, pderiv_X]
      by_cases hji : j = i
      · subst hji
        simp only [Pi.single_eq_same, smul_eq_mul, map_add, map_mul, eval_X, ite_true, mul_one]
        ring
      · simp only [Pi.single_apply, hji, if_false, smul_eq_mul, map_add, map_mul, eval_X,
          map_zero]
        ring

open BookProof.HermiteProductCore BookProof.NavierStokesFlow.DifferentialL2 MeasureTheory MvPolynomial BookProof.HermiteProductBasis BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato BookProof.FarisLavine BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.LagrangianEsa in
theorem solution {d : ℕ} (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    HasDerivAt (fun t : ℝ => pgFun p (sec i x t))
      (pgFun (pderiv i p - (1/2 : ℂ) • (X i * p)) x) (x i) := by
  have hp := poly_deriv_bac9 i x (x i) p
  have hg := (gauss_deriv_bac9 i x (x i)).ofReal_comp
  have h := hp.mul hg
  rw [sec_self_bac9] at h
  refine h.congr_deriv ?_
  simp only [pgFun, map_sub, MvPolynomial.smul_eval, map_mul, eval_X]
  push_cast
  ring
