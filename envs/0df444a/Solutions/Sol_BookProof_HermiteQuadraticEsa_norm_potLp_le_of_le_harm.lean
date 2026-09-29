-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.norm_potLp_le_of_le_harm
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:18:16.145357+00:00
-- url     : https://prove2.me/submissions/82afd658-de6d-471f-bdb6-81516a63f7a5

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.norm_potLp_le_of_le_harm
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem setupPotLp_coeFn (W : Vd d → ℝ) (hWc : Continuous W) (hWb : ExpBounded W) (p : MvPolynomial (Fin d) ℂ) :
    (potLp W hWc hWb p : Vd d → ℂ) =ᵐ[volume] fun x => ((W x : ℝ) : ℂ) * pgFun p x :=
  (memLp_mul_pgFun_of_expBounded hWc hWb p).coeFn_toLp

theorem setupEval_harmPoly (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (harmPoly (d := d)) = ((harmW x : ℝ) : ℂ) := by
  have hnorm : ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := norm_sq_eq_sum x
  unfold harmPoly harmW
  rw [map_sum, hnorm]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp
  ring

theorem solution {V : Vd d → ℝ} (hVc : Continuous V) (hVb : ExpBounded V)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hV : ∀ x, |V x| ≤ a * harmW x + b)
    (p : MvPolynomial (Fin d) ℂ) :
    ‖potLp V hVc hVb p‖ ≤ a * ‖pgLp (harmPoly * p)‖ + b * ‖pgLp p‖ := by
  have hstep : ‖potLp V hVc hVb p‖
      ≤ ‖((a : ℝ) : ℂ) • pgLp (harmPoly * p) + ((b : ℝ) : ℂ) • pgLp p‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [setupPotLp_coeFn V hVc hVb p,
      Lp.coeFn_add (((a : ℝ) : ℂ) • pgLp (harmPoly * p)) (((b : ℝ) : ℂ) • pgLp p),
      Lp.coeFn_smul ((a : ℝ) : ℂ) (pgLp (harmPoly * p)),
      Lp.coeFn_smul ((b : ℝ) : ℂ) (pgLp p),
      pgLp_coeFn (harmPoly * p), pgLp_coeFn p] with x h1 h2 h3 h4 h5 h6
    have hfun : pgFun (harmPoly * p) x = ((harmW x : ℝ) : ℂ) * pgFun p x := by
      simp only [pgFun, map_mul, setupEval_harmPoly]
      ring
    rw [h1, h2, Pi.add_apply, h3, h4, Pi.smul_apply, Pi.smul_apply, h5, h6, hfun,
      smul_eq_mul, smul_eq_mul]
    have hrw : ((a : ℝ) : ℂ) * (((harmW x : ℝ) : ℂ) * pgFun p x) + ((b : ℝ) : ℂ) * pgFun p x
        = ((a * harmW x + b : ℝ) : ℂ) * pgFun p x := by
      push_cast
      ring
    rw [hrw, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hpos : 0 ≤ a * harmW x + b := by
      have : 0 ≤ harmW x := by unfold harmW; positivity
      positivity
    rw [abs_of_nonneg hpos]
    exact hV x
  refine hstep.trans ((norm_add_le _ _).trans ?_)
  rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]

#print axioms solution
