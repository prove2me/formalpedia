-- Prove2me | solution 1 for BookProof.ScalaronHermiteEsa.moments_of_deficiency
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:21:16.445821+00:00
-- url     : https://prove2.me/submissions/1e4388ef-2111-49bf-9eba-cbe5a548a139

-- Generated from ChapterScalaronHermiteEsa.lean — solution of BookProof.ScalaronHermiteEsa.moments_of_deficiency
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
import Theorems.Thm_BookProof_ScalaronHermiteEsa_integrable_pgFun_mul_of_gaussExpDecay
import Theorems.Thm_BookProof_ScalaronHermiteEsa_gaussExpDecay_mul_lp
import Theorems.Thm_BookProof_ScalaronHermiteEsa_moments_of_monomial_moments
import Theorems.Thm_BookProof_ScalaronHermiteEsa_gaussExpDecay_potential_sub
import Theorems.Thm_BookProof_QgHermiteFriedrichs_inner_L2_eq
import Theorems.Thm_BookProof_QgHermiteFriedrichs_potLp_coeFn
import Theorems.Thm_BookProof_QgHermiteOscillator_potCore_pgLp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
open BookProof.ScalaronHermiteEsa




open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {W : Vd d → ℝ} (hWc : Continuous W) (hWb : ExpBounded W)
    {z : ℂ} {w : L2d d}
    (hw : ∀ v : polyGaussCore (d := d),
      (inner ℂ (potCore W hWc hWb v) (w : L2d d) : ℂ) = z * inner ℂ (v : L2d d) (w : L2d d))
    (p : MvPolynomial (Fin d) ℂ) :
    ∫ x : Vd d, pgFun p x * ((((W x : ℝ) : ℂ) - z) * (w : Vd d → ℂ) x) = 0 := by

  obtain ⟨CW, cW, hcW, hWbd⟩ := id hWb
  have hWm : AEStronglyMeasurable (fun x : Vd d => ((W x : ℝ) : ℂ))
      (volume : Measure (Vd d)) :=
    (Complex.continuous_ofReal.comp hWc).aestronglyMeasurable
  have hA : GaussExpDecay (fun x : Vd d => ((W x : ℝ) : ℂ) * (w : Vd d → ℂ) x) :=
    gaussExpDecay_mul_lp hWm (fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hWbd x) w
  have hB : GaussExpDecay (fun x : Vd d => (-z) * (w : Vd d → ℂ) x) :=
    gaussExpDecay_mul_lp (C := ‖z‖) (c := 0) aestronglyMeasurable_const
      (fun x => by simp) w
  have hu := gaussExpDecay_potential_sub hWc hWb z w
  refine moments_of_monomial_moments hu (fun a => ?_) p
  -- the monomial case: read off the moment identity from the deficiency equation
  set q : MvPolynomial (Fin d) ℂ := monomial a (1 : ℂ) with hq
  have hdef := hw ⟨pgLp q, pgLp_mem_core q⟩
  rw [potCore_pgLp] at hdef
  have hlhs : (inner ℂ (potLp W hWc hWb q) (w : L2d d) : ℂ)
      = ∫ x : Vd d, pgFun q x * (((W x : ℝ) : ℂ) * (w : Vd d → ℂ) x) := by
    rw [inner_L2_eq]
    refine integral_congr_ae ?_
    filter_upwards [potLp_coeFn W hWc hWb q] with x hx
    rw [hx, map_mul, Complex.conj_ofReal, conj_pgFun_monomial_one]
    ring
  have hrhs : (inner ℂ ((⟨pgLp q, pgLp_mem_core q⟩ : polyGaussCore (d := d)) : L2d d)
      (w : L2d d) : ℂ) = ∫ x : Vd d, pgFun q x * (w : Vd d → ℂ) x := by
    rw [inner_pgLp]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hq, conj_pgFun_monomial_one]
  rw [hlhs, hrhs] at hdef
  have hsplit : ∀ x : Vd d, pgFun q x * ((((W x : ℝ) : ℂ) - z) * (w : Vd d → ℂ) x)
      = pgFun q x * (((W x : ℝ) : ℂ) * (w : Vd d → ℂ) x)
        + pgFun q x * ((-z) * (w : Vd d → ℂ) x) := by
    intro x; ring
  simp_rw [hsplit]
  rw [integral_add (integrable_pgFun_mul_of_gaussExpDecay hA q)
    (integrable_pgFun_mul_of_gaussExpDecay hB q)]
  have hlast : ∫ x : Vd d, pgFun q x * ((-z) * (w : Vd d → ℂ) x)
      = -z * ∫ x : Vd d, pgFun q x * (w : Vd d → ℂ) x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hlast, hdef]
  ring
