-- Prove2me | solution 1 for BookProof.QgHermiteFriedrichs.hamCore_quadForm_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:23:46.600971+00:00
-- url     : https://prove2.me/submissions/9eaded5b-c417-4713-8ca5-a444dae328ec

-- Generated from ChapterQgHermiteFriedrichs.lean — solution of BookProof.QgHermiteFriedrichs.hamCore_quadForm_ge
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Theorems.Thm_BookProof_QgHermiteFriedrichs_inner_pgLp_pgLp
import Theorems.Thm_BookProof_QgHermiteFriedrichs_hamCore_pgLp
import Theorems.Thm_BookProof_QgHermiteFriedrichs_conj_mul_self
import Theorems.Thm_BookProof_QgHermiteFriedrichs_inner_pgLp_potLp
import Theorems.Thm_BookProof_QgHermiteFriedrichs_re_gaussInt_kinPoly_self
import Theorems.Thm_BookProof_QgHermiteFriedrichs_norm_sq_pgLp
import Theorems.Thm_BookProof_QgHermiteFriedrichs_integrable_potential_normSq
import Theorems.Thm_BookProof_QgHermiteCore_ExpBounded_const_mul
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavine
open BookProof.QgHermiteFriedrichs








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}































variable (W : Vd d → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (hWc : Continuous W) (hWb : ExpBounded W) (c : ℝ)
    (hlb : ∀ x, -c ≤ W x) (x : (polyGaussCore (d := d))) :
    -c * ‖(x : L2d d)‖ ^ 2 ≤ quadForm (hamCore W hWc hWb) x := by

  obtain ⟨p, hp⟩ := x.2
  have hx : x = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  subst hx
  -- the potential part, as a real integral
  have hpot : (inner ℂ (pgLp p) (potLp W hWc hWb p) : ℂ)
      = ((∫ y : Vd d, W y * ‖pgFun p y‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_pgLp_potLp, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hy : (starRingEnd ℂ) (pgFun p y) * (((W y : ℝ) : ℂ) * pgFun p y)
        = ((W y : ℝ) : ℂ) * ((starRingEnd ℂ) (pgFun p y) * pgFun p y) := by ring
    change (starRingEnd ℂ) (pgFun p y) * (((W y : ℝ) : ℂ) * pgFun p y)
        = ((W y * ‖pgFun p y‖ ^ 2 : ℝ) : ℂ)
    rw [hy, conj_mul_self]
    push_cast
    ring
  have hint : Integrable (fun y : Vd d => W y * ‖pgFun p y‖ ^ 2) (volume : Measure (Vd d)) :=
    integrable_potential_normSq W hWc hWb p
  have hint2 : Integrable (fun y : Vd d => -c * ‖pgFun p y‖ ^ 2) (volume : Measure (Vd d)) := by
    have h1 : MemLp (fun y : Vd d => ‖pgFun p y‖) 2 (volume : Measure (Vd d)) :=
      (memLp_pgFun p).norm
    have h2 := h1.integrable_mul h1
    refine (h2.const_mul (-c)).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.mul_apply]
    ring
  have hmono : ∫ y : Vd d, -c * ‖pgFun p y‖ ^ 2 ≤ ∫ y : Vd d, W y * ‖pgFun p y‖ ^ 2 := by
    refine integral_mono hint2 hint fun y => ?_
    have := hlb y
    nlinarith [sq_nonneg ‖pgFun p y‖]
  have hconst : ∫ y : Vd d, -c * ‖pgFun p y‖ ^ 2 = -c * ‖pgLp p‖ ^ 2 := by
    rw [integral_const_mul, ← norm_sq_pgLp]
  -- assemble
  have hquad : quadForm (hamCore W hWc hWb) ⟨pgLp p, pgLp_mem_core p⟩
      = (∑ j : Fin d, ‖pgLp (coreD j p)‖ ^ 2) + ∫ y : Vd d, W y * ‖pgFun p y‖ ^ 2 := by
    simp only [quadForm, hamCore_pgLp, hamPoly, inner_add_right, Complex.add_re]
    rw [inner_pgLp_pgLp, re_gaussInt_kinPoly_self, hpot, Complex.ofReal_re]
  rw [hquad]
  have hkin : 0 ≤ ∑ j : Fin d, ‖pgLp (coreD j p)‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => by positivity
  have hnorm : ‖((⟨pgLp p, pgLp_mem_core p⟩ : (polyGaussCore (d := d))) : L2d d)‖ = ‖pgLp p‖ := rfl
  rw [hnorm]
  linarith [hconst ▸ hmono]
