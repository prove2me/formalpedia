-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.norm_sq_le_quadForm
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T05:21:35.281186+00:00
-- url     : https://prove2.me/submissions/bc413db8-a95a-4dca-8791-b0bb868f6750

import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterWallEsaSemibounded
import Definitions.Def_ChapterWallEsaBddBelow
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Theorems.Thm_BookProof_WallEsaSemibounded_opCc_quadratic_form
import Theorems.Thm_BookProof_WallEsaSemibounded_kinCcR_quadratic_form
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterScalaronCoreEsa
open BookProof.ScalaronEsa
open BookProof.ScalaronFiberFL



open MeasureTheory SchwartzMap
open BookProof.StrichartzWave
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallEsaSemibounded BookProof.WallEsaBddBelow
open BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.SchrodingerCutoff BookProof.FriedrichsExtension

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (W : WallPot) (s : ℝ)

theorem scal_opCc_add (V V' : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hV' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V') (u : ccDomain ℝ) :
    opCc (fun x => V x + V' x) (hV.add hV') u = opCc V hV u + opCc V' hV' u := by
  simp only [opCc, LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe, ← map_add]
  congr 1
  ext x
  change ((V x + V' x : ℝ) : ℂ) * _ = (V x : ℂ) * _ + (V' x : ℂ) * _
  push_cast; ring

theorem scal_opCc_one (f : ccSchwartz ℝ) :
    opCc (fun _ => (1 : ℝ)) contDiff_const (ccEquiv ℝ f) = ((ccEquiv ℝ f : ccDomain ℝ) : L2R) := by
  simp only [opCc, LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have : mulCc (fun _ => (1 : ℝ)) contDiff_const f = (f : 𝓢(ℝ, ℂ)) := by
    ext x
    change ((1 : ℝ) : ℂ) * _ = _
    simp
  rw [this]
  rfl

theorem solution (W : WallPot) (s : ℝ) (hs : 1 ≤ s) (f : ccSchwartz ℝ) :
    ‖((ccEquiv ℝ f : ccDomain ℝ) : L2R)‖ ^ 2 ≤ quadForm (W.ham s) (ccEquiv ℝ f) := by
  set u : L2R := ((ccEquiv ℝ f : ccDomain ℝ) : L2R) with hu
  have hsplit : W.pot s = fun x => (W.pot s x - 1) + 1 := by funext x; ring
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => W.pot s x - 1) :=
    (W.pot_smooth s).sub contDiff_const
  have hop : opCc (W.pot s) (W.pot_smooth s) (ccEquiv ℝ f)
      = opCc (fun x => W.pot s x - 1) hsm (ccEquiv ℝ f) + u := by
    have h1 := scal_opCc_one f
    rw [← hu] at h1
    rw [← h1, ← scal_opCc_add]
    have key : ∀ (V V' : ℝ → ℝ) (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
        (h' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V'), V = V' → opCc V h = opCc V' h' := by
      rintro V V' h h' rfl; rfl
    rw [key _ _ _ ((hsm.add contDiff_const)) hsplit]
  have hk := BookProof.WallEsaSemibounded.kinCcR_quadratic_form f
  have hp := BookProof.WallEsaSemibounded.opCc_quadratic_form (fun x => W.pot s x - 1) hsm f
  have hinner : (inner ℂ (W.ham s (ccEquiv ℝ f)) u : ℂ)
      = ((∫ x, ‖deriv ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ)
        + ((∫ x, (W.pot s x - 1) * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 : ℝ) : ℂ) + (inner ℂ u u : ℂ) := by
    change (inner ℂ ((kinCcR + opCc (W.pot s) (W.pot_smooth s)) (ccEquiv ℝ f)) u : ℂ) = _
    rw [LinearMap.add_apply, inner_add_left, hk, hop, inner_add_left, hp, add_assoc]
  have hq : quadForm (W.ham s) (ccEquiv ℝ f) = (inner ℂ (W.ham s (ccEquiv ℝ f)) u : ℂ).re := by
    rw [quadForm, ← inner_conj_symm, Complex.conj_re]
  have h1 : (0 : ℝ) ≤ ∫ x, ‖deriv ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun x => by positivity
  have h2 : (0 : ℝ) ≤ ∫ x, (W.pot s x - 1) * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 := by
    refine MeasureTheory.integral_nonneg fun x => mul_nonneg ?_ (by positivity)
    have := W.pot_nonneg s (by linarith) x
    have h3 : 0 ≤ x ^ 2 / 4 := by positivity
    have h4 := W.nonneg x
    simp only [WallPot.pot]
    linarith
  rw [hq, hinner]
  simp only [Complex.add_re, Complex.ofReal_re, inner_self_eq_norm_sq_to_K]
  have hre : 0 ≤ (((∫ x, ‖deriv ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ^ 2) + ∫ x, (W.pot s x - 1) * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 : ℝ)) := by linarith
  refine le_trans (le_of_eq ?_) (le_add_of_nonneg_left hre)
  norm_cast
