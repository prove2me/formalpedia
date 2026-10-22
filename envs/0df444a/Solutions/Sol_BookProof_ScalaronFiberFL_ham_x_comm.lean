-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.ham_x_comm
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T05:25:22.459991+00:00
-- url     : https://prove2.me/submissions/e6ce1f35-e5d7-46ed-98b4-807db8112a40

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
import Theorems.Thm_BookProof_ScalaronEsa_ccEquiv_coe
import Theorems.Thm_BookProof_ScalaronEsa_mulCc_apply
import Theorems.Thm_BookProof_ScalaronEsa_opCc_apply
import Theorems.Thm_BookProof_ScalaronWallEsa_kinOpR_apply
import Definitions.Def_ChapterScalaronFiberFL
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


noncomputable def hxcX : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))

theorem hxc_tg : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth :=
  (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).hasTemperateGrowth

theorem hxcX_apply (a : 𝓢(ℝ, ℂ)) (x : ℝ) : hxcX a x = (x : ℂ) * a x := by
  simp [hxcX, SchwartzMap.smulLeftCLM_apply_apply hxc_tg]


theorem hxc_ibp (a b : 𝓢(ℝ, ℂ)) :
    (inner ℂ (a.toLp 2 (volume : Measure ℝ)) ((SchwartzMap.derivCLM ℂ ℂ b).toLp 2 (volume : Measure ℝ)) : ℂ)
      = -(inner ℂ ((SchwartzMap.derivCLM ℂ ℂ a).toLp 2 (volume : Measure ℝ)) (b.toLp 2 (volume : Measure ℝ)) : ℂ) := by
  rw [SchwartzMap.inner_toL2_toL2_eq _ _ volume, SchwartzMap.inner_toL2_toL2_eq _ _ volume]
  have := SchwartzMap.integral_bilinear_deriv_right_eq_neg_left a b
    ((ContinuousLinearMap.mul ℝ ℂ).comp (Complex.conjCLE : ℂ →L[ℝ] ℂ))
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.mul_apply',
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] at this
  simp only [SchwartzMap.derivCLM_apply, RCLike.inner_apply, conj_trivial]
  rw [show (fun x => deriv (⇑b) x * (starRingEnd ℂ) (a x)) = fun x => (starRingEnd ℂ) (a x) * deriv (⇑b) x from funext fun x => mul_comm _ _,
    show (fun x => b x * (starRingEnd ℂ) (deriv (⇑a) x)) = fun x => (starRingEnd ℂ) (deriv (⇑a) x) * b x from funext fun x => mul_comm _ _]
  exact this

theorem hxc_Xsym (a b : 𝓢(ℝ, ℂ)) :
    (inner ℂ ((hxcX a).toLp 2 (volume : Measure ℝ)) (b.toLp 2 (volume : Measure ℝ)) : ℂ)
      = inner ℂ (a.toLp 2 (volume : Measure ℝ)) ((hxcX b).toLp 2 (volume : Measure ℝ)) := by
  rw [SchwartzMap.inner_toL2_toL2_eq _ _ volume, SchwartzMap.inner_toL2_toL2_eq _ _ volume]
  congr 1; funext x
  simp only [hxcX_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem hxc_DX (a : 𝓢(ℝ, ℂ)) :
    SchwartzMap.derivCLM ℂ ℂ (hxcX a) = a + hxcX (SchwartzMap.derivCLM ℂ ℂ a) := by
  ext x
  simp only [SchwartzMap.derivCLM_apply, add_apply, hxcX_apply]
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) * a y) (1 * a x + (x : ℂ) * deriv a x) x :=
    (Complex.ofRealCLM.hasDerivAt (x := x)).mul (a.differentiableAt.hasDerivAt)
  have : (hxcX a : ℝ → ℂ) = fun y : ℝ => (y : ℂ) * a y := funext (hxcX_apply a)
  rw [this, h1.deriv]; simp

theorem solution (W : WallPot) (s : ℝ) (f g : ccSchwartz ℝ) :
    (starRingEnd ℂ) (inner ℂ (xCc (ccEquiv ℝ g)) (W.ham s (ccEquiv ℝ f)) : ℂ)
      - (inner ℂ (xCc (ccEquiv ℝ f)) (W.ham s (ccEquiv ℝ g)) : ℂ)
      = -2 * (inner ℂ ((ccEquiv ℝ f : ccDomain ℝ) : L2R) (derivL2 g) : ℂ) := by
  set F : 𝓢(ℝ, ℂ) := (f : 𝓢(ℝ, ℂ))
  set G : 𝓢(ℝ, ℂ) := (g : 𝓢(ℝ, ℂ))
  set D : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℂ ℂ with hD
  have hmx : ∀ h : ccSchwartz ℝ, mulCc (fun x : ℝ => x) contDiff_id h = hxcX (h : 𝓢(ℝ, ℂ)) := by
    intro h; ext x; rw [BookProof.ScalaronEsa.mulCc_apply, hxcX_apply]
  have hx : ∀ h : ccSchwartz ℝ, xCc (ccEquiv ℝ h) = (hxcX (h : 𝓢(ℝ, ℂ))).toLp 2 (volume : Measure ℝ) := by
    intro h; rw [xCc, BookProof.ScalaronEsa.opCc_apply, hmx]
  have hkin : ∀ h : ccSchwartz ℝ, kinCcR (ccEquiv ℝ h)
      = (-(D (D (h : 𝓢(ℝ, ℂ))))).toLp 2 (volume : Measure ℝ) := by
    intro h
    have e : (schwartzEquiv ℝ).symm
        (Submodule.inclusion (ccDomain_le_schwartzDomain (E := ℝ)) (ccEquiv ℝ h)) = (h : 𝓢(ℝ, ℂ)) := by
      apply (schwartzEquiv ℝ).injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [Submodule.coe_inclusion, BookProof.ScalaronEsa.ccEquiv_coe]
      rfl
    have e2 : kinOpR (h : 𝓢(ℝ, ℂ)) = -(D (D (h : 𝓢(ℝ, ℂ)))) := by
      ext x; rw [BookProof.ScalaronWallEsa.kinOpR_apply]; simp only [D, neg_apply, SchwartzMap.derivCLM_apply]
      congr 2
    simp only [kinCcR, opL2, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      ContinuousLinearMap.coe_coe, e, e2]
    rfl
  have hham : ∀ h : ccSchwartz ℝ, W.ham s (ccEquiv ℝ h)
      = (-(D (D (h : 𝓢(ℝ, ℂ))))).toLp 2 (volume : Measure ℝ)
        + (mulCc (W.pot s) (W.pot_smooth s) h).toLp 2 (volume : Measure ℝ) := by
    intro h
    change (kinCcR + opCc (W.pot s) (W.pot_smooth s)) (ccEquiv ℝ h) = _
    rw [LinearMap.add_apply, hkin, BookProof.ScalaronEsa.opCc_apply]
  have hpot : (inner ℂ ((mulCc (W.pot s) (W.pot_smooth s) f).toLp 2 (volume : Measure ℝ))
        ((hxcX G).toLp 2 (volume : Measure ℝ)) : ℂ)
      = inner ℂ ((hxcX F).toLp 2 (volume : Measure ℝ))
        ((mulCc (W.pot s) (W.pot_smooth s) g).toLp 2 (volume : Measure ℝ)) := by
    rw [SchwartzMap.inner_toL2_toL2_eq _ _ volume, SchwartzMap.inner_toL2_toL2_eq _ _ volume]
    congr 1; funext x
    simp only [hxcX_apply, BookProof.ScalaronEsa.mulCc_apply, RCLike.inner_apply, map_mul,
      Complex.conj_ofReal, F, G]
    ring
  have hTneg : ∀ a : 𝓢(ℝ, ℂ), (-a).toLp 2 (volume : Measure ℝ) = -(a.toLp 2 (volume : Measure ℝ)) :=
    fun a => map_neg (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)) a
  have hTadd : ∀ a b : 𝓢(ℝ, ℂ), (a + b).toLp 2 (volume : Measure ℝ)
      = a.toLp 2 (volume : Measure ℝ) + b.toLp 2 (volume : Measure ℝ) :=
    fun a b => map_add (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)) a b
  rw [hx, hx, hham, hham, ← inner_conj_symm, starRingEnd_self_apply, BookProof.ScalaronEsa.ccEquiv_coe]
  change _ = -2 * (inner ℂ (F.toLp 2 (volume : Measure ℝ)) ((D G).toLp 2 (volume : Measure ℝ)) : ℂ)
  rw [inner_add_left, inner_add_right, hpot, hTneg, hTneg, inner_neg_left, inner_neg_right]
  -- kinetic part
  have k1 := hxc_ibp (D F) (hxcX G)
  have k2 := hxc_ibp (hxcX F) (D G)
  rw [hxc_DX] at k1 k2
  rw [hTadd] at k1 k2
  rw [inner_add_right] at k1
  rw [inner_add_left] at k2
  have k3 := hxc_ibp F G
  have k4 := hxc_Xsym (D F) (D G)
  change -(inner ℂ ((D (D F)).toLp 2 volume) ((hxcX G).toLp 2 volume) : ℂ) + _
      - (-(inner ℂ ((hxcX F).toLp 2 volume) ((D (D G)).toLp 2 volume) : ℂ) + _) = _
  have k1' : (inner ℂ ((D (D F)).toLp 2 (volume : Measure ℝ)) ((hxcX G).toLp 2 (volume : Measure ℝ)) : ℂ)
      = -(inner ℂ ((D F).toLp 2 (volume : Measure ℝ)) (G.toLp 2 (volume : Measure ℝ))
         + inner ℂ ((D F).toLp 2 (volume : Measure ℝ)) ((hxcX (D G)).toLp 2 (volume : Measure ℝ))) := by
    rw [k1]; ring
  rw [k1', k2]
  rw [k3, ← k4]
  ring
