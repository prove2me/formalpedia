-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOfGamma1.contDiff_two_unipotentGL2_ratArchLine_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c0920c60-e228-5c0b-8c21-90527e21f74a

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicTraceProducer
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOfGamma1_contDiff_two_unipotentGL2_ratArchLine_mul

set_option autoImplicit false

open IsDedekindDomain NumberField
open NumberField.AdelicBox NumberField.StandardAddChar AutomorphicForm

noncomputable section

namespace CuspForm
p2m_export "CuspForm" "ext IsAdelicLiftOfGamma1"
namespace IsAdelicLiftOfGamma1
namespace ArchLine
p2m_open "CuspForm.IsAdelicLiftOfGamma1 CuspForm"

open NumberField.AdelicLevel Matrix LanglandsTunnell
open scoped MatrixGroups ModularForm UpperHalfPlane Manifold

theorem isReal_default : (default : InfinitePlace ℚ).IsReal := IsTotallyReal.isReal _

def ratArchHom : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal isReal_default).toRingHom).comp
    ((archComponent ℚ default).comp (glArch (𝓞 ℚ) ℚ))

theorem ratArchHom_apply (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : ratArchHom g = ratArchGL2 g := rfl

theorem ratArch_mul (g g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ratArchGL2 (g * g') = ratArchGL2 g * ratArchGL2 g' := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, ← ratArchHom_apply, map_mul]

theorem ratArch_inv (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : ratArchGL2 g⁻¹ = (ratArchGL2 g)⁻¹ := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, map_inv]

theorem ratArch_finEmbed (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ratArchGL2 (AdelicDock.finEmbed (𝓞 ℚ) ℚ u) = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [AdelicDock.glArch_finEmbed, map_one, map_one]

theorem glFin_unipotentGL2_ratArchLine (t : ℝ) :
    glFin (𝓞 ℚ) ℚ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0)) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glFin_apply, unipotentGL2_coe, Units.val_one]
  fin_cases i <;> fin_cases j <;> rfl

theorem ratArch_unipotentGL2_ratArchLine (t : ℝ) :
    ratArchGL2 (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0)) = unipotentGL2 t := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).toRingHom
      (((((unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0)) : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 default) = ((unipotentGL2 t : GL (Fin 2) ℝ) : Matrix _ _ ℝ) i j
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j
  · show _ = (1 : ℝ)
    exact map_one _
  · show (InfinitePlace.Completion.ringEquivRealOfIsReal _).toRingHom (ratArchLine t default) = t
    rw [ratArchLine_apply]
    exact RingEquiv.apply_symm_apply _ t
  · show _ = (0 : ℝ)
    exact map_zero _
  · show _ = (1 : ℝ)
    exact map_one _

theorem det_unipotentGL2 (t : ℝ) : Matrix.GeneralLinearGroup.det (unipotentGL2 t) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of, Units.val_one]
  ring

theorem contDiff_slash_two_apply_I (f : ℍ → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (A B : GL (Fin 2) ℝ) (hpos : 0 < A.det.val * B.det.val) :
    ContDiff ℝ 2 (fun t : ℝ => (f ∣[(2 : ℤ)] (A * unipotentGL2 t * B)) UpperHalfPlane.I) := by
  set g : ℝ → GL (Fin 2) ℝ := fun t => A * unipotentGL2 t * B with hg
  have hdet : ∀ t, (g t).det.val = A.det.val * B.det.val := by
    intro t
    simp only [hg, map_mul, det_unipotentGL2, mul_one, Units.val_mul]
  have hdetpos : ∀ t, 0 < (g t).det.val := fun t => by rw [hdet]; exact hpos

  have hent : ∀ i j, ContDiff ℝ 2 (fun t => ((g t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
    intro i j
    simp only [hg, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hentC : ∀ i j, ContDiff ℝ 2 (fun t => ((((g t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j : ℝ) : ℂ)) :=
    fun i j => Complex.ofRealCLM.contDiff.comp (hent i j)

  have hden : ContDiff ℝ 2 (fun t => UpperHalfPlane.denom (g t) UpperHalfPlane.I) := by
    show ContDiff ℝ 2 (fun t => ((((g t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * UpperHalfPlane.I +
      ((((g t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℝ) : ℂ))
    exact ((hentC 1 0).mul contDiff_const).add (hentC 1 1)
  have hnum : ContDiff ℝ 2 (fun t => UpperHalfPlane.num (g t) UpperHalfPlane.I) := by
    show ContDiff ℝ 2 (fun t => ((((g t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) : ℂ) * UpperHalfPlane.I +
      ((((g t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) : ℂ))
    exact ((hentC 0 0).mul contDiff_const).add (hentC 0 1)
  have hden0 : ∀ t, UpperHalfPlane.denom (g t) UpperHalfPlane.I ≠ 0 := fun t =>
    UpperHalfPlane.denom_ne_zero (g t) UpperHalfPlane.I

  have horb : ContDiff ℝ 2 (fun t => ((g t • UpperHalfPlane.I : ℍ) : ℂ)) := by
    have heq : (fun t => ((g t • UpperHalfPlane.I : ℍ) : ℂ)) =
        fun t => UpperHalfPlane.num (g t) UpperHalfPlane.I * (UpperHalfPlane.denom (g t) UpperHalfPlane.I)⁻¹ :=
      funext fun t => by rw [UpperHalfPlane.coe_smul_of_det_pos (hdetpos t), div_eq_mul_inv]
    rw [heq]
    exact hnum.mul (hden.inv hden0)

  have hF : ContDiffOn ℝ 2 (f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} := by
    have hd : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
      UpperHalfPlane.mdifferentiable_iff.mp hf
    exact (hd.contDiffOn (isOpen_lt continuous_const Complex.continuous_im)).restrict_scalars ℝ
  have hcomp : ContDiff ℝ 2 (fun t => f (g t • UpperHalfPlane.I)) := by
    have heq : (fun t => f (g t • UpperHalfPlane.I)) =
        (f ∘ UpperHalfPlane.ofComplex) ∘ (fun t => ((g t • UpperHalfPlane.I : ℍ) : ℂ)) := by
      funext t
      simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply]
    rw [heq]
    exact hF.comp_contDiff horb (fun t => (g t • UpperHalfPlane.I).im_pos)

  have hslash : (fun t : ℝ => (f ∣[(2 : ℤ)] (A * unipotentGL2 t * B)) UpperHalfPlane.I) =
      fun t => f (g t • UpperHalfPlane.I) * ((|A.det.val * B.det.val| : ℝ) : ℂ) ^ ((2 : ℤ) - 1) *
        ((UpperHalfPlane.denom (g t) UpperHalfPlane.I)⁻¹) ^ 2 := by
    funext t
    show (f ∣[(2 : ℤ)] (g t)) UpperHalfPlane.I = _
    rw [ModularForm.slash_apply, UpperHalfPlane.σ, if_pos (hdetpos t), hdet t, _root_.zpow_neg, ← _root_.inv_zpow, zpow_ofNat]
    rfl
  rw [hslash]
  exact (hcomp.mul contDiff_const).mul ((hden.inv hden0).pow 2)

end CuspForm.IsAdelicLiftOfGamma1.ArchLine

end

open NumberField.AdelicLevel Matrix LanglandsTunnell CuspForm.IsAdelicLiftOfGamma1.ArchLine in
open scoped MatrixGroups ModularForm in

theorem solution
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ContDiff ℝ 2 (fun t : ℝ => Φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) * g)) := by

  have hN : AdelicDock.ratLevel M ≠ ⊥ := by
    rw [AdelicDock.ratLevel, ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast NeZero.ne M
  obtain ⟨γ, hy, hpos⟩ := NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat hN g
  set G : AdelicGL2 (𝓞 ℚ) ℚ := globalPoints (𝓞 ℚ) ℚ γ with hG
  set y : AdelicGL2 (𝓞 ℚ) ℚ := G * g with hy_def
  have hposY : ratArchGL2 y ∈ Matrix.GLPos (Fin 2) ℝ := hpos default (IsTotallyReal.isReal _)
  have hgy : g = G⁻¹ * y := by rw [hy_def, inv_mul_cancel_left]

  have key : ∀ t : ℝ, Φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) * g) =
      ((⇑h) ∣[(2 : ℤ)] (ratArchGL2 G * unipotentGL2 t * (ratArchGL2 G⁻¹ * ratArchGL2 y))) UpperHalfPlane.I := by
    intro t
    set n : AdelicGL2 (𝓞 ℚ) ℚ := unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) with hn
    set z : AdelicGL2 (𝓞 ℚ) ℚ := G * n * G⁻¹ * y with hz
    have h1 : n * g = globalPoints (𝓞 ℚ) ℚ γ⁻¹ * z := by
      rw [hgy, hz, map_inv, ← hG]; group

    set k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) := glFin (𝓞 ℚ) ℚ z with hk
    set x : AdelicGL2 (𝓞 ℚ) ℚ := z * (AdelicDock.finEmbed (𝓞 ℚ) ℚ k)⁻¹ with hx
    have hzx : z = x * AdelicDock.finEmbed (𝓞 ℚ) ℚ k := by rw [hx, inv_mul_cancel_right]
    have hkmem : k ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) := by
      have hky : k = glFin (𝓞 ℚ) ℚ y := by
        rw [hk, hz, map_mul, map_mul, map_mul, map_inv, hn, glFin_unipotentGL2_ratArchLine, mul_one,
          mul_inv_cancel, one_mul]
      rw [hky]; exact hy
    have hxfin : glFin (𝓞 ℚ) ℚ x = 1 := by
      rw [hx, map_mul, map_inv, AdelicDock.glFin_finEmbed, ← hk, mul_inv_cancel]
    have hxarch : ratArchGL2 x = ratArchGL2 G * unipotentGL2 t * (ratArchGL2 G⁻¹ * ratArchGL2 y) := by
      rw [hx, ratArch_mul, ratArch_inv, ratArch_finEmbed, inv_one, mul_one, hz, ratArch_mul, ratArch_mul,
        ratArch_mul, hn, ratArch_unipotentGL2_ratArchLine, mul_assoc]
    have hxpos : ratArchGL2 x ∈ Matrix.GLPos (Fin 2) ℝ := by
      rw [Matrix.mem_glpos] at hposY ⊢
      rw [hxarch, map_mul, map_mul, map_mul, det_unipotentGL2, mul_one, ratArch_inv, map_inv,
        Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, mul_inv_cancel_left₀ (Units.ne_zero _)]
      exact hposY
    calc Φ (n * g) = Φ (globalPoints (𝓞 ℚ) ℚ γ⁻¹ * z) := by rw [h1]
      _ = Φ z := hΦ.1 γ⁻¹ z
      _ = Φ (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ k) := by rw [← hzx]
      _ = Φ x := hΦ.2.1 k hkmem x
      _ = ((⇑h) ∣[(2 : ℤ)] ratArchGL2 x) UpperHalfPlane.I := hΦ.2.2 x hxfin hxpos
      _ = _ := by rw [hxarch]

  have hdetpos : 0 < (ratArchGL2 G).det.val * (ratArchGL2 G⁻¹ * ratArchGL2 y).det.val := by
    rw [Matrix.mem_glpos] at hposY
    rw [map_mul, ratArch_inv, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      mul_inv_cancel_left₀ (Units.ne_zero _)]
    exact hposY
  have hsmooth := contDiff_slash_two_apply_I (⇑h) (CuspFormClass.holo h) (ratArchGL2 G)
    (ratArchGL2 G⁻¹ * ratArchGL2 y) hdetpos
  rw [show (fun t : ℝ => Φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) * g)) =
      fun t : ℝ => ((⇑h) ∣[(2 : ℤ)] (ratArchGL2 G * unipotentGL2 t * (ratArchGL2 G⁻¹ * ratArchGL2 y))) UpperHalfPlane.I
    from funext key]
  exact hsmooth

end S_CuspForm_IsAdelicLiftOfGamma1_contDiff_two_unipotentGL2_ratArchLine_mul
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOfGamma1_contDiff_two_unipotentGL2_ratArchLine_mul (solution)
