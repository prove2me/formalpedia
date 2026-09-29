-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOf.ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/85a3d20a-e561-5bfd-92d8-f77ec93846bd

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOf_ne_zero

set_option autoImplicit false

noncomputable section

namespace AdelicLiftNonvanishingAux

section Arch

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open scoped MatrixGroups ModularForm UpperHalfPlane

private theorem isReal_rat_infinitePlace (v : InfinitePlace ℚ) : v.IsReal := IsTotallyReal.isReal v

private def ratArchHom : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom).comp
    ((archComponent ℚ default).comp (glArch (𝓞 ℚ) ℚ))

private theorem ratArchHom_apply (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ratArchHom g = LanglandsTunnell.ratArchGL2 g := rfl

private theorem ratArch_mul (g g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (g * g') = LanglandsTunnell.ratArchGL2 g * LanglandsTunnell.ratArchGL2 g' := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, ← ratArchHom_apply, map_mul]

private theorem ratArch_eq_one_of_glArch_eq_one {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    LanglandsTunnell.ratArchGL2 u = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [hu, map_one, map_one]

private theorem ratArch_finEmbed (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (AdelicDock.finEmbed (𝓞 ℚ) ℚ u) = 1 :=
  ratArch_eq_one_of_glArch_eq_one (AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ u)

private theorem ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ) = GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom.comp
      ((archEval ℚ default).comp ((adeleArch (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))))
      ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = (Rat.castHom ℝ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j)
  rw [eq_ratCast, eq_ratCast]

private theorem dense_ratPoints :
    Dense (((↑) : ℍ → ℂ) ⁻¹' {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)}) := by
  have h1 : Dense (Set.range ((↑) : ℚ → ℝ) ×ˢ Set.range ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.prod Rat.denseRange_cast
  have h2 : {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)} =
      Complex.equivRealProdCLM ⁻¹' (Set.range ((↑) : ℚ → ℝ) ×ˢ Set.range ((↑) : ℚ → ℝ)) := by
    ext w; simp [Set.mem_prod]
  have hS : Dense {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)} := by
    rw [h2]; exact h1.preimage Complex.equivRealProdCLM.toHomeomorph.isOpenMap
  exact hS.preimage UpperHalfPlane.isOpenEmbedding_coe.isOpenMap

private theorem lift_ne_zero {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg0 : g ≠ 0)
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφg : g.IsAdelicLiftOf φ) : φ ≠ 0 := by
  intro hφ
  apply hg0
  have hcont : Continuous (⇑g : ℍ → ℂ) := (CuspFormClass.holo g).continuous
  have hEq : Set.EqOn (⇑g : ℍ → ℂ) (fun _ => (0 : ℂ))
      (((↑) : ℍ → ℂ) ⁻¹' {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)}) := by
    rintro z ⟨⟨x, hx⟩, ⟨y, hy⟩⟩

    have hy0 : (0 : ℝ) < y := by rw [hy]; exact z.im_pos
    have hyq : (0 : ℚ) < y := by exact_mod_cast hy0

    let A : Matrix (Fin 2) (Fin 2) ℚ := !![y, x; 0, 1]
    have hdetA : A.det = y := by simp [A, Matrix.det_fin_two_of]
    let γ : GL (Fin 2) ℚ := GeneralLinearGroup.mkOfDetNeZero A (by rw [hdetA]; exact hyq.ne')
    let h : AdelicGL2 (𝓞 ℚ) ℚ :=
      globalPoints (𝓞 ℚ) ℚ γ * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ))⁻¹
    have hfin : glFin (𝓞 ℚ) ℚ h = 1 := by
      simp only [h, map_mul, AdelicDock.glFin_finEmbed, mul_inv_cancel]
    have hP : LanglandsTunnell.ratArchGL2 h = GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
      simp only [h, ratArch_mul, ratArch_finEmbed, mul_one, ratArch_globalPoints]
    have hPmat : ((LanglandsTunnell.ratArchGL2 h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![(y : ℝ), (x : ℝ); 0, 1] := by
      rw [hP]
      ext i j
      change (Rat.castHom ℝ) (A i j) = _
      fin_cases i <;> fin_cases j <;> simp [A]
    have hdetP : ((LanglandsTunnell.ratArchGL2 h).det.val : ℝ) = y := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hPmat, Matrix.det_fin_two_of]; ring
    have hdetpos : (0 : ℝ) < (LanglandsTunnell.ratArchGL2 h).det.val := by rw [hdetP]; exact hy0
    have hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ := by
      rw [Matrix.mem_glpos]; exact hdetpos

    have h3 := hφg.apply_eq h hfin hpos
    rw [hφ, Pi.zero_apply, ModularForm.slash_apply] at h3
    have hne1 : |((LanglandsTunnell.ratArchGL2 h).det.val : ℝ)| ^ ((2 : ℤ) - 1) ≠ 0 :=
      zpow_ne_zero _ (abs_ne_zero.mpr hdetpos.ne')
    have hne2 : UpperHalfPlane.denom (LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I ^ (-(2 : ℤ)) ≠ 0 :=
      zpow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ _)
    have hg1 : (⇑g : ℍ → ℂ) ((LanglandsTunnell.ratArchGL2 h) • UpperHalfPlane.I) = 0 := by
      have := h3.symm
      rw [mul_eq_zero, mul_eq_zero] at this
      rcases this with (h0 | h0) | h0
      · rw [← UpperHalfPlane.σ_sq (LanglandsTunnell.ratArchGL2 h) ((⇑g : ℍ → ℂ) _), h0, map_zero]
      · exact absurd (by exact_mod_cast h0) hne1
      · exact absurd h0 hne2

    have hpt : (LanglandsTunnell.ratArchGL2 h) • UpperHalfPlane.I = z := by
      rw [UpperHalfPlane.coe_re] at hx
      rw [UpperHalfPlane.coe_im] at hy
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_smul_of_det_pos hdetpos]
      simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hPmat, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, UpperHalfPlane.coe_I,
        Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_one, div_one]
      apply Complex.ext <;> simp [← hx, ← hy]
    rw [hpt] at hg1
    exact hg1
  have hfun : (⇑g : ℍ → ℂ) = fun _ => 0 := Continuous.ext_on dense_ratPoints hcont continuous_const hEq
  ext z
  exact congrFun hfun z

end Arch

end AdelicLiftNonvanishingAux

end

theorem solution
    {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hφ : g.IsAdelicLiftOf φ)
    (hg : g ≠ 0) : φ ≠ 0 :=
  AdelicLiftNonvanishingAux.lift_ne_zero hg hφ

end S_CuspForm_IsAdelicLiftOf_ne_zero
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOf_ne_zero (solution)
