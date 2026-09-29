-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOfGamma1.apply_centralScalar_mul_eq_of_forall_snd_eq_one_of_archCoord_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/37636a82-7c03-5a98-8eba-a1eeeee9e8d7

import Mathlib
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOfGamma1_apply_centralScalar_mul_eq_of_forall_snd_eq_one_of_archCoord_pos

set_option autoImplicit false

open NumberField AutomorphicForm
open NumberField.AdelicLevel AdelicDock IsDedekindDomain

namespace K2ArchScalar

noncomputable section

theorem glpair_ext {g h : AdelicGL2 (𝓞 ℚ) ℚ}
    (ha : glArch (𝓞 ℚ) ℚ g = glArch (𝓞 ℚ) ℚ h)
    (hf : glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ h) : g = h := by
  ext i j
  refine Prod.ext ?_ ?_
  · exact congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing ℚ) =>
      (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j) ha
  · exact congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) hf

theorem finEmbed_glFin_of_glArch_eq_one {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : glArch (𝓞 ℚ) ℚ g = 1) :
    finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ g) = g :=
  glpair_ext (by rw [glArch_finEmbed, hg]) (by rw [glFin_finEmbed])

theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    centralScalar (𝓞 ℚ) ℚ z * g = g * centralScalar (𝓞 ℚ) ℚ z := by
  ext : 1
  rw [Units.val_mul, Units.val_mul]
  exact Matrix.scalar_commute (z : AdeleRing (𝓞 ℚ) ℚ) (fun r' => mul_comm _ _)
    ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))

theorem ratArchGL2_mul (g h : AdelicGL2 (𝓞 ℚ) ℚ) :
    LanglandsTunnell.ratArchGL2 (g * h) = LanglandsTunnell.ratArchGL2 g * LanglandsTunnell.ratArchGL2 h := by
  simp only [LanglandsTunnell.ratArchGL2, map_mul]

theorem ratArchGL2_eq_one_of_glArch {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : glArch (𝓞 ℚ) ℚ g = 1) :
    LanglandsTunnell.ratArchGL2 g = 1 := by
  simp only [LanglandsTunnell.ratArchGL2, hg, map_one]

theorem ratArchGL2_inv (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    LanglandsTunnell.ratArchGL2 g⁻¹ = (LanglandsTunnell.ratArchGL2 g)⁻¹ := by
  simp only [LanglandsTunnell.ratArchGL2, map_inv]

theorem glFin_centralScalar_eq_one (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hz : ∀ v : HeightOneSpectrum (𝓞 ℚ), (z : AdeleRing (𝓞 ℚ) ℚ).2 v = 1) :
    glFin (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ z) = 1 := by
  have hz2 : (z : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := by
    refine Subtype.ext (funext fun v => ?_)
    exact hz v
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glFin_apply, Units.val_one]
  show (Matrix.diagonal (fun _ => (z : AdeleRing (𝓞 ℚ) ℚ)) i j).2 = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
  by_cases h : i = j
  · subst h; rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, hz2]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]; rfl

theorem coe_ratArchGL2_centralScalar (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (LanglandsTunnell.ratArchGL2 (centralScalar (𝓞 ℚ) ℚ z) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![RatIdele.archCoord z, 0; 0, RatIdele.archCoord z] := by
  ext i j
  have hw : (default : InfinitePlace ℚ) = Rat.infinitePlace := Subsingleton.elim _ _
  show (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).toRingHom
      ((archComponent ℚ default (glArch (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ z)) : Matrix _ _ _) i j) = _
  rw [archComponent_apply, glArch_apply]
  show (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).toRingHom
      ((Matrix.diagonal (fun _ => (z : AdeleRing (𝓞 ℚ) ℚ)) i j).1 default) = _
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq]
    fin_cases i <;>
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.empty_val', RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      unfold RatIdele.archCoord
      congr 1 <;> first | exact hw ▸ rfl | (subst hw; rfl)
  · rw [Matrix.diagonal_apply_ne _ h, show ((0 : AdeleRing (𝓞 ℚ) ℚ).1 (default : InfinitePlace ℚ)) = 0 from rfl, map_zero]
    fin_cases i <;> fin_cases j <;> simp_all

theorem det_ratArchGL2_centralScalar (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((LanglandsTunnell.ratArchGL2 (centralScalar (𝓞 ℚ) ℚ z) : Matrix (Fin 2) (Fin 2) ℝ)).det
      = RatIdele.archCoord z ^ 2 := by
  rw [coe_ratArchGL2_centralScalar, Matrix.det_fin_two_of]; ring

open scoped ModularForm in

theorem slash_scalar_eq {M : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2) (S : GL (Fin 2) ℝ) (t : ℝ)
    (ht : 0 < t) (hS : (S : Matrix (Fin 2) (Fin 2) ℝ) = !![t, 0; 0, t]) :
    ((⇑f) ∣[(2 : ℤ)] S) = ⇑f := by
  funext τ
  rw [ModularForm.slash_def]
  have hdetM : (S : Matrix (Fin 2) (Fin 2) ℝ).det = t ^ 2 := by rw [hS, Matrix.det_fin_two_of]; ring
  have hdet : ((Matrix.GeneralLinearGroup.det S : ℝˣ) : ℝ) = t ^ 2 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hdetM]
  have hpos : (0 : ℝ) < ((Matrix.GeneralLinearGroup.det S : ℝˣ) : ℝ) := by rw [hdet]; positivity
  have hσ : ∀ w : ℂ, UpperHalfPlane.σ S w = w := by
    intro w; unfold UpperHalfPlane.σ; rw [if_pos hpos]; rfl
  have hden : UpperHalfPlane.denom S (τ : ℂ) = t := by
    simp [UpperHalfPlane.denom, hS]
  have hsmul : S • τ = τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul, hσ, UpperHalfPlane.num, hden, hS]
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    simp [htc]
  simp only [hσ, hdet, hden, hsmul]
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have habs : |t ^ 2| = t ^ 2 := abs_of_pos (by positivity)
  rw [habs]
  push_cast
  field_simp

end

end K2ArchScalar

open K2ArchScalar in
open scoped ModularForm in
theorem solution
    {M : ℕ} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) (hM : M ≠ 0)
    (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hz : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), (z : AdeleRing (𝓞 ℚ) ℚ).2 v = 1)
    (hpos : 0 < RatIdele.archCoord z)
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    Φ (centralScalar (𝓞 ℚ) ℚ z * x) = Φ x := by
  classical

  obtain ⟨γ, hγU, hγpos⟩ := NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat
    (N := ratLevel M) (ratLevel_ne_bot hM) x
  set g : AdelicGL2 (𝓞 ℚ) ℚ := globalPoints (𝓞 ℚ) ℚ γ * x with hg_def
  set k : AdelicGL2 (𝓞 ℚ) ℚ := finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ g) with hk_def
  set h' : AdelicGL2 (𝓞 ℚ) ℚ := g * k⁻¹ with hh'_def
  have hk_fin : glFin (𝓞 ℚ) ℚ g ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel M) := mem_levelOne_iff.mp hγU
  have hh'_fin : glFin (𝓞 ℚ) ℚ h' = 1 := by
    rw [hh'_def, map_mul, map_inv, hk_def, glFin_finEmbed, mul_inv_cancel]
  have hk_arch : glArch (𝓞 ℚ) ℚ k = 1 := by rw [hk_def, glArch_finEmbed]
  have hg_eq : g = h' * k := by rw [hh'_def, inv_mul_cancel_right]

  have hgpos : LanglandsTunnell.ratArchGL2 g ∈ Matrix.GLPos (Fin 2) ℝ :=
    hγpos default (IsTotallyReal.isReal (default : InfinitePlace ℚ))
  have hh'_arch : LanglandsTunnell.ratArchGL2 h' = LanglandsTunnell.ratArchGL2 g := by
    rw [hh'_def, ratArchGL2_mul, ratArchGL2_inv, ratArchGL2_eq_one_of_glArch hk_arch, inv_one, mul_one]

  have hx : Φ x = Φ h' := by
    rw [← hΦ.left_inv γ x, ← hg_def, hg_eq, hk_def, hΦ.level_inv _ hk_fin]
  have hzx : Φ (centralScalar (𝓞 ℚ) ℚ z * x) = Φ (centralScalar (𝓞 ℚ) ℚ z * h') := by
    rw [← hΦ.left_inv γ (centralScalar (𝓞 ℚ) ℚ z * x), ← mul_assoc, ← centralScalar_mul_comm, mul_assoc, ← hg_def,
      hg_eq, ← mul_assoc, hk_def, hΦ.level_inv _ hk_fin]
  rw [hx, hzx]

  have hc_fin : glFin (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ z * h') = 1 := by
    rw [map_mul, glFin_centralScalar_eq_one z hz, hh'_fin, one_mul]
  have hS := coe_ratArchGL2_centralScalar z
  have hdetS := det_ratArchGL2_centralScalar z
  have hc_arch : LanglandsTunnell.ratArchGL2 (centralScalar (𝓞 ℚ) ℚ z * h')
      = LanglandsTunnell.ratArchGL2 (centralScalar (𝓞 ℚ) ℚ z) * LanglandsTunnell.ratArchGL2 h' := ratArchGL2_mul _ _
  have hh'pos : LanglandsTunnell.ratArchGL2 h' ∈ Matrix.GLPos (Fin 2) ℝ := by rw [hh'_arch]; exact hgpos
  have hcpos : LanglandsTunnell.ratArchGL2 (centralScalar (𝓞 ℚ) ℚ z * h') ∈ Matrix.GLPos (Fin 2) ℝ := by
    show (0 : ℝ) < _
    rw [hc_arch, Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Matrix.det_mul, hdetS]
    have h2 : (0 : ℝ) < ((LanglandsTunnell.ratArchGL2 h' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
      have := hh'pos
      rwa [Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply] at this
    positivity
  rw [hΦ.apply_eq _ hc_fin hcpos, hΦ.apply_eq _ hh'_fin hh'pos, hc_arch, SlashAction.slash_mul,
    slash_scalar_eq h _ (RatIdele.archCoord z) hpos hS]

end S_CuspForm_IsAdelicLiftOfGamma1_apply_centralScalar_mul_eq_of_forall_snd_eq_one_of_archCoord_pos
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOfGamma1_apply_centralScalar_mul_eq_of_forall_snd_eq_one_of_archCoord_pos (solution)
