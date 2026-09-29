-- Prove2me | solution 1 for DihedralWeightOne.exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/c68557dc-9025-5d55-b233-f6b6aca9d2a7

import Mathlib
import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
import Theorems.Thm_DihedralWeightOne_weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DihedralWeightOne_exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul

set_option autoImplicit false

open DihedralWeightOne

open NumberField AdelicDock IsDedekindDomain

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain

variable (p : ℕ) [hp : Fact p.Prime]

section GlobalPointsLemmas

private theorem isReal_rat_infinitePlace (v : InfinitePlace ℚ) : v.IsReal := IsTotallyReal.isReal v

private noncomputable def ratArchHom : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (Matrix.GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom).comp
    ((archComponent ℚ default).comp (glArch (𝓞 ℚ) ℚ))

private theorem ratArchHom_apply (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ratArchHom g = LanglandsTunnell.ratArchGL2 g := rfl

private theorem ratArch_mul (g g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (g * g')
      = LanglandsTunnell.ratArchGL2 g * LanglandsTunnell.ratArchGL2 g' := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, ← ratArchHom_apply, map_mul]

private theorem ratArch_inv (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 g⁻¹ = (LanglandsTunnell.ratArchGL2 g)⁻¹ := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, map_inv]

private theorem ratArch_eq_one_of_glArch_eq_one {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    LanglandsTunnell.ratArchGL2 u = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [hu, map_one, map_one]

private theorem ratArch_finEmbed (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (finEmbed (𝓞 ℚ) ℚ u) = 1 :=
  ratArch_eq_one_of_glArch_eq_one (glArch_finEmbed (𝓞 ℚ) ℚ u)

private theorem ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ) = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom.comp
      ((archEval ℚ default).comp ((adeleArch (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))))
      ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = (Rat.castHom ℝ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j)
  rw [eq_ratCast, eq_ratCast]

private theorem glFin_globalPoints_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl

end GlobalPointsLemmas

private theorem gl_ext_of_arch_fin {x y : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (h₁ : glArch (𝓞 ℚ) ℚ x = glArch (𝓞 ℚ) ℚ y) (h₂ : glFin (𝓞 ℚ) ℚ x = glFin (𝓞 ℚ) ℚ y) : x = y := by
  refine Units.ext (Matrix.ext fun a b => Prod.ext ?_ ?_)
  · exact congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing ℚ) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) a b) h₁
  · exact congrArg
      (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) => (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) h₂

private theorem finEmbed_mul_comm_of_glFin_eq_one {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    finEmbed (𝓞 ℚ) ℚ u * h = h * finEmbed (𝓞 ℚ) ℚ u := by
  refine gl_ext_of_arch_fin ?_ ?_
  · rw [map_mul, map_mul, glArch_finEmbed, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_finEmbed, hh, one_mul, mul_one]

private noncomputable def archPart (γ : GL (Fin 2) ℚ) : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) :=
  globalPoints (𝓞 ℚ) ℚ γ * (finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ)))⁻¹

private theorem glFin_archPart (γ : GL (Fin 2) ℚ) : glFin (𝓞 ℚ) ℚ (archPart γ) = 1 := by
  rw [archPart, map_mul, map_inv, glFin_finEmbed, mul_inv_cancel]

private theorem ratArch_archPart (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (archPart γ) = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  rw [archPart, ratArch_mul, ratArch_inv, ratArch_finEmbed, inv_one, mul_one, ratArch_globalPoints]

private theorem globalPoints_eq_archPart_mul (γ : GL (Fin 2) ℚ) :
    globalPoints (𝓞 ℚ) ℚ γ = archPart γ * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ)) := by
  rw [archPart, inv_mul_cancel_right]

end DescentEngine

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain

variable (p : ℕ) [hp : Fact p.Prime]

private theorem glFin_archPart_mul {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hh : glFin (𝓞 ℚ) ℚ h = 1) (γ : GL (Fin 2) ℚ) :
    glFin (𝓞 ℚ) ℚ (archPart γ * h) = 1 := by
  rw [map_mul, glFin_archPart, hh, one_mul]

private theorem ratArch_archPart_mul (h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (archPart γ * h)
      = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ * LanglandsTunnell.ratArchGL2 h := by
  rw [ratArch_mul, ratArch_archPart]

end DescentEngine

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector
open scoped ModularForm

variable (p : ℕ) [hp : Fact p.Prime]

omit hp in

private theorem exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne {M : ℕ} (hM : M ≠ 0)
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ (γ : GL (Fin 2) ℚ) (h : AdelicGL2 (𝓞 ℚ) ℚ)
      (u : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)),
      AdelicLevel.glFin (𝓞 ℚ) ℚ h = 1 ∧
        LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ ∧
          u ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) ∧
            x = globalPoints (𝓞 ℚ) ℚ γ * h * AdelicDock.finEmbed (𝓞 ℚ) ℚ u := by
  obtain ⟨γ', hlev, hpos⟩ :=
    AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat (AdelicDock.ratLevel_ne_bot hM) x
  set y : AdelicGL2 (𝓞 ℚ) ℚ := globalPoints (𝓞 ℚ) ℚ γ' * x with hy
  set u : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    AdelicLevel.glFin (𝓞 ℚ) ℚ y with hu
  refine ⟨γ'⁻¹, y * (AdelicDock.finEmbed (𝓞 ℚ) ℚ u)⁻¹, u, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, map_inv, AdelicDock.glFin_finEmbed, mul_inv_cancel]
  · have hy_pos : LanglandsTunnell.ratArchGL2 y ∈ Matrix.GLPos (Fin 2) ℝ :=
      hpos default (IsTotallyReal.isReal default)
    rw [← map_inv, ratArch_mul, ratArch_finEmbed]
    simpa using hy_pos
  · exact (AdelicLevel.mem_levelOne_iff).mp hlev
  · rw [map_inv, hy]
    group

omit hp in
private theorem σ_apply_of_det_pos {g : GL (Fin 2) ℝ} (hg : 0 < (g.det : ℝ)) (z : ℂ) :
    UpperHalfPlane.σ g z = z := by
  rw [UpperHalfPlane.σ, if_pos hg]
  rfl

omit hp in

private noncomputable def slashHom (k : ℤ) (A : GL (Fin 2) ℝ) : (UpperHalfPlane → ℂ) →+ (UpperHalfPlane → ℂ) where
  toFun f := f ∣[k] A
  map_zero' := SlashAction.zero_slash k A
  map_add' f g := SlashAction.add_slash k A f g

end DescentEngine

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector
open scoped ModularForm

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private noncomputable def slashSpan (g : CuspForm (CongruenceSubgroup.Gamma1 M) 1) : Submodule ℂ (UpperHalfPlane → ℂ) :=
  Submodule.span ℂ (Set.range fun β : GL (Fin 2) ℚ => (⇑g) ∣[(1 : ℤ)] β.map (Rat.castHom ℝ))

private theorem slash_map_mem_slashSpan (β : GL (Fin 2) ℚ) : (⇑g) ∣[(1 : ℤ)] β.map (Rat.castHom ℝ) ∈ slashSpan g :=
  Submodule.subset_span ⟨β, rfl⟩

private def HasReading (y : AdelicSpan φ) (F : UpperHalfPlane → ℂ) : Prop :=
  ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 → LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
    (AdelicSpan.toFn φ y).toFn h = weightOneArchLift F (LanglandsTunnell.ratArchGL2 h)

private theorem weightOneArchLift_zero' (A : GL (Fin 2) ℝ) : weightOneArchLift (0 : UpperHalfPlane → ℂ) A = 0 := by
  unfold weightOneArchLift
  rw [SlashAction.zero_slash, Pi.zero_apply, zero_mul]

private theorem weightOneArchLift_add' (F₁ F₂ : UpperHalfPlane → ℂ) (A : GL (Fin 2) ℝ) :
    weightOneArchLift (F₁ + F₂) A = weightOneArchLift F₁ A + weightOneArchLift F₂ A := by
  unfold weightOneArchLift
  rw [SlashAction.add_slash, Pi.add_apply, add_mul]

private theorem weightOneArchLift_smul' (c : ℂ) (F : UpperHalfPlane → ℂ) {A : GL (Fin 2) ℝ} (hA : 0 < (A.det : ℝ)) :
    weightOneArchLift (c • F) A = c * weightOneArchLift F A := by
  unfold weightOneArchLift
  rw [ModularForm.smul_slash, Pi.smul_apply, σ_apply_of_det_pos hA, smul_eq_mul, mul_assoc]

private theorem weightOneArchLift_mul' (F : UpperHalfPlane → ℂ) (A B : GL (Fin 2) ℝ) :
    weightOneArchLift F (A * B) = (((A.det.val : ℝ)) : ℂ) * weightOneArchLift (F ∣[(1 : ℤ)] A) B := by
  unfold weightOneArchLift
  rw [SlashAction.slash_mul, map_mul, Units.val_mul, Complex.ofReal_mul, zpow_one, zpow_one]
  ring

private theorem hasReading_zero : HasReading (0 : AdelicSpan φ) (0 : UpperHalfPlane → ℂ) := by
  intro h _ _
  rw [weightOneArchLift_zero']
  rfl

private theorem HasReading.add {y₁ y₂ : AdelicSpan φ} {F₁ F₂ : UpperHalfPlane → ℂ} (h₁ : HasReading y₁ F₁)
    (h₂ : HasReading y₂ F₂) : HasReading (y₁ + y₂) (F₁ + F₂) := by
  intro h hh hpos
  rw [weightOneArchLift_add', ← h₁ h hh hpos, ← h₂ h hh hpos]
  rfl

private theorem HasReading.smul {y : AdelicSpan φ} {F : UpperHalfPlane → ℂ} (hy : HasReading y F) (c : ℂ) :
    HasReading (c • y) (c • F) := by
  intro h hh hpos
  rw [weightOneArchLift_smul' c F ((Matrix.mem_glpos _).mp hpos), ← hy h hh hpos]
  rfl

private theorem glFin_conj_eq_one (δ : GL (Fin 2) ℚ) {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : glFin (𝓞 ℚ) ℚ h = 1) :
    glFin (𝓞 ℚ) ℚ ((globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * h * globalPoints (𝓞 ℚ) ℚ δ) = 1 := by
  rw [map_mul, map_mul, hh, mul_one, map_inv, inv_mul_cancel]

private theorem exists_hasReading_finEmbed_smul_self (hM : M ≠ 0)
    (hφleft : ∀ (γ : GL (Fin 2) ℚ) (x : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * x) = φ x)
    (hφlev : ∀ w ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M), ∀ x : AdelicGL2 (𝓞 ℚ) ℚ,
      φ (x * finEmbed (𝓞 ℚ) ℚ w) = φ x)
    (hφeq : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ x = 1 →
      LanglandsTunnell.ratArchGL2 x ∈ Matrix.GLPos (Fin 2) ℝ → φ x = weightOneArchLift (⇑g) (LanglandsTunnell.ratArchGL2 x))
    (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ∃ F ∈ slashSpan g, HasReading ((finEmbed (𝓞 ℚ) ℚ u : AdelicGL2 (𝓞 ℚ) ℚ) • AdelicSpan.self φ) F := by
  obtain ⟨δ, a, w, ha, hapos, hw, hdec⟩ :=
    exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hM (finEmbed (𝓞 ℚ) ℚ u)

  have harch : LanglandsTunnell.ratArchGL2 a = (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) δ)⁻¹ := by
    have h0 : LanglandsTunnell.ratArchGL2 (finEmbed (𝓞 ℚ) ℚ u) = 1 := ratArch_finEmbed _
    rw [hdec, ratArch_mul, ratArch_mul, ratArch_finEmbed, mul_one, ratArch_globalPoints] at h0
    exact eq_inv_of_mul_eq_one_right h0
  refine ⟨((((Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) δ⁻¹).det.val : ℝ)) : ℂ) •
      ((⇑g) ∣[(1 : ℤ)] δ⁻¹.map (Rat.castHom ℝ)),
    Submodule.smul_mem _ _ (slash_map_mem_slashSpan δ⁻¹), ?_⟩
  intro h hh hpos
  have hval : (AdelicSpan.toFn φ ((finEmbed (𝓞 ℚ) ℚ u : AdelicGL2 (𝓞 ℚ) ℚ) • AdelicSpan.self φ)).toFn h
      = φ (h * finEmbed (𝓞 ℚ) ℚ u) := by
    rw [AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul, AdelicSpan.toFn_self, AdelicFnCarrier.toFn_mk]
  rw [hval, hdec, ← mul_assoc, ← mul_assoc, hφlev w hw]
  have hre : h * globalPoints (𝓞 ℚ) ℚ δ * a
      = globalPoints (𝓞 ℚ) ℚ δ * (((globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * h * globalPoints (𝓞 ℚ) ℚ δ) * a) := by
    group
  have hh' : glFin (𝓞 ℚ) ℚ (((globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * h * globalPoints (𝓞 ℚ) ℚ δ) * a) = 1 := by
    rw [map_mul, glFin_conj_eq_one δ hh, ha, mul_one]
  have hratarch : LanglandsTunnell.ratArchGL2 (((globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * h * globalPoints (𝓞 ℚ) ℚ δ) * a)
      = (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) δ)⁻¹ * LanglandsTunnell.ratArchGL2 h := by
    rw [ratArch_mul, ratArch_mul, ratArch_mul, ratArch_inv, ratArch_globalPoints, harch, mul_assoc,
      mul_inv_cancel, mul_one]
  have hpos' : LanglandsTunnell.ratArchGL2 (((globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * h * globalPoints (𝓞 ℚ) ℚ δ) * a)
      ∈ Matrix.GLPos (Fin 2) ℝ := by
    rw [hratarch, ← harch]
    exact Subgroup.mul_mem _ hapos hpos
  rw [hre, hφleft, hφeq _ hh' hpos', hratarch, weightOneArchLift_mul',
    weightOneArchLift_smul' _ _ ((Matrix.mem_glpos _).mp hpos),
    map_inv (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ)) δ, map_inv]

private theorem exists_hasReading_of_mem_span (hM : M ≠ 0)
    (hφleft : ∀ (γ : GL (Fin 2) ℚ) (x : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * x) = φ x)
    (hφlev : ∀ w ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M), ∀ x : AdelicGL2 (𝓞 ℚ) ℚ,
      φ (x * finEmbed (𝓞 ℚ) ℚ w) = φ x)
    (hφeq : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ x = 1 →
      LanglandsTunnell.ratArchGL2 x ∈ Matrix.GLPos (Fin 2) ℝ → φ x = weightOneArchLift (⇑g) (LanglandsTunnell.ratArchGL2 x))
    {y : AdelicSpan φ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (finEmbed (𝓞 ℚ) ℚ u : AdelicGL2 (𝓞 ℚ) ℚ) • AdelicSpan.self φ)) :
    ∃ F ∈ slashSpan g, HasReading y F := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, rfl⟩ := hy
    exact exists_hasReading_finEmbed_smul_self hM hφleft hφlev hφeq u
  | zero => exact ⟨0, Submodule.zero_mem _, hasReading_zero⟩
  | add y₁ y₂ _ _ ih₁ ih₂ =>
    obtain ⟨F₁, hF₁, h₁⟩ := ih₁
    obtain ⟨F₂, hF₂, h₂⟩ := ih₂
    exact ⟨F₁ + F₂, Submodule.add_mem _ hF₁ hF₂, h₁.add h₂⟩
  | smul c y _ ih =>
    obtain ⟨F, hF, h⟩ := ih
    exact ⟨c • F, Submodule.smul_mem _ c hF, h.smul c⟩

end DescentEngine

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain
open scoped ModularForm

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1}

private theorem continuous_denom (A : GL (Fin 2) ℝ) : Continuous fun τ : UpperHalfPlane => UpperHalfPlane.denom A τ := by
  unfold UpperHalfPlane.denom
  exact (continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const

private theorem continuous_slash {f : UpperHalfPlane → ℂ} (hf : Continuous f) (k : ℤ) (A : GL (Fin 2) ℝ) :
    Continuous (f ∣[k] A) := by
  have h1 : Continuous fun τ : UpperHalfPlane => UpperHalfPlane.σ A (f (A • τ)) :=
    (UpperHalfPlane.σ A).continuous.comp (hf.comp (continuous_const_smul A))
  have h2 : Continuous fun τ : UpperHalfPlane => UpperHalfPlane.denom A τ ^ (-k) :=
    (continuous_denom A).zpow₀ _ fun τ => Or.inl (UpperHalfPlane.denom_ne_zero A τ)
  have h3 : Continuous fun τ : UpperHalfPlane =>
      UpperHalfPlane.σ A (f (A • τ)) * |A.det.val| ^ (k - 1) * UpperHalfPlane.denom A τ ^ (-k) :=
    (h1.mul continuous_const).mul h2
  convert h3 using 1
  rfl

private theorem continuous_of_mem_slashSpan {F : UpperHalfPlane → ℂ} (hF : F ∈ slashSpan g) : Continuous F := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨β, rfl⟩ := hF
    exact continuous_slash (CuspFormClass.holo g).continuous 1 _
  | zero => exact continuous_const
  | add F₁ F₂ _ _ h₁ h₂ => exact h₁.add h₂
  | smul c F _ h => exact h.const_smul c

private theorem dense_ratPoints :
    Dense (((↑) : UpperHalfPlane → ℂ) ⁻¹'
      {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)}) := by
  have h1 : Dense (Set.range ((↑) : ℚ → ℝ) ×ˢ Set.range ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.prod Rat.denseRange_cast
  have h2 : {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)} =
      Complex.equivRealProdCLM ⁻¹' (Set.range ((↑) : ℚ → ℝ) ×ˢ Set.range ((↑) : ℚ → ℝ)) := by
    ext w; simp [Set.mem_prod]
  have hS : Dense {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)} := by
    rw [h2]; exact h1.preimage Complex.equivRealProdCLM.toHomeomorph.isOpenMap
  exact hS.preimage UpperHalfPlane.isOpenEmbedding_coe.isOpenMap

private theorem exists_glFin_eq_one_and_smul_I_eq (z : UpperHalfPlane) (hx : (z : ℂ).re ∈ Set.range ((↑) : ℚ → ℝ))
    (hy : (z : ℂ).im ∈ Set.range ((↑) : ℚ → ℝ)) :
    ∃ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 ∧ LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ ∧
      LanglandsTunnell.ratArchGL2 h • UpperHalfPlane.I = z := by
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  have hy0 : (0 : ℝ) < y := by rw [hy]; exact z.im_pos
  have hyq : (0 : ℚ) < y := by exact_mod_cast hy0
  let A : Matrix (Fin 2) (Fin 2) ℚ := !![y, x; 0, 1]
  have hdetA : A.det = y := by simp [A, Matrix.det_fin_two_of]
  let γ : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [hdetA]; exact hyq.ne')
  let h : AdelicGL2 (𝓞 ℚ) ℚ :=
    globalPoints (𝓞 ℚ) ℚ γ * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ))⁻¹
  have hfin : glFin (𝓞 ℚ) ℚ h = 1 := by
    simp only [h, map_mul, glFin_finEmbed, mul_inv_cancel]
  have hP : LanglandsTunnell.ratArchGL2 h = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
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
  refine ⟨h, hfin, (Matrix.mem_glpos _).mpr hdetpos, ?_⟩
  rw [UpperHalfPlane.coe_re] at hx
  rw [UpperHalfPlane.coe_im] at hy
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos hdetpos]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hPmat, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, UpperHalfPlane.coe_I,
    Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_one, div_one]
  apply Complex.ext <;> simp [← hx, ← hy]

private theorem eq_of_forall_weightOneArchLift_eq {F G : UpperHalfPlane → ℂ} (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 → LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
      weightOneArchLift F (LanglandsTunnell.ratArchGL2 h) = weightOneArchLift G (LanglandsTunnell.ratArchGL2 h)) :
    F = G := by
  refine Continuous.ext_on dense_ratPoints hF hG ?_
  rintro z ⟨hx, hy⟩
  obtain ⟨h, hfin, hpos, hz⟩ := exists_glFin_eq_one_and_smul_I_eq z hx hy
  have hdet : (0 : ℝ) < (LanglandsTunnell.ratArchGL2 h).det.val := (Matrix.mem_glpos _).mp hpos
  have key := hFG h hfin hpos
  unfold weightOneArchLift at key
  rw [ModularForm.slash_apply, ModularForm.slash_apply, σ_apply_of_det_pos hdet, σ_apply_of_det_pos hdet, hz]
    at key
  have ha : ((|(LanglandsTunnell.ratArchGL2 h).det.val| : ℝ) : ℂ) ^ ((1 : ℤ) - 1) ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast (abs_ne_zero.mpr hdet.ne'))
  have hb : UpperHalfPlane.denom (LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I ^ (-(1 : ℤ)) ≠ 0 :=
    zpow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ _)
  have hd : (((LanglandsTunnell.ratArchGL2 h).det.val : ℝ) : ℂ) ^ (1 : ℤ) ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast hdet.ne')
  exact mul_right_cancel₀ ha (mul_right_cancel₀ hb (mul_right_cancel₀ hd key))

end DescentEngine

namespace DescentSupportB

open NumberField NumberField.AdelicLevel AdelicDock IsDedekindDomain

section S4c

private theorem natGenerator_padicPlace (p : ℕ) [Fact p.Prime] :
    Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) (padicPlace p) = p :=
  congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, Fact.out⟩)

private theorem eq_padicPlace_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
      ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
    v = padicPlace (Rat.HeightOneSpectrum.natGenerator v) := by
  haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  refine ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm_apply_apply v).symm.trans ?_
  exact congrArg _ (Subtype.ext rfl)

private theorem padicPlace_injective {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (h : padicPlace p = padicPlace q) : p = q :=
  congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective h)

private theorem valued_natCast_eq_of_factorization_eq (ℓ : ℕ) [Fact ℓ.Prime]
    {N M : ℕ} (hN : N ≠ 0) (hM : M ≠ 0) (hfac : N.factorization ℓ = M.factorization ℓ) :
    Valued.v (padicRingEquiv ℓ (N : ℚ_[ℓ])) = Valued.v (padicRingEquiv ℓ (M : ℚ_[ℓ])) := by
  have hN' : (N : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast hN
  have hM' : (M : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast hM
  refine le_antisymm ?_ ?_
  · rw [valued_le_valued_iff ℓ _ _ hM', norm_natCast_eq_zpow_neg_factorization ℓ hN,
      norm_natCast_eq_zpow_neg_factorization ℓ hM, hfac]
  · rw [valued_le_valued_iff ℓ _ _ hN', norm_natCast_eq_zpow_neg_factorization ℓ hN,
      norm_natCast_eq_zpow_neg_factorization ℓ hM, hfac]

private theorem idealBound_ratLevel_eq_of_factorization_eq {q : ℕ} [Fact q.Prime] {N M : ℕ}
    (hN : N ≠ 0) (hM : M ≠ 0)
    (hfac : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ q → N.factorization ℓ = M.factorization ℓ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ≠ padicPlace q) :
    idealBound (𝓞 ℚ) (ratLevel N) v = idealBound (𝓞 ℚ) (ratLevel M) v := by
  haveI hℓp : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hvℓ : v = padicPlace (Rat.HeightOneSpectrum.natGenerator v) :=
    eq_padicPlace_natGenerator v
  have hne : Rat.HeightOneSpectrum.natGenerator v ≠ q := fun heq =>
    hv <| (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective <|
      Subtype.ext <| heq.trans (natGenerator_padicPlace q).symm
  rw [hvℓ, idealBound_ratLevel _ hN, idealBound_ratLevel _ hM,
    valued_natCast_eq_of_factorization_eq _ hN hM (hfac _ hℓp.out hne)]

end S4c

end DescentSupportB

namespace DescentSupportB

open NumberField NumberField.AdelicLevel AdelicDock IsDedekindDomain

section S4d

private theorem algebraMap_intCast_apply_padicPlace_eq (p : ℕ) [Fact p.Prime] (n : ℤ) :
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)) (padicPlace p)
      = padicRingEquiv p ((n : ℤ_[p]) : ℚ_[p]) := by
  have hL : (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)) (padicPlace p) =
      (n : (padicPlace p).adicCompletion ℚ) := by
    change ((algebraMap ℚ ((padicPlace p).adicCompletion ℚ)).comp (Int.castRingHom ℚ)) n = _
    exact eq_intCast _ n
  have hR : padicRingEquiv p ((n : ℤ_[p]) : ℚ_[p]) = (n : (padicPlace p).adicCompletion ℚ) := by
    rw [PadicInt.coe_intCast, map_intCast]
  exact hL.trans hR.symm

private theorem isLevelZeroMatrix_mapMatrix_of_int_entries {N : ℕ} (hN : N ≠ 0)
    (δ : Matrix (Fin 2) (Fin 2) ℚ) (hδ : ∀ a b, ∃ n : ℤ, δ a b = n)
    (hlow : ∃ m : ℤ, δ 1 0 = (N : ℚ) * m) :
    IsLevelZeroMatrix (𝓞 ℚ) ℚ (ratLevel N)
      ((algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix δ) := by
  refine ⟨fun i j v => ?_, fun v => ?_⟩
  all_goals
    haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
      ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
    rw [eq_padicPlace_natGenerator v]
    set ℓ := Rat.HeightOneSpectrum.natGenerator v
  · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    obtain ⟨n, hn⟩ := hδ i j
    rw [hn, algebraMap_intCast_apply_padicPlace_eq ℓ n]
    exact padicRingEquiv_coe_mem ℓ _
  · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    obtain ⟨m, hm⟩ := hlow
    have hNm : δ 1 0 = ((N * m : ℤ) : ℚ) := by push_cast; linarith [hm]
    rw [hNm, algebraMap_intCast_apply_padicPlace_eq ℓ (N * m)]
    rw [(valued_coe_le_idealBound_iff ℓ hN _)]
    have hdvd : (ℓ : ℤ_[ℓ]) ^ N.factorization ℓ ∣ (↑(N * m) : ℤ_[ℓ]) := by
      have hdvdZ : (ℓ : ℤ) ^ N.factorization ℓ ∣ (N * m : ℤ) := by
        refine Dvd.dvd.mul_right ?_ m
        exact_mod_cast Nat.ordProj_dvd N ℓ
      obtain ⟨k, hk⟩ := hdvdZ
      exact ⟨(k : ℤ_[ℓ]), by push_cast [hk]; ring⟩
    exact Ideal.mem_span_singleton.mpr hdvd

private theorem map_algebraMap_mem_finiteLevelZero {N : ℕ} (hN : N ≠ 0) (δ : GL (Fin 2) ℚ)
    (hδ : ∀ a b : Fin 2, ∃ n : ℤ, (δ : Matrix (Fin 2) (Fin 2) ℚ) a b = n)
    (hδ' : ∀ a b : Fin 2, ∃ n : ℤ, ((δ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) a b = n)
    (hlow : ∃ m : ℤ, (δ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (N : ℚ) * m)
    (hlow' : ∃ m : ℤ, ((δ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (N : ℚ) * m) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) δ
      ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) := by
  rw [mem_finiteLevelZero_iff]
  have hcoe : ∀ (γ : GL (Fin 2) ℚ),
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) γ
        : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix (γ : Matrix (Fin 2) (Fin 2) ℚ) :=
    fun γ => Matrix.ext fun i j => Matrix.GeneralLinearGroup.map_apply _ i j γ
  rw [hcoe δ, ← Matrix.GeneralLinearGroup.map_inv, hcoe δ⁻¹]
  exact ⟨isLevelZeroMatrix_mapMatrix_of_int_entries hN _ hδ hlow,
    isLevelZeroMatrix_mapMatrix_of_int_entries hN _ hδ' hlow'⟩

end S4d

end DescentSupportB

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector
open scoped ModularForm

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private abbrev fn (y : AdelicSpan φ) : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := (AdelicSpan.toFn φ y).toFn

private theorem fn_smul_self (u : AdelicGL2 (𝓞 ℚ) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn (u • AdelicSpan.self φ) z = φ (z * u) := by
  rw [fn, AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul, AdelicSpan.toFn_self, AdelicFnCarrier.toFn_mk]

private theorem fn_add (y₁ y₂ : AdelicSpan φ) (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn (y₁ + y₂) z = fn y₁ z + fn y₂ z := rfl

private theorem fn_csmul (c : ℂ) (y : AdelicSpan φ) (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn (c • y) z = c * fn y z := rfl

private theorem fn_zero (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn (0 : AdelicSpan φ) z = 0 := rfl

private theorem hasReading_iff (y : AdelicSpan φ) (F : UpperHalfPlane → ℂ) :
    HasReading y F ↔ ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 →
      LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
        fn y h = weightOneArchLift F (LanglandsTunnell.ratArchGL2 h) := Iff.rfl

end DescentEngine

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector
open scoped ModularForm

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private theorem glFin_globalPoints_eq_map (δ : GL (Fin 2) ℚ) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ)
      = Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) δ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glFin_globalPoints_apply]
  rfl

private theorem mapGL_entry_int (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (a b : Fin 2) :
    ∃ n : ℤ, ((Matrix.SpecialLinearGroup.mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) a b = n :=
  ⟨γ a b, by simp [Matrix.SpecialLinearGroup.mapGL]⟩

private theorem mapGL_lowerLeft_of_mem_Gamma0 {N : ℕ} {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ m : ℤ, ((Matrix.SpecialLinearGroup.mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (N : ℚ) * m := by
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) N).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  refine ⟨m, ?_⟩
  simp [Matrix.SpecialLinearGroup.mapGL, hm]

private theorem glFin_globalPoints_mapGL_mem_finiteLevelZero {N : ℕ} (hN : N ≠ 0) {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ γ)) ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) := by
  rw [glFin_globalPoints_eq_map]
  refine DescentSupportB.map_algebraMap_mem_finiteLevelZero hN _ (mapGL_entry_int γ) ?_
    (mapGL_lowerLeft_of_mem_Gamma0 hγ) ?_
  · rw [← map_inv]
    exact mapGL_entry_int γ⁻¹
  · rw [← map_inv]
    exact mapGL_lowerLeft_of_mem_Gamma0 (Subgroup.inv_mem _ hγ)

private theorem map_castHom_mapGL (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.SpecialLinearGroup.mapGL ℚ γ)
      = Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp [Matrix.SpecialLinearGroup.mapGL]

private theorem mapGL_mem_GLPos (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) ∈ Matrix.GLPos (Fin 2) ℝ := by
  rw [Matrix.mem_glpos]
  simp [Matrix.SpecialLinearGroup.mapGL]

end DescentEngine

namespace GammaOneCuspAux

open scoped ModularForm MatrixGroups Manifold
open UpperHalfPlane OnePoint Matrix.SpecialLinearGroup

private lemma isCusp_SL2Z_map_smul {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) (β : GL (Fin 2) ℚ) :
    IsCusp (β.map (Rat.castHom ℝ) • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  refine ⟨β • c₀, ?_⟩
  have h := OnePoint.map_smul (Rat.castHom ℝ) β c₀
  simpa only [Rat.coe_castHom] using h

private lemma isCusp_SL2Z_of_isCusp_map {Γ : Subgroup SL(2, ℤ)} {c : OnePoint ℝ}
    (hc : IsCusp c (Subgroup.map (mapGL ℝ) Γ)) : IsCusp c 𝒮ℒ :=
  hc.mono (Subgroup.map_le_range _ _)

private lemma isZeroAt_slash_map {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma1 M) 1)
    (β : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsZeroAt ((⇑g) ∣[(1 : ℤ)] β.map (Rat.castHom ℝ)) 1 := by
  rw [← OnePoint.IsZeroAt.smul_iff]
  apply CuspFormClass.zero_at_cusps g
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
  exact isCusp_SL2Z_map_smul hc β

private lemma isZeroAt_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → UpperHalfPlane → ℂ)
    {x : OnePoint ℝ} (hf : ∀ i ∈ s, x.IsZeroAt (f i) 1) :
    x.IsZeroAt (∑ i ∈ s, c i • f i) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro γ _
    simp
    exact Filter.zero_zeroAtFilter _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine OnePoint.IsZeroAt.add ?_ (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    intro γ hγ
    rw [ModularForm.smul_slash]
    exact (hf a (Finset.mem_insert_self a s) γ hγ).smul _

private lemma mdifferentiable_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → UpperHalfPlane → ℂ)
    (hf : ∀ i ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => (simp; exact mdifferentiable_const)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ((hf a (Finset.mem_insert_self a s)).const_smul _).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem exists_gamma1_cuspForm_coe_eq
    {M N : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma1 M) 1)
    {ι : Type} [Fintype ι] (c : ι → ℂ) (β : ι → GL (Fin 2) ℚ)
    (F : UpperHalfPlane → ℂ)
    (hF : F = ∑ i, c i • ((⇑g) ∣[(1 : ℤ)] (β i).map (Rat.castHom ℝ)))
    (hinv : ∀ γ ∈ Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma1 N),
      F ∣[(1 : ℤ)] γ = F) :
    ∃ h : CuspForm (CongruenceSubgroup.Gamma1 N) 1, ⇑h = F :=
  ⟨{ toFun := F
     slash_action_eq' := hinv
     holo' := by
       subst hF
       exact mdifferentiable_sum _ _ _ fun i _ => (CuspFormClass.holo g).slash _ _
     zero_at_cusps' := fun hc => by
       subst hF
       exact isZeroAt_sum _ _ _ fun i _ => isZeroAt_slash_map g (β i) (isCusp_SL2Z_of_isCusp_map hc) },
   rfl⟩

end GammaOneCuspAux

namespace NebentypusDescent

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector
open DescentEngine
open scoped ModularForm

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 1}
variable {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable {N : ℕ} {ε : DirichletCharacter ℂ N} {y : AdelicSpan Φ}

private theorem exists_eq_sum_of_mem_slashSpan' {F : UpperHalfPlane → ℂ} (hF : F ∈ slashSpan g) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (β : ι → GL (Fin 2) ℚ),
      F = ∑ i, c i • ((⇑g) ∣[(1 : ℤ)] (β i).map (Rat.castHom ℝ)) := by
  obtain ⟨l, hl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hF
  refine ⟨l.support, inferInstance, fun i => l i, fun i => (i : GL (Fin 2) ℚ), ?_⟩
  rw [← hl, Finsupp.sum, ← Finset.sum_coe_sort]

private theorem fn_globalPoints_mul_of_mem_span
    (hΦleft : ∀ (γ : GL (Fin 2) ℚ) (x : AdelicGL2 (𝓞 ℚ) ℚ), Φ (globalPoints (𝓞 ℚ) ℚ γ * x) = Φ x)
    (hy : y ∈ Submodule.span ℂ (Set.range fun u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (finEmbed (𝓞 ℚ) ℚ u : AdelicGL2 (𝓞 ℚ) ℚ) • AdelicSpan.self Φ))
    (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, rfl⟩ := hy
    rw [fn_smul_self, fn_smul_self, mul_assoc, hΦleft]
  | zero => rfl
  | add y₁ y₂ _ _ ih₁ ih₂ => rw [fn_add, fn_add, ih₁, ih₂]
  | smul c y _ ih => rw [fn_csmul, fn_csmul, ih]

private theorem fn_mul_finEmbed_of_mem_finiteLevelOne
    (hK0 : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N), ∀ d : ℤ, IsCoprime d (N : ℤ) →
      (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
          - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (ratLevel N) →
      ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = (ε (d : ZMod N))⁻¹ * fn y z)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N))
    (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn y (z * finEmbed (𝓞 ℚ) ℚ u) = fn y z := by
  have h := hK0 u (finiteLevelOne_le_finiteLevelZero (𝓞 ℚ) ℚ _ hu) 1 isCoprime_one_left (by
    rw [Int.cast_one, map_one]
    exact (mem_finiteLevelOne_iff.mp hu).1.lowerRight) z
  rwa [Int.cast_one, map_one, inv_one, one_mul] at h

private theorem slash_eq_inv_smul (hN : N ≠ 0) {F : UpperHalfPlane → ℂ} (hF : Continuous F)
    (hread : HasReading y F)
    (hleft : ∀ γ z, fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z)
    (hK0 : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N), ∀ d : ℤ, IsCoprime d (N : ℤ) →
      (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
          - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (ratLevel N) →
      ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = (ε (d : ZMod N))⁻¹ * fn y z)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (hcop : IsCoprime (γ 0 0 : ℤ) (N : ℤ)) :
    F ∣[(1 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = (ε ((γ 0 0 : ℤ) : ZMod N))⁻¹ • F := by
  set δ : GL (Fin 2) ℚ := Matrix.SpecialLinearGroup.mapGL ℚ γ with hδ
  refine eq_of_forall_weightOneArchLift_eq (continuous_slash hF 1 _)
    (hF.const_smul ((ε ((γ 0 0 : ℤ) : ZMod N))⁻¹)) fun h hh hpos => ?_
  have hpos' : LanglandsTunnell.ratArchGL2 (archPart δ * h) ∈ Matrix.GLPos (Fin 2) ℝ := by
    rw [ratArch_archPart_mul, hδ, map_castHom_mapGL]
    exact Subgroup.mul_mem _ (mapGL_mem_GLPos γ) hpos
  have hread' := (hasReading_iff y F).mp hread
  have h1 := hread' (archPart δ * h) (glFin_archPart_mul hh δ) hpos'
  rw [ratArch_archPart_mul, hδ, map_castHom_mapGL, weightOneArchLift_mul'] at h1
  rw [← hδ] at h1
  have hdet1 : ((((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)).det.val : ℝ) : ℂ) = 1 := by
    rw [Matrix.SpecialLinearGroup.det_mapGL]; simp
  rw [hdet1, one_mul] at h1
  have hG : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ) ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) :=
    glFin_globalPoints_mapGL_mem_finiteLevelZero hN hγ
  have h2 : archPart δ * h
      = globalPoints (𝓞 ℚ) ℚ δ * (h * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ))⁻¹) := by
    rw [archPart, mul_assoc, ← map_inv, finEmbed_mul_comm_of_glFin_eq_one hh]

  have hval : (((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ))⁻¹ :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
          - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (((γ 0 0 : ℤ)) : ℚ)
      ∈ idealBall (𝓞 ℚ) ℚ (ratLevel N) := by
    have hentry : (((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ))⁻¹ :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
          = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (((γ 0 0 : ℤ) : ℚ)) := by
      rw [← map_inv, ← map_inv, glFin_globalPoints_apply, hδ, ← map_inv]
      congr 1
      have hmat : ((Matrix.SpecialLinearGroup.mapGL ℚ γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
          = ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := rfl
      rw [hmat, Matrix.map_apply, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      simp
    rw [hentry, sub_self]
    exact zero_mem_idealBall _
  rw [h2, hleft, hK0 _ (Subgroup.inv_mem _ hG) (γ 0 0) hcop hval] at h1
  rw [← h1, hread' h hh hpos, weightOneArchLift_smul' _ _ ((Matrix.mem_glpos _).mp hpos)]

private theorem eq_zero_of_hasReading_zero' (hN : N ≠ 0) (hread : HasReading y 0)
    (hleft : ∀ γ z, fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z)
    (hK1 : ∀ u ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N), ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = fn y z) :
    y = 0 := by
  refine AdelicSpan.ext _ (AdelicFnCarrier.ext fun z => ?_)
  obtain ⟨γ, h, u, hh, hpos, hu, rfl⟩ := exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hN z
  change fn y _ = fn (0 : AdelicSpan Φ) _
  rw [fn_zero, hK1 u hu, hleft, (hasReading_iff y 0).mp hread h hh hpos, weightOneArchLift_zero']

private theorem isCoprime_and_mul_eq_one {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    IsCoprime (γ 0 0 : ℤ) (N : ℤ) ∧ ((γ 0 0 : ℤ) : ZMod N) * (γ 1 1 : ℤ) = 1 := by
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.mp hγ
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at this
    exact this
  refine ⟨?_, ?_⟩
  · obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
    refine ⟨γ 1 1, -(γ 0 1 * m), ?_⟩
    rw [hm] at hdet
    linear_combination hdet
  · have := congrArg (fun z : ℤ => (z : ZMod N)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, mul_zero, sub_zero] at this
    exact this

end NebentypusDescent

open DescentEngine NebentypusDescent NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm LocalNewvector in
open DihedralWeightOne IsDedekindDomain in
open scoped MatrixGroups ModularForm in

theorem solution
    {M : ℕ} [NeZero M] (h : CuspForm (CongruenceSubgroup.Gamma1 M) 1)
    {N : ℕ} [NeZero N] (ε : DirichletCharacter ℂ N)
    (y : LocalNewvector.AdelicSpan (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h)))
    (hy : y ∈ Submodule.span ℂ (Set.range fun u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (AdelicDock.finEmbed (𝓞 ℚ) ℚ u : AdelicGL2 (𝓞 ℚ) ℚ) •
        LocalNewvector.AdelicSpan.self (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h))))
    (hK0 : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel N), ∀ d : ℤ, IsCoprime d (N : ℤ) →
      (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
          - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (AdelicDock.ratLevel N) →
      ∀ x : AdelicGL2 (𝓞 ℚ) ℚ,
        (LocalNewvector.AdelicSpan.toFn _ y).toFn (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) =
          (ε (d : ZMod N))⁻¹ * (LocalNewvector.AdelicSpan.toFn _ y).toFn x) :
    ∃ F : CuspForm (CongruenceSubgroup.Gamma1 N) 1,
      CuspForm.HasNebentypus ε F ∧
      (LocalNewvector.AdelicSpan.toFn _ y).toFn = weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) ∧
      (F = 0 → y = 0) := by
  classical
  have hM : M ≠ 0 := NeZero.ne M
  have hN : N ≠ 0 := NeZero.ne N

  have hfh : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma1 M → (⇑h) ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = ⇑h :=
    fun γ hγ => SlashInvariantForm.slash_action_eqn h _ ⟨γ, hγ, rfl⟩
  obtain ⟨hφleft, hφlev, hφeq⟩ :=
    DihedralWeightOne.weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift hM (⇑h) hfh

  have hleft : ∀ γ z, fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z :=
    fun γ z => fn_globalPoints_mul_of_mem_span hφleft hy γ z
  have hK1 : ∀ u ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N), ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = fn y z :=
    fun u hu z => fn_mul_finEmbed_of_mem_finiteLevelOne hK0 hu z

  obtain ⟨F, hFspan, hread⟩ := exists_hasReading_of_mem_span hM hφleft hφlev hφeq hy
  have hFcont : Continuous F := continuous_of_mem_slashSpan hFspan

  have hslash : ∀ γ ∈ CongruenceSubgroup.Gamma0 N,
      F ∣[(1 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = (ε ((γ 0 0 : ℤ) : ZMod N))⁻¹ • F :=
    fun γ hγ => slash_eq_inv_smul hN hFcont hread hleft hK0 hγ (isCoprime_and_mul_eq_one hγ).1

  have hinv : ∀ γ' ∈ Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma1 N),
      F ∣[(1 : ℤ)] γ' = F := by
    rintro γ' ⟨γ, hγ, rfl⟩
    have hγ0 : γ ∈ CongruenceSubgroup.Gamma0 _ := CongruenceSubgroup.Gamma1_in_Gamma0 _ hγ
    have ha1 : ((γ 0 0 : ℤ) : ZMod N) = 1 := ((CongruenceSubgroup.Gamma1_mem _ γ).mp hγ).1
    rw [hslash γ hγ0, ha1, map_one, inv_one, one_smul]
  obtain ⟨ι, _, c, β, hF⟩ := exists_eq_sum_of_mem_slashSpan' hFspan
  obtain ⟨F₀, hF₀⟩ := GammaOneCuspAux.exists_gamma1_cuspForm_coe_eq h c β F hF hinv
  refine ⟨F₀, ?_, ?_, ?_⟩
  ·
    intro γ hγ τ
    obtain ⟨-, hmod⟩ := isCoprime_and_mul_eq_one hγ
    have hsl := congrFun (hslash γ hγ) τ
    have hSL : (F ∣[(1 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) τ
        = F (γ • τ) * UpperHalfPlane.denom γ τ ^ (-(1 : ℤ)) := ModularForm.SL_slash_apply (k := 1) F γ τ
    rw [hSL, Pi.smul_apply, smul_eq_mul] at hsl
    have hden : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero γ τ
    have hval : F (γ • τ) = (ε ((γ 0 0 : ℤ) : ZMod N))⁻¹ * (UpperHalfPlane.denom γ τ ^ (1 : ℤ) * F τ) := by
      have := congrArg (fun z => z * UpperHalfPlane.denom γ τ ^ (1 : ℤ)) hsl
      rw [mul_assoc, ← zpow_add₀ hden, show (-(1 : ℤ)) + 1 = 0 by norm_num, zpow_zero, mul_one] at this
      rw [this]; ring
    have hinvε : (ε ((γ 0 0 : ℤ) : ZMod N))⁻¹ = ε ((γ 1 1 : ℤ) : ZMod N) := by
      symm
      apply eq_inv_of_mul_eq_one_right
      rw [← map_mul, hmod, map_one]
    rw [hF₀, hval, hinvε, ModularGroup.denom_apply]
  ·
    have hfF : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma1 N → (⇑F₀) ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = ⇑F₀ :=
      fun γ hγ => SlashInvariantForm.slash_action_eqn F₀ _ ⟨γ, hγ, rfl⟩
    obtain ⟨hLleft, hLlev, hLeq⟩ :=
      DihedralWeightOne.weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift hN (⇑F₀) hfF
    funext x
    obtain ⟨γ, x', u, hx', hpos', hu, rfl⟩ := exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hN x
    change fn y _ = _
    rw [hK1 u hu, hleft, hLlev u hu, hLleft, hLeq x' hx' hpos', hF₀]
    exact hread x' hx' hpos'
  ·
    rintro rfl
    have hF0 : F = 0 := by rw [← hF₀, CuspForm.coe_zero]
    exact eq_zero_of_hasReading_zero' hN (by simpa [hF0] using hread) hleft hK1

end S_DihedralWeightOne_exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul
end P2MW
export P2MW.S_DihedralWeightOne_exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul (solution)
