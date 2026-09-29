-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOf.exists_hasNebentypus_isAdelicLiftOfGamma1_of_mem_span_fnTwist_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/a2cdbfc7-7299-5811-9476-0d545ee99417

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_LocalNewvector_ConductorDatum
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
import Theorems.Thm_CuspForm_IsAdelicLiftOf_apply_mul_finEmbed_levelZero_eq_of_mem_span_fnTwist_of_fixed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOf_exists_hasNebentypus_isAdelicLiftOfGamma1_of_mem_span_fnTwist_of_fixed
p2m_attr_erase "simp" "AutomorphicForm.rightTranslationEmbed_smul_apply"

set_option autoImplicit false

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

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private noncomputable def slashSpan (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) : Submodule ℂ (UpperHalfPlane → ℂ) :=
  Submodule.span ℂ (Set.range fun β : GL (Fin 2) ℚ => (⇑g) ∣[(2 : ℤ)] β.map (Rat.castHom ℝ))

private theorem slash_map_mem_slashSpan (β : GL (Fin 2) ℚ) : (⇑g) ∣[(2 : ℤ)] β.map (Rat.castHom ℝ) ∈ slashSpan g :=
  Submodule.subset_span ⟨β, rfl⟩

private theorem coe_mem_slashSpan : (⇑g : UpperHalfPlane → ℂ) ∈ slashSpan g := by
  simpa [SlashAction.slash_one] using slash_map_mem_slashSpan (g := g) 1

private def HasReading (y : AdelicSpan φ) (F : UpperHalfPlane → ℂ) : Prop :=
  ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 → LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
    (AdelicSpan.toFn φ y).toFn h = (F ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I

private theorem hasReading_zero : HasReading (0 : AdelicSpan φ) (0 : UpperHalfPlane → ℂ) := by
  intro h _ _
  rw [SlashAction.zero_slash]
  rfl

private theorem HasReading.add {y₁ y₂ : AdelicSpan φ} {F₁ F₂ : UpperHalfPlane → ℂ} (h₁ : HasReading y₁ F₁)
    (h₂ : HasReading y₂ F₂) : HasReading (y₁ + y₂) (F₁ + F₂) := by
  intro h hh hpos
  rw [SlashAction.add_slash, Pi.add_apply, ← h₁ h hh hpos, ← h₂ h hh hpos]
  rfl

private theorem HasReading.smul {y : AdelicSpan φ} {F : UpperHalfPlane → ℂ} (hy : HasReading y F) (c : ℂ) :
    HasReading (c • y) (c • F) := by
  intro h hh hpos
  rw [ModularForm.smul_slash, Pi.smul_apply, σ_apply_of_det_pos ((Matrix.mem_glpos _).mp hpos), smul_eq_mul,
    ← hy h hh hpos]
  rfl

private theorem glFin_conj_eq_one (δ : GL (Fin 2) ℚ) {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : glFin (𝓞 ℚ) ℚ h = 1) :
    glFin (𝓞 ℚ) ℚ ((globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * h * globalPoints (𝓞 ℚ) ℚ δ) = 1 := by
  rw [map_mul, map_mul, hh, mul_one, map_inv, inv_mul_cancel]

private theorem exists_hasReading_padic_smul_self (hM : M ≠ 0) (hφg : g.IsAdelicLiftOf φ) {q : ℕ} [Fact q.Prime]
    (x : GL (Fin 2) ℚ_[q]) :
    ∃ F ∈ slashSpan g, HasReading (x • AdelicSpan.self φ) F := by
  obtain ⟨δ, a, u, ha, hapos, hu, hdec⟩ :=
    exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hM (padicToAdelic q x)

  have harch : LanglandsTunnell.ratArchGL2 a = (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) δ)⁻¹ := by
    have h0 : LanglandsTunnell.ratArchGL2 (padicToAdelic q x) = 1 := by
      rw [padicToAdelic_apply]; exact ratArch_finEmbed _
    rw [hdec, ratArch_mul, ratArch_mul, ratArch_finEmbed, mul_one, ratArch_globalPoints] at h0
    exact eq_inv_of_mul_eq_one_right h0
  refine ⟨(⇑g) ∣[(2 : ℤ)] δ⁻¹.map (Rat.castHom ℝ), slash_map_mem_slashSpan δ⁻¹, ?_⟩
  intro h hh hpos
  have hval : (AdelicSpan.toFn φ (x • AdelicSpan.self φ)).toFn h = φ (h * padicToAdelic q x) := by
    rw [AdelicSpan.padic_smul_def, AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul, AdelicSpan.toFn_self,
      AdelicFnCarrier.toFn_mk]
  rw [hval, hdec, ← mul_assoc, ← mul_assoc, hφg.level_inv u hu]
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
  rw [hre, hφg.left_inv, hφg.apply_eq _ hh' hpos', hratarch, SlashAction.slash_mul, map_inv]

private theorem exists_hasReading_of_mem_span (hM : M ≠ 0) (hφg : g.IsAdelicLiftOf φ) {q : ℕ} [Fact q.Prime]
    {y : AdelicSpan φ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self φ)) :
    ∃ F ∈ slashSpan g, HasReading y F := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    exact exists_hasReading_padic_smul_self hM hφg x
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

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}

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
    exact continuous_slash (CuspFormClass.holo g).continuous 2 _
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

private theorem eq_of_forall_slash_apply_I {F G : UpperHalfPlane → ℂ} (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 → LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
      (F ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I
        = (G ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I) :
    F = G := by
  refine Continuous.ext_on dense_ratPoints hF hG ?_
  rintro z ⟨hx, hy⟩
  obtain ⟨h, hfin, hpos, hz⟩ := exists_glFin_eq_one_and_smul_I_eq z hx hy
  have hdet : (0 : ℝ) < (LanglandsTunnell.ratArchGL2 h).det.val := (Matrix.mem_glpos _).mp hpos
  have key := hFG h hfin hpos
  rw [ModularForm.slash_apply, ModularForm.slash_apply, σ_apply_of_det_pos hdet, σ_apply_of_det_pos hdet, hz]
    at key
  have hne : |(LanglandsTunnell.ratArchGL2 h).det.val| ^ ((2 : ℤ) - 1)
      * UpperHalfPlane.denom (LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I ^ (-(2 : ℤ)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast zpow_ne_zero _ (abs_ne_zero.mpr hdet.ne'))
      (zpow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ _))
  rw [mul_assoc, mul_assoc] at key
  exact mul_right_cancel₀ hne key

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

private theorem map_algebraMap_scalar_eq_centralGL {q : ℕ} [Fact q.Prime] (d : ℤ_[q]ˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q])
        (Units.map (algebraMap ℤ_[q] (Matrix (Fin 2) (Fin 2) ℤ_[q])).toMonoidHom d)
      = LocalNewvector.centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom d) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply]
  simp only [LocalNewvector.centralGL, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, Matrix.algebraMap_matrix_apply,
    apply_ite (algebraMap ℤ_[q] ℚ_[q]), map_zero]
  rfl

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

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private abbrev fn (y : AdelicSpan φ) : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := (AdelicSpan.toFn φ y).toFn

private theorem fn_padic_smul_self {q : ℕ} [Fact q.Prime] (x : GL (Fin 2) ℚ_[q]) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn (x • AdelicSpan.self φ) z = φ (z * padicToAdelic q x) := by
  rw [fn, AdelicSpan.padic_smul_def, AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul, AdelicSpan.toFn_self,
    AdelicFnCarrier.toFn_mk]

private theorem fn_add (y₁ y₂ : AdelicSpan φ) (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn (y₁ + y₂) z = fn y₁ z + fn y₂ z := rfl

private theorem fn_csmul (c : ℂ) (y : AdelicSpan φ) (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn (c • y) z = c * fn y z := rfl

private theorem fn_zero (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn (0 : AdelicSpan φ) z = 0 := rfl

private theorem fn_padic_smul {q : ℕ} [Fact q.Prime] (x : GL (Fin 2) ℚ_[q]) (y : AdelicSpan φ) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn (x • y) z = fn y (z * padicToAdelic q x) := by
  rw [fn, fn, AdelicSpan.padic_smul_def, AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul]

private theorem hasReading_iff (y : AdelicSpan φ) (F : UpperHalfPlane → ℂ) :
    HasReading y F ↔ ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 →
      LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
        fn y h = (F ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I := Iff.rfl

end DescentEngine

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector
open scoped ModularForm

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

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

noncomputable section

namespace TwistEngineAux

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector HeckeCharacter

section Archimedean

variable (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)

private def archEquiv (w : InfinitePlace ℚ) : w.Completion ≃+* ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)

private def archHom : ℝ →* AdeleRing (𝓞 ℚ) ℚ where
  toFun s := ((fun w => (archEquiv w).symm s : InfiniteAdeleRing ℚ), (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))
  map_one' := Prod.ext (funext fun w => map_one (archEquiv w).symm) rfl
  map_mul' s t :=
    Prod.ext (funext fun w => map_mul (archEquiv w).symm s t) (one_mul (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)).symm

private theorem archHom_fst_apply (s : ℝ) (w : InfinitePlace ℚ) : (archHom s).1 w = (archEquiv w).symm s := rfl

private theorem archHom_snd (s : ℝ) : (archHom s).2 = 1 := rfl

private theorem apply_map_archHom_eq_one (hη : IsFiniteOrderHeckeChar ℚ η) (u : ℝˣ) (hu : 0 < (u : ℝ)) :
    η (Units.map archHom u) = 1 := by
  obtain ⟨n, hn, hηn⟩ := isOfFinOrder_iff_pow_eq_one.mp hη.isOfFinOrder
  have hs : 0 < (u : ℝ) ^ ((n : ℝ)⁻¹) := Real.rpow_pos_of_pos hu _
  have hu' : u = (Units.mk0 _ hs.ne') ^ n := by
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Real.rpow_inv_natCast_pow hu.le hn.ne']
  have h1 : η (Units.map archHom (Units.mk0 _ hs.ne')) ^ n = 1 := by
    have h2 := congrArg (fun χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ => χ (Units.map archHom (Units.mk0 _ hs.ne'))) hηn
    simpa using h2
  rw [hu', map_pow, map_pow, h1]

private theorem det_eq_map_archHom {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : glFin (𝓞 ℚ) ℚ h = 1) :
    h.det = Units.map archHom (LanglandsTunnell.ratArchGL2 h).det := by
  have h1 : ((LanglandsTunnell.ratArchGL2 h).det : ℝ) = archEquiv default ((h.det : AdeleRing (𝓞 ℚ) ℚ).1 default) := by
    simp only [LanglandsTunnell.ratArchGL2, Matrix.GeneralLinearGroup.map_det, archComponent, glArch, Units.coe_map]
    rfl
  have h2 : (h.det : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := by
    have h3 := congrArg (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) => (g.det : FiniteAdeleRing (𝓞 ℚ) ℚ)) hh
    simp only [glFin, Matrix.GeneralLinearGroup.map_det, Units.coe_map, map_one, Units.val_one] at h3
    exact h3
  ext1
  refine Prod.ext ?_ ?_
  · funext w
    have hw : w = default := Subsingleton.elim w default
    subst hw
    show (h.det : AdeleRing (𝓞 ℚ) ℚ).1 default = (archEquiv default).symm ((LanglandsTunnell.ratArchGL2 h).det : ℝ)
    rw [h1, RingEquiv.symm_apply_apply]
  · exact h2

private theorem eta_det_eq_one_of_glFin_eq_one_of_glPos (hη : IsFiniteOrderHeckeChar ℚ η)
    {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ) :
    (η h.det : ℂ) = 1 := by
  rw [det_eq_map_archHom hh, apply_map_archHom_eq_one η hη _ ((Matrix.mem_glpos _).mp hpos), Units.val_one]

end Archimedean

end TwistEngineAux

end

namespace TwistEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector HeckeCharacter
open DescentEngine TwistEngineAux

section TwistedEngine

open scoped ModularForm

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
variable {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable (ηc : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
variable {q : ℕ} [Fact q.Prime]

private theorem exists_hasReading_padic_smul_self_twist (hM : M ≠ 0) (hφg : g.IsAdelicLiftOf Φ)
    (hη : IsFiniteOrderHeckeChar ℚ ηc) (x : GL (Fin 2) ℚ_[q]) :
    ∃ F ∈ slashSpan g, HasReading (φ := fnTwist ℚ ηc Φ) (x • AdelicSpan.self (fnTwist ℚ ηc Φ)) F := by
  obtain ⟨F₀, hF₀span, hread₀⟩ := exists_hasReading_padic_smul_self hM hφg x
  refine ⟨chiDet (𝓞 ℚ) ℚ ηc (padicToAdelic q x) • F₀, Submodule.smul_mem _ _ hF₀span, ?_⟩
  intro h hh hpos
  change fn (x • AdelicSpan.self (fnTwist ℚ ηc Φ)) h
    = ((chiDet (𝓞 ℚ) ℚ ηc (padicToAdelic q x) • F₀)
        ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I
  rw [fn_padic_smul_self, fnTwist_apply, ModularForm.smul_slash, Pi.smul_apply,
    σ_apply_of_det_pos ((Matrix.mem_glpos _).mp hpos), smul_eq_mul]
  have hR : (F₀ ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I = Φ (h * padicToAdelic q x) := by
    have hrd := hread₀ h hh hpos
    change fn (x • AdelicSpan.self Φ) h = _ at hrd
    rw [fn_padic_smul_self] at hrd
    exact hrd.symm
  rw [hR, chiDet, map_mul, map_mul, Units.val_mul,
    eta_det_eq_one_of_glFin_eq_one_of_glPos ηc hη hh hpos, one_mul, chiDet]

private theorem exists_hasReading_of_mem_span_twist (hM : M ≠ 0) (hφg : g.IsAdelicLiftOf Φ)
    (hη : IsFiniteOrderHeckeChar ℚ ηc)
    {y : AdelicSpan (fnTwist ℚ ηc Φ)}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self (fnTwist ℚ ηc Φ))) :
    ∃ F ∈ slashSpan g, HasReading y F := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨x, rfl⟩ := hy; exact exists_hasReading_padic_smul_self_twist ηc hM hφg hη x
  | zero => exact ⟨0, Submodule.zero_mem _, hasReading_zero⟩
  | add y₁ y₂ _ _ ih₁ ih₂ =>
    obtain ⟨F₁, hF₁, h₁⟩ := ih₁; obtain ⟨F₂, hF₂, h₂⟩ := ih₂
    exact ⟨F₁ + F₂, Submodule.add_mem _ hF₁ hF₂, h₁.add h₂⟩
  | smul c y _ ih => obtain ⟨F, hF, h⟩ := ih; exact ⟨c • F, Submodule.smul_mem _ c hF, h.smul c⟩

end TwistedEngine

end TwistEngine

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

private lemma isZeroAt_slash_map {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    (β : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsZeroAt ((⇑g) ∣[(2 : ℤ)] β.map (Rat.castHom ℝ)) 2 := by
  rw [← OnePoint.IsZeroAt.smul_iff]
  apply CuspFormClass.zero_at_cusps g
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
  exact isCusp_SL2Z_map_smul hc β

private lemma isZeroAt_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → UpperHalfPlane → ℂ)
    {x : OnePoint ℝ} (hf : ∀ i ∈ s, x.IsZeroAt (f i) 2) :
    x.IsZeroAt (∑ i ∈ s, c i • f i) 2 := by
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
    {M N : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    {ι : Type} [Fintype ι] (c : ι → ℂ) (β : ι → GL (Fin 2) ℚ)
    (F : UpperHalfPlane → ℂ)
    (hF : F = ∑ i, c i • ((⇑g) ∣[(2 : ℤ)] (β i).map (Rat.castHom ℝ)))
    (hinv : ∀ γ ∈ Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma1 N),
      F ∣[(2 : ℤ)] γ = F) :
    ∃ h : CuspForm (CongruenceSubgroup.Gamma1 N) 2, ⇑h = F :=
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

namespace TwistEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector HeckeCharacter
open DescentEngine TwistEngineAux

section LevelArith

private theorem level_ne_zero {M : ℕ} (hM : M ≠ 0) (q a : ℕ) (hq : q.Prime) :
    q ^ max a 1 * (M / q ^ M.factorization q) ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ hq.ne_zero) (Nat.ordCompl_pos q hM).ne'

private theorem pow_dvd_level (M q a : ℕ) : q ^ max a 1 ∣ q ^ max a 1 * (M / q ^ M.factorization q) :=
  Dvd.intro _ rfl

private theorem dvd_level (M q a : ℕ) : q ∣ q ^ max a 1 * (M / q ^ M.factorization q) :=
  Dvd.dvd.mul_right (dvd_pow_self q (by omega)) _

end LevelArith

section PadicUnits

variable (q : ℕ) [Fact q.Prime]

private noncomputable abbrev red (n : ℕ) : ℤ_[q]ˣ →* (ZMod (q ^ n))ˣ := Units.map (PadicInt.toZModPow n).toMonoidHom

private theorem norm_natCast_eq_one_of_not_dvd {n : ℕ} (hn : ¬ q ∣ n) : ‖(n : ℚ_[q])‖ = 1 :=
  Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hn)

private noncomputable def natUnit {n : ℕ} (hn : ¬ q ∣ n) : ℤ_[q]ˣ := PadicInt.mkUnits (norm_natCast_eq_one_of_not_dvd q hn)

private theorem coe_natUnit {n : ℕ} (hn : ¬ q ∣ n) : ((natUnit q hn : ℤ_[q]) : ℚ_[q]) = n := by
  rw [natUnit, PadicInt.mkUnits_eq]

private theorem red_val_eq_of_coe_eq_natCast {n m : ℕ} (u : ℤ_[q]ˣ) (hu : ((u : ℤ_[q]) : ℚ_[q]) = m) :
    ((red q n u : (ZMod (q ^ n))ˣ) : ZMod (q ^ n)) = m := by
  have hun : (u : ℤ_[q]) = m := Subtype.ext (by rw [hu, PadicInt.coe_natCast])
  rw [Units.coe_map]
  show PadicInt.toZModPow n (u : ℤ_[q]) = m
  rw [hun, map_natCast]

private theorem not_dvd_val {n : ℕ} (r : (ZMod (q ^ n))ˣ) (hn : 1 ≤ n) : ¬ q ∣ (r : ZMod (q ^ n)).val := by
  intro hdvd
  have hcop := ZMod.val_coe_unit_coprime r
  have hq : q ∣ q ^ n := dvd_pow_self q (by omega)
  have := Nat.Coprime.coprime_dvd_left hdvd (Nat.Coprime.coprime_dvd_right hq hcop)
  exact (Fact.out : q.Prime).ne_one ((Nat.coprime_self q).mp this)

private noncomputable def liftUnit {n : ℕ} (hn : 1 ≤ n) (r : (ZMod (q ^ n))ˣ) : ℤ_[q]ˣ := natUnit q (not_dvd_val q r hn)

private theorem red_liftUnit {n : ℕ} (hn : 1 ≤ n) : Function.RightInverse (liftUnit q hn) (red q n) := by
  intro r
  haveI : NeZero (q ^ n) := ⟨pow_ne_zero n (Fact.out : q.Prime).ne_zero⟩
  apply Units.ext
  rw [liftUnit, red_val_eq_of_coe_eq_natCast q _ (coe_natUnit q _), ZMod.natCast_zmod_val]

private theorem isUnit_intCast_of_not_dvd {a : ℤ} (ha : ¬ (q : ℤ) ∣ a) : IsUnit (a : ℤ_[q]) := by
  rw [PadicInt.isUnit_iff]
  exact le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => ha ((PadicInt.norm_int_lt_one_iff_dvd a).mp h))

end PadicUnits

section MainD2

open scoped ModularForm

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
variable {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable (ηc : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
variable {q : ℕ} [Fact q.Prime]

private theorem exists_eq_sum_of_mem_slashSpan' {F : UpperHalfPlane → ℂ} (hF : F ∈ slashSpan g) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (β : ι → GL (Fin 2) ℚ),
      F = ∑ i, c i • ((⇑g) ∣[(2 : ℤ)] (β i).map (Rat.castHom ℝ)) := by
  obtain ⟨l, hl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hF
  refine ⟨l.support, inferInstance, fun i => l i, fun i => (i : GL (Fin 2) ℚ), ?_⟩
  rw [← hl, Finsupp.sum, ← Finset.sum_coe_sort]

variable {a : ℕ} {θ : ℤ_[q]ˣ →* ℂˣ} {y : AdelicSpan (fnTwist ℚ ηc Φ)}

private theorem fn_mul_finEmbed_of_mem_finiteLevelOne (hM : M ≠ 0)
    (hK0 : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel (q ^ max a 1 * (M / q ^ M.factorization q))),
      ∀ d : ℤ_[q]ˣ,
        Valued.v (((u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1) (padicPlace q)
            - padicRingEquiv q ((d : ℤ_[q]) : ℚ_[q]))
          ≤ idealBound (𝓞 ℚ) (ratLevel (q ^ max a 1 * (M / q ^ M.factorization q))) (padicPlace q) →
        ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = (θ d : ℂ) * fn y z)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel (q ^ max a 1 * (M / q ^ M.factorization q))))
    (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn y (z * finEmbed (𝓞 ℚ) ℚ u) = fn y z := by
  have _ := hM
  have h := hK0 u (finiteLevelOne_le_finiteLevelZero (𝓞 ℚ) ℚ _ hu) 1 (by
    rw [Units.val_one, PadicInt.coe_one, map_one]
    exact (mem_finiteLevelOne_iff.mp hu).1.lowerRight (padicPlace q)) z
  rwa [map_one, Units.val_one, one_mul] at h

private theorem theta_eq_one_of_sub_one_mem
    (hfix : y ∈ fixedSubmodule (padicK1 q a) (AdelicSpan (fnTwist ℚ ηc Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ, centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y = (θ u : ℂ) • y)
    (hy₀ : y ≠ 0) (t : ℤ_[q]ˣ) (ht : (t : ℤ_[q]) - 1 ∈ Ideal.span {(q : ℤ_[q]) ^ max a 1}) :
    θ t = 1 := by
  have hmem : centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom t) ∈ padicK1 q a := by
    refine congruenceK1_antitone (le_max_left a 1) ?_
    rw [LocalNewvector.mem_congruenceK1_iff]
    refine ⟨Units.map (algebraMap ℤ_[q] (Matrix (Fin 2) (Fin 2) ℤ_[q])).toMonoidHom t,
      DescentSupportB.map_algebraMap_scalar_eq_centralGL t, ?_, ?_⟩
    · simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.algebraMap_matrix_apply,
        if_neg (show (1 : Fin 2) ≠ 0 by decide)]
      exact Ideal.zero_mem _
    · simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.algebraMap_matrix_apply]
      exact ht
  have h1 : (θ t : ℂ) • y = y := by rw [← hcent t, mem_fixedSubmodule_iff.mp hfix _ hmem]
  have h2 : ((θ t : ℂ) - 1) • y = 0 := by rw [sub_smul, one_smul, h1, sub_self]
  have h3 : (θ t : ℂ) - 1 = 0 := (smul_eq_zero.mp h2).resolve_right hy₀
  exact Units.val_eq_one.mp (sub_eq_zero.mp h3)

private theorem ker_red_le
    (hfix : y ∈ fixedSubmodule (padicK1 q a) (AdelicSpan (fnTwist ℚ ηc Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ, centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y = (θ u : ℂ) • y)
    (hy₀ : y ≠ 0) : (red q (max a 1)).ker ≤ θ.ker := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  refine theta_eq_one_of_sub_one_mem ηc hfix hcent hy₀ u ?_
  have hval : PadicInt.toZModPow (max a 1) (u : ℤ_[q]) = 1 := by
    have := congrArg (fun r : (ZMod (q ^ max a 1))ˣ => (r : ZMod (q ^ max a 1))) hu
    simp only [Units.coe_map, Units.val_one] at this
    exact this
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, hval, sub_self]

private noncomputable def thetaBar
    (hfix : y ∈ fixedSubmodule (padicK1 q a) (AdelicSpan (fnTwist ℚ ηc Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ, centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y = (θ u : ℂ) • y)
    (hy₀ : y ≠ 0) : (ZMod (q ^ max a 1))ˣ →* ℂˣ :=
  (red q (max a 1)).liftOfRightInverse (liftUnit q (le_max_right a 1)) (red_liftUnit q (le_max_right a 1))
    ⟨θ, ker_red_le ηc hfix hcent hy₀⟩

private theorem thetaBar_red
    (hfix : y ∈ fixedSubmodule (padicK1 q a) (AdelicSpan (fnTwist ℚ ηc Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ, centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y = (θ u : ℂ) • y)
    (hy₀ : y ≠ 0) (u : ℤ_[q]ˣ) :
    thetaBar ηc hfix hcent hy₀ (red q (max a 1) u) = θ u := by
  rw [thetaBar, MonoidHom.liftOfRightInverse_comp_apply]

private noncomputable def eps
    (hfix : y ∈ fixedSubmodule (padicK1 q a) (AdelicSpan (fnTwist ℚ ηc Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ, centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y = (θ u : ℂ) • y)
    (hy₀ : y ≠ 0) : DirichletCharacter ℂ (q ^ max a 1 * (M / q ^ M.factorization q)) :=
  DirichletCharacter.changeLevel (pow_dvd_level M q a) (MulChar.ofUnitHom (thetaBar ηc hfix hcent hy₀)⁻¹)

private theorem eps_coe_units
    (hfix : y ∈ fixedSubmodule (padicK1 q a) (AdelicSpan (fnTwist ℚ ηc Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ, centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y = (θ u : ℂ) • y)
    (hy₀ : y ≠ 0) (x : (ZMod (q ^ max a 1 * (M / q ^ M.factorization q)))ˣ) :
    eps ηc hfix hcent hy₀ (x : ZMod (q ^ max a 1 * (M / q ^ M.factorization q)))
      = ((thetaBar ηc hfix hcent hy₀ (ZMod.unitsMap (pow_dvd_level M q a) x))⁻¹ : ℂˣ) := by
  rw [eps, DirichletCharacter.changeLevel_def, MulChar.ofUnitHom_coe, MonoidHom.comp_apply,
    MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq, Equiv.apply_symm_apply, MonoidHom.inv_apply]

private theorem eps_apply_of_mul_eq_one (hM : M ≠ 0)
    (hfix : y ∈ fixedSubmodule (padicK1 q a) (AdelicSpan (fnTwist ℚ ηc Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ, centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y = (θ u : ℂ) • y)
    (hy₀ : y ≠ 0) (a' d : ℤ)
    (had : (a' : ZMod (q ^ max a 1 * (M / q ^ M.factorization q))) * d = 1)
    (t : ℤ_[q]ˣ) (ht : (t : ℤ_[q]) = a') :
    eps ηc hfix hcent hy₀ (d : ZMod (q ^ max a 1 * (M / q ^ M.factorization q))) = θ t := by
  set N : ℕ := q ^ max a 1 * (M / q ^ M.factorization q) with hN
  have hda : (d : ZMod N) * a' = 1 := by rw [mul_comm]; exact had
  set x : (ZMod N)ˣ := ⟨(d : ZMod N), (a' : ZMod N), hda, had⟩ with hx
  have hxval : ((x : (ZMod N)ˣ) : ZMod N) = d := rfl
  have hux : (ZMod.unitsMap (pow_dvd_level M q a) x)⁻¹ = red q (max a 1) t := by
    apply Units.ext
    rw [← map_inv, ZMod.unitsMap_val, Units.coe_map]
    show ZMod.cast ((x⁻¹ : (ZMod N)ˣ) : ZMod N) = PadicInt.toZModPow (max a 1) (t : ℤ_[q])
    rw [show ((x⁻¹ : (ZMod N)ˣ) : ZMod N) = a' from rfl, ZMod.cast_intCast (pow_dvd_level M q a), ht,
      map_intCast]
  rw [← hxval, eps_coe_units, ← map_inv, hux, thetaBar_red]

private theorem eps_natCast (hM : M ≠ 0)
    (hfix : y ∈ fixedSubmodule (padicK1 q a) (AdelicSpan (fnTwist ℚ ηc Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ, centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y = (θ u : ℂ) • y)
    (hy₀ : y ≠ 0) (d : ℕ) (hd : d.Coprime (q ^ max a 1 * (M / q ^ M.factorization q)))
    (u : ℤ_[q]ˣ) (hu : ((u : ℤ_[q]) : ℚ_[q]) = d) :
    eps ηc hfix hcent hy₀ (d : ZMod (q ^ max a 1 * (M / q ^ M.factorization q))) = ((θ u)⁻¹ : ℂˣ) := by
  set N : ℕ := q ^ max a 1 * (M / q ^ M.factorization q) with hN
  have hxval : ((ZMod.unitOfCoprime d hd : (ZMod N)ˣ) : ZMod N) = d := ZMod.coe_unitOfCoprime d hd
  have hux : ZMod.unitsMap (pow_dvd_level M q a) (ZMod.unitOfCoprime d hd) = red q (max a 1) u := by
    apply Units.ext
    rw [ZMod.unitsMap_val, hxval, ZMod.cast_natCast (pow_dvd_level M q a),
      red_val_eq_of_coe_eq_natCast q u hu]
  rw [← hxval, eps_coe_units, hux, thetaBar_red]

private theorem slash_eq_theta_smul (hM : M ≠ 0) {F : UpperHalfPlane → ℂ} (hF : Continuous F)
    (hread : HasReading y F)
    (hleft : ∀ γ z, fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z)
    (hK0 : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel (q ^ max a 1 * (M / q ^ M.factorization q))),
      ∀ d : ℤ_[q]ˣ,
        Valued.v (((u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1) (padicPlace q)
            - padicRingEquiv q ((d : ℤ_[q]) : ℚ_[q]))
          ≤ idealBound (𝓞 ℚ) (ratLevel (q ^ max a 1 * (M / q ^ M.factorization q))) (padicPlace q) →
        ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = (θ d : ℂ) * fn y z)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 (q ^ max a 1 * (M / q ^ M.factorization q)))
    (t : ℤ_[q]ˣ) (ht : (t : ℤ_[q]) = ((γ 0 0 : ℤ) : ℤ_[q])) :
    F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = (θ t : ℂ) • F := by
  set N : ℕ := q ^ max a 1 * (M / q ^ M.factorization q) with hNdef
  have hN : N ≠ 0 := level_ne_zero hM q a Fact.out
  set δ : GL (Fin 2) ℚ := Matrix.SpecialLinearGroup.mapGL ℚ γ with hδ
  refine eq_of_forall_slash_apply_I (continuous_slash hF 2 _) (hF.const_smul ((θ t : ℂ))) fun h hh hpos => ?_
  have hpos' : LanglandsTunnell.ratArchGL2 (archPart δ * h) ∈ Matrix.GLPos (Fin 2) ℝ := by
    rw [ratArch_archPart_mul, hδ, map_castHom_mapGL]
    exact Subgroup.mul_mem _ (mapGL_mem_GLPos γ) hpos
  have hread' := (hasReading_iff y F).mp hread
  have h1 := hread' (archPart δ * h) (glFin_archPart_mul hh δ) hpos'
  rw [ratArch_archPart_mul, hδ, map_castHom_mapGL, SlashAction.slash_mul] at h1
  rw [← hδ] at h1
  have hG : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ) ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) :=
    glFin_globalPoints_mapGL_mem_finiteLevelZero hN hγ
  have h2 : archPart δ * h
      = globalPoints (𝓞 ℚ) ℚ δ * (h * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ))⁻¹) := by
    rw [archPart, mul_assoc, ← map_inv, finEmbed_mul_comm_of_glFin_eq_one hh]

  have hval : Valued.v ((((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ))⁻¹ :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
          (padicPlace q) - padicRingEquiv q ((t : ℤ_[q]) : ℚ_[q]))
      ≤ idealBound (𝓞 ℚ) (ratLevel N) (padicPlace q) := by
    have hentry : (((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ))⁻¹ :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
          = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (((γ 0 0 : ℤ) : ℚ)) := by
      rw [← map_inv, ← map_inv, glFin_globalPoints_apply, hδ, ← map_inv]
      congr 1
      have hmat : ((Matrix.SpecialLinearGroup.mapGL ℚ γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
          = ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := rfl
      rw [hmat, Matrix.map_apply, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      simp
    rw [hentry, DescentSupportB.algebraMap_intCast_apply_padicPlace_eq q, ← ht, sub_self, Valuation.map_zero]
    exact zero_le'
  rw [h2, hleft, hK0 _ (Subgroup.inv_mem _ hG) t hval] at h1
  rw [← h1, hread' h hh hpos, ModularForm.smul_slash, Pi.smul_apply, smul_eq_mul,
    σ_apply_of_det_pos ((Matrix.mem_glpos _).mp hpos)]

private theorem eq_zero_of_hasReading_zero' (hM : M ≠ 0) (hread : HasReading y 0)
    (hleft : ∀ γ z, fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z)
    (hK1 : ∀ u ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel (q ^ max a 1 * (M / q ^ M.factorization q))),
      ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = fn y z) :
    y = 0 := by
  have hN : q ^ max a 1 * (M / q ^ M.factorization q) ≠ 0 := level_ne_zero hM q a Fact.out
  refine AdelicSpan.ext _ (AdelicFnCarrier.ext fun z => ?_)
  obtain ⟨γ, h, u, hh, hpos, hu, rfl⟩ := exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hN z
  change fn y _ = fn (0 : AdelicSpan (fnTwist ℚ ηc Φ)) _
  rw [fn_zero, hK1 u hu, hleft, (hasReading_iff y 0).mp hread h hh hpos, SlashAction.zero_slash]
  rfl

end MainD2

end TwistEngine

open DescentEngine TwistEngine NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm LocalNewvector HeckeCharacter in
open scoped ModularForm in
theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime]
    (η' : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hη : HeckeCharacter.IsFiniteOrderHeckeChar ℚ η')
    (b : ℕ) (hηb : HeckeCharacter.AdmitsModulus ℚ η' (AdelicDock.ratLevel (q ^ b)))
    (a : ℕ) (θ : ℤ_[q]ˣ →* ℂˣ)
    (y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η' Φ))
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η' Φ)))
    (hy₀ : y ≠ 0)
    (hfix : y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a)
      (LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η' Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ,
      LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y = (θ u : ℂ) • y) :
    ∃ (ε : DirichletCharacter ℂ (q ^ max a 1 * (M / q ^ M.factorization q)))
      (F : CuspForm (CongruenceSubgroup.Gamma1 (q ^ max a 1 * (M / q ^ M.factorization q))) 2),
      F ≠ 0 ∧ CuspForm.HasNebentypus ε F ∧
      (∀ d : ℕ, d.Coprime (q ^ max a 1 * (M / q ^ M.factorization q)) →
        ∀ u : ℤ_[q]ˣ, ((u : ℤ_[q]) : ℚ_[q]) = d →
          ε (d : ZMod (q ^ max a 1 * (M / q ^ M.factorization q))) = ((θ u)⁻¹ : ℂˣ)) ∧
      CuspForm.IsAdelicLiftOfGamma1 F
        (LocalNewvector.AdelicSpan.toFn (AutomorphicForm.fnTwist ℚ η' Φ) y).toFn := by
  have hM : M ≠ 0 := NeZero.ne M
  have hq : q.Prime := Fact.out
  have hN : q ^ max a 1 * (M / q ^ M.factorization q) ≠ 0 := level_ne_zero hM q a hq

  obtain ⟨hleft, hK0⟩ :=
    hΦg.apply_mul_finEmbed_levelZero_eq_of_mem_span_fnTwist_of_fixed q η' hη.isIdeleClassChar b hηb a θ y hy
      hfix hcent
  have hK1 : ∀ u ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel (q ^ max a 1 * (M / q ^ M.factorization q))),
      ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = fn y z :=
    fun u hu z => fn_mul_finEmbed_of_mem_finiteLevelOne η' hM hK0 hu z

  obtain ⟨F, hFspan, hread⟩ := exists_hasReading_of_mem_span_twist η' hM hΦg hη hy
  have hFcont : Continuous F := continuous_of_mem_slashSpan hFspan

  have hslash : ∀ γ ∈ CongruenceSubgroup.Gamma0 (q ^ max a 1 * (M / q ^ M.factorization q)),
      ∀ (t : ℤ_[q]ˣ), (t : ℤ_[q]) = ((γ 0 0 : ℤ) : ℤ_[q]) →
        F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = (θ t : ℂ) • F :=
    fun γ hγ t ht => slash_eq_theta_smul η' hM hFcont hread hleft hK0 hγ t ht

  have hunit : ∀ γ ∈ CongruenceSubgroup.Gamma0 (q ^ max a 1 * (M / q ^ M.factorization q)),
      IsUnit (((γ 0 0 : ℤ) : ℤ_[q])) ∧
        ((γ 0 0 : ℤ) : ZMod (q ^ max a 1 * (M / q ^ M.factorization q))) * (γ 1 1 : ℤ) = 1 := by
    intro γ hγ
    have hc : ((γ 1 0 : ℤ) : ZMod (q ^ max a 1 * (M / q ^ M.factorization q))) = 0 :=
      CongruenceSubgroup.Gamma0_mem.mp hγ
    have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := Matrix.SpecialLinearGroup.det_coe γ
      rw [Matrix.det_fin_two] at this
      exact this
    have hmod : ((γ 0 0 : ℤ) : ZMod (q ^ max a 1 * (M / q ^ M.factorization q))) * (γ 1 1 : ℤ) = 1 := by
      have := congrArg (fun z : ℤ => (z : ZMod (q ^ max a 1 * (M / q ^ M.factorization q)))) hdet
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, mul_zero, sub_zero] at this
      exact this
    refine ⟨isUnit_intCast_of_not_dvd q fun hqa => ?_, hmod⟩
    have hqc : (q : ℤ) ∣ γ 1 0 := by
      have hNc := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
      exact (Int.natCast_dvd_natCast.mpr (dvd_level M q a)).trans hNc
    have h1 : (q : ℤ) ∣ 1 := by
      rw [← hdet]
      exact dvd_sub (hqa.mul_right _) (hqc.mul_left _)
    have h1' : q ∣ 1 := by exact_mod_cast h1
    exact hq.ne_one (Nat.dvd_one.mp h1')

  have hinv : ∀ γ' ∈ Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma1 (q ^ max a 1 * (M / q ^ M.factorization q))), F ∣[(2 : ℤ)] γ' = F := by
    rintro γ' ⟨γ, hγ, rfl⟩
    have hγ0 : γ ∈ CongruenceSubgroup.Gamma0 _ := CongruenceSubgroup.Gamma1_in_Gamma0 _ hγ
    obtain ⟨hu, -⟩ := hunit γ hγ0
    have ht1 : θ hu.unit = 1 := by
      refine theta_eq_one_of_sub_one_mem η' hfix hcent hy₀ hu.unit ?_
      rw [IsUnit.unit_spec]
      have ha1 : ((γ 0 0 : ℤ) : ZMod (q ^ max a 1 * (M / q ^ M.factorization q))) = 1 :=
        ((CongruenceSubgroup.Gamma1_mem _ γ).mp hγ).1
      have hdvdZ : ((q ^ max a 1 * (M / q ^ M.factorization q) : ℕ) : ℤ) ∣ (γ 0 0 : ℤ) - 1 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_one, ha1, sub_self]
      obtain ⟨k, hk⟩ := (Int.natCast_dvd_natCast.mpr (pow_dvd_level M q a) |>.trans hdvdZ)
      refine Ideal.mem_span_singleton.mpr ⟨(k : ℤ_[q]), ?_⟩
      have := congrArg (fun z : ℤ => (z : ℤ_[q])) hk
      push_cast at this ⊢
      exact this
    rw [hslash γ hγ0 hu.unit (IsUnit.unit_spec hu), ht1, Units.val_one, one_smul]
  obtain ⟨ι, _, c, β, hF⟩ := exists_eq_sum_of_mem_slashSpan' hFspan
  obtain ⟨F₀, hF₀⟩ := GammaOneCuspAux.exists_gamma1_cuspForm_coe_eq g c β F hF hinv
  refine ⟨eps η' hfix hcent hy₀, F₀, ?_, ?_, ?_, ?_⟩
  ·
    rintro rfl
    apply hy₀
    have hF0 : F = 0 := by rw [← hF₀, CuspForm.coe_zero]
    exact eq_zero_of_hasReading_zero' η' hM (by simpa [hF0] using hread) hleft hK1
  ·
    intro γ hγ τ
    obtain ⟨hu, hmod⟩ := hunit γ hγ
    have hsl := congrFun (hslash γ hγ hu.unit (IsUnit.unit_spec hu)) τ
    have hSL : (F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) τ
        = F (γ • τ) * UpperHalfPlane.denom γ τ ^ (-(2 : ℤ)) := ModularForm.SL_slash_apply (k := 2) F γ τ
    rw [hSL, Pi.smul_apply, smul_eq_mul] at hsl
    have hden : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero γ τ
    have hval : F (γ • τ) = (θ hu.unit : ℂ) * (UpperHalfPlane.denom γ τ ^ (2 : ℤ) * F τ) := by
      have := congrArg (fun z => z * UpperHalfPlane.denom γ τ ^ (2 : ℤ)) hsl
      rw [mul_assoc, ← zpow_add₀ hden, show (-(2 : ℤ)) + 2 = 0 by norm_num, zpow_zero, mul_one] at this
      rw [this]; ring
    rw [hF₀, hval, eps_apply_of_mul_eq_one η' hM hfix hcent hy₀ (γ 0 0) (γ 1 1) hmod hu.unit
      (IsUnit.unit_spec hu), ModularGroup.denom_apply]
  ·
    intro d hd u hu
    exact eps_natCast η' hM hfix hcent hy₀ d hd u hu
  ·
    refine ⟨hleft, hK1, fun h hh hpos => ?_⟩
    rw [hF₀]
    exact hread h hh hpos

end S_CuspForm_IsAdelicLiftOf_exists_hasNebentypus_isAdelicLiftOfGamma1_of_mem_span_fnTwist_of_fixed
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOf_exists_hasNebentypus_isAdelicLiftOfGamma1_of_mem_span_fnTwist_of_fixed (solution)
