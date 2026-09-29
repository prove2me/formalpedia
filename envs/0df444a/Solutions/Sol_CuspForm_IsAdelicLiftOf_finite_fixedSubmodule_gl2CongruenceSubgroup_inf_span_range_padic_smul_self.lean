-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOf.finite_fixedSubmodule_gl2CongruenceSubgroup_inf_span_range_padic_smul_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/a4f48c72-6c6e-5f57-9cd4-8a23cf2436cb

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_LocalNewvector_CongruenceSubgroupK1
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
import Theorems.Thm_CuspForm_IsAdelicLiftOf_levelZero_inv
import Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOf_finite_fixedSubmodule_gl2CongruenceSubgroup_inf_span_range_padic_smul_self

set_option autoImplicit false

open NumberField AdelicDock IsDedekindDomain

namespace DescentSupportA

private theorem coe_finComponent {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (w : HeightOneSpectrum R) (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ((AdelicLevel.finComponent R K w g) : Matrix (Fin 2) (Fin 2) (w.adicCompletion K))
      = (AdelicLevel.finAdeleEval R K w).mapMatrix
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) := by
  ext i j
  rw [AdelicLevel.finComponent_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    AdelicLevel.finAdeleEval_apply]

private theorem glEq_of_forall_finComponent_eq {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {g h : GL (Fin 2) (FiniteAdeleRing R K)}
    (H : ∀ w : HeightOneSpectrum R, AdelicLevel.finComponent R K w g = AdelicLevel.finComponent R K w h) :
    g = h := by
  refine Matrix.GeneralLinearGroup.ext fun i j => congrFun (congrFun ?_ i) j
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun w => ?_
  rw [← coe_finComponent w g, ← coe_finComponent w h, H w]

private theorem commute_of_finComponent_eq_one (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    {w x : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hw : AdelicLevel.finComponent (𝓞 ℚ) ℚ v w = 1)
    (hx : ∀ w' : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), w' ≠ v →
      AdelicLevel.finComponent (𝓞 ℚ) ℚ w' x = 1) :
    w * x = x * w := by
  refine glEq_of_forall_finComponent_eq fun w' => ?_
  rw [map_mul, map_mul]
  rcases eq_or_ne w' v with rfl | hw'
  · rw [hw, one_mul, mul_one]
  · rw [hx w' hw', mul_one, one_mul]

section S1

private theorem mapMatrix_injective {A B : Type*} [Semiring A] [Semiring B] {f : A →+* B}
    (hf : Function.Injective f) :
    Function.Injective ((RingHom.mapMatrix f : Matrix (Fin 2) (Fin 2) A →+* _)) := fun M N h => by
  ext i j
  exact hf (by simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using congrFun (congrFun h i) j)

private theorem exists_glMap_eq {R : Type*} [CommRing R] {K : Type*} [CommRing K]
    (f : R →+* K) (hf : Function.Injective f) (x : GL (Fin 2) K)
    (hx : ∀ i j, ∃ r, f r = (x : Matrix (Fin 2) (Fin 2) K) i j)
    (hx' : ∀ i j, ∃ r, f r = ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) :
    ∃ c : GL (Fin 2) R, Matrix.GeneralLinearGroup.map (n := Fin 2) f c = x := by
  set M : Matrix (Fin 2) (Fin 2) R := fun i j => Classical.choose (hx i j) with hM
  set M' : Matrix (Fin 2) (Fin 2) R := fun i j => Classical.choose (hx' i j)
  have hMim : f.mapMatrix M = (x : Matrix (Fin 2) (Fin 2) K) :=
    Matrix.ext fun i j => Classical.choose_spec (hx i j)
  have hM'im : f.mapMatrix M' = ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
    Matrix.ext fun i j => Classical.choose_spec (hx' i j)
  have hinj : Function.Injective ((RingHom.mapMatrix f : Matrix (Fin 2) (Fin 2) R →+* _)) :=
    mapMatrix_injective hf
  have hMM' : M * M' = 1 := hinj (by
    rw [map_mul, hMim, hM'im, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have hM'M : M' * M = 1 := hinj (by
    rw [map_mul, hM'im, hMim, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one])
  refine ⟨⟨M, M', hMM', hM'M⟩, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact congrFun (congrFun hMim i) j

end S1

end DescentSupportA

namespace DescentEngine

open NumberField AdelicDock DescentSupportA

variable (p : ℕ) [hp : Fact p.Prime]

private noncomputable abbrev ι : GL (Fin 2) ℤ_[p] →* GL (Fin 2) ℚ_[p] :=
  Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[p] ℚ_[p])

private theorem ι_mem_padicK1_zero (k : GL (Fin 2) ℤ_[p]) : ι p k ∈ LocalNewvector.padicK1 p 0 :=
  ⟨k, rfl, by simp, by simp⟩

private theorem coe_ι (k : GL (Fin 2) ℤ_[p]) :
    ((ι p k : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = (k : Matrix (Fin 2) (Fin 2) ℤ_[p]).map (algebraMap ℤ_[p] ℚ_[p]) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

end DescentEngine

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
  · exact congrArg
      (fun g : GL (Fin 2) (InfiniteAdeleRing ℚ) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) a b) h₁
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

variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

end DescentEngine

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector
open scoped ModularForm

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private noncomputable def slashSpan (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    Submodule ℂ (UpperHalfPlane → ℂ) :=
  Submodule.span ℂ (Set.range fun β : GL (Fin 2) ℚ => (⇑g) ∣[(2 : ℤ)] β.map (Rat.castHom ℝ))

private theorem slash_map_mem_slashSpan (β : GL (Fin 2) ℚ) : (⇑g) ∣[(2 : ℤ)] β.map (Rat.castHom ℝ) ∈ slashSpan g :=
  Submodule.subset_span ⟨β, rfl⟩

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

private theorem continuous_denom (A : GL (Fin 2) ℝ) :
    Continuous fun τ : UpperHalfPlane => UpperHalfPlane.denom A τ := by
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

section S4a

private theorem exists_padicGL_map_eq_finComponent {q : ℕ} [Fact q.Prime] {I : Ideal (𝓞 ℚ)}
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ I) :
    ∃ c : GL (Fin 2) ℤ_[q],
      padicGL q (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) c)
        = finComponent (𝓞 ℚ) ℚ (padicPlace q) u := by
  obtain ⟨hu₁, hu₂⟩ := mem_finiteLevelZero_iff.mp hu
  set cq : GL (Fin 2) ℚ_[q] := Matrix.GeneralLinearGroup.map (n := Fin 2)
    (padicRingEquiv q).symm.toRingHom (finComponent (𝓞 ℚ) ℚ (padicPlace q) u) with hcq
  have hcq_inv : padicGL q cq = finComponent (𝓞 ℚ) ℚ (padicPlace q) u :=
    Matrix.GeneralLinearGroup.ext fun i j => by
      rw [padicGL_apply, hcq, Matrix.GeneralLinearGroup.map_apply]
      exact RingEquiv.apply_symm_apply _ _
  have hex : ∀ (e : GL (Fin 2) ((padicPlace q).adicCompletion ℚ)),
      (∀ i j, (e : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace q).adicCompletionIntegers ℚ) →
      ∀ i j, ∃ r : ℤ_[q], algebraMap ℤ_[q] ℚ_[q] r
        = (Matrix.GeneralLinearGroup.map (n := Fin 2) (padicRingEquiv q).symm.toRingHom e
            : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j := fun e he i j => by
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact ⟨⟨_, (norm_le_one_iff_mem q _).mpr
      ((RingEquiv.apply_symm_apply (padicRingEquiv q) _).symm ▸ he i j)⟩,
      (PadicInt.algebraMap_apply _).trans rfl⟩
  have hmem : ∀ i j, (finComponent (𝓞 ℚ) ℚ (padicPlace q) u
      : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace q).adicCompletionIntegers ℚ := fun i j => by
    rw [finComponent_apply]; exact hu₁.integral i j (padicPlace q)
  have hmem' : ∀ i j, (finComponent (𝓞 ℚ) ℚ (padicPlace q) u⁻¹
      : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace q).adicCompletionIntegers ℚ := fun i j => by
    rw [finComponent_apply]; exact hu₂.integral i j (padicPlace q)
  obtain ⟨c, hc⟩ := DescentSupportA.exists_glMap_eq (algebraMap ℤ_[q] ℚ_[q])
    (IsFractionRing.injective ℤ_[q] ℚ_[q]) cq (hcq ▸ hex _ hmem)
    (by rw [hcq, ← map_inv, ← map_inv]; exact hex _ hmem')
  exact ⟨c, hc ▸ hcq_inv⟩

end S4a

section S4b

private theorem isLevelZeroMatrix_of_finComponent_eq_and {q : ℕ} [Fact q.Prime] {N M : ℕ}
    (hsame : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ padicPlace q →
      idealBound (𝓞 ℚ) (ratLevel N) v = idealBound (𝓞 ℚ) (ratLevel M) v)
    {g u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : IsLevelZeroMatrix (𝓞 ℚ) ℚ (ratLevel N)
      (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)))
    (hgq : finComponent (𝓞 ℚ) ℚ (padicPlace q) g = 1)
    (hgaway : ∀ v ≠ padicPlace q, finComponent (𝓞 ℚ) ℚ v g = finComponent (𝓞 ℚ) ℚ v u) :
    IsLevelZeroMatrix (𝓞 ℚ) ℚ (ratLevel M)
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  refine ⟨fun i j v => ?_, fun v => ?_⟩
  all_goals rcases eq_or_ne v (padicPlace q) with rfl | hv
  · rw [← finComponent_apply, hgq, Units.val_one]
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.one_apply_eq]; exact one_mem _
    · rw [Matrix.one_apply_ne hij]; exact zero_mem _
  · rw [← finComponent_apply, hgaway v hv, finComponent_apply]; exact hu.integral i j v
  · rw [← finComponent_apply, hgq, Units.val_one,
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), map_zero]
    exact zero_le'
  · rw [← finComponent_apply, hgaway v hv, finComponent_apply, ← hsame v hv]
    exact hu.lowerLeft v

private theorem mul_padicToFinAdelic_inv_mem_finiteLevelZero {q : ℕ} [Fact q.Prime] {N M : ℕ}
    (hsame : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ padicPlace q →
      idealBound (𝓞 ℚ) (ratLevel N) v = idealBound (𝓞 ℚ) (ratLevel M) v)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N))
    (c : GL (Fin 2) ℚ_[q]) (hc : finComponent (𝓞 ℚ) ℚ (padicPlace q) u = padicGL q c) :
    u * (padicToFinAdelic q c)⁻¹ ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M) := by
  obtain ⟨hu₁, hu₂⟩ := mem_finiteLevelZero_iff.mp hu
  set g := u * (padicToFinAdelic q c)⁻¹ with hg
  have hgq : finComponent (𝓞 ℚ) ℚ (padicPlace q) g = 1 := by
    rw [hg, map_mul, map_inv, finComponent_padicToFinAdelic_self, hc, mul_inv_cancel]
  have hgaway : ∀ v ≠ padicPlace q,
      finComponent (𝓞 ℚ) ℚ v g = finComponent (𝓞 ℚ) ℚ v u := fun v hv => by
    rw [hg, map_mul, map_inv, finComponent_padicToFinAdelic_of_ne q c hv, inv_one, mul_one]
  rw [mem_finiteLevelZero_iff]
  exact ⟨isLevelZeroMatrix_of_finComponent_eq_and hsame hu₁ hgq hgaway,
    isLevelZeroMatrix_of_finComponent_eq_and hsame hu₂ (g := g⁻¹) (u := u⁻¹)
      (by rw [map_inv, hgq, inv_one])
      (fun v hv => by rw [map_inv, hgaway v hv, map_inv])⟩

end S4b

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

private theorem fn_padic_smul {q : ℕ} [Fact q.Prime] (x : GL (Fin 2) ℚ_[q]) (y : AdelicSpan φ)
    (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn (x • y) z = fn y (z * padicToAdelic q x) := by
  rw [fn, fn, AdelicSpan.padic_smul_def, AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul]

private theorem hasReading_iff (y : AdelicSpan φ) (F : UpperHalfPlane → ℂ) :
    HasReading y F ↔ ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 →
      LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
        fn y h = (F ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I := Iff.rfl

private theorem fn_globalPoints_mul_of_mem_span (hφg : g.IsAdelicLiftOf φ) {q : ℕ} [Fact q.Prime] {y : AdelicSpan φ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self φ))
    (γ : GL (Fin 2) ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ) : fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    rw [fn_padic_smul_self, fn_padic_smul_self, mul_assoc, hφg.left_inv]
  | zero => rfl
  | add y₁ y₂ _ _ ih₁ ih₂ => rw [fn_add, fn_add, ih₁, ih₂]
  | smul c y _ ih => rw [fn_csmul, fn_csmul, ih]

private theorem fn_mul_finEmbed_of_mem_span_of_qtrivial {q : ℕ} [Fact q.Prime]
    (hK₀ : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M), ∀ x, φ (x * finEmbed (𝓞 ℚ) ℚ u) = φ x)
    {y : AdelicSpan φ} (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self φ))
    {w : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hw : w ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M))
    (hwq : finComponent (𝓞 ℚ) ℚ (padicPlace q) w = 1) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn y (z * finEmbed (𝓞 ℚ) ℚ w) = fn y z := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    rw [fn_padic_smul_self, fn_padic_smul_self, padicToAdelic_apply, mul_assoc, ← map_mul,
      DescentSupportA.commute_of_finComponent_eq_one (padicPlace q) hwq
        (fun w' hw' => finComponent_padicToFinAdelic_of_ne q x hw'),
      map_mul, ← mul_assoc, hK₀ w hw]
  | zero => rfl
  | add y₁ y₂ _ _ ih₁ ih₂ => rw [fn_add, fn_add, ih₁, ih₂]
  | smul c y _ ih => rw [fn_csmul, fn_csmul, ih]

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

private theorem glFin_globalPoints_mapGL_mem_finiteLevelZero {N : ℕ} (hN : N ≠ 0)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ γ)) ∈
      finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) := by
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

private theorem exists_eq_sum_of_mem_slashSpan {F : UpperHalfPlane → ℂ} (hF : F ∈ slashSpan g) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (β : ι → GL (Fin 2) ℚ),
      F = ∑ i, c i • ((⇑g) ∣[(2 : ℤ)] (β i).map (Rat.castHom ℝ)) := by
  obtain ⟨l, hl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hF
  refine ⟨l.support, inferInstance, fun i => l i, fun i => (i : GL (Fin 2) ℚ), ?_⟩
  rw [← hl, Finsupp.sum, ← Finset.sum_coe_sort]

end DescentEngine

namespace SlashSums

open scoped ModularForm MatrixGroups Manifold
open UpperHalfPlane OnePoint Matrix.SpecialLinearGroup

private theorem isCusp_SL2Z_map_smul {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) (β : GL (Fin 2) ℚ) :
    IsCusp (β.map (Rat.castHom ℝ) • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  refine ⟨β • c₀, ?_⟩
  have h := OnePoint.map_smul (Rat.castHom ℝ) β c₀
  simpa only [Rat.coe_castHom] using h

private theorem isCusp_SL2Z_of_isCusp_map {Γ : Subgroup SL(2, ℤ)} {c : OnePoint ℝ}
    (hc : IsCusp c (Subgroup.map (mapGL ℝ) Γ)) : IsCusp c 𝒮ℒ :=
  hc.mono (Subgroup.map_le_range _ _)

private theorem isZeroAt_slash_map {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    (β : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsZeroAt ((⇑g) ∣[(2 : ℤ)] β.map (Rat.castHom ℝ)) 2 := by
  rw [← OnePoint.IsZeroAt.smul_iff]
  apply CuspFormClass.zero_at_cusps g
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
  exact isCusp_SL2Z_map_smul hc β

private theorem isZeroAt_sum {I : Type} (s : Finset I) (c : I → ℂ) (f : I → UpperHalfPlane → ℂ)
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

private theorem mdifferentiable_sum {I : Type} (s : Finset I) (c : I → ℂ) (f : I → UpperHalfPlane → ℂ)
    (hf : ∀ i ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => (simp; exact mdifferentiable_const)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ((hf a (Finset.mem_insert_self a s)).const_smul _).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem exists_cuspForm_coe_eq {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    {I : Type} [Fintype I] (c : I → ℂ) (β : I → GL (Fin 2) ℚ) (F : UpperHalfPlane → ℂ)
    (hF : F = ∑ i, c i • ((⇑g) ∣[(2 : ℤ)] (β i).map (Rat.castHom ℝ))) (Γ : Subgroup SL(2, ℤ))
    (hinv : ∀ γ ∈ Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ, F ∣[(2 : ℤ)] γ = F) :
    ∃ h : CuspForm Γ 2, ⇑h = F :=
  ⟨{ toFun := F
     slash_action_eq' := hinv
     holo' := by
       subst hF
       exact mdifferentiable_sum _ _ _ fun i _ => (CuspFormClass.holo g).slash _ _
     zero_at_cusps' := fun hc => by
       subst hF
       exact isZeroAt_sum _ _ _ fun i _ => isZeroAt_slash_map g (β i) (isCusp_SL2Z_of_isCusp_map hc) },
   rfl⟩

end SlashSums

namespace PadicReduction

open Matrix

variable (q : ℕ) [Fact q.Prime]

private theorem glMap_padicInt_injective :
    Function.Injective (GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q])) := by
  apply Units.map_injective
  intro A B hAB
  ext i j
  have hf : Function.Injective (algebraMap ℤ_[q] ℚ_[q]) := IsFractionRing.injective ℤ_[q] ℚ_[q]
  apply hf
  have := congrArg (fun M => M i j) hAB
  simpa [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_comp, MonoidHom.coe_coe] using this

variable (a : ℕ)

private noncomputable def liftK1Fun (k : LocalNewvector.padicK1 q a) : GL (Fin 2) ℤ_[q] :=
  k.2.choose

private theorem glMap_liftK1Fun (k : LocalNewvector.padicK1 q a) :
    GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) (liftK1Fun q a k) = k.1 :=
  (k.2.choose_spec).1

@[simps]
private noncomputable def liftK1 : ↥(LocalNewvector.padicK1 q a) →* GL (Fin 2) ℤ_[q] where
  toFun := liftK1Fun q a
  map_one' := by
    apply glMap_padicInt_injective q
    rw [glMap_liftK1Fun, map_one]
    rfl
  map_mul' := by
    intro k₁ k₂
    apply glMap_padicInt_injective q
    rw [map_mul, glMap_liftK1Fun, glMap_liftK1Fun, glMap_liftK1Fun]
    rfl

private noncomputable def reductionHom (m : ℕ) :
    ↥(LocalNewvector.padicK1 q a) →* GL (Fin 2) (ZMod (q ^ m)) :=
  (GeneralLinearGroup.map (n := Fin 2) (PadicInt.toZModPow m)).comp (liftK1 q a)

private theorem entry_norm_le_of_mem_ker_reductionHom (m : ℕ) (k : LocalNewvector.padicK1 q a)
    (hk : k ∈ (reductionHom q a m).ker) (i j : Fin 2) :
    ‖((k.1 : Matrix (Fin 2) (Fin 2) ℚ_[q]) - 1) i j‖ ≤ (q : ℝ) ^ (-(m : ℤ)) := by
  have hred : GeneralLinearGroup.map (n := Fin 2) (PadicInt.toZModPow m) (liftK1Fun q a k) = 1 := by
    have hk' : (reductionHom q a m) k = 1 := MonoidHom.mem_ker.mp hk
    simpa [reductionHom, liftK1_apply, MonoidHom.comp_apply] using hk'
  have hentry : (PadicInt.toZModPow m) ((liftK1Fun q a k : Matrix (Fin 2) (Fin 2) ℤ_[q]) i j)
      = (1 : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j := by
    have h := congrArg
      (fun g : GL (Fin 2) (ZMod (q ^ m)) => (g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j) hred
    simpa [GeneralLinearGroup.map_apply] using h
  have hk1 : (((k : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) - 1) i j
      = (((liftK1Fun q a k : Matrix (Fin 2) (Fin 2) ℤ_[q]) - 1) i j : ℚ_[q]) := by
    rw [← glMap_liftK1Fun q a k]
    simp only [GeneralLinearGroup.map_apply, PadicInt.algebraMap_apply, Matrix.sub_apply,
      Matrix.one_apply, apply_ite ((↑·) : ℤ_[q] → ℚ_[q]), PadicInt.coe_one, PadicInt.coe_zero,
      PadicInt.coe_sub]
  rw [hk1, ← PadicInt.norm_def, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, Matrix.sub_apply, map_sub, hentry]
  simp only [Matrix.one_apply, apply_ite (PadicInt.toZModPow (p := q) m), map_one, map_zero,
    sub_self]

private theorem finiteIndex_gl2CongruenceSubgroup_subgroupOf_padicK1 (m a : ℕ) :
    ((FLT.SmoothVectors.gl2CongruenceSubgroup q m).subgroupOf
      (LocalNewvector.padicK1 q a)).FiniteIndex := by
  haveI : NeZero (q ^ m) := ⟨pow_ne_zero m (Nat.Prime.ne_zero Fact.out)⟩
  haveI : Finite (reductionHom q a m).range := Subtype.finite
  haveI hker : (reductionHom q a m).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  refine Subgroup.finiteIndex_of_le (H := (reductionHom q a m).ker) ?_
  intro k hk
  rw [Subgroup.mem_subgroupOf, FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff]
  refine ⟨entry_norm_le_of_mem_ker_reductionHom q a m k hk, ?_⟩
  have hkinv : k⁻¹ ∈ (reductionHom q a m).ker := (reductionHom q a m).ker.inv_mem hk
  have := entry_norm_le_of_mem_ker_reductionHom q a m k⁻¹ hkinv
  simpa using this

end PadicReduction

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector
open scoped ModularForm MatrixGroups

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private theorem padic_smul_mem_span {q : ℕ} [Fact q.Prime] (x : GL (Fin 2) ℚ_[q]) {y : AdelicSpan φ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self φ)) :
    x • y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self φ) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x', rfl⟩ := hy
    rw [← mul_smul]
    exact Submodule.subset_span ⟨x * x', rfl⟩
  | zero =>
    rw [smul_zero]
    exact Submodule.zero_mem _
  | add y₁ y₂ _ _ ih₁ ih₂ =>
    rw [smul_add]
    exact Submodule.add_mem _ ih₁ ih₂
  | smul c y _ ih =>
    rw [smul_comm x c y]
    exact Submodule.smul_mem _ c ih

section Principal

variable (q : ℕ) [hq : Fact q.Prime]

private theorem norm_entry_triple_le {A B C : Matrix (Fin 2) (Fin 2) ℚ_[q]} {ε : ℝ} (hε : 0 ≤ ε)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ ε) (hC : ∀ i j, ‖C i j‖ ≤ 1) (i j : Fin 2) :
    ‖(A * B * C) i j‖ ≤ ε := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε fun k _ => ?_
  rw [norm_mul, norm_mul]
  calc ‖A i k‖ * ‖B k l‖ * ‖C l j‖ ≤ 1 * ε * 1 :=
        mul_le_mul (mul_le_mul (hA i k) (hB k l) (norm_nonneg _) zero_le_one) (hC l j) (norm_nonneg _)
          (mul_nonneg zero_le_one hε)
    _ = ε := by rw [one_mul, mul_one]

private theorem norm_entry_ι_le_one (k : GL (Fin 2) ℤ_[q]) (i j : Fin 2) :
    ‖((ι q k : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j‖ ≤ 1 := by
  rw [coe_ι, Matrix.map_apply, PadicInt.algebraMap_apply, ← PadicInt.norm_def]
  exact PadicInt.norm_le_one _

private theorem conj_mem_gl2CongruenceSubgroup {n : ℕ} (k : GL (Fin 2) ℤ_[q]) {m : GL (Fin 2) ℚ_[q]}
    (hm : m ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q n) :
    (ι q k)⁻¹ * m * ι q k ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q n := by
  rw [FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff] at hm ⊢
  have hε : (0 : ℝ) ≤ (q : ℝ) ^ (-(n : ℤ)) := le_of_lt (zpow_pos (by exact_mod_cast hq.out.pos) _)
  have hk : ∀ i j, ‖((ι q k : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j‖ ≤ 1 :=
    norm_entry_ι_le_one q k
  have hk' : ∀ i j, ‖(((ι q k)⁻¹ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j‖ ≤ 1 := by
    rw [← map_inv]
    exact norm_entry_ι_le_one q k⁻¹
  constructor
  · intro i j
    have hexp : (((ι q k)⁻¹ * m * ι q k : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) - 1
        = (((ι q k)⁻¹ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) *
          ((m : Matrix (Fin 2) (Fin 2) ℚ_[q]) - 1) * ((ι q k : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul, Units.val_mul, Units.val_mul]
    rw [hexp]
    exact norm_entry_triple_le q hε hk' hm.1 hk i j
  · intro i j
    have hexp : ((((ι q k)⁻¹ * m * ι q k)⁻¹ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) - 1
        = (((ι q k)⁻¹ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) *
          (((m⁻¹ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) - 1) *
            ((ι q k : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        Units.inv_mul, Units.val_mul, Units.val_mul]
    rw [hexp]
    exact norm_entry_triple_le q hε hk' hm.2 hk i j

private theorem finComponent_glFin_globalPoints_mapGL (γ : SL(2, ℤ)) :
    finComponent (𝓞 ℚ) ℚ (padicPlace q) (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ γ)))
      = padicGL q (ι q (Matrix.SpecialLinearGroup.mapGL ℤ_[q] γ)) := by
  refine Matrix.GeneralLinearGroup.ext fun a b => ?_
  rw [finComponent_apply, padicGL_apply, coe_ι, Matrix.map_apply, PadicInt.algebraMap_apply]
  change (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)
    (((Matrix.SpecialLinearGroup.mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) a b)) (padicPlace q) = _
  have h1 : ((Matrix.SpecialLinearGroup.mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) a b =
      ((γ a b : ℤ) : ℚ) := by
    simp [Matrix.SpecialLinearGroup.mapGL]
  have h2 : ((Matrix.SpecialLinearGroup.mapGL ℤ_[q] γ : GL (Fin 2) ℤ_[q]) : Matrix (Fin 2) (Fin 2) ℤ_[q]) a b
      = ((γ a b : ℤ) : ℤ_[q]) := by
    simp [Matrix.SpecialLinearGroup.mapGL]
  rw [h1, h2, DescentSupportB.algebraMap_intCast_apply_padicPlace_eq]

private theorem dvd_entry_sub_one_of_mem_Gamma {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N)
    (i j : Fin 2) : (N : ℤ) ∣ γ i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j := by
  obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.mp hγ
  have e : ∀ x y : ℤ, ((x : ZMod N) = (y : ZMod N)) → (N : ℤ) ∣ x - y := fun x y hxy =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub y x N).mp hxy.symm
  have d00 : (N : ℤ) ∣ γ 0 0 - 1 := e (γ 0 0) 1 (by rw [Int.cast_one]; exact h00)
  have d01 : (N : ℤ) ∣ γ 0 1 - 0 := e (γ 0 1) 0 (by rw [Int.cast_zero]; exact h01)
  have d10 : (N : ℤ) ∣ γ 1 0 - 0 := e (γ 1 0) 0 (by rw [Int.cast_zero]; exact h10)
  have d11 : (N : ℤ) ∣ γ 1 1 - 1 := e (γ 1 1) 1 (by rw [Int.cast_one]; exact h11)
  fin_cases i <;> fin_cases j
  · simpa using d00
  · simpa using d01
  · simpa using d10
  · simpa using d11

private theorem ι_mapGL_mem_gl2CongruenceSubgroup {N n : ℕ} (hqN : q ^ n ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    ι q (Matrix.SpecialLinearGroup.mapGL ℤ_[q] γ) ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q n := by
  have aux : ∀ {γ : SL(2, ℤ)}, γ ∈ CongruenceSubgroup.Gamma N → ∀ i j,
      ‖(((ι q (Matrix.SpecialLinearGroup.mapGL ℤ_[q] γ) : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) - 1) i j‖
        ≤ (q : ℝ) ^ (-(n : ℤ)) := by
    intro γ hγ i j
    have hentry :
        (((ι q (Matrix.SpecialLinearGroup.mapGL ℤ_[q] γ) : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) - 1) i j
        = ((γ i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℚ_[q]) := by
      rw [Matrix.sub_apply, coe_ι, Matrix.map_apply, PadicInt.algebraMap_apply]
      have h2 : ((Matrix.SpecialLinearGroup.mapGL ℤ_[q] γ : GL (Fin 2) ℤ_[q]) : Matrix (Fin 2) (Fin 2) ℤ_[q]) i j
          = ((γ i j : ℤ) : ℤ_[q]) := by
        simp [Matrix.SpecialLinearGroup.mapGL]
      rw [h2, PadicInt.coe_intCast, Int.cast_sub]
      simp only [Matrix.one_apply]
      split_ifs <;> simp
    rw [hentry]
    refine (Padic.norm_int_le_pow_iff_dvd _ _).mpr ?_
    have h1 : (q : ℤ) ^ n ∣ (N : ℤ) := by exact_mod_cast hqN
    exact h1.trans (dvd_entry_sub_one_of_mem_Gamma hγ i j)
  rw [FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff]
  refine ⟨aux hγ, ?_⟩
  rw [← map_inv, ← map_inv]
  exact aux (Subgroup.inv_mem _ hγ)

private theorem factorization_mul_pow_of_ne (hM : M ≠ 0) (n : ℕ) {ℓ : ℕ} (hℓq : ℓ ≠ q) :
    (M * q ^ n).factorization ℓ = M.factorization ℓ := by
  rw [Nat.factorization_mul hM (pow_ne_zero n hq.out.ne_zero), Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, hq.out.factorization, Finsupp.single_apply, if_neg hℓq.symm, smul_zero, add_zero]

private theorem mem_Gamma0_of_mem_Gamma {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    γ ∈ CongruenceSubgroup.Gamma0 N :=
  CongruenceSubgroup.Gamma0_mem.mpr (CongruenceSubgroup.Gamma_mem.mp hγ).2.2.1

private theorem strip_mem_finiteLevelZero (hM : M ≠ 0) (n : ℕ) {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel (M * q ^ n))) (c : GL (Fin 2) ℚ_[q])
    (hc : finComponent (𝓞 ℚ) ℚ (padicPlace q) u = padicGL q c) :
    u * (padicToFinAdelic q c)⁻¹ ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M) ∧
      finComponent (𝓞 ℚ) ℚ (padicPlace q) (u * (padicToFinAdelic q c)⁻¹) = 1 := by
  have hMn : M * q ^ n ≠ 0 := mul_ne_zero hM (pow_ne_zero n hq.out.ne_zero)
  refine ⟨DescentSupportB.mul_padicToFinAdelic_inv_mem_finiteLevelZero
      (fun v hv => DescentSupportB.idealBound_ratLevel_eq_of_factorization_eq hMn hM
        (fun ℓ _ hℓq => factorization_mul_pow_of_ne q hM n hℓq) v hv) hu c hc, ?_⟩
  rw [map_mul, map_inv, finComponent_padicToFinAdelic_self q, hc, mul_inv_cancel]

private theorem fn_mul_finEmbed_glFin_mapGL_of_mem_Gamma (hM : M ≠ 0)
    (hK₀ : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M), ∀ x, φ (x * finEmbed (𝓞 ℚ) ℚ u) = φ x)
    (n : ℕ) {y : AdelicSpan φ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self φ))
    (hfix : y ∈ fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q n) (AdelicSpan φ))
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma (M * q ^ n)) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn y (z * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ γ))))
      = fn y z := by
  have hMn : M * q ^ n ≠ 0 := mul_ne_zero hM (pow_ne_zero n hq.out.ne_zero)
  set G := glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ γ)) with hGdef
  have hG : G ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel (M * q ^ n)) :=
    glFin_globalPoints_mapGL_mem_finiteLevelZero hMn (mem_Gamma0_of_mem_Gamma hγ)
  set c : GL (Fin 2) ℚ_[q] := ι q (Matrix.SpecialLinearGroup.mapGL ℤ_[q] γ) with hcdef
  have hc : finComponent (𝓞 ℚ) ℚ (padicPlace q) G = padicGL q c := finComponent_glFin_globalPoints_mapGL q γ
  obtain ⟨hw, hwq⟩ := strip_mem_finiteLevelZero q hM n hG c hc
  have hcy : c • y = y :=
    mem_fixedSubmodule_iff.mp hfix c (ι_mapGL_mem_gl2CongruenceSubgroup q (dvd_mul_left (q ^ n) M) hγ)
  have hsplit : G = G * (padicToFinAdelic q c)⁻¹ * padicToFinAdelic q c := by group
  rw [hsplit, map_mul, ← mul_assoc, ← padicToAdelic_apply, ← fn_padic_smul, hcy,
    fn_mul_finEmbed_of_mem_span_of_qtrivial hK₀ hy hw hwq]

private theorem slash_mapGL_eq_of_hasReading {y : AdelicSpan φ} {F : UpperHalfPlane → ℂ} (hF : Continuous F)
    (hread : HasReading y F) (hleft : ∀ γ z, fn y (globalPoints (𝓞 ℚ) ℚ γ * z) = fn y z) (γ : SL(2, ℤ))
    (hright : ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ
      (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ γ)))⁻¹) = fn y z) :
    F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = F := by
  set δ : GL (Fin 2) ℚ := Matrix.SpecialLinearGroup.mapGL ℚ γ with hδ
  refine eq_of_forall_slash_apply_I (continuous_slash hF 2 _) hF fun h hh hpos => ?_
  have hpos' : LanglandsTunnell.ratArchGL2 (archPart δ * h) ∈ Matrix.GLPos (Fin 2) ℝ := by
    rw [ratArch_archPart_mul, hδ, map_castHom_mapGL]
    exact Subgroup.mul_mem _ (mapGL_mem_GLPos γ) hpos
  have hread' := (hasReading_iff y F).mp hread
  have h1 := hread' (archPart δ * h) (glFin_archPart_mul hh δ) hpos'
  rw [ratArch_archPart_mul, hδ, map_castHom_mapGL, SlashAction.slash_mul] at h1
  have h2 : archPart δ * h
      = globalPoints (𝓞 ℚ) ℚ δ * (h * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ))⁻¹) := by
    rw [archPart, mul_assoc, ← map_inv, finEmbed_mul_comm_of_glFin_eq_one hh]
  rw [h2, hleft, hright] at h1
  rw [← h1, hread' h hh hpos]

private theorem eq_of_hasReading {y : AdelicSpan φ} {F F' : UpperHalfPlane → ℂ} (hF : Continuous F)
    (hF' : Continuous F') (h : HasReading y F) (h' : HasReading y F') : F = F' :=
  eq_of_forall_slash_apply_I hF hF' fun x hx hpos => ((hasReading_iff y F).mp h x hx hpos).symm.trans
    ((hasReading_iff y F').mp h' x hx hpos)

private theorem exists_cuspForm_hasReading (hM : M ≠ 0) (hφg : g.IsAdelicLiftOf φ)
    (hK₀ : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M), ∀ x, φ (x * finEmbed (𝓞 ℚ) ℚ u) = φ x)
    (n : ℕ) {y : AdelicSpan φ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self φ))
    (hfix : y ∈ fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q n) (AdelicSpan φ)) :
    ∃ hF : CuspForm (CongruenceSubgroup.Gamma (M * q ^ n)) 2, HasReading y ⇑hF := by
  haveI : NeZero M := ⟨hM⟩
  obtain ⟨F, hFspan, hread⟩ := exists_hasReading_of_mem_span hM hφg hy
  obtain ⟨I, _, c, β, hF⟩ := exists_eq_sum_of_mem_slashSpan hFspan
  have hcont : Continuous F := continuous_of_mem_slashSpan hFspan
  obtain ⟨hF', hh⟩ := SlashSums.exists_cuspForm_coe_eq g c β F hF (CongruenceSubgroup.Gamma (M * q ^ n))
    (by
      rintro _ ⟨γ, hγ, rfl⟩
      refine slash_mapGL_eq_of_hasReading hcont hread (fn_globalPoints_mul_of_mem_span hφg hy) γ fun z => ?_
      rw [← map_inv, ← map_inv, ← map_inv]
      exact fn_mul_finEmbed_glFin_mapGL_of_mem_Gamma q hM hK₀ n hy hfix (Subgroup.inv_mem _ hγ) z)
  refine ⟨hF', ?_⟩
  rw [hh]
  exact hread

private theorem eq_zero_of_forall_hasReading_smul_zero (hM : M ≠ 0) (hφg : g.IsAdelicLiftOf φ)
    (hK₀ : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M), ∀ x, φ (x * finEmbed (𝓞 ℚ) ℚ u) = φ x)
    (n : ℕ) {y : AdelicSpan φ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self φ))
    (hfix : y ∈ fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q n) (AdelicSpan φ))
    (hread : ∀ k ∈ padicK1 q 0, ∃ k' ∈ padicK1 q 0,
      k'⁻¹ * k ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q n ∧ HasReading (k' • y) 0) :
    y = 0 := by
  have hMn : M * q ^ n ≠ 0 := mul_ne_zero hM (pow_ne_zero n hq.out.ne_zero)
  refine AdelicSpan.ext φ (AdelicFnCarrier.ext fun z => ?_)
  obtain ⟨γ, h, u, hh, hpos, hu, rfl⟩ := exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hMn z
  have hu₀ : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel (M * q ^ n)) := finiteLevelOne_le_finiteLevelZero (𝓞 ℚ) ℚ _ hu
  obtain ⟨c, hc⟩ := DescentSupportB.exists_padicGL_map_eq_finComponent (q := q) hu₀
  obtain ⟨hw, hwq⟩ := strip_mem_finiteLevelZero q hM n hu₀ (ι q c) hc.symm
  obtain ⟨k', hk', hmem, hread0⟩ := hread (ι q c) (ι_mem_padicK1_zero q c)
  have hk'c : (k'⁻¹ * ι q c) • y = y := mem_fixedSubmodule_iff.mp hfix _ hmem
  have hcy : ι q c • y = k' • y :=
    calc ι q c • y = k' • (k'⁻¹ * ι q c) • y := by rw [← mul_smul, mul_inv_cancel_left]
      _ = k' • y := by rw [hk'c]
  have hsplit : u = u * (padicToFinAdelic q (ι q c))⁻¹ * padicToFinAdelic q (ι q c) := by group
  change fn y _ = fn (0 : AdelicSpan φ) _
  rw [fn_zero, mul_assoc, fn_globalPoints_mul_of_mem_span hφg hy, hsplit, map_mul, ← mul_assoc,
    ← padicToAdelic_apply, ← fn_padic_smul, hcy,
    fn_mul_finEmbed_of_mem_span_of_qtrivial hK₀ (padic_smul_mem_span k' hy) hw hwq,
    (hasReading_iff (k' • y) 0).mp hread0 h hh hpos, SlashAction.zero_slash]
  rfl

end Principal

end DescentEngine

open DescentEngine NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm LocalNewvector in
theorem solution
    {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hgΦ : g.IsAdelicLiftOf Φ)
    (n : ℕ) :
    Module.Finite ℂ
      ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q n)
          (LocalNewvector.AdelicSpan Φ) ⊓
        Submodule.span ℂ
          (Set.range fun h : GL (Fin 2) ℚ_[q] => h • LocalNewvector.AdelicSpan.self Φ)) := by
  classical
  have hM : M ≠ 0 := NeZero.ne M
  have hK₀ := hgΦ.levelZero_inv hM
  haveI : NeZero (M * q ^ n) := ⟨mul_ne_zero hM (pow_ne_zero n (Fact.out : q.Prime).ne_zero)⟩

  set K₀ : Subgroup (GL (Fin 2) ℚ_[q]) := padicK1 q 0 with hK₀def
  set H : Subgroup K₀ := (FLT.SmoothVectors.gl2CongruenceSubgroup q n).subgroupOf K₀ with hHdef
  haveI : H.FiniteIndex := PadicReduction.finiteIndex_gl2CongruenceSubgroup_subgroupOf_padicK1 q n 0
  haveI : Fintype (K₀ ⧸ H) := Fintype.ofFinite _

  haveI : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma (M * q ^ n)) 2) :=
    CuspForm.finiteDimensional_of_isArithmetic _ 2
  set W := LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q n) (AdelicSpan Φ) ⊓
    Submodule.span ℂ (Set.range fun h : GL (Fin 2) ℚ_[q] => h • LocalNewvector.AdelicSpan.self Φ) with hWdef

  have hWsmul : ∀ k ∈ padicK1 q 0, ∀ y ∈ W, k • y ∈ W := by
    rintro k ⟨k₀, rfl, -, -⟩ y hy
    obtain ⟨hyfix, hyspan⟩ := Submodule.mem_inf.mp hy
    refine Submodule.mem_inf.mpr ⟨mem_fixedSubmodule_iff.mpr fun m hm => ?_, padic_smul_mem_span _ hyspan⟩
    have hconj := mem_fixedSubmodule_iff.mp hyfix _ (conj_mem_gl2CongruenceSubgroup q k₀ hm)
    calc m • ι q k₀ • y = ι q k₀ • ((ι q k₀)⁻¹ * m * ι q k₀) • y := by
          rw [← mul_smul, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
      _ = ι q k₀ • y := by rw [hconj]

  have key : ∀ y ∈ W, ∀ j : K₀ ⧸ H, ∃ hF : CuspForm (CongruenceSubgroup.Gamma (M * q ^ n)) 2,
      HasReading (((Quotient.out j : K₀) : GL (Fin 2) ℚ_[q]) • y) ⇑hF := fun y hy j => by
    obtain ⟨hfix, hspan⟩ := Submodule.mem_inf.mp (hWsmul _ (Quotient.out j : K₀).2 y hy)
    exact exists_cuspForm_hasReading q hM hgΦ hK₀ n hspan hfix
  choose! rd hrd using key
  have hrd_unique : ∀ y ∈ W, ∀ (j : K₀ ⧸ H) (hF : CuspForm (CongruenceSubgroup.Gamma (M * q ^ n)) 2),
      HasReading (((Quotient.out j : K₀) : GL (Fin 2) ℚ_[q]) • y) ⇑hF → rd y j = hF := fun y hy j hF hread =>
    DFunLike.ext' (eq_of_hasReading (CuspFormClass.holo (rd y j)).continuous (CuspFormClass.holo hF).continuous
      (hrd y hy j) hread)

  let L : ↥W →ₗ[ℂ] (K₀ ⧸ H → CuspForm (CongruenceSubgroup.Gamma (M * q ^ n)) 2) :=
    { toFun := fun y j => rd y.1 j
      map_add' := fun y y' => funext fun j => by
        have h := (hrd y.1 y.2 j).add (hrd y'.1 y'.2 j)
        rw [← smul_add, ← CuspForm.coe_add] at h
        exact hrd_unique (y.1 + y'.1) (Submodule.add_mem _ y.2 y'.2) j _ h
      map_smul' := fun c y => funext fun j => by
        have h := (hrd y.1 y.2 j).smul c
        rw [(smul_comm ((Quotient.out j : K₀) : GL (Fin 2) ℚ_[q]) c y.1).symm, ← CuspForm.IsGLPos.coe_smul] at h
        exact hrd_unique (c • y.1) (Submodule.smul_mem _ c y.2) j _ h }

  refine FiniteDimensional.of_injective L fun y y' hyy => ?_
  rw [← sub_eq_zero]
  refine Subtype.ext ?_
  have hd : (y - y').1 ∈ W := (y - y').2
  obtain ⟨hfix, hspan⟩ := Submodule.mem_inf.mp hd
  refine eq_zero_of_forall_hasReading_smul_zero q hM hgΦ hK₀ n hspan hfix fun k hk => ?_
  refine ⟨((Quotient.out (QuotientGroup.mk (⟨k, hk⟩ : K₀) : K₀ ⧸ H) : K₀) : GL (Fin 2) ℚ_[q]),
    (Quotient.out (QuotientGroup.mk (⟨k, hk⟩ : K₀) : K₀ ⧸ H) : K₀).2, ?_, ?_⟩
  · have h1 : (Quotient.out (QuotientGroup.mk (⟨k, hk⟩ : K₀) : K₀ ⧸ H) : K₀)⁻¹ * ⟨k, hk⟩ ∈ H :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' _)
    have h2 := Subgroup.mem_subgroupOf.mp h1
    simpa using h2
  · have hL : L (y - y') = 0 := by rw [map_sub, hyy, sub_self]
    have hj := congrFun hL (QuotientGroup.mk (⟨k, hk⟩ : K₀))
    change rd (y - y').1 _ = 0 at hj
    have := hrd (y - y').1 hd (QuotientGroup.mk (⟨k, hk⟩ : K₀))
    rw [hj, CuspForm.coe_zero] at this
    exact this

end S_CuspForm_IsAdelicLiftOf_finite_fixedSubmodule_gl2CongruenceSubgroup_inf_span_range_padic_smul_self
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOf_finite_fixedSubmodule_gl2CongruenceSubgroup_inf_span_range_padic_smul_self (solution)
