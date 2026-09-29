-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOfGamma1.memLp_two_restrict_productionPinsGeneral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/1f0091d7-e6e9-5a77-9d43-89ba42e6896c

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOfGamma1_memLp_two_restrict_productionPinsGeneral

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

noncomputable section

namespace Ws41
namespace Lift134

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

local notation "𝔾" => GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)

theorem isReal_rat_infinitePlace (v : InfinitePlace ℚ) : v.IsReal := IsTotallyReal.isReal v

def ratArchHom : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom).comp
    ((archComponent ℚ default).comp (glArch (𝓞 ℚ) ℚ))

theorem ratArchHom_apply (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ratArchHom g = LanglandsTunnell.ratArchGL2 g := rfl

theorem ratArch_mul (g g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (g * g') = LanglandsTunnell.ratArchGL2 g * LanglandsTunnell.ratArchGL2 g' := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, ← ratArchHom_apply, map_mul]

theorem ratArch_inv (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 g⁻¹ = (LanglandsTunnell.ratArchGL2 g)⁻¹ := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, map_inv]

theorem ratArch_eq_one_of_glArch_eq_one {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    LanglandsTunnell.ratArchGL2 u = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [hu, map_one, map_one]

theorem ratArch_finEmbed (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (AdelicDock.finEmbed (𝓞 ℚ) ℚ u) = 1 :=
  ratArch_eq_one_of_glArch_eq_one (AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ u)

theorem ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ) = GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom.comp
      ((archEval ℚ default).comp ((adeleArch (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))))
      ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = (Rat.castHom ℝ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j)
  rw [eq_ratCast, eq_ratCast]

theorem ratArch_globalPoints_mapGL (ε : SL(2, ℤ)) :
    LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε)) =
      (ε : GL (Fin 2) ℝ) := by
  rw [ratArch_globalPoints]
  exact Matrix.SpecialLinearGroup.map_mapGL (S := ℚ) (T := ℝ) ε

theorem det_ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    ((LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ)).det.val : ℝ) =
      (((GeneralLinearGroup.det γ : ℚˣ) : ℚ) : ℝ) := by
  rw [ratArch_globalPoints, GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_coe, eq_ratCast]

theorem exists_algebraMap_eq_of_mem_integralFiniteAdeles {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {q : K}
    (hq : algebraMap K (FiniteAdeleRing R K) q ∈ integralFiniteAdeles R K) :
    ∃ r : R, algebraMap R K r = q := by
  have h : ∀ v : HeightOneSpectrum R, v.valuation K q ≤ 1 := fun v => by
    have h1 := hq v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      show (algebraMap K (FiniteAdeleRing R K) q) v = ((q : K) : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
    exact h1
  exact HeightOneSpectrum.mem_integers_of_valuation_le_one K q h

theorem exists_intCast_eq_of_mem_integralFiniteAdeles {q : ℚ}
    (hq : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_mem_integralFiniteAdeles hq
  exact ⟨Rat.ringOfIntegersEquiv r, by rw [← hr, Rat.ringOfIntegersEquiv_apply_coe]⟩

theorem glFin_globalPoints_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl

theorem exists_mapGL_eq_of_mem_finiteIntegralGL2 {γ : GL (Fin 2) ℚ}
    (hint : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ)
    (hpos : 0 < ((Matrix.GeneralLinearGroup.det γ : ℚˣ) : ℚ)) :
    ∃ δ : SL(2, ℤ), Matrix.SpecialLinearGroup.mapGL ℚ δ = γ := by
  rw [mem_finiteIntegralGL2_iff] at hint
  obtain ⟨hγ, hγinv⟩ := hint
  have hγ' : ∀ i j, ∃ n : ℤ, (n : ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℚ) i j := fun i j =>
    exists_intCast_eq_of_mem_integralFiniteAdeles (by rw [← glFin_globalPoints_apply]; exact hγ i j)
  have hγinv' : ∀ i j, ∃ n : ℤ, (n : ℚ) = ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j :=
    fun i j => exists_intCast_eq_of_mem_integralFiniteAdeles (by
      rw [← glFin_globalPoints_apply, map_inv, map_inv]; exact hγinv i j)
  choose a ha using hγ'
  choose b hb using hγinv'
  set A : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j => a i j with hA
  set B : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j => b i j with hB
  have hAmap : A.map (Int.castRingHom ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j; simp [hA, ha]
  have hBmap : B.map (Int.castRingHom ℚ) = ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j; simp [hB, hb]
  have hAB : A * B = 1 := by
    have hinj : Function.Injective fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom ℚ) :=
      Matrix.map_injective (f := ⇑(Int.castRingHom ℚ)) Int.cast_injective
    apply hinj
    dsimp only
    rw [Matrix.map_mul, hAmap, hBmap, Matrix.map_one _ (map_zero _) (map_one _),
      ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdetAB : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  have hdetQ : ((A.det : ℤ) : ℚ) = ((Matrix.GeneralLinearGroup.det γ : ℚˣ) : ℚ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← hAmap]
    exact (RingHom.map_det (Int.castRingHom ℚ) A)
  have hdetA : A.det = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdetAB with h1 | h1
    · exact h1
    · exfalso
      rw [← hdetQ, h1] at hpos
      norm_num at hpos
  refine ⟨⟨A, hdetA⟩, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  change (algebraMap ℤ ℚ) (A i j) = _
  rw [← hAmap, Matrix.map_apply]
  rfl

theorem exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne {M : ℕ} (hM : M ≠ 0)
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

variable {M : ℕ}

theorem apply_decomp {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφg : g.IsAdelicLiftOf φ) {γ : GL (Fin 2) ℚ} {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ)
    (hk : k ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M)) :
    φ (globalPoints (𝓞 ℚ) ℚ γ * h * AdelicDock.finEmbed (𝓞 ℚ) ℚ k) = ((⇑g) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I := by
  rw [mul_assoc, hφg.left_inv, hφg.level_inv k hk, hφg.apply_eq h hh hpos]

abbrev archPart (k : 𝔾) : 𝔾 := adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ k)

abbrev finPart (k : 𝔾) : 𝔾 := AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ k)

theorem eq_of_glArch_eq_of_glFin_eq {g g' : 𝔾} (ha : glArch (𝓞 ℚ) ℚ g = glArch (𝓞 ℚ) ℚ g')
    (hf : glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g') : g = g' := by
  refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
  · have := congrFun (congrFun (congrArg
      (fun m : GL (Fin 2) (InfiniteAdeleRing ℚ) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))) ha) i) j
    rwa [glArch_apply, glArch_apply] at this
  · have := congrFun (congrFun (congrArg
      (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))) hf) i) j
    rwa [glFin_apply, glFin_apply] at this

theorem glArch_archPart (k : 𝔾) : glArch (𝓞 ℚ) ℚ (archPart k) = glArch (𝓞 ℚ) ℚ k :=
  glArch_adelicArchGLIncl ℚ _

theorem glFin_archPart (k : 𝔾) : glFin (𝓞 ℚ) ℚ (archPart k) = 1 :=
  glFin_adelicArchGLIncl ℚ _

theorem glArch_finPart (k : 𝔾) : glArch (𝓞 ℚ) ℚ (finPart k) = 1 :=
  AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ _

theorem glFin_finPart (k : 𝔾) : glFin (𝓞 ℚ) ℚ (finPart k) = glFin (𝓞 ℚ) ℚ k :=
  AdelicDock.glFin_finEmbed (𝓞 ℚ) ℚ _

theorem archPart_mul_finPart (k : 𝔾) : archPart k * finPart k = k :=
  eq_of_glArch_eq_of_glFin_eq (by rw [map_mul, glArch_archPart, glArch_finPart, mul_one])
    (by rw [map_mul, glFin_archPart, glFin_finPart, one_mul])

theorem archPart_mul_finPart_comm (k k' : 𝔾) : archPart k * finPart k' = finPart k' * archPart k :=
  eq_of_glArch_eq_of_glFin_eq (by rw [map_mul, map_mul, glArch_archPart, glArch_finPart, mul_one, one_mul])
    (by rw [map_mul, map_mul, glFin_archPart, glFin_finPart, one_mul, mul_one])

theorem finPart_eq_self_of_glArch_eq_one {u : 𝔾} (hu : glArch (𝓞 ℚ) ℚ u = 1) : finPart u = u :=
  eq_of_glArch_eq_of_glFin_eq (by rw [glArch_finPart, hu]) (glFin_finPart u)

theorem ratArch_archPart (k : 𝔾) : LanglandsTunnell.ratArchGL2 (archPart k) = LanglandsTunnell.ratArchGL2 k := by
  unfold LanglandsTunnell.ratArchGL2
  rw [glArch_archPart]

theorem continuous_ratArch : Continuous LanglandsTunnell.ratArchGL2 := by
  have hcont : Continuous
      (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom := by
    have : ⇑(InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom
        = InfinitePlace.Completion.extensionEmbeddingOfIsReal (isReal_rat_infinitePlace default) := by
      funext x; rfl
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous
  have hmap : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2)
      (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom) :=
    Continuous.units_map _ ((continuous_id.matrix_map hcont) :
      Continuous fun m : Matrix (Fin 2) (Fin 2) _ => m.map _)
  exact hmap.comp ((continuous_archComponent ℚ default).comp (continuous_glArch (𝓞 ℚ) ℚ))

theorem continuous_entry (i j : Fin 2) : Continuous fun h : GL (Fin 2) ℝ => (((h : Matrix (Fin 2) (Fin 2) ℝ) i j :
    ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp (Units.continuous_val.matrix_elem i j)

theorem continuous_denom_I : Continuous fun h : GL (Fin 2) ℝ => denom h UpperHalfPlane.I := by
  show Continuous fun h : GL (Fin 2) ℝ =>
    (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * UpperHalfPlane.I + (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℝ) : ℂ)
  exact ((continuous_entry 1 0).mul continuous_const).add (continuous_entry 1 1)

theorem continuous_num_I : Continuous fun h : GL (Fin 2) ℝ => num h UpperHalfPlane.I := by
  show Continuous fun h : GL (Fin 2) ℝ =>
    (((h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) : ℂ) * UpperHalfPlane.I + (((h : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) : ℂ)
  exact ((continuous_entry 0 0).mul continuous_const).add (continuous_entry 0 1)

theorem continuous_det_val : Continuous fun h : GL (Fin 2) ℝ => h.det.val := by
  show Continuous fun h : GL (Fin 2) ℝ => (Matrix.GeneralLinearGroup.det h).val
  simp_rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact Units.continuous_val.matrix_det

theorem isOpen_detPos : IsOpen {h : GL (Fin 2) ℝ | 0 < h.det.val} :=
  isOpen_lt continuous_const continuous_det_val

theorem continuousOn_coe_smul_I :
    ContinuousOn (fun h : GL (Fin 2) ℝ => ((h • UpperHalfPlane.I : ℍ) : ℂ)) {h | 0 < h.det.val} := by
  refine ContinuousOn.congr (f := fun h : GL (Fin 2) ℝ => num h UpperHalfPlane.I / denom h UpperHalfPlane.I) ?_ ?_
  · exact (continuous_num_I.div continuous_denom_I fun h => denom_ne_zero h _).continuousOn
  · intro h hh
    exact coe_smul_of_det_pos hh _

variable {M : ℕ}

def archV (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2) (h : GL (Fin 2) ℝ) : ℂ :=
  ((⇑f) ∣[(2 : ℤ)] h) UpperHalfPlane.I

theorem archV_eq_of_det_pos (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2) (h : GL (Fin 2) ℝ) (hh : 0 < h.det.val) :
    archV f h = f (h • UpperHalfPlane.I) * (((h.det.val : ℝ) : ℂ)) ^ (1 : ℤ) * denom h UpperHalfPlane.I ^ (-2 : ℤ) := by
  have h' : 0 < ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rwa [← Matrix.GeneralLinearGroup.val_det_apply]
  have hσ : ∀ w : ℂ, σ h w = w := fun w => by simp [σ, h']
  unfold archV
  rw [ModularForm.slash_apply, hσ, abs_of_pos hh]
  norm_num

theorem continuousOn_archV (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2) :
    ContinuousOn (archV f) {h : GL (Fin 2) ℝ | 0 < h.det.val} := by
  have hdet : Continuous fun h : GL (Fin 2) ℝ => (((h.det.val : ℝ) : ℂ)) := Complex.continuous_ofReal.comp continuous_det_val
  have hdet0 : ∀ h : GL (Fin 2) ℝ, (((h.det.val : ℝ) : ℂ)) ≠ 0 := fun h => by exact_mod_cast h.det.ne_zero
  have hf : Continuous (⇑f : ℍ → ℂ) := f.holo'.continuous
  have hsmul : ContinuousOn (fun h : GL (Fin 2) ℝ => (h • UpperHalfPlane.I : ℍ)) {h | 0 < h.det.val} :=
    UpperHalfPlane.isEmbedding_coe.continuousOn_iff.mpr continuousOn_coe_smul_I
  refine ContinuousOn.congr (f := fun h : GL (Fin 2) ℝ => f (h • UpperHalfPlane.I)
      * (((h.det.val : ℝ) : ℂ)) ^ (1 : ℤ) * denom h UpperHalfPlane.I ^ (-2 : ℤ))
    ?_ fun h hh => archV_eq_of_det_pos f h hh
  refine ((hf.comp_continuousOn hsmul).mul ?_).mul ?_
  · exact (hdet.zpow₀ _ fun h => Or.inl (hdet0 h)).continuousOn
  · exact (continuous_denom_I.zpow₀ _ fun h => Or.inl (denom_ne_zero h _)).continuousOn

theorem norm_archV_le [NeZero M] (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2) :
    ∃ C : ℝ, ∀ h : GL (Fin 2) ℝ, 0 < h.det.val → ‖archV f h‖ ≤ C := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound (k := 2)
    (Γ := ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) f
  refine ⟨C, fun h hh => ?_⟩
  have hz := hC (h • UpperHalfPlane.I)
  have him : (h • UpperHalfPlane.I).im = h.det.val / Complex.normSq (denom h UpperHalfPlane.I) := by
    rw [im_smul_eq_div_normSq, abs_of_pos hh, UpperHalfPlane.I_im, mul_one]
  have hd : denom h UpperHalfPlane.I ≠ 0 := denom_ne_zero h UpperHalfPlane.I
  have hnsq : 0 < Complex.normSq (denom h UpperHalfPlane.I) := Complex.normSq_pos.mpr hd
  have hnorm : ‖archV f h‖ = ‖f (h • UpperHalfPlane.I)‖ * (h • UpperHalfPlane.I).im := by
    rw [archV, ModularForm.slash_apply, σ, if_pos hh]
    simp only [ContinuousAlgEquiv.refl_apply, norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hh]
    rw [him, Complex.normSq_eq_norm_sq]
    have hd0 : ‖denom h UpperHalfPlane.I‖ ≠ 0 := norm_ne_zero_iff.mpr hd
    have hdet' : (h.det.val : ℝ) ≠ 0 := hh.ne'
    rw [show (2 : ℤ) - 1 = 1 by norm_num]
    simp only [_root_.zpow_neg, zpow_one]
    field_simp
  rw [hnorm]
  have himpos : 0 < (h • UpperHalfPlane.I).im := (h • UpperHalfPlane.I).im_pos
  calc ‖f (h • UpperHalfPlane.I)‖ * (h • UpperHalfPlane.I).im
      ≤ C / (h • UpperHalfPlane.I).im ^ ((2 : ℤ) / 2 : ℝ) * (h • UpperHalfPlane.I).im := by
        gcongr
    _ = C := by
        rw [show ((2 : ℤ) / 2 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_one]
        field_simp

end Ws41.Lift134

end

namespace Ws41
namespace Lift134

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

variable {M : ℕ}

theorem apply_decomp₁ {f : CuspForm (CongruenceSubgroup.Gamma1 M) 2} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφ : CuspForm.IsAdelicLiftOfGamma1 f φ) {γ : GL (Fin 2) ℚ} {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ)
    (hk : k ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M)) :
    φ (globalPoints (𝓞 ℚ) ℚ γ * h * AdelicDock.finEmbed (𝓞 ℚ) ℚ k) = archV f (LanglandsTunnell.ratArchGL2 h) := by
  rw [mul_assoc, hφ.left_inv, hφ.level_inv k hk, hφ.apply_eq h hh hpos]
  rfl

theorem apply_eq_archV_of_near {f : CuspForm (CongruenceSubgroup.Gamma1 M) 2} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφ : CuspForm.IsAdelicLiftOfGamma1 f φ) {γ₀ : GL (Fin 2) ℚ} {h₀ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    {k₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hh₀ : glFin (𝓞 ℚ) ℚ h₀ = 1)
    (hk₀ : k₀ ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M)) (t : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
    (ht : glFin (𝓞 ℚ) ℚ t ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M))
    (hdet : 0 < (LanglandsTunnell.ratArchGL2 h₀ * LanglandsTunnell.ratArchGL2 t).det.val) :
    φ (globalPoints (𝓞 ℚ) ℚ γ₀ * h₀ * AdelicDock.finEmbed (𝓞 ℚ) ℚ k₀ * t)
      = archV f (LanglandsTunnell.ratArchGL2 h₀ * LanglandsTunnell.ratArchGL2 t) := by
  have hsplit : globalPoints (𝓞 ℚ) ℚ γ₀ * h₀ * AdelicDock.finEmbed (𝓞 ℚ) ℚ k₀ * t
      = globalPoints (𝓞 ℚ) ℚ γ₀ * (h₀ * archPart t) * AdelicDock.finEmbed (𝓞 ℚ) ℚ (k₀ * glFin (𝓞 ℚ) ℚ t) := by
    conv_lhs => rw [← archPart_mul_finPart t]
    have hcomm : AdelicDock.finEmbed (𝓞 ℚ) ℚ k₀ * archPart t = archPart t * AdelicDock.finEmbed (𝓞 ℚ) ℚ k₀ := by
      have := archPart_mul_finPart_comm t (AdelicDock.finEmbed (𝓞 ℚ) ℚ k₀)
      rw [show finPart (AdelicDock.finEmbed (𝓞 ℚ) ℚ k₀) = AdelicDock.finEmbed (𝓞 ℚ) ℚ k₀ from
        finPart_eq_self_of_glArch_eq_one (AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ k₀)] at this
      exact this.symm
    rw [map_mul, show finPart t = AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ t) from rfl]
    simp only [mul_assoc]
    rw [← mul_assoc (AdelicDock.finEmbed (𝓞 ℚ) ℚ k₀) (archPart t), hcomm, mul_assoc (archPart t)]
  have hfin : glFin (𝓞 ℚ) ℚ (h₀ * archPart t) = 1 := by rw [map_mul, hh₀, glFin_archPart, one_mul]
  have hpos : LanglandsTunnell.ratArchGL2 (h₀ * archPart t) ∈ GLPos (Fin 2) ℝ := by
    show 0 < (LanglandsTunnell.ratArchGL2 (h₀ * archPart t)).det.val
    rwa [ratArch_mul, ratArch_archPart]
  rw [hsplit, apply_decomp₁ hφ hfin hpos (Subgroup.mul_mem _ hk₀ ht), ratArch_mul, ratArch_archPart]

end Ws41.Lift134

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix Ws41.Lift134 in
open scoped MatrixGroups ModularForm in

theorem solution_L3
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) :
    ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖Φ g‖ ≤ C := by
  obtain ⟨C, hC⟩ := norm_archV_le h
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, y, k, hh, hpos, hk, hx⟩ := exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne (NeZero.ne M) g
  rw [hx, apply_decomp₁ hΦ hh hpos hk]
  exact hC _ hpos

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix Ws41.Lift134 in
open scoped MatrixGroups ModularForm in

theorem solution_L1
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) :
    Continuous Φ := by
  have hM : M ≠ 0 := NeZero.ne M
  refine continuous_iff_continuousAt.mpr fun g₀ => ?_
  obtain ⟨γ₀, h₀, k₀, hh₀, hpos₀, hk₀, hx₀⟩ := exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hM g₀
  have hdet₀ : 0 < (LanglandsTunnell.ratArchGL2 h₀).det.val := hpos₀
  have hinner : Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
      LanglandsTunnell.ratArchGL2 h₀ * LanglandsTunnell.ratArchGL2 (g₀⁻¹ * g) :=
    continuous_const.mul (continuous_ratArch.comp (continuous_const.mul continuous_id))
  let W : Set (AdelicGL2 (𝓞 ℚ) ℚ) := {g | glFin (𝓞 ℚ) ℚ (g₀⁻¹ * g) ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M)
    ∧ 0 < (LanglandsTunnell.ratArchGL2 h₀ * LanglandsTunnell.ratArchGL2 (g₀⁻¹ * g)).det.val}
  have hWopen : IsOpen W := by
    refine IsOpen.inter ?_ ?_
    · exact (isOpen_finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel_ne_bot hM)).preimage
        ((continuous_glFin (𝓞 ℚ) ℚ).comp (continuous_const.mul continuous_id))
    · exact isOpen_detPos.preimage hinner
  have hg₀W : g₀ ∈ W := by
    refine ⟨?_, ?_⟩
    · show glFin (𝓞 ℚ) ℚ (g₀⁻¹ * g₀) ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M)
      rw [inv_mul_cancel, map_one]
      exact Subgroup.one_mem _
    · show 0 < (LanglandsTunnell.ratArchGL2 h₀ * LanglandsTunnell.ratArchGL2 (g₀⁻¹ * g₀)).det.val
      rw [inv_mul_cancel, show LanglandsTunnell.ratArchGL2 (1 : AdelicGL2 (𝓞 ℚ) ℚ) = 1 from by
        rw [← ratArchHom_apply, map_one], mul_one]
      exact hdet₀
  have hEq : Set.EqOn Φ (fun g => archV h (LanglandsTunnell.ratArchGL2 h₀ * LanglandsTunnell.ratArchGL2 (g₀⁻¹ * g))) W := by
    intro g hg
    have := apply_eq_archV_of_near (γ₀ := γ₀) hΦ hh₀ hk₀ (g₀⁻¹ * g) hg.1 hg.2
    rwa [← hx₀, mul_inv_cancel_left] at this
  have hpt : ContinuousAt (archV h) (LanglandsTunnell.ratArchGL2 h₀ * LanglandsTunnell.ratArchGL2 (g₀⁻¹ * g₀)) :=
    (continuousOn_archV h).continuousAt (isOpen_detPos.mem_nhds hg₀W.2)
  have hmodel : ContinuousAt (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
      archV h (LanglandsTunnell.ratArchGL2 h₀ * LanglandsTunnell.ratArchGL2 (g₀⁻¹ * g))) g₀ :=
    ContinuousAt.comp (f := fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
      LanglandsTunnell.ratArchGL2 h₀ * LanglandsTunnell.ratArchGL2 (g₀⁻¹ * g)) (x := g₀) hpt hinner.continuousAt
  exact hmodel.congr ((Filter.eventuallyEq_of_mem (hWopen.mem_nhds hg₀W) hEq).symm)

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix Ws41.Lift134 MeasureTheory in
open scoped MatrixGroups ModularForm in

theorem solution
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) :
    letI := (productionPinsGeneral ℚ).mS
    MemLp Φ 2 (((productionPinsGeneral ℚ).μ).restrict (productionPinsGeneral ℚ).D) := by
  letI := (productionPinsGeneral ℚ).mS
  haveI : BorelSpace (AdelicGL2 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI : IsFiniteMeasure (((productionPinsGeneral ℚ).μ).restrict (productionPinsGeneral ℚ).D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (productionPinsGeneral_μ_D_pos_lt_top ℚ).2⟩
  obtain ⟨C, hC⟩ := solution_L3 hΦ
  exact MemLp.of_bound (solution_L1 hΦ).aestronglyMeasurable C (Filter.Eventually.of_forall hC)

end S_CuspForm_IsAdelicLiftOfGamma1_memLp_two_restrict_productionPinsGeneral
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOfGamma1_memLp_two_restrict_productionPinsGeneral (solution)
