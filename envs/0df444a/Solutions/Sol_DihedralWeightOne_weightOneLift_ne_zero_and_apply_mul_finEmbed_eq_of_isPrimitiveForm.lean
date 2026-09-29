-- Prove2me | solution 1 for DihedralWeightOne.weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/9a4afe40-d4d8-583e-b8d5-6fd924ebc639

import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Theorems.Thm_AutomorphicForm_exists_mem_productionPinsCompact_U_mul_eq_rat
import Theorems.Thm_LanglandsTunnell_isCuspidalFn_weightOneLift
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_LanglandsTunnell_weightOneLift_centralScalar_mul
import Theorems.Thm_LanglandsTunnell_isKfSmooth_weightOneLift
import Theorems.Thm_LanglandsTunnell_isBoundedOnSiegelWindows_weightOneLift
import Theorems.Thm_LanglandsTunnell_isHeckeCosetEigenfunctionAt_weightOneLift
import Theorems.Thm_LanglandsTunnell_weightOneLift_centralScalar_det_gen_mul
import Theorems.Thm_LanglandsTunnell_dirichletIdeleChar_mul_modulus_det_gen
import Theorems.Thm_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_ModularForm_HeckeOperator
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DihedralWeightOne_weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm
p2m_attr_erase "instance" "instCountableOfNumberField_definitions HeckeIntegralSeam.finite_padicInt_quotient_span_p Deep.NTSupply.instNormalRayClassSubgroup"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups ModularForm UpperHalfPlane
open UpperHalfPlane Matrix

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ratArchGL2"
namespace P4
namespace I2
p2m_open "LanglandsTunnell"

end LanglandsTunnell.P4.I2

end

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open scoped MatrixGroups

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ratArchGL2"
namespace P4
namespace I2
p2m_open "LanglandsTunnell"

private theorem exists_algebraMap_eq_of_mem_integralFiniteAdeles {R : Type*} [CommRing R] [IsDedekindDomain R]
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

private theorem exists_intCast_eq_of_mem_integralFiniteAdeles {q : ℚ}
    (hq : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_mem_integralFiniteAdeles hq
  exact ⟨Rat.ringOfIntegersEquiv r, by rw [← hr, Rat.ringOfIntegersEquiv_apply_coe]⟩

private theorem glFin_globalPoints_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl

private theorem exists_mapGL_eq_of_mem_finiteIntegralGL2 {γ : GL (Fin 2) ℚ}
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

end LanglandsTunnell.P4.I2

end

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open scoped MatrixGroups

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ratArchGL2"
namespace P4
namespace I2
p2m_open "LanglandsTunnell"

private theorem isReal_rat_infinitePlace (v : InfinitePlace ℚ) : v.IsReal := IsTotallyReal.isReal v

private def ratArchHom : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom).comp
    ((archComponent ℚ default).comp (glArch (𝓞 ℚ) ℚ))

private def ratArch (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom
    (archComponent ℚ default (glArch (𝓞 ℚ) ℚ g))

private theorem ratArchHom_apply (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : ratArchHom g = ratArch g := rfl

private theorem ratArch_mul (g g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ratArch (g * g') = ratArch g * ratArch g' := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, ← ratArchHom_apply, map_mul]

private theorem ratArch_inv (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : ratArch g⁻¹ = (ratArch g)⁻¹ := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, map_inv]

private theorem ratArch_one : ratArch 1 = 1 := by rw [← ratArchHom_apply, map_one]

private theorem ratArch_eq_one_of_glArch_eq_one {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    ratArch u = 1 := by
  unfold ratArch
  rw [hu, map_one, map_one]

private theorem ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    ratArch (globalPoints (𝓞 ℚ) ℚ γ) = GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom.comp
      ((archEval ℚ default).comp ((adeleArch (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))))
      ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = (Rat.castHom ℝ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j)
  rw [eq_ratCast, eq_ratCast]

private theorem ratArch_globalPoints_mapGL (ε : SL(2, ℤ)) :
    ratArch (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε)) = (ε : GL (Fin 2) ℝ) := by
  rw [ratArch_globalPoints]
  exact Matrix.SpecialLinearGroup.map_mapGL (S := ℚ) (T := ℝ) ε

private theorem det_ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    ((ratArch (globalPoints (𝓞 ℚ) ℚ γ)).det.val : ℝ) = (((GeneralLinearGroup.det γ : ℚˣ) : ℚ) : ℝ) := by
  rw [ratArch_globalPoints, GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_coe, eq_ratCast]

end LanglandsTunnell.P4.I2

end

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open scoped MatrixGroups

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ratArchGL2"
namespace P4
namespace I2
p2m_open "LanglandsTunnell"

end LanglandsTunnell.P4.I2

end

noncomputable section

open NumberField IsDedekindDomain Matrix AutomorphicForm NumberField.AdelicLevel MeasureTheory Complex
p2m_open "UpperHalfPlane~I"
open scoped MatrixGroups ModularForm Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ratArchGL2"
namespace P4
namespace I2
p2m_open "LanglandsTunnell"

local notation "𝔾" => GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)

private abbrev archPart (k : 𝔾) : 𝔾 := adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ k)

private abbrev finPart (k : 𝔾) : 𝔾 := AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ k)

private theorem eq_of_glArch_eq_of_glFin_eq {g g' : 𝔾} (ha : glArch (𝓞 ℚ) ℚ g = glArch (𝓞 ℚ) ℚ g')
    (hf : glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g') : g = g' := by
  refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
  · have := congrFun (congrFun (congrArg
      (fun m : GL (Fin 2) (InfiniteAdeleRing ℚ) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))) ha) i) j
    rwa [glArch_apply, glArch_apply] at this
  · have := congrFun (congrFun (congrArg
      (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))) hf) i) j
    rwa [glFin_apply, glFin_apply] at this

private theorem glArch_archPart (k : 𝔾) : glArch (𝓞 ℚ) ℚ (archPart k) = glArch (𝓞 ℚ) ℚ k :=
  glArch_adelicArchGLIncl ℚ _

private theorem glFin_archPart (k : 𝔾) : glFin (𝓞 ℚ) ℚ (archPart k) = 1 :=
  glFin_adelicArchGLIncl ℚ _

private theorem glArch_finPart (k : 𝔾) : glArch (𝓞 ℚ) ℚ (finPart k) = 1 :=
  AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ _

private theorem glFin_finPart (k : 𝔾) : glFin (𝓞 ℚ) ℚ (finPart k) = glFin (𝓞 ℚ) ℚ k :=
  AdelicDock.glFin_finEmbed (𝓞 ℚ) ℚ _

private theorem archPart_mul_finPart (k : 𝔾) : archPart k * finPart k = k :=
  eq_of_glArch_eq_of_glFin_eq (by rw [map_mul, glArch_archPart, glArch_finPart, mul_one])
    (by rw [map_mul, glFin_archPart, glFin_finPart, one_mul])

private theorem archPart_mul_finPart_comm (k k' : 𝔾) : archPart k * finPart k' = finPart k' * archPart k :=
  eq_of_glArch_eq_of_glFin_eq (by rw [map_mul, map_mul, glArch_archPart, glArch_finPart, mul_one, one_mul])
    (by rw [map_mul, map_mul, glFin_archPart, glFin_finPart, one_mul, mul_one])

private theorem finPart_eq_self_of_glArch_eq_one {u : 𝔾} (hu : glArch (𝓞 ℚ) ℚ u = 1) : finPart u = u :=
  eq_of_glArch_eq_of_glFin_eq (by rw [glArch_finPart, hu]) (glFin_finPart u)

private theorem ratArch_archPart (k : 𝔾) : ratArch (archPart k) = ratArch k := by
  unfold ratArch
  rw [glArch_archPart]

private theorem continuous_ratArch : Continuous ratArch := by
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

private theorem continuous_entry (i j : Fin 2) : Continuous fun h : GL (Fin 2) ℝ => (((h : Matrix (Fin 2) (Fin 2) ℝ) i j :
    ℝ) : ℂ) :=
  continuous_ofReal.comp (Units.continuous_val.matrix_elem i j)

private theorem continuous_denom_I : Continuous fun h : GL (Fin 2) ℝ => denom h UpperHalfPlane.I := by
  show Continuous fun h : GL (Fin 2) ℝ =>
    (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * UpperHalfPlane.I + (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℝ) : ℂ)
  exact ((continuous_entry 1 0).mul continuous_const).add (continuous_entry 1 1)

private theorem continuous_num_I : Continuous fun h : GL (Fin 2) ℝ => num h UpperHalfPlane.I := by
  show Continuous fun h : GL (Fin 2) ℝ =>
    (((h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) : ℂ) * UpperHalfPlane.I + (((h : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) : ℂ)
  exact ((continuous_entry 0 0).mul continuous_const).add (continuous_entry 0 1)

private theorem continuous_det_val : Continuous fun h : GL (Fin 2) ℝ => h.det.val := by
  show Continuous fun h : GL (Fin 2) ℝ => (Matrix.GeneralLinearGroup.det h).val
  simp_rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact Units.continuous_val.matrix_det

private theorem isOpen_detPos : IsOpen {h : GL (Fin 2) ℝ | 0 < h.det.val} :=
  isOpen_lt continuous_const continuous_det_val

private theorem continuousOn_coe_smul_I :
    ContinuousOn (fun h : GL (Fin 2) ℝ => ((h • UpperHalfPlane.I : ℍ) : ℂ)) {h | 0 < h.det.val} := by
  refine ContinuousOn.congr (f := fun h : GL (Fin 2) ℝ => num h UpperHalfPlane.I / denom h UpperHalfPlane.I) ?_ ?_
  · exact (continuous_num_I.div continuous_denom_I fun h => denom_ne_zero h _).continuousOn
  · intro h hh
    exact coe_smul_of_det_pos hh _

end LanglandsTunnell.P4.I2

end

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix UpperHalfPlane DihedralWeightOne

open scoped ModularForm MatrixGroups

namespace P2GProbe
namespace R1

variable (f : ℍ → ℂ)

private theorem weightOneArchLift_def (h : GL (Fin 2) ℝ) :
    weightOneArchLift f h = (f ∣[(1 : ℤ)] h) UpperHalfPlane.I * ((h.det.val : ℝ) : ℂ) ^ (1 : ℤ) :=
  rfl

private theorem weightOneArchLift_mul_of_slash_eq (γ h : GL (Fin 2) ℝ) (hγ : f ∣[(1 : ℤ)] γ = f)
    (hdet : γ.det.val = 1) :
    weightOneArchLift f (γ * h) = weightOneArchLift f h := by
  unfold weightOneArchLift
  rw [SlashAction.slash_mul, hγ]
  congr 2
  rw [map_mul, Units.val_mul, hdet, one_mul]

private theorem weightOneArchLift_iwasawa (z : ℍ) (h : GL (Fin 2) ℝ)
    (hh : (h : Matrix (Fin 2) (Fin 2) ℝ) = !![z.im, z.re; 0, 1]) :
    weightOneArchLift f h = (z.im : ℂ) * f z := by
  have h00 : h 0 0 = z.im := by
    have := congr_fun (congr_fun hh 0) 0; simpa using this
  have h01 : h 0 1 = z.re := by
    have := congr_fun (congr_fun hh 0) 1; simpa using this
  have h10 : h 1 0 = 0 := by
    have := congr_fun (congr_fun hh 1) 0; simpa using this
  have h11 : h 1 1 = 1 := by
    have := congr_fun (congr_fun hh 1) 1; simpa using this
  have hdet : h.det.val = z.im := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdetpos : 0 < h.det.val := by rw [hdet]; exact z.im_pos
  have hsmul : h • UpperHalfPlane.I = z := by
    apply UpperHalfPlane.ext
    rw [coe_smul_of_det_pos hdetpos, num, denom, h00, h01, h10, h11]
    simp only [UpperHalfPlane.coe_I, Complex.ofReal_zero, Complex.ofReal_one, zero_mul, zero_add,
      div_one]
    apply Complex.ext <;> simp
  unfold weightOneArchLift
  rw [ModularForm.slash_apply, σ, if_pos hdetpos, hsmul, denom, h10, h11, hdet]
  simp only [ContinuousAlgEquiv.refl_apply, Complex.ofReal_zero, Complex.ofReal_one, zero_mul,
    zero_add, sub_self, zpow_zero, mul_one, _root_.zpow_neg, inv_one, zpow_one]
  ring

private theorem norm_weightOneArchLift_le (C : ℝ)
    (hf : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2))
    (h : GL (Fin 2) ℝ) (hh : 0 < h.det.val) :
    ‖weightOneArchLift f h‖ ≤ C * Real.sqrt h.det.val := by
  have hd : denom h UpperHalfPlane.I ≠ 0 := denom_ne_zero h UpperHalfPlane.I
  have hdn : 0 < ‖denom h UpperHalfPlane.I‖ := norm_pos_iff.mpr hd

  have him : (h • UpperHalfPlane.I).im = h.det.val / ‖denom h UpperHalfPlane.I‖ ^ 2 := by
    rw [im_smul_eq_div_normSq, abs_of_pos hh, UpperHalfPlane.I_im, mul_one,
      Complex.normSq_eq_norm_sq]
  have himpos : 0 < (h • UpperHalfPlane.I).im := (h • UpperHalfPlane.I).im_pos

  have hnorm : ‖weightOneArchLift f h‖ =
      ‖f (h • UpperHalfPlane.I)‖ * ‖denom h UpperHalfPlane.I‖⁻¹ * h.det.val := by
    unfold weightOneArchLift
    rw [ModularForm.slash_apply, σ, if_pos hh]
    simp only [ContinuousAlgEquiv.refl_apply, sub_self, zpow_zero, mul_one, _root_.zpow_neg, zpow_one,
      norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]

  have hsq : (h • UpperHalfPlane.I).im ^ (((1 : ℤ) : ℝ) / 2) = Real.sqrt (h • UpperHalfPlane.I).im := by
    rw [Real.sqrt_eq_rpow]; norm_num
  have hspos : 0 < Real.sqrt (h • UpperHalfPlane.I).im := Real.sqrt_pos.mpr himpos
  have hpet : ‖f (h • UpperHalfPlane.I)‖ * Real.sqrt (h • UpperHalfPlane.I).im ≤ C := by
    have h1 := hf (h • UpperHalfPlane.I)
    rw [hsq] at h1
    calc ‖f (h • UpperHalfPlane.I)‖ * Real.sqrt (h • UpperHalfPlane.I).im
        ≤ C / Real.sqrt (h • UpperHalfPlane.I).im * Real.sqrt (h • UpperHalfPlane.I).im :=
          mul_le_mul_of_nonneg_right h1 hspos.le
      _ = C := by field_simp

  have hsqrt_im : Real.sqrt (h • UpperHalfPlane.I).im
      = Real.sqrt h.det.val / ‖denom h UpperHalfPlane.I‖ := by
    rw [him, Real.sqrt_div hh.le, Real.sqrt_sq hdn.le]
  have hds : Real.sqrt h.det.val * Real.sqrt h.det.val = h.det.val := Real.mul_self_sqrt hh.le

  have hkey : ‖weightOneArchLift f h‖ =
      (‖f (h • UpperHalfPlane.I)‖ * Real.sqrt (h • UpperHalfPlane.I).im) * Real.sqrt h.det.val := by
    rw [hnorm, hsqrt_im, div_eq_mul_inv]
    calc ‖f (h • UpperHalfPlane.I)‖ * ‖denom h UpperHalfPlane.I‖⁻¹ * h.det.val
        = ‖f (h • UpperHalfPlane.I)‖ * ‖denom h UpperHalfPlane.I‖⁻¹
            * (Real.sqrt h.det.val * Real.sqrt h.det.val) := by rw [hds]
      _ = ‖f (h • UpperHalfPlane.I)‖ * (Real.sqrt h.det.val * ‖denom h UpperHalfPlane.I‖⁻¹)
            * Real.sqrt h.det.val := by ring
  rw [hkey]
  exact mul_le_mul_of_nonneg_right hpet (Real.sqrt_nonneg _)

end P2GProbe.R1

namespace P2GProbe
namespace R3

private theorem hasWeightOneDecomp_of_ne_bot {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥)
    (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : DihedralWeightOne.HasWeightOneDecomp N g := by
  obtain ⟨γ, h, u, hu, hfin, hpos, hg⟩ :=
    AutomorphicForm.exists_mem_productionPinsCompact_U_mul_eq_rat hN g
  exact ⟨γ, h, u, hu, hfin, hpos default (IsTotallyReal.isReal default), hg⟩

end P2GProbe.R3

namespace P2GProbe
namespace R4a

open LanglandsTunnell.P4.I2 CongruenceSubgroup

private theorem ratArchGL2_eq_ratArch (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 g = ratArch g := rfl

private theorem mem_of_algebraMap_mem_idealBall {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) {r : 𝓞 ℚ}
    (h : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ r) ∈ idealBall (𝓞 ℚ) ℚ N) :
    r ∈ N := by
  classical
  rw [← Ideal.iInf_maxPowDividing_eq hN, Ideal.mem_iInf]
  intro v
  have h1 := h v
  rw [show (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ r)) v
      = algebraMap ℚ (v.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ r) from rfl, valued_algebraMap,
    idealBound_of_ne_bot hN, HeightOneSpectrum.intValuation_le_pow_iff_mem] at h1
  exact h1

private theorem dvd_of_algebraMap_intCast_mem_idealBall {n : ℕ} (hn : n ≠ 0) {k : ℤ}
    (h : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (k : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)})) :
    (n : ℤ) ∣ k := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  have h' : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ (k : 𝓞 ℚ))
      ∈ idealBall (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
    rwa [map_intCast]
  have hmem : (k : 𝓞 ℚ) ∈ Ideal.span {(n : 𝓞 ℚ)} := mem_of_algebraMap_mem_idealBall hN h'
  have hdvd : (n : 𝓞 ℚ) ∣ (k : 𝓞 ℚ) := Ideal.mem_span_singleton.mp hmem
  have := map_dvd Rat.ringOfIntegersEquiv hdvd
  simpa using this

private theorem glFin_globalPoints_mapGL_apply (ε : SL(2, ℤ)) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((ε i j : ℤ) : ℚ) := by
  rw [glFin_globalPoints_apply]
  congr 1

private theorem mem_Gamma1_of_glFin_mem_finiteLevelOne {n : ℕ} (hn : n ≠ 0) (ε : SL(2, ℤ))
    (hε : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ ε))
      ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)})) :
    ε ∈ Gamma1 n := by
  have hL := (mem_finiteLevelOne_iff.mp hε).1

  have hc : (n : ℤ) ∣ ε 1 0 := by
    apply dvd_of_algebraMap_intCast_mem_idealBall hn
    have := hL.lowerLeft
    rwa [glFin_globalPoints_mapGL_apply] at this

  have hd : (n : ℤ) ∣ ε 1 1 - 1 := by
    apply dvd_of_algebraMap_intCast_mem_idealBall hn
    have := hL.lowerRight
    rw [glFin_globalPoints_mapGL_apply] at this
    rwa [Int.cast_sub, Int.cast_one, map_sub, map_one]
  have hc' : (ε 1 0 : ZMod n) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr hc
  have hd' : (ε 1 1 : ZMod n) = 1 := by
    have h0 : ((ε 1 1 - 1 : ℤ) : ZMod n) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr hd
    rw [Int.cast_sub, Int.cast_one, sub_eq_zero] at h0
    exact h0

  have hdet : ε 0 0 * ε 1 1 - ε 0 1 * ε 1 0 = 1 := by
    have := ε.det_coe
    rwa [Matrix.det_fin_two] at this
  have ha' : (ε 0 0 : ZMod n) = 1 := by
    have h1 : ((ε 0 0 * ε 1 1 - ε 0 1 * ε 1 0 : ℤ) : ZMod n) = 1 := by rw [hdet, Int.cast_one]
    push_cast at h1
    rwa [hd', hc', mul_one, mul_zero, sub_zero] at h1
  exact (Gamma1_mem n ε).mpr ⟨ha', hd', hc'⟩

private theorem finiteLevelZero_le_finiteIntegralGL2 (N : Ideal (𝓞 ℚ)) :
    finiteLevelZero (𝓞 ℚ) ℚ N ≤ finiteIntegralGL2 (𝓞 ℚ) ℚ := by
  intro g hg
  rw [mem_finiteLevelZero_iff] at hg
  show g ∈ finiteLevelZero (𝓞 ℚ) ℚ ⊤
  rw [mem_finiteLevelZero_iff]
  have key : ∀ m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ),
      IsLevelZeroMatrix (𝓞 ℚ) ℚ N m → IsLevelZeroMatrix (𝓞 ℚ) ℚ ⊤ m := fun m hm =>
    ⟨hm.integral, fun v => (hm.lowerLeft v).trans
      ((idealBound_le_one N v).trans (idealBound_top v).ge)⟩
  exact ⟨key _ hg.1, key _ hg.2⟩

private theorem weightOneArchLift_eq_of_decomps {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    {g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} {γ γ' : GL (Fin 2) ℚ}
    {h u h' u' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ)
    (hg : g = globalPoints (𝓞 ℚ) ℚ γ * h * u)
    (hu' : u' ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) (hh' : glFin (𝓞 ℚ) ℚ h' = 1)
    (hpos' : LanglandsTunnell.ratArchGL2 h' ∈ GLPos (Fin 2) ℝ)
    (hg' : g = globalPoints (𝓞 ℚ) ℚ γ' * h' * u') :
    weightOneArchLift f (LanglandsTunnell.ratArchGL2 h)
      = weightOneArchLift f (LanglandsTunnell.ratArchGL2 h') := by
  simp only [ratArchGL2_eq_ratArch] at hpos hpos' ⊢
  have hufin := glFin_mem_finiteLevelOne_of_mem_productionPinsCompact_U ℚ _ hu
  have hu'fin := glFin_mem_finiteLevelOne_of_mem_productionPinsCompact_U ℚ _ hu'
  have huarch := glArch_eq_one_of_mem_productionPinsCompact_U ℚ _ hu
  have hu'arch := glArch_eq_one_of_mem_productionPinsCompact_U ℚ _ hu'
  set P := globalPoints (𝓞 ℚ) ℚ with hP
  set δ : GL (Fin 2) ℚ := γ'⁻¹ * γ with hδ
  have hquot : P δ = h' * u' * u⁻¹ * h⁻¹ := by
    have E : P γ * (h * u) = P γ' * (h' * u') := by rw [← mul_assoc, ← mul_assoc, ← hg, ← hg']
    rw [hδ, map_mul, map_inv]
    have : P γ = P γ' * (h' * u') * (h * u)⁻¹ := eq_mul_inv_of_mul_eq E
    rw [this, _root_.mul_inv_rev]
    group

  have hlevel : glFin (𝓞 ℚ) ℚ (P δ) ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}) := by
    rw [hquot, map_mul, map_mul, map_mul, map_inv, map_inv, hh, hh', one_mul, inv_one, mul_one]
    exact Subgroup.mul_mem _ hu'fin (Subgroup.inv_mem _ hufin)
  have hint : glFin (𝓞 ℚ) ℚ (P δ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ :=
    finiteLevelZero_le_finiteIntegralGL2 _ (finiteLevelOne_le_finiteLevelZero _ _ _ hlevel)

  have harch : ratArch (P δ) = ratArch h' * (ratArch h)⁻¹ := by
    rw [hquot, ratArch_mul, ratArch_mul, ratArch_mul, ratArch_inv, ratArch_inv,
      ratArch_eq_one_of_glArch_eq_one huarch, ratArch_eq_one_of_glArch_eq_one hu'arch, inv_one,
      mul_one, mul_one]
  have hdetpos : 0 < ((GeneralLinearGroup.det δ : ℚˣ) : ℚ) := by
    have h1 : 0 < ((ratArch (P δ)).det.val : ℝ) := by
      rw [harch, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      exact mul_pos hpos' (inv_pos.mpr hpos)
    rw [det_ratArch_globalPoints] at h1
    exact_mod_cast h1
  obtain ⟨ε, hε⟩ := exists_mapGL_eq_of_mem_finiteIntegralGL2 hint hdetpos

  have hεΓ : ε ∈ Gamma1 n := by
    apply mem_Gamma1_of_glFin_mem_finiteLevelOne hn
    rw [hε]
    exact hlevel
  have hh'eq : ratArch h' = (ε : GL (Fin 2) ℝ) * ratArch h := by
    rw [← ratArch_globalPoints_mapGL, hε, harch, inv_mul_cancel_right]
  have hεdet : ((ε : GL (Fin 2) ℝ)).det.val = 1 := by simp
  rw [hh'eq, R1.weightOneArchLift_mul_of_slash_eq f _ _ (hf ε hεΓ) hεdet]

private theorem weightOneLift_eq {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
    (hu : u ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) (hfin : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ)
    (hg : g = globalPoints (𝓞 ℚ) ℚ γ * h * u) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g = weightOneArchLift f (LanglandsTunnell.ratArchGL2 h) := by
  have H : HasWeightOneDecomp (Ideal.span {(n : 𝓞 ℚ)}) g := ⟨γ, h, u, hu, hfin, hpos, hg⟩
  unfold DihedralWeightOne.weightOneLift
  rw [dif_pos H]
  obtain ⟨u₀, hu₀, hh₀, hpos₀, hg₀⟩ := H.choose_spec.choose_spec
  exact weightOneArchLift_eq_of_decomps hn f hf hu₀ hh₀ hpos₀ hg₀ hu hfin hpos hg

private theorem weightOneLift_mul_of_mem_U {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) {u₀ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hu₀ : u₀ ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (g * u₀) = weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  obtain ⟨γ, h, u, hu, hfin, hpos, hg⟩ := R3.hasWeightOneDecomp_of_ne_bot hN g
  have hg' : g * u₀ = globalPoints (𝓞 ℚ) ℚ γ * h * (u * u₀) := by
    rw [hg]; simp only [mul_assoc]
  rw [weightOneLift_eq hn f hf (g * u₀) γ h (u * u₀) (Subgroup.mul_mem _ hu hu₀) hfin hpos hg',
    weightOneLift_eq hn f hf g γ h u hu hfin hpos hg]

private theorem weightOneLift_globalPoints_mul {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (γ₀ : GL (Fin 2) ℚ) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (globalPoints (𝓞 ℚ) ℚ γ₀ * g)
      = weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  obtain ⟨γ, h, u, hu, hfin, hpos, hg⟩ := R3.hasWeightOneDecomp_of_ne_bot hN g
  have hg' : globalPoints (𝓞 ℚ) ℚ γ₀ * g = globalPoints (𝓞 ℚ) ℚ (γ₀ * γ) * h * u := by
    rw [hg, map_mul]; simp only [mul_assoc]
  rw [weightOneLift_eq hn f hf _ (γ₀ * γ) h u hu hfin hpos hg',
    weightOneLift_eq hn f hf g γ h u hu hfin hpos hg]

end P2GProbe.R4a

namespace P2GProbe
namespace R7

open LanglandsTunnell.P4.I2 AutomorphicForm.WindowedSiegel NumberField.AdelicVolume

private theorem exists_algebraMap_eq_of_mem_integral {R : Type*} [CommRing R] [IsDedekindDomain R]
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

private theorem exists_intCast_eq_of_mem_integral {q : ℚ}
    (hq : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_mem_integral hq
  exact ⟨Rat.ringOfIntegersEquiv r, by rw [← hr, Rat.ringOfIntegersEquiv_apply_coe]⟩

private theorem abs_eq_one_of_mem_integral {q : ℚ} (hq0 : q ≠ 0)
    (hq : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hq' : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q⁻¹ ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) : |q| = 1 := by
  obtain ⟨a, ha⟩ := exists_intCast_eq_of_mem_integral hq
  obtain ⟨b, hb⟩ := exists_intCast_eq_of_mem_integral hq'
  have hab : a * b = 1 := by
    have : ((a * b : ℤ) : ℚ) = 1 := by
      rw [Int.cast_mul, ha, hb, mul_inv_cancel₀ hq0]
    exact_mod_cast this
  rw [← ha]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hab with h1 | h1 <;> simp [h1]

private theorem algebraMap_det_mem_integral (γ : GL (Fin 2) ℚ)
    (h : ∀ i j, (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((GeneralLinearGroup.det γ : ℚˣ) : ℚ)
      ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, map_sub, map_mul, map_mul]
  simp only [← glFin_globalPoints_apply]
  exact sub_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (h 0 0) (h 1 1))
    (mul_mem_integralFiniteAdeles (h 0 1) (h 1 0))

private theorem abs_det_eq_one_of_glFin_mem_finiteIntegralGL2 {γ : GL (Fin 2) ℚ}
    (hint : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ) :
    |((GeneralLinearGroup.det γ : ℚˣ) : ℚ)| = 1 := by
  rw [mem_finiteIntegralGL2_iff] at hint
  obtain ⟨hγ, hγinv⟩ := hint
  have hγinv' : ∀ i j, (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ⁻¹) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    intro i j
    rw [map_inv, map_inv]
    exact hγinv i j
  have h1 := algebraMap_det_mem_integral γ hγ
  have h2 := algebraMap_det_mem_integral γ⁻¹ hγinv'
  rw [map_inv, Units.val_inv_eq_inv_val] at h2
  exact abs_eq_one_of_mem_integral (GeneralLinearGroup.det γ).ne_zero h1 h2

private theorem archDetNorm_default_eq (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    archDetNorm (default : InfinitePlace ℚ) g = |(ratArch g).det.val| := by
  unfold archDetNorm ratArch
  rw [GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_coe, GeneralLinearGroup.val_det_apply,
    ← Real.norm_eq_abs]
  have hiso := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (isReal_rat_infinitePlace (default : InfinitePlace ℚ))
  exact (hiso.norm_map_of_map_zero (map_zero _) _).symm

private theorem det_ratArch_eq_archDetNorm {n : ℕ} {g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} {γ : GL (Fin 2) ℚ}
    {h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hgint : glFin (𝓞 ℚ) ℚ g ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ)
    (hu : u ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ)
    (hg : g = globalPoints (𝓞 ℚ) ℚ γ * h * u) :
    (LanglandsTunnell.ratArchGL2 h).det.val = archDetNorm (default : InfinitePlace ℚ) g := by
  simp only [R4a.ratArchGL2_eq_ratArch] at hpos ⊢
  have huarch := glArch_eq_one_of_mem_productionPinsCompact_U ℚ _ hu
  have hufin : glFin (𝓞 ℚ) ℚ u ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ :=
    R4a.finiteLevelZero_le_finiteIntegralGL2 _ (finiteLevelOne_le_finiteLevelZero _ _ _
      (glFin_mem_finiteLevelOne_of_mem_productionPinsCompact_U ℚ _ hu))
  have hγ : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ := by
    have hsplit : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) = glFin (𝓞 ℚ) ℚ g * (glFin (𝓞 ℚ) ℚ u)⁻¹ := by
      rw [hg, map_mul, map_mul, hh, mul_one, mul_inv_cancel_right]
    rw [hsplit]
    exact Subgroup.mul_mem _ hgint (Subgroup.inv_mem _ hufin)
  have habs : |(((GeneralLinearGroup.det γ : ℚˣ) : ℚ) : ℝ)| = 1 := by
    exact_mod_cast abs_det_eq_one_of_glFin_mem_finiteIntegralGL2 hγ
  have hpos' : 0 < (ratArch h).det.val := hpos
  rw [archDetNorm_default_eq, hg, ratArch_mul, ratArch_mul, ratArch_eq_one_of_glArch_eq_one huarch,
    mul_one, map_mul, Units.val_mul, abs_mul, det_ratArch_globalPoints, habs, one_mul, abs_of_pos hpos']

private theorem norm_weightOneLift_le_of_mem_D {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2))
    {g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hgD : g ∈ (productionPinsCompact ℚ).D) :
    ‖weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g‖ ≤ C * Real.sqrt 2 := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  obtain ⟨γ, h, u, hu, hh, hpos, hg⟩ := R3.hasWeightOneDecomp_of_ne_bot hN g
  rw [R4a.weightOneLift_eq hn f hf g γ h u hu hh hpos hg]
  have hC0 : 0 ≤ C := by
    have h1 := hC UpperHalfPlane.I
    rw [UpperHalfPlane.I_im, Real.one_rpow, div_one] at h1
    exact (norm_nonneg _).trans h1
  have hdetpos : 0 < (LanglandsTunnell.ratArchGL2 h).det.val := hpos
  have hD := mem_centreCutSiegelSet_iff.mp hgD
  have hwin : archDetNorm (default : InfinitePlace ℚ) g ∈ Set.Icc (1 / 2 : ℝ) 2 := hD.2.2.2 default
  have hdet := det_ratArch_eq_archDetNorm hD.1 hu hh hpos hg
  calc ‖weightOneArchLift f (LanglandsTunnell.ratArchGL2 h)‖
      ≤ C * Real.sqrt (LanglandsTunnell.ratArchGL2 h).det.val :=
        R1.norm_weightOneArchLift_le f C hC _ hdetpos
    _ ≤ C * Real.sqrt 2 := by
        apply mul_le_mul_of_nonneg_left _ hC0
        apply Real.sqrt_le_sqrt
        rw [hdet]
        exact hwin.2

end P2GProbe.R7

namespace P2GProbe
namespace R7

open LanglandsTunnell.P4.I2 MeasureTheory
open scoped Topology

private theorem weightOneArchLift_eq_of_det_pos (f : ℍ → ℂ) (h : GL (Fin 2) ℝ) (hh : 0 < h.det.val) :
    weightOneArchLift f h
      = f (h • UpperHalfPlane.I) * (denom h UpperHalfPlane.I)⁻¹ * ((h.det.val : ℝ) : ℂ) := by
  have h' : 0 < ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rwa [← Matrix.GeneralLinearGroup.val_det_apply]
  have hσ : ∀ w : ℂ, σ h w = w := fun w => by simp [σ, h']
  rw [R1.weightOneArchLift_def, ModularForm.slash_apply, hσ]
  simp

private theorem continuousOn_weightOneArchLift (f : ℍ → ℂ) (hf : Continuous f) :
    ContinuousOn (weightOneArchLift f) {h : GL (Fin 2) ℝ | 0 < h.det.val} := by
  have hsmul : ContinuousOn (fun h : GL (Fin 2) ℝ => (h • UpperHalfPlane.I : ℍ)) {h | 0 < h.det.val} :=
    UpperHalfPlane.isEmbedding_coe.continuousOn_iff.mpr continuousOn_coe_smul_I
  have hdet : Continuous fun h : GL (Fin 2) ℝ => ((h.det.val : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp continuous_det_val
  refine ContinuousOn.congr (f := fun h : GL (Fin 2) ℝ =>
      f (h • UpperHalfPlane.I) * (denom h UpperHalfPlane.I)⁻¹ * ((h.det.val : ℝ) : ℂ))
    ?_ fun h hh => weightOneArchLift_eq_of_det_pos f h hh
  exact ((hf.comp_continuousOn hsmul).mul (continuous_denom_I.inv₀ fun h => denom_ne_zero h _).continuousOn).mul
    hdet.continuousOn

private theorem mem_U_iff (N : Ideal (𝓞 ℚ)) (u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    u ∈ (productionPinsCompact ℚ).U N ↔
      glFin (𝓞 ℚ) ℚ u ∈ finiteLevelOne (𝓞 ℚ) ℚ N ∧ glArch (𝓞 ℚ) ℚ u = 1 :=
  Iff.rfl

private theorem finPart_mem_U {N : Ideal (𝓞 ℚ)} {k : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hk : glFin (𝓞 ℚ) ℚ k ∈ finiteLevelOne (𝓞 ℚ) ℚ N) : finPart k ∈ (productionPinsCompact ℚ).U N :=
  (mem_U_iff N _).mpr ⟨by rwa [glFin_finPart], glArch_finPart k⟩

private theorem weightOneLift_mul_eq {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    {g₀ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} {γ₀ : GL (Fin 2) ℚ} {h₀ u₀ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hu₀ : u₀ ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)})) (hh₀ : glFin (𝓞 ℚ) ℚ h₀ = 1)
    (hg₀ : g₀ = globalPoints (𝓞 ℚ) ℚ γ₀ * h₀ * u₀) (k : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
    (hkf : glFin (𝓞 ℚ) ℚ k ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)}))
    (hdet : 0 < (ratArch h₀ * ratArch k).det.val) :
    weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (g₀ * k) = weightOneArchLift f (ratArch h₀ * ratArch k) := by
  have hu : u₀ * finPart k ∈ (productionPinsCompact ℚ).U (Ideal.span {(n : 𝓞 ℚ)}) :=
    Subgroup.mul_mem _ hu₀ (finPart_mem_U hkf)
  have hfin : glFin (𝓞 ℚ) ℚ (h₀ * archPart k) = 1 := by
    rw [map_mul, hh₀, glFin_archPart, mul_one]
  have hpos : LanglandsTunnell.ratArchGL2 (h₀ * archPart k) ∈ GLPos (Fin 2) ℝ := by
    show 0 < (LanglandsTunnell.ratArchGL2 (h₀ * archPart k)).det.val
    rw [R4a.ratArchGL2_eq_ratArch, ratArch_mul, ratArch_archPart]
    exact hdet
  have hu₀' : finPart u₀ = u₀ := finPart_eq_self_of_glArch_eq_one ((mem_U_iff _ u₀).mp hu₀).2
  have hg : g₀ * k = globalPoints (𝓞 ℚ) ℚ γ₀ * (h₀ * archPart k) * (u₀ * finPart k) :=
    calc g₀ * k = globalPoints (𝓞 ℚ) ℚ γ₀ * h₀ * u₀ * (archPart k * finPart k) := by
          rw [archPart_mul_finPart, hg₀]
      _ = globalPoints (𝓞 ℚ) ℚ γ₀ * h₀ * (finPart u₀ * archPart k) * finPart k := by rw [hu₀']; group
      _ = globalPoints (𝓞 ℚ) ℚ γ₀ * h₀ * (archPart k * finPart u₀) * finPart k := by
          rw [archPart_mul_finPart_comm]
      _ = globalPoints (𝓞 ℚ) ℚ γ₀ * (h₀ * archPart k) * (u₀ * finPart k) := by rw [hu₀']; group
  rw [R4a.weightOneLift_eq hn f hf (g₀ * k) γ₀ _ _ hu hfin hpos hg, R4a.ratArchGL2_eq_ratArch, ratArch_mul,
    ratArch_archPart]

private theorem continuous_weightOneLift {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ) (hf_cont : Continuous f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f) :
    Continuous (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine continuous_iff_continuousAt.mpr fun g₀ => ?_
  obtain ⟨γ₀, h₀, u₀, hu₀, hh₀, hpos₀, hg₀⟩ := R3.hasWeightOneDecomp_of_ne_bot hN g₀
  have hh₀pos : 0 < (ratArch h₀).det.val := by
    rw [← R4a.ratArchGL2_eq_ratArch]
    exact hpos₀
  have hinner : Continuous fun g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) => ratArch h₀ * ratArch (g₀⁻¹ * g) :=
    continuous_const.mul (continuous_ratArch.comp (continuous_const.mul continuous_id))
  let W : Set (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :=
    {g | glFin (𝓞 ℚ) ℚ (g₀⁻¹ * g) ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)})
      ∧ 0 < (ratArch h₀ * ratArch (g₀⁻¹ * g)).det.val}
  have hWopen : IsOpen W := by
    refine IsOpen.inter ?_ ?_
    · exact (isOpen_finiteLevelOne (𝓞 ℚ) ℚ (N := Ideal.span {(n : 𝓞 ℚ)}) hN).preimage
        ((continuous_glFin (𝓞 ℚ) ℚ).comp (continuous_const.mul continuous_id))
    · exact isOpen_detPos.preimage hinner
  have hg₀W : g₀ ∈ W := by
    refine ⟨?_, ?_⟩
    · show glFin (𝓞 ℚ) ℚ (g₀⁻¹ * g₀) ∈ finiteLevelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)})
      rw [inv_mul_cancel, map_one]
      exact Subgroup.one_mem _
    · show 0 < (ratArch h₀ * ratArch (g₀⁻¹ * g₀)).det.val
      rwa [inv_mul_cancel, ratArch_one, mul_one]
  have hEq : Set.EqOn (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f)
      (fun g => weightOneArchLift f (ratArch h₀ * ratArch (g₀⁻¹ * g))) W := by
    intro g hg
    have := weightOneLift_mul_eq hn f hf hu₀ hh₀ hg₀ (g₀⁻¹ * g) hg.1 hg.2
    rwa [mul_inv_cancel_left] at this
  have hpt : ContinuousAt (weightOneArchLift f) (ratArch h₀ * ratArch (g₀⁻¹ * g₀)) :=
    (continuousOn_weightOneArchLift f hf_cont).continuousAt (isOpen_detPos.mem_nhds hg₀W.2)
  have hmodel : ContinuousAt (fun g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) =>
      weightOneArchLift f (ratArch h₀ * ratArch (g₀⁻¹ * g))) g₀ :=
    ContinuousAt.comp (f := fun g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) => ratArch h₀ * ratArch (g₀⁻¹ * g))
      (x := g₀) hpt hinner.continuousAt
  exact hmodel.congr ((Filter.eventuallyEq_of_mem (hWopen.mem_nhds hg₀W) hEq).symm)

private theorem memLp_two_weightOneLift {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ) (hf_cont : Continuous f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2)) :
    letI := (productionPinsCompact ℚ).mS
    MemLp (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) 2
      (((productionPinsCompact ℚ).μ).restrict (productionPinsCompact ℚ).D) := by
  letI := (productionPinsCompact ℚ).mS
  haveI : BorelSpace (GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :=
    NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI : IsFiniteMeasure (((productionPinsCompact ℚ).μ).restrict (productionPinsCompact ℚ).D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (productionPinsCompact_μ_D_pos_lt_top ℚ).2⟩
  refine MemLp.of_bound (continuous_weightOneLift hn f hf_cont hf).aestronglyMeasurable (C * Real.sqrt 2) ?_
  exact ae_restrict_of_forall_mem (measurableSet_productionPinsCompact_D ℚ)
    fun g hg => norm_weightOneLift_le_of_mem_D hn f hf C hC hg

end P2GProbe.R7

namespace P2GProbe
namespace R4a

end P2GProbe.R4a

end

namespace P2GProbe
namespace Alpha

open LanglandsTunnell.P4.I2 NumberField AutomorphicForm DihedralWeightOne Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

private noncomputable def archMat (τ : ℍ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![τ.im, τ.re; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simpa using τ.im_ne_zero)

private theorem coe_archMat (τ : ℍ) :
    ((archMat τ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![τ.im, τ.re; 0, 1] := rfl

private theorem det_archMat_pos (τ : ℍ) : 0 < (archMat τ).det.val := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_archMat, Matrix.det_fin_two_of]
  simpa using τ.im_pos

private noncomputable def ratArchEquiv :
    (default : InfinitePlace ℚ).Completion ≃+* ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)

private noncomputable def archPoint (τ : ℍ) : AdelicGL2 (𝓞 ℚ) ℚ :=
  adelicArchGLIncl ℚ (archGLIncl ℚ default
    (Matrix.GeneralLinearGroup.map (ratArchEquiv.symm : ℝ ≃+* _).toRingHom (archMat τ)))

private theorem glFin_archPoint (τ : ℍ) : NumberField.AdelicLevel.glFin (𝓞 ℚ) ℚ (archPoint τ) = 1 :=
  glFin_adelicArchGLIncl ℚ _

private theorem ratArch_archPoint (τ : ℍ) : ratArch (archPoint τ) = archMat τ := by
  unfold ratArch archPoint
  rw [glArch_adelicArchGLIncl, archComponent_archGLIncl_self]
  ext i j
  simp [ratArchEquiv]

private theorem weightOneLift_exists_ne_zero {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (hf0 : ∃ τ : ℍ, f τ ≠ 0) :
    ∃ g : AdelicGL2 (𝓞 ℚ) ℚ, weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g ≠ 0 := by
  obtain ⟨τ, hτ⟩ := hf0
  refine ⟨archPoint τ, ?_⟩
  have h1 : weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (1 * archPoint τ)
      = weightOneArchLift f (ratArch 1 * ratArch (archPoint τ)) :=
    P2GProbe.R7.weightOneLift_mul_eq hn f hf (g₀ := 1) (γ₀ := 1) (h₀ := 1) (u₀ := 1)
      (Subgroup.one_mem _) (map_one _) (by simp) (archPoint τ)
      (by rw [glFin_archPoint]; exact Subgroup.one_mem _)
      (by rw [ratArch_one, one_mul, ratArch_archPoint]; exact det_archMat_pos τ)
  rw [one_mul] at h1
  rw [h1, ratArch_one, one_mul, ratArch_archPoint,
    P2GProbe.R1.weightOneArchLift_iwasawa f τ (archMat τ) (coe_archMat τ)]
  exact mul_ne_zero (by exact_mod_cast τ.im_ne_zero) hτ

end P2GProbe.Alpha

noncomputable section

namespace Ws1
namespace L1

open NumberField IsDedekindDomain AutomorphicForm
open CongruenceSubgroup
open scoped ModularForm MatrixGroups

variable {N : ℕ} [NeZero N]

theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 ℚ)) : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 ℚ) ∈ v.asIdeal := by
  have key : ∀ n : ℕ, (n : 𝓞 ℚ) ∈ v.asIdeal → n ≠ 1 → n ≠ 0 → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 ℚ) ∈ v.asIdeal := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn h1 h0
      obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
      obtain ⟨k, rfl⟩ := hpn
      have hk0 : k ≠ 0 := by rintro rfl; exact h0 (by simp)
      rw [Nat.cast_mul] at hn
      rcases v.isPrime.mem_or_mem hn with h | h
      · exact ⟨p, hp, h⟩
      · by_cases hk1 : k = 1
        · subst hk1
          exact absurd (v.asIdeal.eq_top_of_isUnit_mem (by simpa using h) isUnit_one) v.isPrime.ne_top
        · exact ih k (lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hk0) hp.one_lt) h hk1 hk0
  refine key (Ideal.absNorm v.asIdeal) (Ideal.absNorm_mem v.asIdeal) ?_ ?_
  · rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  · rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot

theorem absNorm_asIdeal_eq {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) :
    Ideal.absNorm v.asIdeal = p := by
  have hdvd : Ideal.absNorm v.asIdeal ∣ p := by
    have h1 : Ideal.span {(p : 𝓞 ℚ)} ≤ v.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hv
    have h2 := Ideal.absNorm_dvd_absNorm_of_le h1
    have h3 : Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) = p := by
      rw [Ideal.absNorm_span_singleton]
      have : (p : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (p : ℤ) := by simp
      rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one, Int.natAbs_natCast]
    rwa [h3] at h2
  have hne1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact absurd h hne1
  · exact h

theorem slash_eq (f : CuspForm (Gamma1 N) 1) (ε : SL(2, ℤ)) (hε : ε ∈ Gamma1 N) :
    (⇑f) ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = ⇑f :=
  SlashInvariantForm.slash_action_eqn f (ε : GL (Fin 2) ℝ) ⟨ε, hε, rfl⟩

theorem slash_eq_smul_of_hasNebentypus (ψ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hψ : CuspForm.HasNebentypus ψ f) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    (⇑f) ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = ψ ((γ 1 1 : ℤ) : ZMod N) • (⇑f) := by
  ext τ
  rw [← ModularForm.SL_slash, ModularForm.SL_slash_apply, hψ γ hγ τ, Pi.smul_apply, smul_eq_mul]
  have hd : UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
    simp [UpperHalfPlane.denom]
  have hd0 : UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ
  rw [hd] at hd0 ⊢
  rw [zpow_neg, zpow_one]
  field_simp

end Ws1.L1

end

open Ws1.L1 in
open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne in
open IsDedekindDomain NumberField.AdelicLevel in
open CongruenceSubgroup in
open scoped ModularForm MatrixGroups in

theorem solution
    (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf : CuspForm.IsPrimitiveForm ψ f) :
    weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f) ≠ 0 ∧
    ∀ g ∈ NumberField.AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel N),
      ∀ x, weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f) (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ g) =
        weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f) x := by
  classical
  have hN : N ≠ 0 := NeZero.ne N
  have hsl : ∀ ε : SL(2, ℤ), ε ∈ Gamma1 N → (⇑f) ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = ⇑f := slash_eq f

  have hΓ : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1
  have hf0 : ∃ τ : UpperHalfPlane, f τ ≠ 0 := by
    by_contra h
    push Not at h
    have han := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
    have h1 := hf.1.qCoeff_one
    have hzeroFn : (⇑f : UpperHalfPlane → ℂ) = (0 : ℂ) • (⇑f) := by
      ext τ; simp [h τ]
    have h2 : ModularFormClass.qCoeff ((0 : ℂ) • (⇑f)) 1 = 0 := by
      simp only [ModularFormClass.qCoeff]
      rw [UpperHalfPlane.qExpansion_smul han]
      simp
    rw [← hzeroFn] at h2
    rw [h2] at h1
    exact zero_ne_one h1
  refine ⟨?_, fun g hg x => ?_⟩
  · obtain ⟨g, hg⟩ := P2GProbe.Alpha.weightOneLift_exists_ne_zero hN (⇑f) hsl hf0
    exact fun h0 => hg (by rw [h0]; rfl)
  · have hu : AdelicDock.finEmbed (𝓞 ℚ) ℚ g ∈ (productionPinsCompact ℚ).U (Ideal.span {(N : 𝓞 ℚ)}) := by
      rw [P2GProbe.R7.mem_U_iff, AdelicDock.glFin_finEmbed, AdelicDock.glArch_finEmbed]
      exact ⟨hg, rfl⟩
    exact P2GProbe.R4a.weightOneLift_mul_of_mem_U hN (⇑f) hsl x hu

end S_DihedralWeightOne_weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm
end P2MW
export P2MW.S_DihedralWeightOne_weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm (solution)
