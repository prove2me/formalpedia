-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOfGamma1.isCuspidalFn_productionPinsGeneral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/a93a5c82-db5a-52d1-b7b9-7327075dad09

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent

import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_NumberField_AdelicTraceProducer
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
import Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_continuous
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_exists_forall_norm_le
import Theorems.Thm_CuspForm_intervalIntegral_slash_vadd_eq_zero
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_exists_forall_apply_unipotentGL2_add_ratArchLine_mul_eq_slash_apply_I
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOfGamma1_isCuspidalFn_productionPinsGeneral
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace Ws41
namespace Lift5

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix UpperHalfPlane MeasureTheory NumberField.AdelicBox NumberField.AdelicHaar

open scoped MatrixGroups ModularForm

local notation "𝔾" => GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "ν₀" => ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) (adelicBox ℚ)

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
    (hq : algebraMap K (FiniteAdeleRing R K) q ∈ AdelicLevel.integralFiniteAdeles R K) :
    ∃ r : R, algebraMap R K r = q := by
  have h : ∀ v : HeightOneSpectrum R, v.valuation K q ≤ 1 := fun v => by
    have h1 := hq v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      show (algebraMap K (FiniteAdeleRing R K) q) v = ((q : K) : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
    exact h1
  exact HeightOneSpectrum.mem_integers_of_valuation_le_one K q h

theorem exists_intCast_eq_of_mem_integralFiniteAdeles {q : ℚ}
    (hq : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ) :
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

theorem exists_borel_mul_mapGL (γ : GL (Fin 2) ℚ) :
    ∃ β : GL (Fin 2) ℚ, β ∈ AutomorphicForm.borelSubgroup ℚ ∧
      ∃ δ : SL(2, ℤ), γ = β * Matrix.SpecialLinearGroup.mapGL ℚ δ := by
  set c : ℚ := (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 with hc
  set d : ℚ := (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 with hd
  by_cases h0 : c = 0
  · exact ⟨γ, by rw [AutomorphicForm.mem_borelSubgroup_iff, ← hc, h0], 1, by rw [map_one, mul_one]⟩

  set r : ℚ := d / c with hr
  have hcop : IsCoprime r.num (-(r.den : ℤ)) := by
    refine IsCoprime.neg_right (Int.isCoprime_iff_gcd_eq_one.mpr ?_)
    rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast]
    exact r.reduced
  obtain ⟨g, -, hg⟩ := ModularGroup.bottom_row_surj (R := ℤ)
    (show ![r.num, -(r.den : ℤ)] ∈ {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} from hcop)
  have hg0 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = r.num := by
    have := congrFun hg 0; simpa using this
  have hg1 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = -(r.den : ℤ) := by
    have := congrFun hg 1; simpa using this

  let δ : SL(2, ℤ) := Matrix.SpecialLinearGroup.transpose g * ModularGroup.S
  have hδ00 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = r.num := by
    simp [δ, Matrix.SpecialLinearGroup.coe_transpose, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two, hg0]
  have hδ10 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -(r.den : ℤ) := by
    simp [δ, Matrix.SpecialLinearGroup.coe_transpose, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two, hg1]
  refine ⟨γ * Matrix.SpecialLinearGroup.mapGL ℚ δ, ?_, δ⁻¹, by rw [map_inv, mul_inv_cancel_right]⟩

  rw [AutomorphicForm.mem_borelSubgroup_iff, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe, Matrix.mul_apply,
    Fin.sum_univ_two, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, hδ00, hδ10, ← hc, ← hd]
  have hden : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hnum : (r.num : ℚ) = r * r.den := (div_eq_iff hden).mp (Rat.num_div_den r)
  simp only [map_neg, eq_intCast, Int.cast_natCast]
  rw [hnum, hr]
  field_simp
  ring

variable {M : ℕ}

theorem slash_unipotent_mul_apply_I (F : UpperHalfPlane → ℂ) (r : ℝ) (H : GL (Fin 2) ℝ) :
    (F ∣[(2 : ℤ)] (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), r; 0, 1]
        (by rw [Matrix.det_fin_two_of]; norm_num) * H)) UpperHalfPlane.I
      = ((fun z : UpperHalfPlane => F (r +ᵥ z)) ∣[(2 : ℤ)] H) UpperHalfPlane.I := by
  set n : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), r; 0, 1]
    (by rw [Matrix.det_fin_two_of]; norm_num) with hn
  have hdetn : n.det.val = 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hn]
    simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two_of]
  have hslash : F ∣[(2 : ℤ)] n = fun z => F (r +ᵥ z) := by
    funext z
    have hpos : 0 < n.det.val := by rw [hdetn]; exact one_pos
    have hsmul : n • z = r +ᵥ z := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_smul_of_det_pos hpos, UpperHalfPlane.coe_vadd, UpperHalfPlane.num, UpperHalfPlane.denom, hn]
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
      ring
    rw [ModularForm.slash_apply, UpperHalfPlane.σ, if_pos hpos, hsmul, hdetn, UpperHalfPlane.denom, hn]
    simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
  rw [SlashAction.slash_mul, hslash]

theorem ratArchGL2_unipotentGL2 (x : InfiniteAdeleRing ℚ) (y : FiniteAdeleRing (𝓞 ℚ) ℚ) (t r : ℝ)
    (hr : InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default) (x default) = r) :
    LanglandsTunnell.ratArchGL2 (unipotentGL2 (R := 𝔸) (x + NumberField.StandardAddChar.ratArchLine t, y))
      = Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), r + t; 0, 1]
          (by rw [Matrix.det_fin_two_of]; norm_num) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have hE : ∀ (a : 𝔸) (i j : Fin 2), ((LanglandsTunnell.ratArchGL2 (unipotentGL2 (R := 𝔸) a) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j
      = InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)
          (((((unipotentGL2 (R := 𝔸) a : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 default)) := fun a i j => rfl
  rw [hE, unipotentGL2_coe]
  set φ := InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default) with hφ
  fin_cases i <;> fin_cases j
  · show φ (((1 : 𝔸)).1 default) = 1
    rw [show ((1 : 𝔸)).1 default = 1 from rfl, map_one]
  · show φ (x default + NumberField.StandardAddChar.ratArchLine t default) = r + t
    rw [map_add, NumberField.StandardAddChar.ratArchLine_apply, hr, hφ, RingEquiv.apply_symm_apply]
  · show φ (((0 : 𝔸)).1 default) = 0
    rw [show ((0 : 𝔸)).1 default = 0 from rfl, map_zero]
  · show φ (((1 : 𝔸)).1 default) = 1
    rw [show ((1 : 𝔸)).1 default = 1 from rfl, map_one]

theorem constantTerm_eq_zero_of_arch_mul [NeZero M] {f : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {φ : 𝔾 → ℂ} (hφ : CuspForm.IsAdelicLiftOfGamma1 f φ)
    {h₁ q : 𝔾} (hh₁ : glFin (𝓞 ℚ) ℚ h₁ = 1) (hh₁pos : 0 < (LanglandsTunnell.ratArchGL2 h₁).det.val)
    (hq : glArch (𝓞 ℚ) ℚ q = 1) (hqint : glFin (𝓞 ℚ) ℚ q ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ) :
    constantTerm ν₀ (fun x => unipotentGL2 x) φ (h₁ * q) = 0 := by
  haveI : IsProbabilityMeasure ν₀ := isProbabilityMeasure_cond_adelicBox ℚ
  have hM : M ≠ 0 := NeZero.ne M
  have hnpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  set K : ℝ → 𝔸 → ℂ := fun s x => φ (unipotentGL2 (R := 𝔸) (x.1 + NumberField.StandardAddChar.ratArchLine s, x.2) * (h₁ * q)) with hKdef

  have hA : ∀ s : ℝ, constantTerm ν₀ (fun x => unipotentGL2 x) φ (h₁ * q) = ∫ x, K s x ∂ν₀ := by
    intro s
    rw [← AutomorphicForm.constantTerm_adelicBox_unipotentGL2_mul ℚ (φ := φ)
      (fun k g => hφ.left_inv (unipotentGL2 k) g) ((NumberField.StandardAddChar.ratArchLine s, 0) : 𝔸) (h₁ * q)]
    unfold constantTerm constantTermIntegrand
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show φ (unipotentGL2 x * (unipotentGL2 (R := 𝔸) (NumberField.StandardAddChar.ratArchLine s, 0) * (h₁ * q))) = K s x
    rw [hKdef, ← mul_assoc, ← unipotentGL2_add]
    show φ (unipotentGL2 (R := 𝔸) (x + (show 𝔸 from (NumberField.StandardAddChar.ratArchLine s, 0))) * (h₁ * q))
      = φ (unipotentGL2 (R := 𝔸) (x.1 + NumberField.StandardAddChar.ratArchLine s, x.2) * (h₁ * q))
    congr 3
    exact Prod.ext rfl (add_zero _)

  have hB : ∀ x : 𝔸, x ∈ adelicBox ℚ → ∫ s in (0 : ℝ)..(M : ℝ), K s x = 0 := by
    intro x hx
    obtain ⟨ρ, hρ⟩ := CuspForm.IsAdelicLiftOfGamma1.exists_forall_apply_unipotentGL2_add_ratArchLine_mul_eq_slash_apply_I
      hφ x hx.2 h₁ q hh₁ hh₁pos hq hqint
    set r : ℝ := InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default) (x.1 default) with hr
    set H : GL (Fin 2) ℝ := LanglandsTunnell.ratArchGL2 h₁ with hH
    set z : UpperHalfPlane := H • UpperHalfPlane.I with hz
    have hK : ∀ s : ℝ, K s x = ((⇑f ∣[(2 : ℤ)] ((ρ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)) ((r + s) +ᵥ z))
        * (((H.det.val : ℝ) : ℂ)) ^ (1 : ℤ) * UpperHalfPlane.denom H UpperHalfPlane.I ^ (-2 : ℤ) := by
      intro s
      have h1 := hρ s
      rw [hKdef]
      show φ (unipotentGL2 (R := 𝔸) (x.1 + NumberField.StandardAddChar.ratArchLine s, x.2) * (h₁ * q)) = _
      have hcoe : ((ρ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) = ((ρ : GL (Fin 2) ℝ))⁻¹ := by
        show Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ρ⁻¹) = _
        rw [map_inv, map_inv]
      rw [h1, ratArch_mul, ratArchGL2_unipotentGL2 x.1 x.2 s r hr.symm, ← hH, ← hcoe,
        SlashAction.slash_mul, slash_unipotent_mul_apply_I _ _ H]

      have hσ : ∀ w : ℂ, σ H w = w := fun w => by rw [UpperHalfPlane.σ, if_pos hh₁pos]; rfl
      rw [ModularForm.slash_apply, hσ, abs_of_pos hh₁pos, ← hz]
      norm_num
    simp_rw [hK]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
    simp_rw [add_comm r, add_vadd]
    rw [CuspForm.intervalIntegral_slash_vadd_eq_zero f ρ⁻¹ (r +ᵥ z), zero_mul, zero_mul]

  have hKcont : Continuous (Function.uncurry K) := by
    have h0 : Continuous fun p : ℝ × 𝔸 => ((p.2.1 + NumberField.StandardAddChar.ratArchLine p.1, p.2.2) : 𝔸) :=
      ((continuous_fst.comp continuous_snd).add
        (NumberField.StandardAddChar.continuous_ratArchLine.comp continuous_fst)).prodMk (continuous_snd.comp continuous_snd)
    have h2 : Continuous fun p : ℝ × 𝔸 => (unipotentGL2 (R := 𝔸) (p.2.1 + NumberField.StandardAddChar.ratArchLine p.1, p.2.2) : 𝔾) * (h₁ * q) :=
      (AutomorphicForm.continuous_unipotentGL2.comp h0).mul continuous_const
    exact (CuspForm.IsAdelicLiftOfGamma1.continuous hφ).comp h2
  obtain ⟨C, hC⟩ := CuspForm.IsAdelicLiftOfGamma1.exists_forall_norm_le hφ
  have hmeas : MeasurableSet (adelicBox ℚ) := measurableSet_adelicBox ℚ
  have hint : Integrable (Function.uncurry K) ((volume.restrict (Set.Ioc (0 : ℝ) M)).prod ν₀) :=
    memLp_one_iff_integrable.mp (MemLp.of_bound hKcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun p => hC _))
  have hswap : ∫ s in (0 : ℝ)..(M : ℝ), ∫ x, K s x ∂ν₀ = ∫ x, (∫ s in (0 : ℝ)..(M : ℝ), K s x) ∂ν₀ := by
    rw [intervalIntegral.integral_of_le hnpos.le]
    simp_rw [intervalIntegral.integral_of_le hnpos.le]
    exact integral_integral_swap hint
  have hinner : ∫ x, (∫ s in (0 : ℝ)..(M : ℝ), K s x) ∂ν₀ = 0 := by
    calc ∫ x, (∫ s in (0 : ℝ)..(M : ℝ), K s x) ∂ν₀ = ∫ _x, (0 : ℂ) ∂ν₀ := by
          refine integral_congr_ae ?_
          filter_upwards [ProbabilityTheory.ae_cond_mem hmeas] with x hx
          exact hB x hx
      _ = 0 := integral_zero _ _
  have hCT : ∫ s in (0 : ℝ)..(M : ℝ), constantTerm ν₀ (fun x => unipotentGL2 x) φ (h₁ * q)
      = ∫ s in (0 : ℝ)..(M : ℝ), ∫ x, K s x ∂ν₀ :=
    intervalIntegral.integral_congr fun s _ => hA s
  have hconst : ∫ s in (0 : ℝ)..(M : ℝ), constantTerm ν₀ (fun x => unipotentGL2 x) φ (h₁ * q)
      = ((M : ℝ) : ℂ) * constantTerm ν₀ (fun x => unipotentGL2 x) φ (h₁ * q) := by
    rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul]
  have hmain : ((M : ℝ) : ℂ) * constantTerm ν₀ (fun x => unipotentGL2 x) φ (h₁ * q) = 0 := by
    rw [← hconst, hCT, hswap, hinner]
  have hn' : ((M : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hM
  exact (mul_eq_zero.mp hmain).resolve_left hn'

theorem intCast_mem_integralFiniteAdeles' (n : ℤ) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ) ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by
  intro v
  have h := NumberField.AdelicBox.algebraMap_mem_adicCompletionIntegers (R := 𝓞 ℚ) (K := ℚ) v (n : 𝓞 ℚ)
  rw [map_intCast] at h
  exact h

theorem constantTerm_eq_zero [NeZero M] {f : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {φ : 𝔾 → ℂ} (hφ : CuspForm.IsAdelicLiftOfGamma1 f φ) (g : 𝔾) :
    constantTerm ν₀ (fun x => unipotentGL2 x) φ g = 0 := by
  have hM : M ≠ 0 := NeZero.ne M
  obtain ⟨γ, h, u, hh, hpos, hu, hg⟩ := exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hM g
  have hhpos : 0 < (LanglandsTunnell.ratArchGL2 h).det.val := hpos
  obtain ⟨β, hβ, δ, hγ⟩ := exists_borel_mul_mapGL γ
  set k : 𝔾 := globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ δ) with hk
  have hg' : g = globalPoints (𝓞 ℚ) ℚ β * (k * h * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) := by
    rw [hg, hγ, map_mul, hk]
    simp only [mul_assoc]
  rw [hg', AutomorphicForm.constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup ℚ (φ := φ)
    (fun γ' _ h' => hφ.left_inv γ' h') hβ]
  have harch : archPart h = h :=
    eq_of_glArch_eq_of_glFin_eq (glArch_archPart h) (by rw [glFin_archPart, hh])
  have hsplit : k * h * AdelicDock.finEmbed (𝓞 ℚ) ℚ u = archPart k * h * (finPart k * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) := by
    calc k * h * AdelicDock.finEmbed (𝓞 ℚ) ℚ u = archPart k * finPart k * archPart h * AdelicDock.finEmbed (𝓞 ℚ) ℚ u := by
          rw [archPart_mul_finPart, harch]
      _ = archPart k * (archPart h * finPart k) * AdelicDock.finEmbed (𝓞 ℚ) ℚ u := by rw [archPart_mul_finPart_comm h k]; group
      _ = archPart k * h * (finPart k * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) := by rw [harch]; group
  rw [hsplit]
  refine constantTerm_eq_zero_of_arch_mul hφ ?_ ?_ ?_ ?_
  · rw [map_mul, glFin_archPart, one_mul, hh]
  · rw [ratArch_mul, ratArch_archPart, hk, ratArch_globalPoints_mapGL, map_mul, Units.val_mul,
      show ((δ : GL (Fin 2) ℝ)).det.val = 1 by simp, one_mul]
    exact hhpos
  · rw [map_mul, glArch_finPart, AdelicDock.glArch_finEmbed, mul_one]
  · rw [map_mul, glFin_finPart, AdelicDock.glFin_finEmbed]
    refine Subgroup.mul_mem _ ?_ ?_
    ·
      rw [mem_finiteIntegralGL2_iff, hk]
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [glFin_globalPoints_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
        exact intCast_mem_integralFiniteAdeles' _
      · rw [← map_inv, ← map_inv, ← map_inv, glFin_globalPoints_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
        exact intCast_mem_integralFiniteAdeles' _
    · exact (mem_finiteIntegralGL2_iff).mpr ⟨(finiteLevelOne_le_finiteLevelZero _ _ _ hu).1.integral,
        (finiteLevelOne_le_finiteLevelZero _ _ _ hu).2.integral⟩

end Ws41.Lift5

end

theorem solution
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) :
    @IsCuspidalFn _ (productionPinsGeneral ℚ).nS _ _ (productionPinsGeneral ℚ).ν unipotentGL2 Φ := by
  intro g
  exact Ws41.Lift5.constantTerm_eq_zero hΦ g

end S_CuspForm_IsAdelicLiftOfGamma1_isCuspidalFn_productionPinsGeneral
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOfGamma1_isCuspidalFn_productionPinsGeneral (solution)
