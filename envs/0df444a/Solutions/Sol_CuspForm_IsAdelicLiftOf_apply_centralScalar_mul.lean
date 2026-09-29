-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOf.apply_centralScalar_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/0c020197-06a6-59db-99a5-2af0ad7ed520

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_RatIdele_Normalizer
import Theorems.Thm_CuspForm_IsAdelicLiftOf_levelZero_inv
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOf_apply_centralScalar_mul

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

noncomputable section

namespace Ws41
namespace Lift

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open scoped MatrixGroups ModularForm

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

local notation "𝔸ℚ" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸ℚf" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem centralScalar_mul_comm (z : (𝔸ℚ)ˣ) (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    centralScalar (𝓞 ℚ) ℚ z * x = x * centralScalar (𝓞 ℚ) ℚ z := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  show Matrix.scalar (Fin 2) (z : 𝔸ℚ) * (x : Matrix (Fin 2) (Fin 2) 𝔸ℚ)
      = (x : Matrix (Fin 2) (Fin 2) 𝔸ℚ) * Matrix.scalar (Fin 2) (z : 𝔸ℚ)
  exact (Matrix.scalar_commute (z : 𝔸ℚ) (fun r => Commute.all _ r) (x : Matrix (Fin 2) (Fin 2) 𝔸ℚ)).eq

theorem centralScalar_principal (q : ℚˣ) :
    centralScalar (𝓞 ℚ) ℚ (Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q)
      = globalPoints (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) q) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show ((Matrix.scalar (Fin 2)) ((algebraMap ℚ 𝔸ℚ) (q : ℚ))) i j
      = algebraMap ℚ 𝔸ℚ (((Matrix.scalar (Fin 2)) (q : ℚ)) i j)
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

def archOnly (w : (𝔸ℚ)ˣ) : (𝔸ℚ)ˣ := MulEquiv.prodUnits.symm ((MulEquiv.prodUnits w).1, 1)

def finOnly (w : (𝔸ℚ)ˣ) : (𝔸ℚ)ˣ := MulEquiv.prodUnits.symm (1, (MulEquiv.prodUnits w).2)

theorem coe_archOnly_fst (w : (𝔸ℚ)ˣ) : ((archOnly w : (𝔸ℚ)ˣ) : 𝔸ℚ).1 = (w : 𝔸ℚ).1 := rfl
theorem coe_archOnly_snd (w : (𝔸ℚ)ˣ) : ((archOnly w : (𝔸ℚ)ˣ) : 𝔸ℚ).2 = 1 := rfl
theorem coe_finOnly_fst (w : (𝔸ℚ)ˣ) : ((finOnly w : (𝔸ℚ)ˣ) : 𝔸ℚ).1 = 1 := rfl
theorem coe_finOnly_snd (w : (𝔸ℚ)ˣ) : ((finOnly w : (𝔸ℚ)ˣ) : 𝔸ℚ).2 = (w : 𝔸ℚ).2 := rfl

theorem archOnly_mul_finOnly (w : (𝔸ℚ)ˣ) : archOnly w * finOnly w = w := by
  refine Units.ext (Prod.ext ?_ ?_)
  · show ((archOnly w : (𝔸ℚ)ˣ) : 𝔸ℚ).1 * ((finOnly w : (𝔸ℚ)ˣ) : 𝔸ℚ).1 = (w : 𝔸ℚ).1
    rw [coe_archOnly_fst, coe_finOnly_fst, mul_one]
  · show ((archOnly w : (𝔸ℚ)ˣ) : 𝔸ℚ).2 * ((finOnly w : (𝔸ℚ)ˣ) : 𝔸ℚ).2 = (w : 𝔸ℚ).2
    rw [coe_archOnly_snd, coe_finOnly_snd, one_mul]

theorem glFin_centralScalar_archOnly (w : (𝔸ℚ)ˣ) :
    glFin (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ (archOnly w)) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glFin_apply, Units.val_one]
  show ((Matrix.scalar (Fin 2) ((archOnly w : (𝔸ℚ)ˣ) : 𝔸ℚ)) i j).2 = (1 : Matrix (Fin 2) (Fin 2) 𝔸ℚf) i j
  rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem glArch_centralScalar_finOnly (w : (𝔸ℚ)ˣ) :
    glArch (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ (finOnly w)) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glArch_apply, Units.val_one]
  show ((Matrix.scalar (Fin 2) ((finOnly w : (𝔸ℚ)ˣ) : 𝔸ℚ)) i j).1 = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j
  rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> rfl

def archScalar (w : (𝔸ℚ)ˣ) : ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default) ((w : 𝔸ℚ).1 default)

theorem archScalar_ne_zero (w : (𝔸ℚ)ˣ) : archScalar w ≠ 0 := by
  unfold archScalar
  rw [map_ne_zero]
  have hu : IsUnit ((w : 𝔸ℚ).1 default) := by
    have h1 : IsUnit ((w : 𝔸ℚ).1) := (Prod.isUnit_iff.mp w.isUnit).1
    exact h1.map (Pi.evalMonoidHom (fun v : InfinitePlace ℚ => v.Completion) default)
  exact hu.ne_zero

theorem coe_ratArchGL2_centralScalar_archOnly (w : (𝔸ℚ)ˣ) :
    ((LanglandsTunnell.ratArchGL2 (centralScalar (𝓞 ℚ) ℚ (archOnly w)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = archScalar w • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  show (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom
      ((((Matrix.scalar (Fin 2) ((archOnly w : (𝔸ℚ)ˣ) : 𝔸ℚ)) i j).1) default) = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs with h
  · rw [smul_eq_mul, mul_one]; rfl
  · rw [smul_zero]
    show (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom
        (((0 : 𝔸ℚ)).1 default) = 0
    exact map_zero _

theorem slash_two_scalar (f : UpperHalfPlane → ℂ) (c : GL (Fin 2) ℝ) (r : ℝ) (hr : r ≠ 0)
    (hc : (c : Matrix (Fin 2) (Fin 2) ℝ) = r • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    f ∣[(2 : ℤ)] c = f := by
  have h00 : c 0 0 = r := by
    have := congr_fun (congr_fun hc 0) 0; simpa using this
  have h01 : c 0 1 = 0 := by
    have := congr_fun (congr_fun hc 0) 1; simpa using this
  have h10 : c 1 0 = 0 := by
    have := congr_fun (congr_fun hc 1) 0; simpa using this
  have h11 : c 1 1 = r := by
    have := congr_fun (congr_fun hc 1) 1; simpa using this
  have hdet : c.det.val = r * r := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdetpos : 0 < c.det.val := by rw [hdet]; exact mul_self_pos.mpr hr
  have hsmul : ∀ z : UpperHalfPlane, c • z = z := by
    intro z
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdetpos, UpperHalfPlane.num, UpperHalfPlane.denom, h00, h01, h10, h11]
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    push_cast
    rw [zero_mul, zero_add, add_zero, mul_div_cancel_left₀ _ hr']
  funext z
  rw [ModularForm.slash_apply, UpperHalfPlane.σ, if_pos hdetpos, hsmul z, UpperHalfPlane.denom, h10, h11,
    hdet]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  simp only [ContinuousAlgEquiv.refl_apply, Complex.ofReal_zero, zero_mul, zero_add]
  field_simp
  rw [abs_of_nonneg (sq_nonneg r), show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one]
  push_cast
  ring

theorem det_ratArchGL2_centralScalar_archOnly_pos (w : (𝔸ℚ)ˣ) :
    LanglandsTunnell.ratArchGL2 (centralScalar (𝓞 ℚ) ℚ (archOnly w)) ∈ GLPos (Fin 2) ℝ := by
  have hc := coe_ratArchGL2_centralScalar_archOnly w
  set c := LanglandsTunnell.ratArchGL2 (centralScalar (𝓞 ℚ) ℚ (archOnly w))
  have h00 : c 0 0 = archScalar w := by
    have := congr_fun (congr_fun hc 0) 0; simpa using this
  have h01 : c 0 1 = 0 := by
    have := congr_fun (congr_fun hc 0) 1; simpa using this
  have h10 : c 1 0 = 0 := by
    have := congr_fun (congr_fun hc 1) 0; simpa using this
  have h11 : c 1 1 = archScalar w := by
    have := congr_fun (congr_fun hc 1) 1; simpa using this
  show 0 < c.det.val
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h01, h10, h11, mul_zero, sub_zero]
  exact mul_self_pos.mpr (archScalar_ne_zero w)

theorem glFin_centralScalar_finOnly_mem_finiteLevelZero (N : Ideal (𝓞 ℚ)) (w : (𝔸ℚ)ˣ)
    (hw : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((w : 𝔸ℚ).2 v) = 1) :
    glFin (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ (finOnly w)) ∈ finiteLevelZero (𝓞 ℚ) ℚ N := by
  have hw' : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v (((w⁻¹ : (𝔸ℚ)ˣ) : 𝔸ℚ).2 v) = 1 := fun v => by
    have h := RatIdele.valued_snd_inv_mul w v
    rwa [hw v, mul_one] at h
  have hint : ∀ (u : (𝔸ℚ)ˣ), (∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((u : 𝔸ℚ).2 v) = 1) →
      ∀ i j, ((Matrix.scalar (Fin 2) (u : 𝔸ℚ)) i j).2 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    intro u hu i j v
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (hu v).le
    · exact zero_mem _
  have hll : ∀ (u : (𝔸ℚ)ˣ), ((Matrix.scalar (Fin 2) (u : 𝔸ℚ)) 1 0).2 ∈ idealBall (𝓞 ℚ) ℚ N := by
    intro u
    rw [Matrix.scalar_apply, Matrix.diagonal_apply, if_neg (by decide)]
    exact zero_mem_idealBall N
  refine ⟨⟨fun i j => ?_, ?_⟩, ⟨fun i j => ?_, ?_⟩⟩
  · exact hint (finOnly w) (fun v => hw v) i j
  · exact hll (finOnly w)
  · rw [← map_inv, ← map_inv]
    exact hint (finOnly w)⁻¹ (fun v => hw' v) i j
  · rw [← map_inv, ← map_inv]
    exact hll (finOnly w)⁻¹

theorem valued_snd_mul_principal_inv (z : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (((z * (Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ)
        (Units.mk0 (RatIdele.ρ z) (RatIdele.ρ_ne_zero z)))⁻¹ : (𝔸ℚ)ˣ) : 𝔸ℚ).2 v) = 1 := by
  rw [RatIdele.valued_snd_mul, ← map_inv]
  show Valued.v ((z : 𝔸ℚ).2 v) *
      Valued.v (((algebraMap ℚ 𝔸ℚ) ((Units.mk0 (RatIdele.ρ z) (RatIdele.ρ_ne_zero z))⁻¹ : ℚˣ)).2 v) = 1
  rw [RatIdele.algebraMap_adeleRing_snd, RatIdele.valued_algebraMap_rat, (RatIdele.ρ_spec z).1 v,
    Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀,
    mul_inv_cancel₀ (by rw [← (RatIdele.ρ_spec z).1 v]; exact RatIdele.valued_snd_ne_zero z v)]

theorem finEmbed_glFin_of_glArch_eq_one' (u : AdelicGL2 (𝓞 ℚ) ℚ) (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ u) = u := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have hmat : AdelicDock.finMat (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) := by
    refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_
    · rw [AdelicDock.mapMatrix_arch_finMat]
      ext i j
      have h : (glArch (𝓞 ℚ) ℚ u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j
          = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j := by rw [hu, Units.val_one]
      rw [glArch_apply] at h
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply]
      exact h.symm
    · rw [AdelicDock.mapMatrix_fin_finMat]
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleFin_apply, glFin_apply]
  rw [AdelicDock.coe_finEmbed, hmat]

end Ws41.Lift

end

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix Ws41.Lift in
open scoped MatrixGroups ModularForm in
theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : g.IsAdelicLiftOf Φ)
    (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    Φ (centralScalar (𝓞 ℚ) ℚ z * x) = Φ x := by
  have hM : M ≠ 0 := NeZero.ne M

  set q : ℚˣ := Units.mk0 (RatIdele.ρ z) (RatIdele.ρ_ne_zero z) with hq
  set w : (AdeleRing (𝓞 ℚ) ℚ)ˣ := z * (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* _) q)⁻¹ with hw
  have hz : z = Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* _) q * w := by
    rw [hw, mul_inv_cancel_comm_assoc]
  have hwv : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((w : AdeleRing (𝓞 ℚ) ℚ).2 v) = 1 :=
    fun v => valued_snd_mul_principal_inv z v

  obtain ⟨γ, h, k, hh, hpos, hk, hx⟩ := exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hM x

  set a := centralScalar (𝓞 ℚ) ℚ (archOnly w) with ha
  set b := centralScalar (𝓞 ℚ) ℚ (finOnly w) with hb
  have hab : centralScalar (𝓞 ℚ) ℚ w = a * b := by
    rw [ha, hb, ← map_mul, archOnly_mul_finOnly]
  have hb_fin : b = AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ b) :=
    (Ws41.Lift.finEmbed_glFin_of_glArch_eq_one' b (glArch_centralScalar_finOnly w)).symm
  have hbK0 : glFin (𝓞 ℚ) ℚ b ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) :=
    glFin_centralScalar_finOnly_mem_finiteLevelZero _ w hwv

  have ca : ∀ X : AdelicGL2 (𝓞 ℚ) ℚ, a * X = X * a := fun X => centralScalar_mul_comm (archOnly w) X
  have cb : ∀ X : AdelicGL2 (𝓞 ℚ) ℚ, b * X = X * b := fun X => centralScalar_mul_comm (finOnly w) X
  have hfin_ah : glFin (𝓞 ℚ) ℚ (a * h) = 1 := by
    rw [map_mul, glFin_centralScalar_archOnly, one_mul, hh]
  have hpos_ah : LanglandsTunnell.ratArchGL2 (a * h) ∈ GLPos (Fin 2) ℝ := by
    rw [ratArch_mul]
    exact Subgroup.mul_mem _ (det_ratArchGL2_centralScalar_archOnly_pos w) hpos
  calc Φ (centralScalar (𝓞 ℚ) ℚ z * x)
      = Φ (globalPoints (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 2) q) * (centralScalar (𝓞 ℚ) ℚ w * x)) := by
        rw [hz, map_mul, centralScalar_principal, mul_assoc]
    _ = Φ (centralScalar (𝓞 ℚ) ℚ w * x) := hΦ.left_inv _ _
    _ = Φ (globalPoints (𝓞 ℚ) ℚ γ * (a * h) * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ b * k)) := by
        rw [hx, hab, map_mul, ← hb_fin]
        congr 1
        rw [mul_assoc a b, cb (globalPoints (𝓞 ℚ) ℚ γ * h * AdelicDock.finEmbed (𝓞 ℚ) ℚ k),
          mul_assoc (globalPoints (𝓞 ℚ) ℚ γ * h) (AdelicDock.finEmbed (𝓞 ℚ) ℚ k) b,
          ← mul_assoc a (globalPoints (𝓞 ℚ) ℚ γ * h), ← mul_assoc a (globalPoints (𝓞 ℚ) ℚ γ) h,
          ca (globalPoints (𝓞 ℚ) ℚ γ), mul_assoc (globalPoints (𝓞 ℚ) ℚ γ) a h,
          ← cb (AdelicDock.finEmbed (𝓞 ℚ) ℚ k)]
    _ = Φ (globalPoints (𝓞 ℚ) ℚ γ * (a * h)) :=
        CuspForm.IsAdelicLiftOf.levelZero_inv hM hΦ _
          (Subgroup.mul_mem _ hbK0 (finiteLevelOne_le_finiteLevelZero _ _ _ hk)) _
    _ = ((⇑g) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 (a * h)) UpperHalfPlane.I := by
        rw [hΦ.left_inv, hΦ.apply_eq (a * h) hfin_ah hpos_ah]
    _ = ((⇑g) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I := by
        rw [ratArch_mul, SlashAction.slash_mul,
          slash_two_scalar _ _ (archScalar w) (archScalar_ne_zero w) (coe_ratArchGL2_centralScalar_archOnly w)]
    _ = Φ x := by rw [hx, apply_decomp hΦ hh hpos hk]

end S_CuspForm_IsAdelicLiftOf_apply_centralScalar_mul
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOf_apply_centralScalar_mul (solution)
