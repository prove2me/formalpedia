-- Prove2me | solution 1 for DihedralWeightOne.weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/aad0c0f5-052c-5ce7-b00a-545d19048ae1

import Mathlib
import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_AutomorphicForm_ArchType
import Theorems.Thm_AutomorphicForm_exists_mem_productionPinsCompact_U_mul_eq_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DihedralWeightOne_weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift

set_option autoImplicit false

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

end LanglandsTunnell.P4.I2

end

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix UpperHalfPlane DihedralWeightOne

open scoped ModularForm MatrixGroups

namespace P2GProbe
namespace R1

variable (f : ℍ → ℂ)

private theorem weightOneArchLift_mul_of_slash_eq (γ h : GL (Fin 2) ℝ) (hγ : f ∣[(1 : ℤ)] γ = f)
    (hdet : γ.det.val = 1) :
    weightOneArchLift f (γ * h) = weightOneArchLift f h := by
  unfold weightOneArchLift
  rw [SlashAction.slash_mul, hγ]
  congr 2
  rw [map_mul, Units.val_mul, hdet, one_mul]

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

end P2GProbe.R4a

namespace P2GProbe
namespace R7

open LanglandsTunnell.P4.I2 AutomorphicForm.WindowedSiegel NumberField.AdelicVolume

end P2GProbe.R7

namespace P2GProbe
namespace R7

open LanglandsTunnell.P4.I2 MeasureTheory
open scoped Topology

end P2GProbe.R7

end

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix UpperHalfPlane DihedralWeightOne

open scoped ModularForm MatrixGroups

namespace P2GProbe
namespace R4a

open LanglandsTunnell.P4.I2 CongruenceSubgroup

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

end

open NumberField NumberField.AdelicLevel AutomorphicForm DihedralWeightOne IsDedekindDomain
open scoped MatrixGroups ModularForm

theorem solution
    {N : ℕ} (hN : N ≠ 0) (f : UpperHalfPlane → ℂ)
    (hf : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma1 N → f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = f) :
    (∀ (γ : GL (Fin 2) ℚ) (x : AdelicGL2 (𝓞 ℚ) ℚ),
        weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f (globalPoints (𝓞 ℚ) ℚ γ * x) =
          weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f x) ∧
    (∀ u ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel N), ∀ x : AdelicGL2 (𝓞 ℚ) ℚ,
        weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) =
          weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f x) ∧
    ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 →
      LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
        weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f h = weightOneArchLift f (LanglandsTunnell.ratArchGL2 h) := by
  refine ⟨fun γ x => P2GProbe.R4a.weightOneLift_globalPoints_mul hN f hf γ x, fun u hu x => ?_,
    fun h hh hpos => ?_⟩
  · exact P2GProbe.R4a.weightOneLift_mul_of_mem_U hN f hf x
      (Subgroup.mem_inf.mpr
        ⟨AdelicLevel.mem_levelOne_iff.mpr (by rw [AdelicDock.glFin_finEmbed]; exact hu),
         (mem_finiteAdelicGL2Subgroup_iff _ _).mpr (AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ u)⟩)
  · exact P2GProbe.R4a.weightOneLift_eq hN f hf h 1 h 1 (one_mem _) hh hpos
      (by rw [map_one, one_mul, mul_one])

end S_DihedralWeightOne_weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift
end P2MW
export P2MW.S_DihedralWeightOne_weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift (solution)
