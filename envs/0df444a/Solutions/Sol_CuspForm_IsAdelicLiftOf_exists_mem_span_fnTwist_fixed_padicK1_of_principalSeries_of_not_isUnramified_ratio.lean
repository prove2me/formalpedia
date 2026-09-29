-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOf.exists_mem_span_fnTwist_fixed_padicK1_of_principalSeries_of_not_isUnramified_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/09dd0813-af8e-5395-a5d3-a98b513f1c1f

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_AdelicDock_LocalEmbedding
import Mathlib.NumberTheory.Padics.RingHoms
import Definitions.Def_LocalNewvector_CongruenceSubgroupK1
import Theorems.Thm_CuspForm_IsAdelicLiftOf_isUnramified_mul_of_linearMap_psCarrier_ne_zero
import Theorems.Thm_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_hasCharConductor_of_ratio
import Theorems.Thm_LocalNewvector_PSCarrier_finrank_fixedSubmodule_padicK1_of_add_le
import Theorems.Thm_LocalNewvector_exists_mem_fixedSubmodule_and_map_eq_of_map_mem_fixedSubmodule
import Theorems.Thm_CuspForm_IsAdelicLiftOf_levelZero_inv
import Theorems.Thm_LocalNewvector_gl2CongruenceSubgroup_le_padicK1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOf_exists_mem_span_fnTwist_fixed_padicK1_of_principalSeries_of_not_isUnramified_ratio
p2m_attr_erase "instance" "FLT.SpectralSide.instCompactSpaceMatrix"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv"

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace RamifiedRatioTwistDescent

section LocalComponent

variable (q : ℕ) [Fact q.Prime]

private noncomputable def iotaQ : ℚ_[q]ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ)).comp
    ((AdelicLevel.localUnit (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)).comp
      (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom))

private theorem iotaQ_apply (z : ℚ_[q]ˣ) :
    iotaQ q z = Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ)
      (AdelicLevel.localUnit (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
        (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom z)) := rfl

private noncomputable def etaLoc (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) : ℚ_[q]ˣ →* ℂˣ := η.comp (iotaQ q)

private theorem etaLoc_apply (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (z : ℚ_[q]ˣ) : etaLoc q η z = η (iotaQ q z) := rfl

private theorem exists_units_map_eq_of_norm_eq_one {u : ℚ_[q]ˣ} (hu : ‖(u : ℚ_[q])‖ = 1) :
    ∃ u' : ℤ_[q]ˣ, Units.map PadicInt.Coe.ringHom.toMonoidHom u' = u := by
  exact ⟨PadicInt.mkUnits hu, Units.ext rfl⟩

private theorem toZModPow_eq_one_of_norm_sub_one_le {b : ℕ} (u : ℤ_[q]ˣ)
    (h : b = 0 ∨ ‖((u : ℤ_[q]) : ℚ_[q]) - 1‖ ≤ (q : ℝ) ^ (-(b : ℤ))) :
    Units.map (PadicInt.toZModPow b).toMonoidHom u = 1 := by
  rcases h with hb | hle
  · subst hb
    haveI : Subsingleton (ZMod (q ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero q)
    exact Subsingleton.elim _ _
  · apply Units.ext
    rw [Units.coe_map, Units.val_one, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    have hmem : (u : ℤ_[q]) - 1 ∈ Ideal.span {(q : ℤ_[q]) ^ b} := by
      rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
      have : ‖((u : ℤ_[q]) - 1 : ℤ_[q])‖ = ‖((u : ℤ_[q]) : ℚ_[q]) - 1‖ := by
        rw [PadicInt.norm_def]; push_cast; rfl
      rw [this]; exact hle
    have hker : (u : ℤ_[q]) - 1 ∈ RingHom.ker (PadicInt.toZModPow b) := by
      rw [PadicInt.ker_toZModPow]; exact hmem
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hker
    exact hker

private theorem exists_hasCharConductor_le {μ : ℚ_[q]ˣ →* ℂˣ} {b : ℕ}
    (h : ∀ u ∈ LocalNewvector.higherUnits q b, μ u = 1) :
    ∃ n ≤ b, LocalNewvector.HasCharConductor q μ n := by
  classical
  have hex : ∃ n, ∀ u ∈ LocalNewvector.higherUnits q n, μ u = 1 := ⟨b, h⟩
  refine ⟨Nat.find hex, Nat.find_min' hex h, Nat.find_spec hex, fun m hm => ?_⟩
  have := Nat.find_min hex hm
  push Not at this
  exact this

end LocalComponent

section Determinants

variable (q : ℕ) [Fact q.Prime]

private theorem det_borelElem (a₁ a₂ : ℚ_[q]ˣ) (x : ℚ_[q]) :
    Matrix.GeneralLinearGroup.det (LocalNewvector.borelElem q a₁ a₂ x) = a₁ * a₂ := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, LocalNewvector.coe_borelElem, Matrix.det_fin_two_of,
    Units.val_mul]
  ring

private theorem coe_centralGL (z : ℚ_[q]ˣ) :
    ((LocalNewvector.centralGL q z : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) =
      Matrix.scalar (Fin 2) (z : ℚ_[q]) := by
  show algebraMap ℚ_[q] (Matrix (Fin 2) (Fin 2) ℚ_[q]) (z : ℚ_[q]) = _
  rw [Matrix.algebraMap_eq_diagonal]
  ext i j
  rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  rfl

private theorem centralGL_eq_borelElem (z : ℚ_[q]ˣ) :
    LocalNewvector.centralGL q z = LocalNewvector.borelElem q z z 0 := by
  apply Units.ext
  rw [coe_centralGL, LocalNewvector.coe_borelElem]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

private theorem exists_det_eq_of_mem_gl2CongruenceSubgroup {n : ℕ} (hn : 1 ≤ n) {k : GL (Fin 2) ℚ_[q]}
    (hk : k ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q n) :
    ∃ d : ℤ_[q]ˣ, Units.map PadicInt.Coe.ringHom.toMonoidHom d = Matrix.GeneralLinearGroup.det k ∧
      ‖((d : ℤ_[q]) : ℚ_[q]) - 1‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := by
  have hent := (FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff_of_one_le q hn).mp hk
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (Nat.Prime.one_lt (Fact.out (p := q.Prime))).le
  have hr1 : (q : ℝ) ^ (-(n : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ hq1 (by omega)
  have hrpos : (0 : ℝ) < (q : ℝ) ^ (-(n : ℤ)) := by positivity
  have h00 : ‖(k : Matrix (Fin 2) (Fin 2) ℚ_[q]) 0 0 - 1‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := by
    simpa [Matrix.sub_apply] using hent 0 0
  have h11 : ‖(k : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 1 - 1‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := by
    simpa [Matrix.sub_apply] using hent 1 1
  have h01 : ‖(k : Matrix (Fin 2) (Fin 2) ℚ_[q]) 0 1‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := by
    simpa [Matrix.sub_apply] using hent 0 1
  have h10 : ‖(k : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := by
    simpa [Matrix.sub_apply] using hent 1 0
  have hdet : (k : Matrix (Fin 2) (Fin 2) ℚ_[q]).det - 1 =
      ((k : Matrix (Fin 2) (Fin 2) ℚ_[q]) 0 0 - 1) * ((k : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 1 - 1) +
        ((k : Matrix (Fin 2) (Fin 2) ℚ_[q]) 0 0 - 1) + ((k : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 1 - 1) -
          (k : Matrix (Fin 2) (Fin 2) ℚ_[q]) 0 1 * (k : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0 := by
    rw [Matrix.det_fin_two]
    ring
  have hA : ‖((k : Matrix (Fin 2) (Fin 2) ℚ_[q]) 0 0 - 1) * ((k : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 1 - 1)‖ ≤
      (q : ℝ) ^ (-(n : ℤ)) := by
    rw [norm_mul]
    calc _ ≤ (q : ℝ) ^ (-(n : ℤ)) * 1 := mul_le_mul h00 (h11.trans hr1) (norm_nonneg _) hrpos.le
      _ = _ := mul_one _
  have hD : ‖(k : Matrix (Fin 2) (Fin 2) ℚ_[q]) 0 1 * (k : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0‖ ≤
      (q : ℝ) ^ (-(n : ℤ)) := by
    rw [norm_mul]
    calc _ ≤ (q : ℝ) ^ (-(n : ℤ)) * 1 := mul_le_mul h01 (h10.trans hr1) (norm_nonneg _) hrpos.le
      _ = _ := mul_one _
  have hbound : ‖(k : Matrix (Fin 2) (Fin 2) ℚ_[q]).det - 1‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := by
    rw [hdet, sub_eq_add_neg]
    refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
    · refine (Padic.nonarchimedean _ _).trans (max_le ?_ h11)
      exact (Padic.nonarchimedean _ _).trans (max_le hA h00)
    · rw [norm_neg]
      exact hD
  have hlt : ‖(k : Matrix (Fin 2) (Fin 2) ℚ_[q]).det - 1‖ < 1 :=
    lt_of_le_of_lt hbound (zpow_lt_one_of_neg₀ (Nat.one_lt_cast.mpr (Nat.Prime.one_lt (Fact.out (p := q.Prime))))
      (by omega))
  have hnorm : ‖(k : Matrix (Fin 2) (Fin 2) ℚ_[q]).det‖ = 1 := by
    have h := Padic.add_eq_max_of_ne (p := q)
      (show ‖(k : Matrix (Fin 2) (Fin 2) ℚ_[q]).det - 1‖ ≠ ‖(1 : ℚ_[q])‖ by rw [norm_one]; exact hlt.ne)
    rw [sub_add_cancel, norm_one] at h
    rw [h, max_eq_right hlt.le]
  refine ⟨PadicInt.mkUnits hnorm, Units.ext ?_, hbound⟩
  rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.GeneralLinearGroup.val_det_apply]
  rfl

end Determinants

section PSTwist

variable (q : ℕ) [Fact q.Prime]

private theorem mul_chiDet_mem_principalSeries (χ μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
    (hχ : IsLocallyConstant fun g : GL (Fin 2) ℚ_[q] => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ))
    {f : GL (Fin 2) ℚ_[q] → ℂ} (hf : f ∈ LocalNewvector.principalSeries q μ₁ μ₂) :
    (fun g => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * f g) ∈
      LocalNewvector.principalSeries q (μ₁ * χ) (μ₂ * χ) := by
  obtain ⟨hlc, htr⟩ := (LocalNewvector.mem_principalSeries_iff q).mp hf
  refine (LocalNewvector.mem_principalSeries_iff q).mpr ⟨hχ.mul hlc, fun a₁ a₂ x g => ?_⟩
  show ((χ (Matrix.GeneralLinearGroup.det (LocalNewvector.borelElem q a₁ a₂ x * g)) : ℂˣ) : ℂ) * f _ = _
  rw [map_mul, det_borelElem, htr, map_mul, map_mul, MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul,
    Units.val_mul, Units.val_mul, Units.val_mul]
  ring

private noncomputable def psTwist (χ μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
    (hχ : IsLocallyConstant fun g : GL (Fin 2) ℚ_[q] => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) :
    LocalNewvector.PSCarrier q μ₁ μ₂ →ₗ[ℂ] LocalNewvector.PSCarrier q (μ₁ * χ) (μ₂ * χ) where
  toFun f := LocalNewvector.PSCarrier.mk q (μ₁ * χ) (μ₂ * χ)
    ⟨fun g => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * LocalNewvector.PSCarrier.toFn q μ₁ μ₂ f g,
      mul_chiDet_mem_principalSeries q χ μ₁ μ₂ hχ (LocalNewvector.PSCarrier.toFn_mem q μ₁ μ₂ f)⟩
  map_add' f f' := LocalNewvector.PSCarrier.ext q _ _ fun g => by
    show _ * (LocalNewvector.PSCarrier.toFn q μ₁ μ₂ f g + LocalNewvector.PSCarrier.toFn q μ₁ μ₂ f' g) =
      _ * LocalNewvector.PSCarrier.toFn q μ₁ μ₂ f g + _ * LocalNewvector.PSCarrier.toFn q μ₁ μ₂ f' g
    ring
  map_smul' c f := LocalNewvector.PSCarrier.ext q _ _ fun g => by
    show _ * (c * LocalNewvector.PSCarrier.toFn q μ₁ μ₂ f g) = c * (_ * LocalNewvector.PSCarrier.toFn q μ₁ μ₂ f g)
    ring

private theorem toFn_psTwist (χ μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
    (hχ : IsLocallyConstant fun g : GL (Fin 2) ℚ_[q] => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ))
    (f : LocalNewvector.PSCarrier q μ₁ μ₂) (g : GL (Fin 2) ℚ_[q]) :
    LocalNewvector.PSCarrier.toFn q _ _ (psTwist q χ μ₁ μ₂ hχ f) g =
      ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * LocalNewvector.PSCarrier.toFn q μ₁ μ₂ f g := rfl

private theorem psTwist_smul (χ μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
    (hχ : IsLocallyConstant fun g : GL (Fin 2) ℚ_[q] => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ))
    (x : GL (Fin 2) ℚ_[q]) (f : LocalNewvector.PSCarrier q μ₁ μ₂) :
    psTwist q χ μ₁ μ₂ hχ (x • f) =
      (((χ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) • (x • psTwist q χ μ₁ μ₂ hχ f) := by
  refine LocalNewvector.PSCarrier.ext q _ _ fun g => ?_
  rw [toFn_psTwist, LocalNewvector.PSCarrier.toFn_smul, LocalNewvector.PSCarrier.toFn_csmul,
    LocalNewvector.PSCarrier.toFn_smul, toFn_psTwist, map_mul, map_mul, Units.val_mul]
  have hx : (((χ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
      ((χ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) = 1 := Units.inv_mul _
  linear_combination (-(((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
    LocalNewvector.PSCarrier.toFn q μ₁ μ₂ f (g * x))) * hx

private theorem psTwist_injective (χ μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
    (hχ : IsLocallyConstant fun g : GL (Fin 2) ℚ_[q] => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) :
    Function.Injective (psTwist q χ μ₁ μ₂ hχ) := by
  intro f f' h
  refine LocalNewvector.PSCarrier.ext q _ _ fun g => ?_
  have := congrArg (fun F => LocalNewvector.PSCarrier.toFn q _ _ F g) h
  simp only [toFn_psTwist] at this
  exact mul_left_cancel₀ (Units.ne_zero _) this

end PSTwist

section Embedding

variable (q : ℕ) [Fact q.Prime]

private theorem coe_padicGL_eq_mapMatrix (x : GL (Fin 2) ℚ_[q]) :
    (AdelicDock.padicGL q x : Matrix (Fin 2) (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ)) =
      (AdelicDock.padicRingEquiv q : ℚ_[q] →+* (AdelicDock.padicPlace q).adicCompletion ℚ).mapMatrix
        (x : Matrix (Fin 2) (Fin 2) ℚ_[q]) := by
  ext i j
  rw [AdelicDock.padicGL_apply, RingHom.mapMatrix_apply, Matrix.map_apply, RingEquiv.coe_toRingHom]

private theorem localUnit_val_apply_self (t : ((AdelicDock.padicPlace q).adicCompletion ℚ)ˣ) :
    ((AdelicLevel.localUnit (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) (AdelicDock.padicPlace q) = t := by
  classical
  show Function.update (1 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w.adicCompletion ℚ) (AdelicDock.padicPlace q)
      (t : (AdelicDock.padicPlace q).adicCompletion ℚ) (AdelicDock.padicPlace q) = t
  simp

private theorem localUnit_val_apply_of_ne (t : ((AdelicDock.padicPlace q).adicCompletion ℚ)ˣ)
    {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ AdelicDock.padicPlace q) :
    ((AdelicLevel.localUnit (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) w = 1 := by
  classical
  show Function.update (1 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w.adicCompletion ℚ) (AdelicDock.padicPlace q)
      (t : (AdelicDock.padicPlace q).adicCompletion ℚ) w = 1
  simp [Function.update_of_ne hw]

private theorem det_padicToAdelic (x : GL (Fin 2) ℚ_[q]) :
    Matrix.GeneralLinearGroup.det (AdelicDock.padicToAdelic q x) = iotaQ q (Matrix.GeneralLinearGroup.det x) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, AdelicDock.padicToAdelic_apply, AdelicDock.coe_finEmbed,
    AdelicDock.padicToFinAdelic_apply, AdelicDock.coe_localEmbed, iotaQ_apply, Units.coe_map]
  refine Prod.ext ?_ ?_
  · have h := RingHom.map_det (AdelicLevel.adeleArch (𝓞 ℚ) ℚ)
      (AdelicDock.finMat (𝓞 ℚ) ℚ (AdelicDock.localMat (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
        (AdelicDock.padicGL q x : Matrix _ _ _)))
    rw [AdelicDock.mapMatrix_arch_finMat, Matrix.det_one] at h
    exact h
  · have h := RingHom.map_det (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)
      (AdelicDock.finMat (𝓞 ℚ) ℚ (AdelicDock.localMat (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
        (AdelicDock.padicGL q x : Matrix _ _ _)))
    rw [AdelicDock.mapMatrix_fin_finMat] at h
    refine h.trans ?_
    rw [AdelicLevel.finIncl_apply_snd]
    ext w : 1
    show (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w)
        (AdelicDock.localMat (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicDock.padicGL q x : Matrix _ _ _)).det = _
    rw [RingHom.map_det]
    by_cases hw : w = AdelicDock.padicPlace q
    · subst hw
      rw [AdelicDock.mapMatrix_localMat_self, coe_padicGL_eq_mapMatrix, ← RingHom.map_det, RingEquiv.coe_toRingHom,
        localUnit_val_apply_self]
      rfl
    · rw [AdelicDock.mapMatrix_localMat_of_ne (𝓞 ℚ) ℚ _ _ hw, Matrix.det_one, localUnit_val_apply_of_ne q _ hw]

private theorem chiDet_padicToAdelic (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (x : GL (Fin 2) ℚ_[q]) :
    AutomorphicForm.chiDet (𝓞 ℚ) ℚ η (AdelicDock.padicToAdelic q x) =
      ((etaLoc q η (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) := by
  show ((η (Matrix.GeneralLinearGroup.det (AdelicDock.padicToAdelic q x)) : ℂˣ) : ℂ) = _
  rw [det_padicToAdelic, etaLoc_apply]

private theorem padicToAdelic_mul_comm_of (A : GL (Fin 2) ℚ_[q]) (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)
    (hc : (AdelicDock.padicGL q A : Matrix (Fin 2) (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ)) *
        (AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ h) : Matrix _ _ _) =
      (AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ h) : Matrix _ _ _) *
        (AdelicDock.padicGL q A : Matrix _ _ _)) :
    AdelicDock.padicToAdelic q A * h = h * AdelicDock.padicToAdelic q A := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, AdelicDock.padicToAdelic_apply, AdelicDock.coe_finEmbed,
    AdelicDock.padicToFinAdelic_apply, AdelicDock.coe_localEmbed]
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_
  · rw [map_mul, map_mul, AdelicDock.mapMatrix_arch_finMat, one_mul, mul_one]
  · rw [map_mul, map_mul, AdelicDock.mapMatrix_fin_finMat]
    refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    rw [map_mul, map_mul]
    by_cases hw : w = AdelicDock.padicPlace q
    · subst hw
      rw [AdelicDock.mapMatrix_localMat_self]
      have hh : (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)).mapMatrix
          ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) =
          (AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ h) :
            Matrix _ _ _) := by
        ext i j
        rfl
      rw [hh, hc]
    · rw [AdelicDock.mapMatrix_localMat_of_ne (𝓞 ℚ) ℚ _ _ hw, one_mul, mul_one]

private theorem exists_padicGL_eq (B : GL (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ)) :
    ∃ A : GL (Fin 2) ℚ_[q], AdelicDock.padicGL q A = B := by
  refine ⟨Matrix.GeneralLinearGroup.map (AdelicDock.padicRingEquiv q).symm.toRingHom B, ?_⟩
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicDock.padicGL_apply, Matrix.GeneralLinearGroup.map_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]

private theorem exists_eq_padicToAdelic_mul_comm (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ (x : GL (Fin 2) ℚ_[q]) (g' : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ),
      g = AdelicDock.padicToAdelic q x * g' ∧
        ∀ y : GL (Fin 2) ℚ_[q], AdelicDock.padicToAdelic q y * g' = g' * AdelicDock.padicToAdelic q y := by
  obtain ⟨x, hx⟩ := exists_padicGL_eq q
    (AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ g))
  refine ⟨x, (AdelicDock.padicToAdelic q x)⁻¹ * g, by rw [mul_inv_cancel_left], fun y => ?_⟩
  refine padicToAdelic_mul_comm_of q y _ ?_
  have h1 : AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
      (AdelicLevel.glFin (𝓞 ℚ) ℚ ((AdelicDock.padicToAdelic q x)⁻¹ * g)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_inv, AdelicDock.glFin_padicToAdelic,
      AdelicDock.finComponent_padicToFinAdelic_self, hx, inv_mul_cancel]
  rw [h1, Units.val_one, mul_one, one_mul]

private theorem padicToAdelic_centralGL_comm (z : ℚ_[q]ˣ) (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    AdelicDock.padicToAdelic q (LocalNewvector.centralGL q z) * h =
      h * AdelicDock.padicToAdelic q (LocalNewvector.centralGL q z) := by
  refine padicToAdelic_mul_comm_of q _ h ?_
  rw [coe_padicGL_eq_mapMatrix, coe_centralGL]
  have hmap : (AdelicDock.padicRingEquiv q : ℚ_[q] →+* (AdelicDock.padicPlace q).adicCompletion ℚ).mapMatrix
      (Matrix.scalar (Fin 2) (z : ℚ_[q])) = Matrix.scalar (Fin 2) (AdelicDock.padicRingEquiv q (z : ℚ_[q])) := by
    ext i j : 1
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply, Matrix.diagonal_apply]
    split_ifs
    · rfl
    · exact map_zero _
  rw [hmap]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq

private theorem isLevelZeroMatrix_padicToFinAdelic_borelElem (N : Ideal (𝓞 ℚ))
    (a₁ a₂ : ℚ_[q]ˣ) (x : ℚ_[q]) (h₁ : ‖(a₁ : ℚ_[q])‖ ≤ 1) (h₂ : ‖(a₂ : ℚ_[q])‖ ≤ 1) (hx : ‖x‖ ≤ 1) :
    AdelicLevel.IsLevelZeroMatrix (𝓞 ℚ) ℚ N
      (AdelicDock.padicToFinAdelic q (LocalNewvector.borelElem q a₁ a₂ x) : Matrix _ _ _) := by
  rw [AdelicDock.padicToFinAdelic_apply, AdelicDock.coe_localEmbed]
  refine ⟨fun i j w => ?_, fun w => ?_⟩
  · by_cases hw : w = AdelicDock.padicPlace q
    · subst hw
      rw [AdelicDock.localMat_apply_self, AdelicDock.padicGL_apply, ← AdelicDock.norm_le_one_iff_mem,
        LocalNewvector.coe_borelElem]
      fin_cases i <;> fin_cases j <;> simp [h₁, h₂, hx]
    · rw [AdelicDock.localMat_apply_of_ne (𝓞 ℚ) ℚ _ _ i j hw, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  · by_cases hw : w = AdelicDock.padicPlace q
    · subst hw
      have h10 : (!![(a₁ : ℚ_[q]), x; 0, (a₂ : ℚ_[q])] : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 0 = 0 := by simp
      rw [AdelicDock.localMat_apply_self, AdelicDock.padicGL_apply, LocalNewvector.coe_borelElem, h10, map_zero,
        map_zero]
      exact zero_le'
    · rw [AdelicDock.localMat_apply_of_ne (𝓞 ℚ) ℚ _ _ 1 0 hw, Matrix.one_apply_ne (by decide), map_zero]
      exact zero_le'

private theorem padicToFinAdelic_centralGL_mem_finiteLevelZero (N : Ideal (𝓞 ℚ)) (u : ℚ_[q]ˣ)
    (hu : ‖(u : ℚ_[q])‖ = 1) :
    AdelicDock.padicToFinAdelic q (LocalNewvector.centralGL q u) ∈ AdelicLevel.finiteLevelZero (𝓞 ℚ) ℚ N := by
  have hinv : ‖((u⁻¹ : ℚ_[q]ˣ) : ℚ_[q])‖ = 1 := by rw [Units.val_inv_eq_inv_val, norm_inv, hu, inv_one]
  rw [centralGL_eq_borelElem, AdelicLevel.mem_finiteLevelZero_iff, ← map_inv, LocalNewvector.borelElem_inv]
  exact ⟨isLevelZeroMatrix_padicToFinAdelic_borelElem q N u u 0 hu.le hu.le (by simp),
    isLevelZeroMatrix_padicToFinAdelic_borelElem q N u⁻¹ u⁻¹ _ hinv.le hinv.le (by simp)⟩

end Embedding

section SpanTwist

variable (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (Φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)

private noncomputable def untwistFn : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] LocalNewvector.AdelicFnCarrier ℚ where
  toFun ψ := LocalNewvector.AdelicFnCarrier.mk fun g =>
    (((η (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * ψ.toFn g
  map_add' ψ ψ' := LocalNewvector.AdelicFnCarrier.ext fun g => by
    simp only [LocalNewvector.AdelicFnCarrier.toFn_mk, LocalNewvector.AdelicFnCarrier.toFn_add, Pi.add_apply]
    ring
  map_smul' c ψ := LocalNewvector.AdelicFnCarrier.ext fun g => by
    simp only [LocalNewvector.AdelicFnCarrier.toFn_mk, LocalNewvector.AdelicFnCarrier.toFn_csmul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

private theorem toFn_untwistFn (ψ : LocalNewvector.AdelicFnCarrier ℚ) (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    (untwistFn η ψ).toFn g = (((η (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * ψ.toFn g := rfl

private theorem untwistFn_smul (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) (ψ : LocalNewvector.AdelicFnCarrier ℚ) :
    untwistFn η (g • ψ) = ((η (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • (g • untwistFn η ψ) := by
  refine LocalNewvector.AdelicFnCarrier.ext fun x => ?_
  rw [toFn_untwistFn, LocalNewvector.AdelicFnCarrier.toFn_smul, LocalNewvector.AdelicFnCarrier.toFn_csmul,
    Pi.smul_apply, LocalNewvector.AdelicFnCarrier.toFn_smul, toFn_untwistFn, smul_eq_mul, map_mul, map_mul,
    mul_inv_rev, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]

private theorem untwistFn_mk_fnTwist :
    untwistFn η (LocalNewvector.AdelicFnCarrier.mk (AutomorphicForm.fnTwist ℚ η Φ)) =
      LocalNewvector.AdelicFnCarrier.mk Φ := by
  refine LocalNewvector.AdelicFnCarrier.ext fun g => ?_
  rw [toFn_untwistFn, LocalNewvector.AdelicFnCarrier.toFn_mk, LocalNewvector.AdelicFnCarrier.toFn_mk,
    AutomorphicForm.fnTwist_apply]
  show _ * (((η (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * Φ g) = Φ g
  rw [← mul_assoc, Units.inv_mul, one_mul]

private theorem untwistFn_mem (ψ : LocalNewvector.AdelicFnCarrier ℚ)
    (hψ : ψ ∈ LocalNewvector.AdelicSpanSubmodule (AutomorphicForm.fnTwist ℚ η Φ)) :
    untwistFn η ψ ∈ LocalNewvector.AdelicSpanSubmodule Φ := by
  refine Submodule.span_induction (fun ψ' hψ' => ?_) (by rw [map_zero]; exact zero_mem _)
    (fun x y _ _ hx hy => by rw [map_add]; exact add_mem hx hy)
    (fun c x _ hx => by rw [map_smul]; exact Submodule.smul_mem _ c hx) hψ
  obtain ⟨g, rfl⟩ := hψ'
  rw [untwistFn_smul, untwistFn_mk_fnTwist]
  exact Submodule.smul_mem _ _ (LocalNewvector.smul_mem_adelicSpanSubmodule Φ g
    (LocalNewvector.mk_mem_adelicSpanSubmodule Φ))

private noncomputable def untwist :
    LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ) →ₗ[ℂ] LocalNewvector.AdelicSpan Φ where
  toFun ψ := LocalNewvector.AdelicSpan.mk Φ (untwistFn η (LocalNewvector.AdelicSpan.toFn _ ψ))
    (untwistFn_mem η Φ _ (ψ : LocalNewvector.AdelicSpanSubmodule (AutomorphicForm.fnTwist ℚ η Φ)).2)
  map_add' ψ ψ' := LocalNewvector.AdelicSpan.ext Φ (by
    show untwistFn η (LocalNewvector.AdelicSpan.toFn _ (ψ + ψ')) =
      untwistFn η (LocalNewvector.AdelicSpan.toFn _ ψ) + untwistFn η (LocalNewvector.AdelicSpan.toFn _ ψ')
    rw [← map_add]
    rfl)
  map_smul' c ψ := LocalNewvector.AdelicSpan.ext Φ (by
    show untwistFn η (LocalNewvector.AdelicSpan.toFn _ (c • ψ)) =
      c • untwistFn η (LocalNewvector.AdelicSpan.toFn _ ψ)
    rw [← map_smul]
    rfl)

private theorem toFn_untwist (ψ : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)) :
    LocalNewvector.AdelicSpan.toFn Φ (untwist η Φ ψ) = untwistFn η (LocalNewvector.AdelicSpan.toFn _ ψ) := rfl

private theorem untwist_smul (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)) :
    untwist η Φ (g • ψ) = ((η (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • (g • untwist η Φ ψ) := by
  refine LocalNewvector.AdelicSpan.ext Φ ?_
  rw [toFn_untwist, LocalNewvector.AdelicSpan.toFn_smul, untwistFn_smul]
  rfl

private theorem untwist_padic_smul (q : ℕ) [Fact q.Prime] (x : GL (Fin 2) ℚ_[q])
    (ψ : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)) :
    untwist η Φ (x • ψ) = ((etaLoc q η (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) • (x • untwist η Φ ψ) := by
  rw [LocalNewvector.AdelicSpan.padic_smul_def, untwist_smul, LocalNewvector.AdelicSpan.padic_smul_def,
    etaLoc_apply, det_padicToAdelic]

private theorem untwist_smul_self (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    untwist η Φ (g • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)) =
      ((η (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • (g • LocalNewvector.AdelicSpan.self Φ) := by
  rw [untwist_smul]
  congr 2
  refine LocalNewvector.AdelicSpan.ext Φ ?_
  rw [toFn_untwist, LocalNewvector.AdelicSpan.toFn_self, untwistFn_mk_fnTwist, LocalNewvector.AdelicSpan.toFn_self]

end SpanTwist

section SpanLemmas

variable (q : ℕ) [Fact q.Prime]

private theorem smul_mem_span_range (x : GL (Fin 2) ℚ_[q]) {φ' : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    {w : LocalNewvector.AdelicSpan φ'}
    (hw : w ∈ Submodule.span ℂ (Set.range fun y : GL (Fin 2) ℚ_[q] => y • LocalNewvector.AdelicSpan.self φ')) :
    x • w ∈ Submodule.span ℂ (Set.range fun y : GL (Fin 2) ℚ_[q] => y • LocalNewvector.AdelicSpan.self φ') := by
  refine Submodule.span_induction (fun w' hw' => ?_)
    (by rw [smul_zero]; exact zero_mem _) (fun a c _ _ ha hc => by rw [smul_add]; exact add_mem ha hc)
    (fun c a _ ha => by rw [smul_comm]; exact Submodule.smul_mem _ c ha) hw
  obtain ⟨y, rfl⟩ := hw'
  exact Submodule.subset_span ⟨x * y, by simp only [mul_smul]⟩

private theorem eq_zero_of_forall_apply_smul_self {φ' : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {N : Type*}
    [AddCommGroup N] [Module ℂ N] (T : LocalNewvector.AdelicSpan φ' →ₗ[ℂ] N)
    (hT : ∀ g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ, T (g • LocalNewvector.AdelicSpan.self φ') = 0) : T = 0 := by
  have key : ∀ χ (hχ : χ ∈ LocalNewvector.AdelicSpanSubmodule φ'),
      T (LocalNewvector.AdelicSpan.mk φ' χ hχ) = 0 := by
    intro χ hχ
    induction hχ using Submodule.span_induction with
    | mem χ' hχ' =>
      obtain ⟨g, rfl⟩ := hχ'
      exact hT g
    | zero => exact map_zero T
    | add a c ha hc iha ihc =>
      have : LocalNewvector.AdelicSpan.mk φ' (a + c) (add_mem ha hc) =
          LocalNewvector.AdelicSpan.mk φ' a ha + LocalNewvector.AdelicSpan.mk φ' c hc := rfl
      rw [this, map_add, iha, ihc, add_zero]
    | smul r a ha iha =>
      have : LocalNewvector.AdelicSpan.mk φ' (r • a) (Submodule.smul_mem _ r ha) =
          r • LocalNewvector.AdelicSpan.mk φ' a ha := rfl
      rw [this, map_smul, iha, smul_zero]
  refine LinearMap.ext fun ψ => ?_
  exact key _ (ψ : LocalNewvector.AdelicSpanSubmodule φ').2

end SpanLemmas

section Lift

variable {M : ℕ} [NeZero M] (q : ℕ) [Fact q.Prime]
  (Φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)

private theorem apply_mul_padicToAdelic_of_mem_padicK1 {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hΦg : g.IsAdelicLiftOf Φ) {n : ℕ} (hn : M.factorization q ≤ n) {k : GL (Fin 2) ℚ_[q]}
    (hk : k ∈ LocalNewvector.padicK1 q n) (x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    Φ (x * AdelicDock.padicToAdelic q k) = Φ x := by
  have hmem := AdelicDock.padicToAdelic_mem_levelOne q (NeZero.ne M) hn hk
  have hfin : AdelicDock.padicToFinAdelic q k ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) := by
    have := Subgroup.mem_comap.mp hmem
    rwa [AdelicDock.glFin_padicToAdelic] at this
  rw [AdelicDock.padicToAdelic_apply]
  exact hΦg.2.1 _ hfin x

private theorem centralGL_smul_mk_fnTwist {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hΦg : g.IsAdelicLiftOf Φ)
    (u : ℚ_[q]ˣ) (hu : ‖(u : ℚ_[q])‖ = 1) :
    (AdelicDock.padicToAdelic q (LocalNewvector.centralGL q u) : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) •
        LocalNewvector.AdelicFnCarrier.mk (AutomorphicForm.fnTwist ℚ η Φ) =
      (((etaLoc q η u : ℂˣ) : ℂ) ^ 2) • LocalNewvector.AdelicFnCarrier.mk (AutomorphicForm.fnTwist ℚ η Φ) := by
  refine LocalNewvector.AdelicFnCarrier.ext fun x => ?_
  rw [LocalNewvector.AdelicFnCarrier.toFn_smul, LocalNewvector.AdelicFnCarrier.toFn_csmul,
    LocalNewvector.AdelicFnCarrier.toFn_mk, Pi.smul_apply, smul_eq_mul, AutomorphicForm.fnTwist_apply,
    AutomorphicForm.fnTwist_apply]
  have hΦ : Φ (x * AdelicDock.padicToAdelic q (LocalNewvector.centralGL q u)) = Φ x := by
    rw [AdelicDock.padicToAdelic_apply]
    exact CuspForm.IsAdelicLiftOf.levelZero_inv (NeZero.ne M) hΦg _
      (padicToFinAdelic_centralGL_mem_finiteLevelZero q (AdelicDock.ratLevel M) u hu) x
  rw [hΦ]
  show ((η (Matrix.GeneralLinearGroup.det (x * _)) : ℂˣ) : ℂ) * Φ x =
    _ * (((η (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * Φ x)
  rw [map_mul, det_padicToAdelic, map_mul, Units.val_mul, ← etaLoc_apply, centralGL_eq_borelElem, det_borelElem,
    map_mul, Units.val_mul, sq]
  ring

private theorem centralGL_smul_eq {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hΦg : g.IsAdelicLiftOf Φ)
    (u : ℚ_[q]ˣ) (hu : ‖(u : ℚ_[q])‖ = 1) (ψ : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)) :
    LocalNewvector.centralGL q u • ψ = (((etaLoc q η u : ℂˣ) : ℂ) ^ 2) • ψ := by
  have hfix : ∀ χ ∈ LocalNewvector.AdelicSpanSubmodule (AutomorphicForm.fnTwist ℚ η Φ),
      (AdelicDock.padicToAdelic q (LocalNewvector.centralGL q u) : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) • χ =
        (((etaLoc q η u : ℂˣ) : ℂ) ^ 2) • χ := by
    intro χ hχ
    refine Submodule.span_induction (fun χ' hχ' => ?_) (by rw [smul_zero, smul_zero])
      (fun χ₁ χ₂ _ _ h₁ h₂ => by rw [smul_add, smul_add, h₁, h₂])
      (fun c χ' _ h => by rw [smul_comm, h, smul_comm]) hχ
    obtain ⟨h, rfl⟩ := hχ'
    rw [smul_smul, padicToAdelic_centralGL_comm, ← smul_smul, centralGL_smul_mk_fnTwist q Φ η hΦg u hu, smul_comm]
  apply LocalNewvector.AdelicSpan.ext
  rw [LocalNewvector.AdelicSpan.padic_smul_def q, LocalNewvector.AdelicSpan.toFn_smul]
  exact hfix _ (ψ : LocalNewvector.AdelicSpanSubmodule (AutomorphicForm.fnTwist ℚ η Φ)).2

private theorem etaLoc_det_eq_one {b : ℕ} (χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ)
    (hχu : ∀ x : ℤ_[q]ˣ, etaLoc q η (Units.map PadicInt.Coe.ringHom.toMonoidHom x) =
      (χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom x))⁻¹)
    {n : ℕ} (hn : 1 ≤ n) (hbn : b ≤ n) {k : GL (Fin 2) ℚ_[q]}
    (hk : k ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q n) :
    etaLoc q η (Matrix.GeneralLinearGroup.det k) = 1 := by
  obtain ⟨d, hd, hdn⟩ := exists_det_eq_of_mem_gl2CongruenceSubgroup q hn hk
  have hdb : b = 0 ∨ ‖((d : ℤ_[q]) : ℚ_[q]) - 1‖ ≤ (q : ℝ) ^ (-(b : ℤ)) := by
    right
    have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (Nat.Prime.one_lt (Fact.out (p := q.Prime))).le
    exact hdn.trans (zpow_le_zpow_right₀ hq1 (by omega))
  rw [← hd, hχu, toZModPow_eq_one_of_norm_sub_one_le q d hdb, map_one, inv_one]

private theorem isLocallyConstant_etaLoc_det {b : ℕ} (χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ)
    (hχu : ∀ x : ℤ_[q]ˣ, etaLoc q η (Units.map PadicInt.Coe.ringHom.toMonoidHom x) =
      (χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom x))⁻¹) :
    IsLocallyConstant fun g : GL (Fin 2) ℚ_[q] => ((etaLoc q η (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g => ?_
  have hopen : IsOpen ((fun k => g⁻¹ * k) ⁻¹'
      (FLT.SmoothVectors.gl2CongruenceSubgroup q (max b 1) : Set (GL (Fin 2) ℚ_[q]))) :=
    (FLT.SmoothVectors.isOpen_coe_gl2CongruenceSubgroup q _).preimage (continuous_const.mul continuous_id)
  have hg : g ∈ (fun k => g⁻¹ * k) ⁻¹'
      (FLT.SmoothVectors.gl2CongruenceSubgroup q (max b 1) : Set (GL (Fin 2) ℚ_[q])) := by
    show g⁻¹ * g ∈ (FLT.SmoothVectors.gl2CongruenceSubgroup q (max b 1) : Set (GL (Fin 2) ℚ_[q]))
    rw [inv_mul_cancel]
    exact Subgroup.one_mem _
  filter_upwards [hopen.mem_nhds hg] with k hk
  have hk' : g⁻¹ * k ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q (max b 1) := hk
  have : k = g * (g⁻¹ * k) := by rw [mul_inv_cancel_left]
  rw [this, map_mul, map_mul, etaLoc_det_eq_one q η χ₀ hχu (le_max_right b 1) (le_max_left b 1) hk', mul_one]

private theorem smooth_of_mem_span {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hΦg : g.IsAdelicLiftOf Φ)
    {b : ℕ} (χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ)
    (hχu : ∀ x : ℤ_[q]ˣ, etaLoc q η (Units.map PadicInt.Coe.ringHom.toMonoidHom x) =
      (χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom x))⁻¹) :
    ∀ w ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] =>
        x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)),
      ∃ U : Subgroup (GL (Fin 2) ℚ_[q]), IsOpen (U : Set (GL (Fin 2) ℚ_[q])) ∧ ∀ u ∈ U, u • w = w := by
  have hKfix : ∀ k ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q (max (M.factorization q) (max b 1)),
      k • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ) =
        LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ) := by
    intro k hk
    apply LocalNewvector.AdelicSpan.ext
    rw [LocalNewvector.AdelicSpan.padic_smul_def q, LocalNewvector.AdelicSpan.toFn_smul,
      LocalNewvector.AdelicSpan.toFn_self]
    refine LocalNewvector.AdelicFnCarrier.ext fun x => ?_
    rw [LocalNewvector.AdelicFnCarrier.toFn_smul, LocalNewvector.AdelicFnCarrier.toFn_mk,
      AutomorphicForm.fnTwist_apply, AutomorphicForm.fnTwist_apply,
      apply_mul_padicToAdelic_of_mem_padicK1 q Φ hΦg (le_max_left _ _)
        (LocalNewvector.gl2CongruenceSubgroup_le_padicK1 q _ hk) x]
    show ((η (Matrix.GeneralLinearGroup.det (x * _)) : ℂˣ) : ℂ) * Φ x =
      ((η (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * Φ x
    rw [map_mul, det_padicToAdelic, map_mul, ← etaLoc_apply,
      etaLoc_det_eq_one q η χ₀ hχu ((le_max_right b 1).trans (le_max_right _ _))
        ((le_max_left b 1).trans (le_max_right _ _)) hk, mul_one]
  intro w hw
  refine Submodule.span_induction (fun w' hw' => ?_) ⟨⊤, isOpen_univ, fun u _ => smul_zero u⟩
    (fun x y _ _ hx hy => ?_) (fun c x _ hx => ?_) hw
  · obtain ⟨x, rfl⟩ := hw'
    refine ⟨(FLT.SmoothVectors.gl2CongruenceSubgroup q (max (M.factorization q) (max b 1))).comap
      (MulAut.conj x⁻¹).toMonoidHom, ?_, fun u hu => ?_⟩
    · show IsOpen ((fun u => x⁻¹ * u * x⁻¹⁻¹) ⁻¹'
        (FLT.SmoothVectors.gl2CongruenceSubgroup q (max (M.factorization q) (max b 1)) : Set (GL (Fin 2) ℚ_[q])))
      exact (FLT.SmoothVectors.isOpen_coe_gl2CongruenceSubgroup q _).preimage
        ((continuous_const.mul continuous_id).mul continuous_const)
    · have hk : x⁻¹ * u * x⁻¹⁻¹ ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q (max (M.factorization q) (max b 1)) :=
        Subgroup.mem_comap.mp hu
      rw [inv_inv] at hk
      show u • x • LocalNewvector.AdelicSpan.self _ = x • LocalNewvector.AdelicSpan.self _
      have hux : u * x = x * (x⁻¹ * u * x) := by group
      rw [smul_smul, hux, ← smul_smul, hKfix _ hk]
  · obtain ⟨U₁, hU₁, h₁⟩ := hx
    obtain ⟨U₂, hU₂, h₂⟩ := hy
    exact ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun u hu => by rw [smul_add, h₁ u hu.1, h₂ u hu.2]⟩
  · obtain ⟨U, hU, h⟩ := hx
    exact ⟨U, hU, fun u hu => by rw [smul_comm, h u hu]⟩

end Lift

end RamifiedRatioTwistDescent

open RamifiedRatioTwistDescent in
theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (q : ℕ) [Fact q.Prime] (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
    (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hfequiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hf0 : f ≠ 0)
    (b : ℕ) (χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ)
    (hχ₀compat : ∀ u : ℤ_[q]ˣ,
      μ₁ (Units.map PadicInt.Coe.ringHom.toMonoidHom u) =
        χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom u))
    (hratio : ¬ LocalNewvector.IsUnramified q (μ₁⁻¹ * μ₂))
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hηu : ∀ u : ℤ_[q]ˣ,
      η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
          (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
            (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u))))
        = (χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom u))⁻¹) :
    ∃ y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ),
      y ∈ Submodule.span ℂ
        (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)) ∧
      y ≠ 0 ∧
      y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q b) (LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)) ∧
      ∀ u : ℤ_[q]ˣ, LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y =
        ((η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
            (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
              (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom
                (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) : ℂ) ^ 2) • y := by

  have hχu : ∀ x : ℤ_[q]ˣ, etaLoc q η (Units.map PadicInt.Coe.ringHom.toMonoidHom x) =
      (χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom x))⁻¹ := fun x => hηu x

  have hcentral : LocalNewvector.IsUnramified q (μ₁ * μ₂) :=
    CuspForm.IsAdelicLiftOf.isUnramified_mul_of_linearMap_psCarrier_ne_zero g q Φ hΦg μ₁ μ₂ f hfequiv hf0

  have hν₁ : LocalNewvector.HasCharConductor q (μ₁ * etaLoc q η) 0 := by
    rw [LocalNewvector.hasCharConductor_zero_iff_isUnramified]
    intro u hu
    obtain ⟨u', rfl⟩ := exists_units_map_eq_of_norm_eq_one q hu
    rw [MonoidHom.mul_apply, hχ₀compat, hχu, mul_inv_cancel]
  have hν₂b : ∀ u ∈ LocalNewvector.higherUnits q b, (μ₂ * etaLoc q η) u = 1 := by
    intro u hu
    obtain ⟨hnorm, hball⟩ := hu
    obtain ⟨u', rfl⟩ := exists_units_map_eq_of_norm_eq_one q hnorm
    have hred : Units.map (PadicInt.toZModPow b).toMonoidHom u' = 1 :=
      toZModPow_eq_one_of_norm_sub_one_le q u' hball
    have h1 : μ₁ (Units.map PadicInt.Coe.ringHom.toMonoidHom u') = 1 := by rw [hχ₀compat, hred, map_one]
    have h12 : (μ₁ * μ₂) (Units.map PadicInt.Coe.ringHom.toMonoidHom u') = 1 := hcentral _ hnorm
    rw [MonoidHom.mul_apply, h1, one_mul] at h12
    rw [MonoidHom.mul_apply, h12, hχu, hred, map_one, inv_one, mul_one]
  obtain ⟨n₂, hn₂b, hν₂⟩ := exists_hasCharConductor_le q hν₂b
  have hratio' : ¬ LocalNewvector.IsUnramified q ((μ₁ * etaLoc q η)⁻¹ * (μ₂ * etaLoc q η)) := by
    intro h
    apply hratio
    intro u hu
    have h1 := h u hu
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.mul_apply, MonoidHom.mul_apply, mul_inv,
      mul_mul_mul_comm, inv_mul_cancel, mul_one] at h1
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply]
    exact h1

  have hirr : LocalNewvector.IsIrreducibleGLRep q
      (LocalNewvector.PSCarrier q (μ₁ * etaLoc q η) (μ₂ * etaLoc q η)) :=
    LocalNewvector.PSCarrier.isIrreducibleGLRep_of_hasCharConductor_of_ratio q hν₁ hν₂ (fun h => absurd h hratio')

  have hrank := LocalNewvector.PSCarrier.finrank_fixedSubmodule_padicK1_of_add_le q hν₁ hν₂ (m := b) (by omega)
  obtain ⟨w₀, hw₀fix, hw₀⟩ : ∃ w₀ ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q b)
      (LocalNewvector.PSCarrier q (μ₁ * etaLoc q η) (μ₂ * etaLoc q η)), w₀ ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hbot : LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q b)
        (LocalNewvector.PSCarrier q (μ₁ * etaLoc q η) (μ₂ * etaLoc q η)) = ⊥ :=
      (Submodule.eq_bot_iff _).mpr hnone
    rw [hbot, finrank_bot] at hrank
    omega

  have hχlc := isLocallyConstant_etaLoc_det q η χ₀ hχu
  obtain ⟨T, hT, hTgen⟩ : ∃ T : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ) →ₗ[ℂ]
      LocalNewvector.PSCarrier q (μ₁ * etaLoc q η) (μ₂ * etaLoc q η),
      (∀ (x : GL (Fin 2) ℚ_[q]) v, T (x • v) = x • T v) ∧
        ∃ g₀ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ,
          T (g₀ • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)) ≠ 0 := by
    refine ⟨psTwist q (etaLoc q η) μ₁ μ₂ hχlc ∘ₗ f ∘ₗ untwist η Φ, fun x v => ?_, ?_⟩
    · show psTwist q (etaLoc q η) μ₁ μ₂ hχlc (f (untwist η Φ (x • v))) =
        x • psTwist q (etaLoc q η) μ₁ μ₂ hχlc (f (untwist η Φ v))
      rw [untwist_padic_smul, map_smul, hfequiv, map_smul, psTwist_smul, smul_smul, Units.mul_inv, one_smul]
    · by_contra hnone
      push Not at hnone
      apply hf0
      refine eq_zero_of_forall_apply_smul_self f fun g₀ => ?_
      have h1 : psTwist q (etaLoc q η) μ₁ μ₂ hχlc
          (f (untwist η Φ (g₀ • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)))) = 0 := hnone g₀
      rw [untwist_smul_self, map_smul, map_smul] at h1
      have h3 := (smul_eq_zero.mp h1).resolve_left (Units.ne_zero _)
      exact psTwist_injective q _ _ _ hχlc (h3.trans (map_zero _).symm)
  obtain ⟨g₀, hg₀⟩ := hTgen

  obtain ⟨x₀, g₁, hg₀eq, hcomm⟩ := exists_eq_padicToAdelic_mul_comm q g₀
  have hg₁ : T (g₁ • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)) ≠ 0 := by
    intro h0
    apply hg₀
    rw [hg₀eq, mul_smul, ← LocalNewvector.AdelicSpan.padic_smul_def, hT, h0, smul_zero]

  obtain ⟨T', hT', hT'self⟩ : ∃ T' : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ) →ₗ[ℂ]
      LocalNewvector.PSCarrier q (μ₁ * etaLoc q η) (μ₂ * etaLoc q η),
      (∀ (x : GL (Fin 2) ℚ_[q]) v, T' (x • v) = x • T' v) ∧
        T' (LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)) ≠ 0 := by
    refine ⟨T ∘ₗ DistribSMul.toLinearMap ℂ _ g₁, fun x v => ?_, hg₁⟩
    show T (g₁ • (x • v)) = x • T (g₁ • v)
    rw [← hT, LocalNewvector.AdelicSpan.padic_smul_def, LocalNewvector.AdelicSpan.padic_smul_def, smul_smul,
      smul_smul, hcomm]

  have hWstab : ∀ x : GL (Fin 2) ℚ_[q], ∀ w ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] =>
      x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)),
      x • w ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] =>
        x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)) :=
    fun x w hw => smul_mem_span_range q x hw
  have hselfW : LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ) ∈
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] =>
        x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)) :=
    Submodule.subset_span ⟨1, one_smul _ _⟩
  have hW'stab : ∀ x : GL (Fin 2) ℚ_[q], ∀ z ∈ (Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] =>
      x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ))).map T', x • z ∈
      (Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] =>
        x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ))).map T' := by
    rintro x z ⟨w, hw, rfl⟩
    exact ⟨x • w, hWstab x w hw, hT' x w⟩
  have hW'top : (Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] =>
      x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ))).map T' = ⊤ := by
    rcases hirr.2 _ hW'stab with h | h
    · exfalso
      apply hT'self
      have hmem := Submodule.mem_map_of_mem (f := T') hselfW
      rw [h, Submodule.mem_bot] at hmem
      exact hmem
    · exact h
  obtain ⟨v, hvW, hTv⟩ : ∃ v ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] =>
      x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)), T' v = w₀ := by
    have hmem : w₀ ∈ (Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] =>
        x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ))).map T' := by
      rw [hW'top]
      exact Submodule.mem_top
    exact Submodule.mem_map.mp hmem

  obtain ⟨y, hyW, hyfix, hTy⟩ :=
    LocalNewvector.exists_mem_fixedSubmodule_and_map_eq_of_map_mem_fixedSubmodule q (μ₁ * etaLoc q η)
      (μ₂ * etaLoc q η) T' hT' _ hWstab (smooth_of_mem_span q Φ η hΦg χ₀ hχu) b hvW (by rw [hTv]; exact hw₀fix)
  refine ⟨y, hyW, ?_, hyfix, fun u => ?_⟩
  · intro hy0
    apply hw₀
    rw [← hTv, ← hTy, hy0, map_zero]
  · have hu : ‖((Units.map PadicInt.Coe.ringHom.toMonoidHom u : ℚ_[q]ˣ) : ℚ_[q])‖ = 1 :=
      PadicInt.isUnit_iff.mp (Units.isUnit u)
    exact centralGL_smul_eq q Φ η hΦg _ hu y

#print axioms solution

end S_CuspForm_IsAdelicLiftOf_exists_mem_span_fnTwist_fixed_padicK1_of_principalSeries_of_not_isUnramified_ratio
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOf_exists_mem_span_fnTwist_fixed_padicK1_of_principalSeries_of_not_isUnramified_ratio (solution)
