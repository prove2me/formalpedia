-- Prove2me | solution 1 for CuspForm.IsNewform.exists_linearMap_fixedSubmodule_H1_gammaH_laws_of_isCuspidalOfType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/3e69f28f-6c4e-5bc4-9cda-f29df8a93428

import Mathlib
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor
import Definitions.Def_CohCarrier_Level
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_CuspForm_IsAdelicLiftOf_exists_linearMap_components_of_fixedSubmodule_of_range_eq_span
import Theorems.Thm_CuspForm_IsAdelicLiftOf_heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform
import Theorems.Thm_CuspForm_exists_linearEquiv_gamma_inf_gamma0_gammaH_slash_heckeDiagMatrix_and_periodOf_eq
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_comp_of_coe_eq_slash
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash
import Theorems.Thm_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero
import Theorems.Thm_ModularCurve_periodMapOf_apply_eq_periodOf
import Theorems.Thm_CuspForm_stableT
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_exists_linearMap_fixedSubmodule_H1_gammaH_laws_of_isCuspidalOfType
p2m_attr_erase "instance" "HeckeIntegralSeam.finite_padicInt_quotient_span_p HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace OccRoot

section Periods

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

theorem periodMapOf_add (f g : CuspForm Γ 2) :
    ModularCurve.periodMapOf Γ (f + g) = ModularCurve.periodMapOf Γ f + ModularCurve.periodMapOf Γ g := by
  refine AddMonoidHom.ext fun x => ?_
  rw [AddMonoidHom.add_apply, show x = Additive.ofMul (Additive.toMul x) from rfl,
    ModularCurve.periodMapOf_apply_eq_periodOf, ModularCurve.periodMapOf_apply_eq_periodOf,
    ModularCurve.periodMapOf_apply_eq_periodOf, map_add]

theorem periodMapOf_smul (c : ℂ) (f : CuspForm Γ 2) :
    ModularCurve.periodMapOf Γ (c • f) = c • ModularCurve.periodMapOf Γ f := by
  refine AddMonoidHom.ext fun x => ?_
  rw [AddMonoidHom.smul_apply, show x = Additive.ofMul (Additive.toMul x) from rfl,
    ModularCurve.periodMapOf_apply_eq_periodOf, ModularCurve.periodMapOf_apply_eq_periodOf, map_smul,
    smul_eq_mul]

noncomputable def periodMapLin : CuspForm Γ 2 →ₗ[ℂ] (Additive ↥Γ →+ ℂ) where
  toFun := ModularCurve.periodMapOf Γ
  map_add' := periodMapOf_add Γ
  map_smul' := periodMapOf_smul Γ

@[scoped simp] theorem periodMapLin_apply (f : CuspForm Γ 2) :
    periodMapLin Γ f = ModularCurve.periodMapOf Γ f := rfl

theorem eq_zero_of_periodMapOf_eq_zero (f : CuspForm Γ 2) (h : ModularCurve.periodMapOf Γ f = 0) :
    f = 0 := by
  apply ModularCurve.eq_zero_of_forall_re_periodOf_eq_zero Γ f
  intro γ
  rw [← ModularCurve.periodMapOf_apply_eq_periodOf, h, AddMonoidHom.zero_apply, Complex.zero_re]

end Periods

theorem gammaH_isCongruenceSubgroup (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    IsCongruenceSubgroup (CohCarrier.GammaH M H) := by
  refine ⟨M, NeZero.ne _, fun A hA => ?_⟩
  rw [Gamma_mem] at hA
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨by rw [Gamma0_mem]; exact hA.2.2.1, ?_⟩
  have h1 : CohCarrier.gamma0Units M ⟨A, by rw [Gamma0_mem]; exact hA.2.2.1⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    exact hA.2.2.2
  rw [h1]
  exact one_mem H

scoped instance gammaH_finiteIndex (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  (gammaH_isCongruenceSubgroup M H).finiteIndex

theorem heckeT_periodMapOf_eq_smul_of_heckeTLinH_eq_smul (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (F G : CuspForm (CohCarrier.GammaH M H) 2) (c : ℂ)
    (hT : CuspForm.heckeTLinH 2 hℓ hℓM F = c • G) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    CohCarrier.heckeT M H ℓ ℂ (ModularCurve.periodMapOf (CohCarrier.GammaH M H) F) =
      c • ModularCurve.periodMapOf (CohCarrier.GammaH M H) G := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hcoe := CuspForm.coe_heckeTLinH_apply (M := M) (H := H) 2 hℓ hℓM (CuspForm.stableT M H 2 hℓ hℓM) F
  have h89 := ModularCurve.periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash M H hℓ hℓM
    (CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM)) (CuspForm.gammaLift_apply_11 (M := M) hℓ hℓM)
    F (CuspForm.heckeTLinH 2 hℓ hℓM F) hcoe
  rw [← h89, hT, periodMapOf_smul]

section Model

variable {q : ℕ} [Fact q.Prime]
  {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ}
  {V : Type} [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
  [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]

theorem apply_mem_span (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ)
    (hfr : LinearMap.range f =
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (v : V) :
    f v ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ) := by
  rw [← hfr]; exact LinearMap.mem_range_self f v

theorem apply_mem_fixedSubmodule (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v)
    (w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)) :
    f (w : V) ∈ LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1)
      (LocalNewvector.AdelicSpan Φ) := by
  rw [LocalNewvector.mem_fixedSubmodule_iff]
  intro k hk
  rw [← hf, (LocalNewvector.mem_fixedSubmodule_iff.mp w.2) k hk]

theorem exists_unit_coe_eq {ℓ : ℕ} (h : (ℓ : ZMod q) ≠ 0) : ∃ ℓq : ℤ_[q]ˣ, (ℓq : ℤ_[q]) = ℓ := by
  have hu : IsUnit ((ℓ : ℕ) : ℤ_[q]) := by
    by_contra hx
    apply h
    have hm : ((ℓ : ℕ) : ℤ_[q]) ∈ IsLocalRing.maximalIdeal ℤ_[q] := hx
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast] at hm
    exact hm
  exact ⟨hu.unit, rfl⟩

theorem unitsMap_toZMod_eq_mk0 {ℓ : ℕ} (h : (ℓ : ZMod q) ≠ 0) (ℓq : ℤ_[q]ˣ) (hℓq : (ℓq : ℤ_[q]) = ℓ) :
    Units.map PadicInt.toZMod.toMonoidHom ℓq = Units.mk0 (ℓ : ZMod q) h := by
  ext
  rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, hℓq, map_natCast, Units.val_mk0]

end Model

section LevelIso

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

abbrev GamH : Subgroup SL(2, ℤ) := CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')

abbrev GamF : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M'

variable {q M'}

theorem cast_gamma0Units {A : SL(2, ℤ)} (hA0 : A ∈ Gamma0 (q ^ 2 * M')) :
    ((ZMod.unitsMap (ModularCurve.FullLevel.dvd_sq_mul q M') (CohCarrier.gamma0Units (q ^ 2 * M') ⟨A, hA0⟩) :
      (ZMod q)ˣ) : ZMod q) = ((A 1 1 : ℤ) : ZMod q) := by
  rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units]
  show ZMod.castHom _ (ZMod q) (((A 1 1 : ℤ) : ZMod (q ^ 2 * M'))) = _
  rw [map_intCast]

theorem mem_GamH_iff {A : SL(2, ℤ)} :
    A ∈ GamH q M' ↔ ((A 1 0 : ℤ) : ZMod (q ^ 2 * M')) = 0 ∧ ((A 1 1 : ℤ) : ZMod q) = 1 := by
  constructor
  · intro hA
    obtain ⟨hA0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hA
    refine ⟨Gamma0_mem.mp hA0, ?_⟩
    rw [ModularCurve.FullLevel.mem_levelH_iff] at hH
    rw [← cast_gamma0Units hA0, hH, Units.val_one]
  · rintro ⟨h10, h11⟩
    rw [CohCarrier.mem_GammaH_iff]
    refine ⟨Gamma0_mem.mpr h10, ?_⟩
    rw [ModularCurve.FullLevel.mem_levelH_iff]
    ext
    rw [cast_gamma0Units, h11, Units.val_one]

theorem mem_GamF_iff {A : SL(2, ℤ)} :
    A ∈ GamF q M' ↔ A ∈ CongruenceSubgroup.Gamma q ∧ ((A 1 0 : ℤ) : ZMod M') = 0 := by
  rw [Subgroup.mem_inf, Gamma0_mem]

theorem dvd_of_mem_GamH {A : SL(2, ℤ)} (hA : A ∈ GamH q M') : (q : ℤ) ∣ A 1 0 := by
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (mem_GamH_iff.mp hA).1
  refine dvd_trans ?_ h
  push_cast
  exact Dvd.intro ((q : ℤ) * M') (by ring)

theorem dvd_of_mem_GamF {A : SL(2, ℤ)} (hA : A ∈ GamF q M') : (q : ℤ) ∣ A 0 1 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma_mem.mp (mem_GamF_iff.mp hA).1).2.1

theorem det_entries (A : SL(2, ℤ)) : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  have := Matrix.SpecialLinearGroup.det_coe A
  rw [Matrix.det_fin_two] at this
  exact this

omit [Fact q.Prime] in
@[scoped simp] theorem conjLowerMat_apply_00 (A : SL(2, ℤ)) (h : (q : ℤ) ∣ A 1 0) :
    (CohCarrier.conjLowerMat q A h) 0 0 = A 0 0 := by simp [CohCarrier.conjLowerMat]
omit [Fact q.Prime] in
@[scoped simp] theorem conjLowerMat_apply_01 (A : SL(2, ℤ)) (h : (q : ℤ) ∣ A 1 0) :
    (CohCarrier.conjLowerMat q A h) 0 1 = A 0 1 * q := by simp [CohCarrier.conjLowerMat]
omit [Fact q.Prime] in
@[scoped simp] theorem conjLowerMat_apply_10 (A : SL(2, ℤ)) (h : (q : ℤ) ∣ A 1 0) :
    (CohCarrier.conjLowerMat q A h) 1 0 = A 1 0 / q := by simp [CohCarrier.conjLowerMat]
omit [Fact q.Prime] in
@[scoped simp] theorem conjLowerMat_apply_11 (A : SL(2, ℤ)) (h : (q : ℤ) ∣ A 1 0) :
    (CohCarrier.conjLowerMat q A h) 1 1 = A 1 1 := by simp [CohCarrier.conjLowerMat]
omit [Fact q.Prime] in
@[scoped simp] theorem conjUpperMat_apply_00 (A : SL(2, ℤ)) (h : (q : ℤ) ∣ A 0 1) :
    (CohCarrier.conjUpperMat q A h) 0 0 = A 0 0 := by simp [CohCarrier.conjUpperMat]
omit [Fact q.Prime] in
@[scoped simp] theorem conjUpperMat_apply_01 (A : SL(2, ℤ)) (h : (q : ℤ) ∣ A 0 1) :
    (CohCarrier.conjUpperMat q A h) 0 1 = A 0 1 / q := by simp [CohCarrier.conjUpperMat]

theorem conjLowerMat_mem_GamF {A : SL(2, ℤ)} (hA : A ∈ GamH q M') :
    CohCarrier.conjLowerMat q A (dvd_of_mem_GamH hA) ∈ GamF q M' := by
  obtain ⟨h10, h11⟩ := mem_GamH_iff.mp hA
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hquot : A 1 0 / (q : ℤ) = ((q * M' : ℕ) : ℤ) * t := by
    apply Int.ediv_eq_of_eq_mul_right hq0
    rw [ht]; push_cast; ring
  have hc : ((A 1 0 : ℤ) : ZMod q) = 0 := by
    rw [ht, ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact Dvd.intro ((q : ℤ) * M' * t) (by ring)
  have ha : ((A 0 0 : ℤ) : ZMod q) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod q)) (det_entries A)
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, h11, mul_one, mul_zero, sub_zero] at this
    exact this
  rw [mem_GamF_iff, Gamma_mem]
  simp only [conjLowerMat_apply_00, conjLowerMat_apply_01, conjLowerMat_apply_10, conjLowerMat_apply_11]
  refine ⟨⟨ha, ?_, ?_, h11⟩, ?_⟩
  · push_cast; simp
  · rw [hquot, ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact Dvd.intro ((M' : ℤ) * t) (by ring)
  · rw [hquot, ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact Dvd.intro ((q : ℤ) * t) (by ring)

theorem conjUpperMat_mem_GamH (hqM' : ¬ q ∣ M') {A : SL(2, ℤ)} (hA : A ∈ GamF q M') :
    CohCarrier.conjUpperMat q A (dvd_of_mem_GamF hA) ∈ GamH q M' := by
  obtain ⟨hAq, hAM⟩ := mem_GamF_iff.mp hA
  obtain ⟨_, _, h10, h11⟩ := Gamma_mem.mp hAq
  have hqc : (q : ℤ) ∣ A 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  have hMc : (M' : ℤ) ∣ A 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hAM
  have hcop : IsCoprime (q : ℤ) (M' : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).mpr hqM')).symm
  have hqM : (q : ℤ) * M' ∣ A 1 0 := hcop.mul_dvd hqc hMc
  rw [mem_GamH_iff]
  simp only [CohCarrier.conjUpperMat_apply_10, CohCarrier.conjUpperMat_apply_11]
  refine ⟨?_, h11⟩
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [show (q : ℤ) ^ 2 * M' = (q * M') * q by ring]
  exact mul_dvd_mul_right hqM _

variable (q M')

def up : ↥(GamH q M') →* ↥(GamF q M') where
  toFun δ := ⟨CohCarrier.conjLowerMat q δ (dvd_of_mem_GamH δ.2), conjLowerMat_mem_GamF δ.2⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [CohCarrier.conjLowerMat]
  map_mul' γ δ := Subtype.ext (CohCarrier.conjLowerMat_mul q _ _ (dvd_of_mem_GamH γ.2) (dvd_of_mem_GamH δ.2)
    (dvd_of_mem_GamH (γ * δ).2))

def down (hqM' : ¬ q ∣ M') : ↥(GamF q M') →* ↥(GamH q M') where
  toFun ε := ⟨CohCarrier.conjUpperMat q ε (dvd_of_mem_GamF ε.2), conjUpperMat_mem_GamH hqM' ε.2⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [CohCarrier.conjUpperMat]
  map_mul' γ δ := Subtype.ext (CohCarrier.conjUpperMat_mul q _ _ (dvd_of_mem_GamF γ.2) (dvd_of_mem_GamF δ.2)
    (dvd_of_mem_GamF (γ * δ).2))

def conjF (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 M') : ↥(GamF q M') →* ↥(GamF q M') where
  toFun ε := ⟨σ * ε * σ⁻¹, by
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp ε.2
    exact Subgroup.mem_inf.mpr ⟨(Gamma_normal q).conj_mem _ h1 σ,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hσ h2) (Subgroup.inv_mem _ hσ)⟩⟩
  map_one' := Subtype.ext (by simp)
  map_mul' γ δ := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[scoped simp] theorem coe_up_apply (δ : ↥(GamH q M')) :
    ((up q M' δ : ↥(GamF q M')) : SL(2, ℤ)) = CohCarrier.conjLowerMat q δ (dvd_of_mem_GamH δ.2) := rfl
@[scoped simp] theorem coe_down_apply (hqM' : ¬ q ∣ M') (ε : ↥(GamF q M')) :
    ((down q M' hqM' ε : ↥(GamH q M')) : SL(2, ℤ)) = CohCarrier.conjUpperMat q ε (dvd_of_mem_GamF ε.2) := rfl
@[scoped simp] theorem coe_conjF_apply (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 M') (ε : ↥(GamF q M')) :
    ((conjF q M' σ hσ ε : ↥(GamF q M')) : SL(2, ℤ)) = σ * ε * σ⁻¹ := rfl

theorem coe_conjLowerMat (A : SL(2, ℤ)) (h : (q : ℤ) ∣ A 1 0) :
    ((CohCarrier.conjLowerMat q A h : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      ModularForm.heckeDiagMatrix q * (A : GL (Fin 2) ℝ) * (ModularForm.heckeDiagMatrix q)⁻¹ := by
  have hq0 : (q : ℕ) ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
  rw [eq_mul_inv_iff_mul_eq]
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  have hqR' : ((q : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hq0
  have hdiv : (((A 1 0 / (q : ℤ) : ℤ)) : ℝ) = (A 1 0 : ℝ) / (q : ℝ) := by
    rw [Int.cast_div h hqR', Int.cast_natCast]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ModularForm.val_heckeDiagMatrix hq0, CohCarrier.conjLowerMat,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe, hdiv] <;>
    (first
      | ring1
      | (rw [mul_comm (q : ℝ), mul_inv_cancel_right₀ hqR])
      | (rw [mul_assoc, mul_inv_cancel₀ hqR, mul_one])
      | (rw [div_mul_cancel₀ _ hqR])
      | (rw [mul_div_cancel₀ _ hqR])
      | (rw [mul_comm, mul_assoc, inv_mul_cancel₀ hqR, mul_one]))

theorem coe_conjUpperMat (A : SL(2, ℤ)) (h : (q : ℤ) ∣ A 0 1) :
    ((CohCarrier.conjUpperMat q A h : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      (ModularForm.heckeDiagMatrix q)⁻¹ * (A : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix q := by
  have hq0 : (q : ℕ) ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
  rw [mul_assoc, eq_inv_mul_iff_mul_eq]
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  have hqR' : ((q : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hq0
  have hdiv : (((A 0 1 / (q : ℤ) : ℤ)) : ℝ) = (A 0 1 : ℝ) / (q : ℝ) := by
    rw [Int.cast_div h hqR', Int.cast_natCast]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ModularForm.val_heckeDiagMatrix hq0, CohCarrier.conjUpperMat,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe, hdiv] <;>
    (first
      | ring1
      | (rw [mul_comm (q : ℝ), mul_inv_cancel_right₀ hqR])
      | (rw [mul_assoc, mul_inv_cancel₀ hqR, mul_one])
      | (rw [div_mul_cancel₀ _ hqR])
      | (rw [mul_div_cancel₀ _ hqR])
      | (rw [mul_comm, mul_assoc, inv_mul_cancel₀ hqR, mul_one]))

theorem coe_down_conjF_up (hqM' : ¬ q ∣ M') (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 M')
    (δ : ↥(GamH q M')) :
    (((down q M' hqM' (conjF q M' σ hσ (up q M' δ)) : ↥(GamH q M')) : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      ((ModularForm.heckeDiagMatrix q)⁻¹ * (σ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix q) *
        ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        ((ModularForm.heckeDiagMatrix q)⁻¹ * (σ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix q)⁻¹ := by
  rw [coe_down_apply, coe_conjUpperMat, coe_conjF_apply, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv,
    coe_up_apply, coe_conjLowerMat]
  group

theorem det_pos_conj_heckeDiag (σ : SL(2, ℤ)) :
    0 < ((Matrix.GeneralLinearGroup.det
      ((ModularForm.heckeDiagMatrix q)⁻¹ * (σ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix q) : ℝˣ) : ℝ) := by
  have hdetσ : Matrix.GeneralLinearGroup.det (σ : GL (Fin 2) ℝ) = 1 := Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.det_coe, Units.val_one])
  rw [map_mul, map_mul, map_inv, hdetσ, mul_one, inv_mul_cancel, Units.val_one]
  exact one_pos

end LevelIso

theorem K2_conj_equivariance
    (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime] (hqN : ¬ q ∣ N)
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    (Fc1 : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) →ₗ[ℂ]
      CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) 2)
    (hE : ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 N → ∀ w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V),
        ⇑(Fc1 (LocalNewvector.gl2ReductionRep q V
            (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ)) w)) =
          (⇑(Fc1 w)) ∣[(2 : ℤ)] ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ))
    (L : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) 2 ≃ₗ[ℂ]
        CuspForm (CohCarrier.GammaH (q ^ 2 * N)
          (ZMod.unitsMap (dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) N)).ker) 2)
    (hL : ∀ F : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) 2,
          ⇑(L F) = (⇑F) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q)
    (red : Gamma0 N →* CuspidalType.GL2 q)
    (hred : red = (Matrix.SpecialLinearGroup.toGL.comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)
    (conj : ↥red.ker →* ↥(CohCarrier.GammaH (q ^ 2 * N) (ModularCurve.FullLevel.levelH q N)))
    (hconj : ∀ x : ↥red.ker,
          (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 =
            ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 ∧
          (q : ℤ) * (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 =
            ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 ∧
          (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 =
            (q : ℤ) * ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 ∧
          (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 =
            ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1)
    (γ y : Gamma0 N) (hy : y ∈ red.ker) (hy' : γ * y * γ⁻¹ ∈ red.ker) (w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)) :
    ModularCurve.periodMapOf (CohCarrier.GammaH (q ^ 2 * N) (ModularCurve.FullLevel.levelH q N))
        (L (Fc1 (LocalNewvector.gl2ReductionRep q V (red γ) w))) (Additive.ofMul (conj ⟨γ * y * γ⁻¹, hy'⟩)) =
      ModularCurve.periodMapOf (CohCarrier.GammaH (q ^ 2 * N) (ModularCurve.FullLevel.levelH q N))
        (L (Fc1 w)) (Additive.ofMul (conj ⟨y, hy⟩)) := by
  classical
  subst hred
  haveI : (CohCarrier.GammaH (q ^ 2 * N) (ModularCurve.FullLevel.levelH q N)).FiniteIndex := inferInstance
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hγ0 : ((γ : SL(2, ℤ)))⁻¹ ∈ CongruenceSubgroup.Gamma0 N := inv_mem γ.2

  let c : ↥(GamH q N) →* ↥(GamH q N) :=
    (down q N hqN).comp ((conjF q N ((γ : SL(2, ℤ)))⁻¹ hγ0).comp (up q N))

  let α : GL (Fin 2) ℝ := (ModularForm.heckeDiagMatrix q)⁻¹ *
    ((((γ : SL(2, ℤ)))⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix q
  have hα : 0 < ((Matrix.GeneralLinearGroup.det α : ℝˣ) : ℝ) := det_pos_conj_heckeDiag q _
  have hc : ∀ δ : ↥(GamH q N), (((c δ : ↥(GamH q N)) : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      α * ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) * α⁻¹ := fun δ =>
    coe_down_conjF_up q N hqN _ hγ0 δ

  have hredγ : ((Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp
      (Gamma0 N).subtype) γ =
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) (γ : SL(2, ℤ))) := rfl
  have hslash : ⇑(L (Fc1 (LocalNewvector.gl2ReductionRep q V
      (((Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp
        (Gamma0 N).subtype) γ) w))) = ⇑(L (Fc1 w)) ∣[(2 : ℤ)] α := by
    rw [hL, hL, hredγ, hE _ γ.2 w, ← SlashAction.slash_mul, ← SlashAction.slash_mul]
    congr 1
    simp only [α, ← mul_assoc, mul_inv_cancel, one_mul]
  have hper := ModularCurve.periodMapOf_gammaH_eq_comp_of_coe_eq_slash (q ^ 2 * N)
    (ModularCurve.FullLevel.levelH q N) α hα c hc (L (Fc1 w)) _ hslash
  rw [hper, AddMonoidHom.comp_apply]
  show ModularCurve.periodMapOf _ (L (Fc1 w)) (Additive.ofMul (c (conj ⟨γ * y * γ⁻¹, hy'⟩))) = _
  congr 2

  have hup : ∀ x : ↥(((Matrix.SpecialLinearGroup.toGL.comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype).ker),
      ((up q N (conj x) : ↥(GamF q N)) : SL(2, ℤ)) = ((x : Gamma0 N) : SL(2, ℤ)) := by
    intro x
    obtain ⟨h00, h01, h10, h11⟩ := hconj x
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, coe_up_apply, conjLowerMat_apply_00,
        conjLowerMat_apply_01, conjLowerMat_apply_10, conjLowerMat_apply_11]
    · exact h00
    · rw [mul_comm]; exact h01
    · rw [h10, Int.mul_ediv_cancel_left _ hq0]
    · exact h11
  have hdown : ∀ (ε : ↥(GamF q N)) (x : ↥(((Matrix.SpecialLinearGroup.toGL.comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype).ker)),
      (ε : SL(2, ℤ)) = ((x : Gamma0 N) : SL(2, ℤ)) → down q N hqN ε = conj x := by
    intro ε x hεx
    obtain ⟨h00, h01, h10, h11⟩ := hconj x
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, coe_down_apply, conjUpperMat_apply_00,
        conjUpperMat_apply_01, CohCarrier.conjUpperMat_apply_10, CohCarrier.conjUpperMat_apply_11]
    · rw [hεx]; exact h00.symm
    · rw [hεx]; exact Int.ediv_eq_of_eq_mul_right hq0 h01.symm
    · rw [hεx, mul_comm]; exact h10.symm
    · rw [hεx]; exact h11.symm
  show (down q N hqN) ((conjF q N ((γ : SL(2, ℤ)))⁻¹ hγ0) (up q N (conj ⟨γ * y * γ⁻¹, hy'⟩))) = conj ⟨y, hy⟩
  apply hdown
  rw [coe_conjF_apply, hup]
  show ((γ : SL(2, ℤ)))⁻¹ * ((γ * y * γ⁻¹ : Gamma0 N) : SL(2, ℤ)) * ((γ : SL(2, ℤ)))⁻¹⁻¹ = (y : SL(2, ℤ))
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem main_native
    (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime] (hqN : ¬ q ∣ N)
    (g : CuspForm (Gamma0 (q ^ 2 * N)) 2) (hg : g.IsNewform)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    [FiniteDimensional ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)]
    (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ) (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v)
    (hfi : Function.Injective f)
    (hfr : LinearMap.range f =
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (θ : (GaloisField q 2)ˣ →* ℂˣ) (hθ : CuspidalType.IsCuspidalOfType θ (LocalNewvector.gl2ReductionRep q V))
    (red : Gamma0 N →* CuspidalType.GL2 q)
    (hred : red = (Matrix.SpecialLinearGroup.toGL.comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype) :
    ∃ Ψ : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) →ₗ[ℂ]
        CohCarrier.H1 (q ^ 2 * N) (ModularCurve.FullLevel.levelH q N) ℂ,
      Ψ ≠ 0 ∧
      (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ q ^ 2 * N → ∀ h : ((ℓ : ZMod q) ≠ 0),
        ∀ w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V),
          CohCarrier.heckeT (q ^ 2 * N) (ModularCurve.FullLevel.levelH q N) ℓ ℂ (Ψ w) =
            ModularFormClass.qCoeff g ℓ •
              Ψ (LocalNewvector.gl2ReductionRep q V (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) w)) ∧
      ∀ (conj : ↥red.ker →* ↥(CohCarrier.GammaH (q ^ 2 * N) (ModularCurve.FullLevel.levelH q N))),
        (∀ x : ↥red.ker,
          (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 =
            ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 ∧
          (q : ℤ) * (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 =
            ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 ∧
          (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 =
            (q : ℤ) * ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 ∧
          (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 =
            ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1) →
        ∀ (γ y : Gamma0 N) (hy : y ∈ red.ker) (hy' : γ * y * γ⁻¹ ∈ red.ker)
          (w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)),
          Ψ (LocalNewvector.gl2ReductionRep q V (red γ) w) (Additive.ofMul (conj ⟨γ * y * γ⁻¹, hy'⟩)) =
            Ψ w (Additive.ofMul (conj ⟨y, hy⟩)) := by
  classical

  obtain ⟨Fc, hC, -, hI, hD, hE⟩ :=
    CuspForm.IsAdelicLiftOf.exists_linearMap_components_of_fixedSubmodule_of_range_eq_span
      q hqN hΦg V f hf hfi hfr

  obtain ⟨-, -, L, hL, hLper⟩ :=
    CuspForm.exists_linearEquiv_gamma_inf_gamma0_gammaH_slash_heckeDiagMatrix_and_periodOf_eq q N hqN

  let ΓH : Subgroup SL(2, ℤ) := CohCarrier.GammaH (q ^ 2 * N) (ModularCurve.FullLevel.levelH q N)
  let Ψ : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) →ₗ[ℂ] CohCarrier.H1 (q ^ 2 * N) (ModularCurve.FullLevel.levelH q N) ℂ :=
    (periodMapLin ΓH) ∘ₗ L.toLinearMap ∘ₗ (Fc 1)
  have hΨ : ∀ w, Ψ w = ModularCurve.periodMapOf ΓH (L (Fc 1 w)) := fun w => rfl
  refine ⟨Ψ, ?_, ?_, ?_⟩
  ·

    intro h0
    have hpos : 0 < Module.finrank ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) := by
      rw [hθ.finrank_eq]
      exact Nat.sub_pos_of_lt (Fact.out : q.Prime).one_lt
    obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    apply hw
    apply hI
    intro u
    rw [← hD u w]
    have h1 : Ψ (LocalNewvector.gl2ReductionRep q V
        (CuspidalType.diagElem q (Units.map PadicInt.toZMod.toMonoidHom u)) w) = 0 := by
      rw [h0, LinearMap.zero_apply]
    rw [hΨ] at h1
    have h2 := eq_zero_of_periodMapOf_eq_zero ΓH _ h1
    exact L.injective (h2.trans (map_zero L).symm)
  ·

    intro ℓ _ hℓ hℓN h w
    obtain ⟨ℓq, hℓq⟩ := exists_unit_coe_eq (q := q) h
    have hy := apply_mem_span f hfr (w : V)
    have hfix := apply_mem_fixedSubmodule f hf w

    have hF : ∀ hh : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ hh = 1 →
          LanglandsTunnell.ratArchGL2 hh ∈ Matrix.GLPos (Fin 2) ℝ →
            (LocalNewvector.AdelicSpan.toFn Φ (f (w : V))).toFn
                (hh * AdelicDock.padicToAdelic q
                  (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom (ℓq * ℓq⁻¹)))) =
              ((⇑(Fc 1 w)) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 hh) UpperHalfPlane.I := by
      rw [mul_inv_cancel]
      exact hC 1 w
    have key := CuspForm.IsAdelicLiftOf.heckeTLinH_eq_qCoeff_smul_of_components_of_isNewform q hg hΦg
      (f (w : V)) hy hfix hℓ hℓN ℓq hℓq ℓq (Fc 1 w) (Fc ℓq w) hF (hC ℓq w) (L (Fc 1 w)) (L (Fc ℓq w))
      (hL _) (hL _)
    rw [hΨ, hΨ, ← unitsMap_toZMod_eq_mk0 h ℓq hℓq, hD ℓq w]
    exact heckeT_periodMapOf_eq_smul_of_heckeTLinH_eq_smul (q ^ 2 * N) (ModularCurve.FullLevel.levelH q N)
      hℓ hℓN (L (Fc 1 w)) (L (Fc ℓq w)) _ key
  ·
    intro conj hconj γ y hy hy' w
    rw [hΨ, hΨ]
    exact K2_conj_equivariance N q hqN V (Fc 1) hE L hL red hred conj hconj γ y hy hy' w

end OccRoot
p2m_reactivate "P2MW.S_CuspForm_IsNewform_exists_linearMap_fixedSubmodule_H1_gammaH_laws_of_isCuspidalOfType.OccRoot"

open OccRoot in
theorem solution
    (N : ℕ) [NeZero N] {q : ℕ} [Fact q.Prime] (hqN : ¬ q ∣ N)
    (g : CuspForm (Gamma0 (N * q ^ 2)) 2) (hg : g.IsNewform)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    [FiniteDimensional ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)]
    (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ) (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v)
    (hfi : Function.Injective f)
    (hfr : LinearMap.range f =
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (θ : (GaloisField q 2)ˣ →* ℂˣ) (hθ : CuspidalType.IsCuspidalOfType θ (LocalNewvector.gl2ReductionRep q V))
    (red : Gamma0 N →* CuspidalType.GL2 q)
    (hred : red = (Matrix.SpecialLinearGroup.toGL.comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype) :
    ∃ Ψ : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) →ₗ[ℂ]
        CohCarrier.H1 (N * q ^ 2) (ZMod.unitsMap ((dvd_pow_self q two_ne_zero).mul_left N)).ker ℂ,
      Ψ ≠ 0 ∧
      (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q ^ 2 → ∀ h : ((ℓ : ZMod q) ≠ 0),
        ∀ w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V),
          CohCarrier.heckeT (N * q ^ 2) (ZMod.unitsMap ((dvd_pow_self q two_ne_zero).mul_left N)).ker ℓ ℂ (Ψ w) =
            ModularFormClass.qCoeff g ℓ •
              Ψ (LocalNewvector.gl2ReductionRep q V (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) w)) ∧
      ∀ (conj : ↥red.ker →*
          ↥(CohCarrier.GammaH (N * q ^ 2) (ZMod.unitsMap ((dvd_pow_self q two_ne_zero).mul_left N)).ker)),
        (∀ x : ↥red.ker,
          (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 =
            ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 ∧
          (q : ℤ) * (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 =
            ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 ∧
          (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 =
            (q : ℤ) * ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 ∧
          (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 =
            ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1) →
        ∀ (γ y : Gamma0 N) (hy : y ∈ red.ker) (hy' : γ * y * γ⁻¹ ∈ red.ker)
          (w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)),
          Ψ (LocalNewvector.gl2ReductionRep q V (red γ) w) (Additive.ofMul (conj ⟨γ * y * γ⁻¹, hy'⟩)) =
            Ψ w (Additive.ofMul (conj ⟨y, hy⟩)) := by

  suffices key : ∀ (Lv : ℕ) (hLv : Lv = q ^ 2 * N) (hq : q ∣ Lv) (g : CuspForm (Gamma0 Lv) 2) (hg : g.IsNewform)
      (hΦg : g.IsAdelicLiftOf Φ),
      ∃ Ψ : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) →ₗ[ℂ] CohCarrier.H1 Lv (ZMod.unitsMap hq).ker ℂ,
        Ψ ≠ 0 ∧
        (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ Lv → ∀ h : ((ℓ : ZMod q) ≠ 0),
          ∀ w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V),
            CohCarrier.heckeT Lv (ZMod.unitsMap hq).ker ℓ ℂ (Ψ w) =
              ModularFormClass.qCoeff g ℓ •
                Ψ (LocalNewvector.gl2ReductionRep q V (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) w)) ∧
        ∀ (conj : ↥red.ker →* ↥(CohCarrier.GammaH Lv (ZMod.unitsMap hq).ker)),
          (∀ x : ↥red.ker,
            (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 =
              ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 ∧
            (q : ℤ) * (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 =
              ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 ∧
            (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 =
              (q : ℤ) * ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 ∧
            (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 =
              ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1) →
          ∀ (γ y : Gamma0 N) (hy : y ∈ red.ker) (hy' : γ * y * γ⁻¹ ∈ red.ker)
            (w : ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)),
            Ψ (LocalNewvector.gl2ReductionRep q V (red γ) w) (Additive.ofMul (conj ⟨γ * y * γ⁻¹, hy'⟩)) =
              Ψ w (Additive.ofMul (conj ⟨y, hy⟩)) from
    key (N * q ^ 2) (mul_comm _ _) _ g hg hΦg
  intro Lv hLv hq g hg hΦg
  subst hLv
  exact main_native N q hqN g hg Φ hΦg V f hf hfi hfr θ hθ red hred

end S_CuspForm_IsNewform_exists_linearMap_fixedSubmodule_H1_gammaH_laws_of_isCuspidalOfType
end P2MW
export P2MW.S_CuspForm_IsNewform_exists_linearMap_fixedSubmodule_H1_gammaH_laws_of_isCuspidalOfType (solution)
