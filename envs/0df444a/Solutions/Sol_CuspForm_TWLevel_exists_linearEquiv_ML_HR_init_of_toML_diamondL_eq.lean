-- Prove2me | solution 1 for CuspForm.TWLevel.exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/66e48faa-a754-590b-8485-6cc5fc0eb3b8

import Mathlib
import Definitions.Def_CohCarrier_HeckeData
import Definitions.Def_CuspForm_TWLevelHeckeModule
import Definitions.Def_CuspForm_TWLevelHeckeRing
import Theorems.Thm_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime
import Theorems.Thm_CohCarrier_HeckeData_exists_linearEquiv_ML_of_degeneracy_atkinLehner_identities
import Theorems.Thm_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem
import Theorems.Thm_CohCarrier_heckeT_comm_of_prime
import Theorems.Thm_CohCarrier_heckeT_diamondRaw_comm
import Theorems.Thm_CohCarrier_exists_gamma0_lift_dvd
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_dvd
import Theorems.Thm_CohCarrier_jDeg_heckeT_comm_flat
import Theorems.Thm_CohCarrier_jDeg_heckeT_comm_of_dvd_of_coprime
import Theorems.Thm_CohCarrier_jDeg_diamondRaw_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_TWLevel_exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_symm_apply IharaLemma.IdempotentSplitting.coe_cornerSmul IharaLemma.IdempotentSplitting.mk.injEq IharaLemma.IdempotentSplitting.mk.sizeOf_spec IharaLemma.IdempotentSplitting.coe_toCornerRing IharaLemma.toCorner_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

noncomputable section

namespace TWStepGeo

p2m_open "CongruenceSubgroup CohCarrier~coe_iotaDeg_one"
open scoped MatrixGroups

theorem castH1 (r : ℕ) (𝒪 : Type) [CommRing 𝒪] :
    ∀ (M₁ M₂ : ℕ) [NeZero M₁] [NeZero M₂] (h : M₁ = M₂) (d₁ : r ∣ M₁) (d₂ : r ∣ M₂),
    ∃ φ : H1 M₁ (ZMod.unitsMap d₁).ker 𝒪 ≃ₗ[𝒪] H1 M₂ (ZMod.unitsMap d₂).ker 𝒪,
      (∀ (n : ℕ) [NeZero n] (v : H1 M₁ (ZMod.unitsMap d₁).ker 𝒪),
        φ (heckeTL M₁ (ZMod.unitsMap d₁).ker 𝒪 n v) = heckeTL M₂ (ZMod.unitsMap d₂).ker 𝒪 n (φ v)) ∧
      (∀ (u : (ZMod M₂)ˣ) (v : H1 M₁ (ZMod.unitsMap d₁).ker 𝒪),
        φ (diamondL M₁ (ZMod.unitsMap d₁).ker 𝒪 (ZMod.unitsMap (dvd_of_eq h) u) v) =
          diamondL M₂ (ZMod.unitsMap d₂).ker 𝒪 u (φ v)) := by
  intro M₁ M₂ _ _ h d₁ d₂
  subst h
  refine ⟨LinearEquiv.refl 𝒪 _, fun n _ v => rfl, fun u v => ?_⟩
  rw [ZMod.unitsMap_self]
  rfl

variable (M q : ℕ) [NeZero M] [NeZero q] (H : Subgroup (ZMod M)ˣ) (H' : Subgroup (ZMod (M * q))ˣ)
  (h1 : LevelLE M (M * q) H H' 1)

scoped instance instNeZeroMul : NeZero (M * q) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne q)⟩

theorem coe_iotaDeg_one (γ : ↥(GammaH (M * q) H')) :
    ((iotaDeg M (M * q) H H' 1 h1 γ : ↥(GammaH M H)) : SL(2, ℤ)) = (γ : SL(2, ℤ)) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [iotaDeg, conjLowerMat]

def toGamma0 (σ : Gamma0 (M * q)) : Gamma0 M :=
  ⟨σ.1, by
    have h := Gamma0_mem.mp σ.2
    rw [Gamma0_mem]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h ⊢
    exact (Int.natCast_dvd_natCast.mpr (dvd_mul_right M q)).trans h⟩

@[scoped simp] theorem coe_toGamma0 (σ : Gamma0 (M * q)) : ((toGamma0 M q σ : Gamma0 M) : SL(2, ℤ)) = σ := rfl

theorem gamma0Units_toGamma0 (σ : Gamma0 (M * q)) :
    gamma0Units M (toGamma0 M q σ) = ZMod.unitsMap (dvd_mul_right M q) (gamma0Units (M * q) σ) := by
  apply Units.ext
  simp [gamma0Units, Gamma0Map, toGamma0, ZMod.unitsMap]

theorem iDegL_diamondRaw (𝒪 : Type) [CommRing 𝒪] (σ : Gamma0 (M * q)) (φ : H1 M H 𝒪) :
    iDegL M (M * q) H H' 1 𝒪 𝒪 h1 (diamondRaw M H 𝒪 (toGamma0 M q σ) φ) =
      diamondRaw (M * q) H' 𝒪 σ (iDegL M (M * q) H H' 1 𝒪 𝒪 h1 φ) := by
  apply AddMonoidHom.ext
  intro x
  show φ (Additive.ofMul (conjHom M H (toGamma0 M q σ)
      (iotaDeg M (M * q) H H' 1 h1 (Additive.toMul x)))) =
    φ (Additive.ofMul (iotaDeg M (M * q) H H' 1 h1 (conjHom (M * q) H' σ (Additive.toMul x))))
  congr 2
  apply Subtype.ext
  simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk, coe_iotaDeg_one, coe_toGamma0]

theorem iDegL_diamondL (𝒪 : Type) [CommRing 𝒪] (u : (ZMod (M * q))ˣ) :
    iDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ diamondL M H 𝒪 (ZMod.unitsMap (dvd_mul_right M q) u) =
      diamondL (M * q) H' 𝒪 u ∘ₗ iDegL M (M * q) H H' 1 𝒪 𝒪 h1 := by
  obtain ⟨σ, hσ⟩ := gamma0Units_surjective (M * q) u
  apply LinearMap.ext
  intro φ
  rw [LinearMap.comp_apply, LinearMap.comp_apply, diamondL_eq_diamondRaw (M * q) _ 𝒪 u σ hσ,
    diamondL_eq_diamondRaw M _ 𝒪 _ (toGamma0 M q σ) (by rw [gamma0Units_toGamma0, hσ])]
  exact iDegL_diamondRaw M q H H' h1 𝒪 σ φ

theorem jDegL_diamondL (𝒪 : Type) [CommRing 𝒪] (u : (ZMod (M * q))ˣ) :
    jDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ diamondL (M * q) H' 𝒪 u =
      diamondL M H 𝒪 (ZMod.unitsMap (dvd_mul_right M q) u) ∘ₗ jDegL M (M * q) H H' 1 𝒪 𝒪 h1 := by
  obtain ⟨σ, hσ⟩ := gamma0Units_surjective (M * q) u
  apply LinearMap.ext
  intro φ
  rw [LinearMap.comp_apply, LinearMap.comp_apply, diamondL_eq_diamondRaw (M * q) _ 𝒪 u σ hσ,
    diamondL_eq_diamondRaw M _ 𝒪 _ (toGamma0 M q σ) (by rw [gamma0Units_toGamma0, hσ])]
  have hσ' : ((toGamma0 M q σ : Gamma0 M) : SL(2, ℤ)) ∈ Gamma0 (M * q) := σ.2
  exact (jDeg_diamondRaw_comm (A := 𝒪) (toGamma0 M q σ) hσ' h1 φ).symm

theorem iDegL_heckeTL_of_not_dvd (𝒪 : Type) [CommRing 𝒪] (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime)
    (hℓM : ¬ ℓ ∣ M * q) :
    iDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ heckeTL M H 𝒪 ℓ =
      heckeTL (M * q) H' 𝒪 ℓ ∘ₗ iDegL M (M * q) H H' 1 𝒪 𝒪 h1 := by
  apply LinearMap.ext
  intro φ
  exact iDeg_heckeT_comm_of_coprime (A := 𝒪) h1 (Nat.coprime_one_right ℓ) hℓ hℓM φ

theorem iDegL_heckeTL_of_dvd (𝒪 : Type) [CommRing 𝒪] (ℓ : ℕ) [NeZero ℓ] (hℓM : ℓ ∣ M) :
    iDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ heckeTL M H 𝒪 ℓ =
      heckeTL (M * q) H' 𝒪 ℓ ∘ₗ iDegL M (M * q) H H' 1 𝒪 𝒪 h1 := by
  apply LinearMap.ext
  intro φ
  exact iDeg_heckeT_comm_of_dvd (A := 𝒪) h1 (Nat.coprime_one_right ℓ) hℓM φ

theorem jDegL_heckeTL_of_not_dvd (𝒪 : Type) [CommRing 𝒪] (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime)
    (hℓM : ¬ ℓ ∣ M * q) :
    jDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ heckeTL (M * q) H' 𝒪 ℓ =
      heckeTL M H 𝒪 ℓ ∘ₗ jDegL M (M * q) H H' 1 𝒪 𝒪 h1 := by
  apply LinearMap.ext
  intro φ
  exact (jDeg_heckeT_comm_flat (A := 𝒪) h1 (Nat.coprime_one_right ℓ) hℓ hℓM φ).symm

theorem jDegL_heckeTL_of_dvd (𝒪 : Type) [CommRing 𝒪] (ℓ : ℕ) [NeZero ℓ] (hℓM : ℓ ∣ M)
    (hℓq : Nat.Coprime ℓ q) :
    jDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ heckeTL (M * q) H' 𝒪 ℓ =
      heckeTL M H 𝒪 ℓ ∘ₗ jDegL M (M * q) H H' 1 𝒪 𝒪 h1 := by
  apply LinearMap.ext
  intro φ
  have hdiv : M * q / (M * 1) = q := by
    rw [mul_one, Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero (NeZero.ne M))]
  have hℓe : Nat.Coprime ℓ (M * q / (M * 1)) := by rw [hdiv]; exact hℓq
  exact (jDeg_heckeT_comm_of_dvd_of_coprime (A := 𝒪) h1 hℓe hℓM φ).symm

theorem diamondL_heckeTL_comm (L : ℕ) [NeZero L] (H : Subgroup (ZMod L)ˣ) (𝒪 : Type) [CommRing 𝒪]
    (n : ℕ) [NeZero n] (u : (ZMod L)ˣ) :
    diamondL L H 𝒪 u * heckeTL L H 𝒪 n = heckeTL L H 𝒪 n * diamondL L H 𝒪 u := by
  obtain ⟨σ, hσu, hσdvd⟩ := CohCarrier.exists_gamma0_lift_dvd L n u
  apply LinearMap.ext
  intro F
  change diamondL L H 𝒪 u (heckeTL L H 𝒪 n F) = heckeTL L H 𝒪 n (diamondL L H 𝒪 u F)
  rw [diamondL_eq_diamondRaw L H 𝒪 u σ hσu, diamondL_eq_diamondRaw L H 𝒪 u σ hσu, heckeTL_apply,
    heckeTL_apply]
  exact (CohCarrier.heckeT_diamondRaw_comm L H n σ hσdvd F).symm

theorem heckeTL_comm_of_prime (L : ℕ) (H : Subgroup (ZMod L)ˣ) (𝒪 : Type) [CommRing 𝒪]
    (a b : ℕ) [NeZero a] [NeZero b] (ha : a.Prime) (hb : b.Prime) :
    heckeTL L H 𝒪 a * heckeTL L H 𝒪 b = heckeTL L H 𝒪 b * heckeTL L H 𝒪 a := by
  by_cases hab : a = b
  · subst hab
    rfl
  · apply LinearMap.ext
    intro F
    change heckeT L H a 𝒪 (heckeT L H b 𝒪 F) = heckeT L H b 𝒪 (heckeT L H a 𝒪 F)
    exact CohCarrier.heckeT_comm_of_prime L H a b ha ((Nat.coprime_primes ha hb).mpr hab) F

theorem isUnit_diamondL (L : ℕ) [NeZero L] (H : Subgroup (ZMod L)ˣ) (𝒪 : Type) [CommRing 𝒪]
    (u : (ZMod L)ˣ) : IsUnit (diamondL L H 𝒪 u) := by
  refine ⟨⟨diamondL L H 𝒪 u, diamondL L H 𝒪 u⁻¹, ?_, ?_⟩, rfl⟩
  · rw [← diamondL_mul, mul_inv_cancel, diamondL_one]
  · rw [← diamondL_mul, inv_mul_cancel, diamondL_one]

end TWStepGeo
p2m_reactivate "P2MW.S_CuspForm_TWLevel_exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq.TWStepGeo"

namespace TWStepData

p2m_open "IsLocalRing CuspForm.TWLevel CohCarrier~coe_iotaDeg_one P2MW.S_CuspForm_TWLevel_exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq.TWStepGeo"

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
  (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
  (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* ResidueField 𝒪)
  {t : ℕ} (qv : Fin (t + 1) → ℕ) [∀ i, NeZero (qv i)] [∀ i, NeZero (Fin.init qv i)]
  (α : Fin (t + 1) → ResidueField 𝒪)

abbrev L0 : ℕ := level N r (Fin.init qv)

abbrev qq : ℕ := qv (Fin.last t)

abbrev Hq : Subgroup (ZMod (L0 N r qv * qq qv))ˣ :=
  (ZMod.unitsMap ((dvd_level_r N r (Fin.init qv)).trans (dvd_mul_right _ (qq qv)))).ker

theorem mem_Hq_iff (v : (ZMod (L0 N r qv * qq qv))ˣ) :
    v ∈ Hq N r qv ↔ ZMod.unitsMap (dvd_mul_right _ _) v ∈ HR N r (Fin.init qv) := by
  show v ∈ Hq N r qv ↔ ZMod.unitsMap (dvd_mul_right _ _) v ∈ (ZMod.unitsMap (dvd_level_r N r (Fin.init qv))).ker
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]

theorem h1 : LevelLE (L0 N r qv) (L0 N r qv * qq qv) (HR N r (Fin.init qv)) (Hq N r qv) 1 :=
  ⟨dvd_mul_right _ _, one_dvd _, fun u hu => (mem_Hq_iff N r qv u).mp hu⟩

abbrev Wq : Type := H1 (L0 N r qv * qq qv) (Hq N r qv) 𝒪

abbrev V0 : Type := Carrier N r (Fin.init qv) 𝒪 (HR N r (Fin.init qv))

omit [NeZero N] [NeZero r] [∀ i, NeZero (qv i)] [∀ i, NeZero (Fin.init qv i)] in

theorem level_eq : level N r qv = L0 N r qv * qq qv := by
  simp only [CuspForm.TWLevel.level, Fin.prod_univ_castSucc, Fin.init]
  ring

def opW : Gen (level N r qv) S (t + 1) → Module.End 𝒪 (Wq (𝒪 := 𝒪) N r qv)
  | .T ℓ hℓ _ _ => haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeTL (L0 N r qv * qq qv) (Hq N r qv) 𝒪 ℓ
  | .U i => heckeTL (L0 N r qv * qq qv) (Hq N r qv) 𝒪 (qv i)

variable (hq : ∀ i, (qv i).Prime)

include hq in
theorem opW_eq_heckeTL (g : Gen (level N r qv) S (t + 1)) :
    ∃ (a : ℕ) (ha : a.Prime), opW (𝒪 := 𝒪) S N r qv g =
      (haveI : NeZero a := ⟨ha.ne_zero⟩; heckeTL (L0 N r qv * qq qv) (Hq N r qv) 𝒪 a) := by
  cases g with
  | T ℓ hℓ hℓS hℓL => exact ⟨ℓ, hℓ, rfl⟩
  | U i => exact ⟨qv i, hq i, rfl⟩

include hq in
theorem opV_eq_heckeTL (g : Gen (level N r (Fin.init qv)) S t) :
    ∃ (a : ℕ) (ha : a.Prime), op N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) g =
      (haveI : NeZero a := ⟨ha.ne_zero⟩; heckeTL (L0 N r qv) (HR N r (Fin.init qv)) 𝒪 a) := by
  cases g with
  | T ℓ hℓ hℓS hℓL => exact ⟨ℓ, hℓ, rfl⟩
  | U i => exact ⟨qv i.castSucc, hq i.castSucc, rfl⟩

include hq in
theorem opW_comm (g h : Gen (level N r qv) S (t + 1)) :
    opW (𝒪 := 𝒪) S N r qv g * opW S N r qv h = opW S N r qv h * opW S N r qv g := by
  obtain ⟨a, ha, hga⟩ := opW_eq_heckeTL (𝒪 := 𝒪) S N r qv hq g
  obtain ⟨b, hb, hhb⟩ := opW_eq_heckeTL (𝒪 := 𝒪) S N r qv hq h
  rw [hga, hhb]
  haveI : NeZero a := ⟨ha.ne_zero⟩
  haveI : NeZero b := ⟨hb.ne_zero⟩
  exact heckeTL_comm_of_prime _ _ 𝒪 a b ha hb

include hq in
theorem opW_diamondL_comm (g : Gen (level N r qv) S (t + 1)) (u : (ZMod (L0 N r qv * qq qv))ˣ) :
    opW (𝒪 := 𝒪) S N r qv g * diamondL _ (Hq N r qv) 𝒪 u = diamondL _ (Hq N r qv) 𝒪 u * opW S N r qv g := by
  obtain ⟨a, ha, hga⟩ := opW_eq_heckeTL (𝒪 := 𝒪) S N r qv hq g
  rw [hga]
  haveI : NeZero a := ⟨ha.ne_zero⟩
  exact (diamondL_heckeTL_comm _ _ 𝒪 a u).symm

include hq in
theorem opV_diamondL_comm (g : Gen (level N r (Fin.init qv)) S t) (u : (ZMod (L0 N r qv))ˣ) :
    op N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) g * diamondL _ (HR N r (Fin.init qv)) 𝒪 u =
      diamondL _ (HR N r (Fin.init qv)) 𝒪 u * op N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) g := by
  obtain ⟨a, ha, hga⟩ := opV_eq_heckeTL (𝒪 := 𝒪) S N r qv hq g
  rw [hga]
  haveI : NeZero a := ⟨ha.ne_zero⟩
  exact (diamondL_heckeTL_comm _ _ 𝒪 a u).symm

def opWp (u : (ZMod (L0 N r qv * qq qv))ˣ) :
    Gen (level N r qv) S (t + 1) ⊕ Unit → Module.End 𝒪 (Wq (𝒪 := 𝒪) N r qv)
  | .inl g => opW S N r qv g
  | .inr _ => diamondL _ (Hq N r qv) 𝒪 u

def thetaWp : Gen (level N r qv) S (t + 1) ⊕ Unit → ResidueField 𝒪
  | .inl g => thetaQ N r qv S (ResidueField 𝒪) θ α g
  | .inr _ => 1

include hq in
theorem opWp_comm (u : (ZMod (L0 N r qv * qq qv))ˣ) (g h : Gen (level N r qv) S (t + 1) ⊕ Unit) :
    opWp (𝒪 := 𝒪) S N r qv u g * opWp S N r qv u h = opWp S N r qv u h * opWp S N r qv u g := by
  rcases g with g | g <;> rcases h with h | h
  · exact opW_comm S N r qv hq g h
  · exact opW_diamondL_comm S N r qv hq g u
  · exact (opW_diamondL_comm S N r qv hq h u).symm
  · rfl

def opVp (u : (ZMod (L0 N r qv * qq qv))ˣ) :
    Gen (level N r (Fin.init qv)) S t ⊕ Unit → Module.End 𝒪 (V0 (𝒪 := 𝒪) N r qv)
  | .inl g => op N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) g
  | .inr _ => diamondL _ (HR N r (Fin.init qv)) 𝒪 (ZMod.unitsMap (dvd_mul_right _ _) u)

def thetaVp : Gen (level N r (Fin.init qv)) S t ⊕ Unit → ResidueField 𝒪
  | .inl g => thetaQ N r (Fin.init qv) S (ResidueField 𝒪) θ (Fin.init α) g
  | .inr _ => 1

include hq in
theorem opVp_comm (hc₀ : OpComm N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)))
    (u : (ZMod (L0 N r qv * qq qv))ˣ) (g h : Gen (level N r (Fin.init qv)) S t ⊕ Unit) :
    opVp (𝒪 := 𝒪) S N r qv u g * opVp S N r qv u h = opVp S N r qv u h * opVp S N r qv u g := by
  rcases g with g | g <;> rcases h with h | h
  · exact hc₀ g h
  · exact opV_diamondL_comm S N r qv hq g _
  · exact (opV_diamondL_comm S N r qv hq h _).symm
  · rfl

def DW : HeckeData 𝒪 (Wq (𝒪 := 𝒪) N r qv) (ResidueField 𝒪) where
  Gen := Gen (level N r qv) S (t + 1)
  op := opW S N r qv
  comm := opW_comm S N r qv hq
  θbar := thetaQ N r qv S (ResidueField 𝒪) θ α

def DWp (u : (ZMod (L0 N r qv * qq qv))ˣ) : HeckeData 𝒪 (Wq (𝒪 := 𝒪) N r qv) (ResidueField 𝒪) where
  Gen := Gen (level N r qv) S (t + 1) ⊕ Unit
  op := opWp S N r qv u
  comm := opWp_comm S N r qv hq u
  θbar := thetaWp S N r θ qv α

def DVp (hc₀ : OpComm N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv))) (u : (ZMod (L0 N r qv * qq qv))ˣ) :
    HeckeData 𝒪 (V0 (𝒪 := 𝒪) N r qv) (ResidueField 𝒪) where
  Gen := Gen (level N r (Fin.init qv)) S t ⊕ Unit
  op := opVp S N r qv u
  comm := opVp_comm S N r qv hq hc₀ u
  θbar := thetaVp S N r θ qv α

inductive GC (L : ℕ) (S : Set ℕ) (t : ℕ) : Type
  | T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L)
  | U (i : Fin t)

def sigmaW : (GC (level N r qv) S t ⊕ Unit) ⊕ Unit ≃ Gen (level N r qv) S (t + 1) ⊕ Unit where
  toFun
    | .inl (.inl (.T ℓ hℓ hℓS hℓL)) => .inl (.T ℓ hℓ hℓS hℓL)
    | .inl (.inl (.U i)) => .inl (.U i.castSucc)
    | .inl (.inr _) => .inr ()
    | .inr _ => .inl (.U (Fin.last t))
  invFun
    | .inl (.T ℓ hℓ hℓS hℓL) => .inl (.inl (.T ℓ hℓ hℓS hℓL))
    | .inl (.U i) => Fin.lastCases (.inr ()) (fun j => .inl (.inl (.U j))) i
    | .inr _ => .inl (.inr ())
  left_inv := by
    rintro ((⟨ℓ, hℓ, hℓS, hℓL⟩ | i) | ⟨⟩) <;> simp
  right_inv := by
    rintro ((⟨ℓ, hℓ, hℓS, hℓL⟩ | i) | ⟨⟩)
    · rfl
    · induction i using Fin.lastCases with
      | last => simp
      | cast j => simp
    · rfl

omit [NeZero N] [NeZero r] [∀ i, NeZero (qv i)] [∀ i, NeZero (Fin.init qv i)] in
theorem not_dvd_L0_of_not_dvd_level {ℓ : ℕ} (h : ¬ ℓ ∣ level N r qv) : ¬ ℓ ∣ level N r (Fin.init qv) :=
  fun h' => h (h'.trans ⟨qv (Fin.last t), level_eq N r qv⟩)

omit [NeZero N] [NeZero r] [∀ i, NeZero (qv i)] [∀ i, NeZero (Fin.init qv i)] in
include hq in
theorem not_dvd_level_of_ne {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ¬ ℓ ∣ level N r (Fin.init qv))
    (hne : ℓ ≠ qv (Fin.last t)) : ¬ ℓ ∣ level N r qv := by
  rw [level_eq N r qv]
  intro h'
  rcases (Nat.Prime.dvd_mul hℓ).mp h' with h' | h'
  · exact h h'
  · exact hne ((Nat.prime_dvd_prime_iff_eq hℓ (hq (Fin.last t))).mp h')

omit [NeZero N] [NeZero r] [∀ i, NeZero (qv i)] [∀ i, NeZero (Fin.init qv i)] in
theorem ne_of_not_dvd_level {ℓ : ℕ} (h : ¬ ℓ ∣ level N r qv) : ℓ ≠ qv (Fin.last t) :=
  fun e => h (e ▸ dvd_level_q N r qv (Fin.last t))

def sigmaV (hqS : qv (Fin.last t) ∉ S) (hqL : ¬ qv (Fin.last t) ∣ level N r (Fin.init qv)) :
    (GC (level N r qv) S t ⊕ Unit) ⊕ Unit ≃ Gen (level N r (Fin.init qv)) S t ⊕ Unit where
  toFun
    | .inl (.inl (.T ℓ hℓ hℓS hℓL)) => .inl (.T ℓ hℓ hℓS (not_dvd_L0_of_not_dvd_level N r qv hℓL))
    | .inl (.inl (.U i)) => .inl (.U i)
    | .inl (.inr _) => .inr ()
    | .inr _ => .inl (.T (qv (Fin.last t)) (hq (Fin.last t)) hqS hqL)
  invFun
    | .inl (.T ℓ hℓ hℓS hℓL) =>
        if hne : ℓ = qv (Fin.last t) then .inr ()
        else .inl (.inl (.T ℓ hℓ hℓS (not_dvd_level_of_ne N r qv hq hℓ hℓL hne)))
    | .inl (.U i) => .inl (.inl (.U i))
    | .inr _ => .inl (.inr ())
  left_inv := by
    rintro ((⟨ℓ, hℓ, hℓS, hℓL⟩ | i) | ⟨⟩)
    · simp only [dif_neg (ne_of_not_dvd_level N r qv hℓL)]
    · rfl
    · rfl
    · simp
  right_inv := by
    rintro ((⟨ℓ, hℓ, hℓS, hℓL⟩ | i) | ⟨⟩)
    · by_cases hne : ℓ = qv (Fin.last t)
      · subst hne
        simp
      · simp only [dif_neg hne]
    · rfl
    · rfl

end TWStepData
p2m_reactivate "P2MW.S_CuspForm_TWLevel_exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq.TWStepGeo"

namespace TWStepTransport

p2m_open "CohCarrier~coe_iotaDeg_one"

attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

variable {𝒪 : Type} [CommRing 𝒪] {k : Type} [Field k] [Algebra 𝒪 k]
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module 𝒪 V₁] [AddCommGroup V₂] [Module 𝒪 V₂]
  (D₁ : HeckeData 𝒪 V₁ k) (D₂ : HeckeData 𝒪 V₂ k)
  (φ : V₁ →ₗ[𝒪] V₂) (eG : D₁.Gen → D₂.Gen)

def R : D₁.FreeAlg →ₐ[𝒪] D₂.FreeAlg := MvPolynomial.rename eG

@[scoped simp] theorem R_X (g : D₁.Gen) : R D₁ D₂ eG (MvPolynomial.X g) = MvPolynomial.X (eG g) := by
  simp [R, MvPolynomial.rename_X]

theorem thetaTilde_R (hθ : ∀ g, D₂.θbar (eG g) = D₁.θbar g) (f : D₁.FreeAlg) :
    D₂.thetaTilde (R D₁ D₂ eG f) = D₁.thetaTilde f := by
  simp only [HeckeData.thetaTilde, R, MvPolynomial.aeval_rename, Function.comp_def, hθ]

theorem R_mem_primeCompl (hθ : ∀ g, D₂.θbar (eG g) = D₁.θbar g) (s : D₁.mTheta.primeCompl) :
    R D₁ D₂ eG (s : D₁.FreeAlg) ∈ D₂.mTheta.primeCompl := by
  have hs : (s : D₁.FreeAlg) ∉ D₁.mTheta := s.2
  intro h
  apply hs
  have h' : D₂.thetaTilde (R D₁ D₂ eG (s : D₁.FreeAlg)) = 0 := by
    simp only [HeckeData.mTheta, RingHom.mem_ker] at h
    exact h
  rw [thetaTilde_R D₁ D₂ eG hθ] at h'
  simp only [HeckeData.mTheta, RingHom.mem_ker] at h'
  exact h'

def RS (hθ : ∀ g, D₂.θbar (eG g) = D₁.θbar g) (s : D₁.mTheta.primeCompl) : D₂.mTheta.primeCompl :=
  ⟨R D₁ D₂ eG (s : D₁.FreeAlg), R_mem_primeCompl D₁ D₂ eG hθ s⟩

@[scoped simp] theorem coe_RS (hθ : ∀ g, D₂.θbar (eG g) = D₁.θbar g) (s : D₁.mTheta.primeCompl) :
    (RS D₁ D₂ eG hθ s : D₂.FreeAlg) = R D₁ D₂ eG (s : D₁.FreeAlg) := rfl

theorem RS_mul (hθ : ∀ g, D₂.θbar (eG g) = D₁.θbar g) (s s' : D₁.mTheta.primeCompl) :
    RS D₁ D₂ eG hθ (s * s') = RS D₁ D₂ eG hθ s * RS D₁ D₂ eG hθ s' :=
  Subtype.ext (by simp)

theorem opAlgHom_R (hop : ∀ g v, φ (D₁.op g v) = D₂.op (eG g) (φ v)) (f : D₁.FreeAlg) (v : V₁) :
    φ (D₁.opAlgHom f v) = D₂.opAlgHom (R D₁ D₂ eG f) (φ v) := by
  induction f using MvPolynomial.induction_on generalizing v with
  | C a =>
    have h1 : (MvPolynomial.C a : D₁.FreeAlg) = algebraMap 𝒪 D₁.FreeAlg a := rfl
    have h2 : R D₁ D₂ eG (algebraMap 𝒪 D₁.FreeAlg a) = algebraMap 𝒪 D₂.FreeAlg a :=
      AlgHom.commutes _ a
    rw [h1, h2, AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, map_smul]
  | add p q hp hq => rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      map_add, hp, hq]
  | mul_X p g hp =>
    rw [map_mul, map_mul, HeckeData.opAlgHom_X, R_X, map_mul, HeckeData.opAlgHom_X,
      Module.End.mul_apply, Module.End.mul_apply, ← hop, hp]

theorem smul_R (hop : ∀ g v, φ (D₁.op g v) = D₂.op (eG g) (φ v)) (f : D₁.FreeAlg) (v : V₁) :
    φ (f • v) = (R D₁ D₂ eG f) • φ v :=
  opAlgHom_R D₁ D₂ φ eG hop f v

def mapFun (hθ : ∀ g, D₂.θbar (eG g) = D₁.θbar g)
    (hop : ∀ g v, φ (D₁.op g v) = D₂.op (eG g) (φ v)) : D₁.ML → D₂.ML := fun x =>
  x.liftOn (fun p => LocalizedModule.mk (φ p.1) (RS D₁ D₂ eG hθ p.2)) (by
    rintro ⟨v, s⟩ ⟨v', s'⟩ ⟨u, hu⟩
    dsimp only at hu ⊢
    apply LocalizedModule.mk_eq.mpr
    refine ⟨RS D₁ D₂ eG hθ u, ?_⟩
    have := congrArg φ hu
    simp only [Submonoid.smul_def, smul_R D₁ D₂ φ eG hop] at this
    simpa only [Submonoid.smul_def, coe_RS] using this)

theorem mapFun_mk (hθ : ∀ g, D₂.θbar (eG g) = D₁.θbar g)
    (hop : ∀ g v, φ (D₁.op g v) = D₂.op (eG g) (φ v)) (v : V₁) (s : D₁.mTheta.primeCompl) :
    mapFun D₁ D₂ φ eG hθ hop (LocalizedModule.mk v s) =
      LocalizedModule.mk (φ v) (RS D₁ D₂ eG hθ s) := rfl

def mapL (hθ : ∀ g, D₂.θbar (eG g) = D₁.θbar g)
    (hop : ∀ g v, φ (D₁.op g v) = D₂.op (eG g) (φ v)) : D₁.ML →ₗ[𝒪] D₂.ML where
  toFun := mapFun D₁ D₂ φ eG hθ hop
  map_add' x y := by
    induction x using LocalizedModule.induction_on with
    | h v s =>
      induction y using LocalizedModule.induction_on with
      | h v' s' =>
        rw [LocalizedModule.mk_add_mk, mapFun_mk, mapFun_mk, mapFun_mk, LocalizedModule.mk_add_mk,
          RS_mul]
        congr 1
        rw [map_add, Submonoid.smul_def, Submonoid.smul_def, smul_R D₁ D₂ φ eG hop,
          smul_R D₁ D₂ φ eG hop]
        rfl
  map_smul' a x := by
    induction x using LocalizedModule.induction_on with
    | h v s =>
      rw [RingHom.id_apply, ← algebraMap_smul D₁.FreeAlg a (LocalizedModule.mk v s),
        LocalizedModule.smul'_mk, mapFun_mk, mapFun_mk,
        ← algebraMap_smul D₂.FreeAlg a (LocalizedModule.mk (φ v) _), LocalizedModule.smul'_mk,
        algebraMap_smul, algebraMap_smul, map_smul]

theorem mapL_mk (hθ : ∀ g, D₂.θbar (eG g) = D₁.θbar g)
    (hop : ∀ g v, φ (D₁.op g v) = D₂.op (eG g) (φ v)) (v : V₁) (s : D₁.mTheta.primeCompl) :
    mapL D₁ D₂ φ eG hθ hop (LocalizedModule.mk v s) =
      LocalizedModule.mk (φ v) (RS D₁ D₂ eG hθ s) := rfl

theorem mapL_X_smul (hθ : ∀ g, D₂.θbar (eG g) = D₁.θbar g)
    (hop : ∀ g v, φ (D₁.op g v) = D₂.op (eG g) (φ v)) (g : D₁.Gen) (x : D₁.ML) :
    mapL D₁ D₂ φ eG hθ hop ((MvPolynomial.X g : D₁.FreeAlg) • x) =
      (MvPolynomial.X (eG g) : D₂.FreeAlg) • mapL D₁ D₂ φ eG hθ hop x := by
  induction x using LocalizedModule.induction_on with
  | h v s =>
    rw [LocalizedModule.smul'_mk, mapL_mk, mapL_mk, LocalizedModule.smul'_mk, smul_R D₁ D₂ φ eG hop,
      R_X]

theorem exists_linearEquiv_ML_of_genEquiv (D₁ : HeckeData 𝒪 V₁ k) (D₂ : HeckeData 𝒪 V₂ k)
    (φ : V₁ ≃ₗ[𝒪] V₂) (eG : D₁.Gen ≃ D₂.Gen)
    (hop : ∀ g v, φ (D₁.op g v) = D₂.op (eG g) (φ v))
    (hθ : ∀ g, D₂.θbar (eG g) = D₁.θbar g) :
    ∃ e : D₁.ML ≃ₗ[𝒪] D₂.ML,
      (∀ (g : D₁.Gen) (x : D₁.ML),
        e ((MvPolynomial.X g : D₁.FreeAlg) • x) = (MvPolynomial.X (eG g) : D₂.FreeAlg) • e x) ∧
      (∀ (v : V₁), e (D₁.toML v) = D₂.toML (φ v)) := by
  have hop' : ∀ g w, φ.symm (D₂.op g w) = D₁.op (eG.symm g) (φ.symm w) := by
    intro g w
    apply φ.injective
    rw [LinearEquiv.apply_symm_apply, hop, Equiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hθ' : ∀ g, D₁.θbar (eG.symm g) = D₂.θbar g := by
    intro g
    rw [← hθ, Equiv.apply_symm_apply]
  let F := mapL D₁ D₂ φ.toLinearMap eG hθ hop
  let G := mapL D₂ D₁ φ.symm.toLinearMap eG.symm hθ' hop'
  have hRR : ∀ f : D₁.FreeAlg, R D₂ D₁ eG.symm (R D₁ D₂ eG f) = f := by
    intro f
    simp only [R, MvPolynomial.rename_rename, Equiv.symm_comp_self, MvPolynomial.rename_id,
      AlgHom.coe_id, id_eq]
  have hRR' : ∀ f : D₂.FreeAlg, R D₁ D₂ eG (R D₂ D₁ eG.symm f) = f := by
    intro f
    simp only [R, MvPolynomial.rename_rename, Equiv.self_comp_symm, MvPolynomial.rename_id,
      AlgHom.coe_id, id_eq]
  have hGF : ∀ x, G (F x) = x := by
    intro x
    induction x using LocalizedModule.induction_on with
    | h v s =>
      simp only [F, G, mapL_mk, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      congr 1
      exact Subtype.ext (by simp only [coe_RS, hRR])
  have hFG : ∀ y, F (G y) = y := by
    intro y
    induction y using LocalizedModule.induction_on with
    | h w s =>
      simp only [F, G, mapL_mk, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      congr 1
      exact Subtype.ext (by simp only [coe_RS, hRR'])
  refine ⟨LinearEquiv.ofLinear F G (LinearMap.ext hFG) (LinearMap.ext hGF), ?_, ?_⟩
  · intro g x
    exact mapL_X_smul D₁ D₂ φ.toLinearMap eG hθ hop g x
  · intro v
    show mapL D₁ D₂ φ.toLinearMap eG hθ hop (LocalizedModule.mk v 1) = LocalizedModule.mk (φ v) 1
    rw [mapL_mk]
    congr 1
    exact Subtype.ext (by simp only [coe_RS, OneMemClass.coe_one, map_one])

end TWStepTransport
p2m_reactivate "P2MW.S_CuspForm_TWLevel_exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq.TWStepGeo P2MW.S_CuspForm_TWLevel_exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq.TWStepTransport"

namespace TWStepMain

p2m_open "IsLocalRing CuspForm.TWLevel CohCarrier~coe_iotaDeg_one P2MW.S_CuspForm_TWLevel_exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq.TWStepGeo P2MW.S_CuspForm_TWLevel_exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq.TWStepData"

attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

set_option linter.unusedVariables false in

theorem main
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    {t : ℕ} (qv : Fin (t + 1) → ℕ) [∀ i, NeZero (qv i)] [∀ i, NeZero (Fin.init qv i)]
    (hq : ∀ i, (qv i).Prime) (hqS : qv (Fin.last t) ∉ S)
    (hqL : ¬ qv (Fin.last t) ∣ level N r (Fin.init qv))
    (hq1 : ((qv (Fin.last t) : ℕ) : ResidueField 𝒪) = 1)
    (α : Fin (t + 1) → ResidueField 𝒪)
    (hα : α (Fin.last t) ^ 2 -
          θ (CuspForm.heckeAlgebra.T (hq (Fin.last t))
            (not_dvd_of_not_dvd_level N r (Fin.init qv) hqL) hqS) * α (Fin.last t) +
            (qv (Fin.last t) : ResidueField 𝒪) = 0 ∧
      2 * α (Fin.last t) ≠
        θ (CuspForm.heckeAlgebra.T (hq (Fin.last t))
          (not_dvd_of_not_dvd_level N r (Fin.init qv) hqL) hqS))
    (hc₁ : OpComm N r qv S 𝒪 (HR N r qv))
    (hc₀ : OpComm N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)))
    (hdia₁ : ∀ (u : (ZMod (level N r qv))ˣ) (v : Carrier N r qv 𝒪 (HR N r qv)),
      (heckeData N r qv S 𝒪 (HR N r qv) θ α hc₁).toML
          (CohCarrier.diamondL (level N r qv) (HR N r qv) 𝒪 u v) =
        (heckeData N r qv S 𝒪 (HR N r qv) θ α hc₁).toML v)
    (hdia₀ : ∀ (u : (ZMod (level N r (Fin.init qv)))ˣ)
        (v : Carrier N r (Fin.init qv) 𝒪 (HR N r (Fin.init qv))),
      (heckeData N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) θ (Fin.init α) hc₀).toML
          (CohCarrier.diamondL (level N r (Fin.init qv)) (HR N r (Fin.init qv)) 𝒪 u v) =
        (heckeData N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) θ (Fin.init α) hc₀).toML v) :
    ∃ e : ML N r qv S 𝒪 (HR N r qv) θ α hc₁ ≃ₗ[𝒪]
        ML N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) θ (Fin.init α) hc₀,
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv)
          (hℓL' : ¬ ℓ ∣ level N r (Fin.init qv)) (x : ML N r qv S 𝒪 (HR N r qv) θ α hc₁),
        e ((MvPolynomial.X (CuspForm.TWLevel.Gen.T ℓ hℓ hℓS hℓL) :
            (heckeData N r qv S 𝒪 (HR N r qv) θ α hc₁).FreeAlg) • x) =
          (MvPolynomial.X (CuspForm.TWLevel.Gen.T ℓ hℓ hℓS hℓL') :
            (heckeData N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) θ (Fin.init α) hc₀).FreeAlg) •
            e x) ∧
      (∀ (i : Fin t) (x : ML N r qv S 𝒪 (HR N r qv) θ α hc₁),
        e ((MvPolynomial.X (CuspForm.TWLevel.Gen.U i.castSucc) :
            (heckeData N r qv S 𝒪 (HR N r qv) θ α hc₁).FreeAlg) • x) =
          (MvPolynomial.X (CuspForm.TWLevel.Gen.U i) :
            (heckeData N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) θ (Fin.init α) hc₀).FreeAlg) •
            e x) := by
  classical
  have hk : Function.Surjective (algebraMap 𝒪 (ResidueField 𝒪)) := IsLocalRing.residue_surjective

  set DWs := heckeData N r qv S 𝒪 (HR N r qv) θ α hc₁ with hDWs
  set DV := heckeData N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) θ (Fin.init α) hc₀ with hDV

  obtain ⟨φ, hφT, hφd⟩ :
      ∃ φ : Carrier N r qv 𝒪 (HR N r qv) ≃ₗ[𝒪] Wq (𝒪 := 𝒪) N r qv,
        (∀ (n : ℕ) [NeZero n] (v : Carrier N r qv 𝒪 (HR N r qv)),
          φ (heckeTL (level N r qv) (HR N r qv) 𝒪 n v) = heckeTL (L0 N r qv * qq qv) (Hq N r qv) 𝒪 n (φ v)) ∧
        (∀ (u : (ZMod (L0 N r qv * qq qv))ˣ) (v : Carrier N r qv 𝒪 (HR N r qv)),
          φ (diamondL (level N r qv) (HR N r qv) 𝒪 (ZMod.unitsMap (dvd_of_eq (level_eq N r qv)) u) v) =
            diamondL (L0 N r qv * qq qv) (Hq N r qv) 𝒪 u (φ v)) :=
    castH1 r 𝒪 (level N r qv) (L0 N r qv * qq qv) (level_eq N r qv) (dvd_level_r N r qv)
      ((dvd_level_r N r (Fin.init qv)).trans (dvd_mul_right _ (qq qv)))

  set DW' := DW S N r θ qv α hq with hDW'
  obtain ⟨ε, hεX, hεML⟩ := TWStepTransport.exists_linearEquiv_ML_of_genEquiv DWs DW' φ (Equiv.refl _)
    (by
      rintro (⟨ℓ, hℓ, hℓS, hℓL⟩ | i) v
      · exact @hφT ℓ ⟨hℓ.ne_zero⟩ v
      · exact hφT (qv i) v)
    (fun g => rfl)

  obtain ⟨u, w, hu, h₁, h₂, h₃, h₄, h₅, hwT, hwd⟩ :=
    CohCarrier.exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime (L0 N r qv) (qq qv)
      (hq (Fin.last t)) hqL (HR N r (Fin.init qv)) (Hq N r qv) (mem_Hq_iff N r qv) (h1 N r qv) 𝒪

  set DWp' := DWp S N r θ qv α hq u with hDWp'
  set DVp' := DVp S N r θ qv α hq hc₀ u with hDVp'
  haveI : Module.Finite 𝒪 (V0 (𝒪 := 𝒪) N r qv) :=
    CohCarrier.H1_moduleFinite (L0 N r qv) (HR N r (Fin.init qv)) 𝒪 𝒪
  haveI : Module.Finite 𝒪 (Wq (𝒪 := 𝒪) N r qv) :=
    CohCarrier.H1_moduleFinite (L0 N r qv * qq qv) (Hq N r qv) 𝒪 𝒪

  have hnilV : ∀ v : V0 (𝒪 := 𝒪) N r qv,
      DV.toML (((DVp'.op ((Equiv.refl _) (Sum.inr ())) - DV.opAlgHom 1) ^ 1) v) ∈
        (maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 DV.ML) := by
    intro v
    rw [pow_one, map_one, LinearMap.sub_apply, Module.End.one_apply, map_sub]
    have : DVp'.op ((Equiv.refl _) (Sum.inr ())) v =
        diamondL (L0 N r qv) (HR N r (Fin.init qv)) 𝒪 (ZMod.unitsMap (dvd_mul_right _ _) u) v := rfl
    rw [this, show DV.toML (diamondL (L0 N r qv) (HR N r (Fin.init qv)) 𝒪
        (ZMod.unitsMap (dvd_mul_right _ _) u) v) = DV.toML v from hdia₀ _ v, sub_self]
    exact Submodule.zero_mem _
  obtain ⟨eV, heV⟩ := CohCarrier.HeckeData.exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem hk
    DV DVp' (Equiv.refl _) (fun g => rfl) (fun g => rfl) 1 (by rw [map_one]; rfl) 1 hnilV

  have hdiaW : ∀ (v : Wq (𝒪 := 𝒪) N r qv),
      DW'.toML (diamondL (L0 N r qv * qq qv) (Hq N r qv) 𝒪 u v) = DW'.toML v := by
    intro v'
    obtain ⟨v, rfl⟩ := φ.surjective v'
    rw [← hφd u v, ← hεML, ← hεML]
    exact congrArg ε (hdia₁ _ v)
  have hnilW : ∀ v : Wq (𝒪 := 𝒪) N r qv,
      DW'.toML (((DWp'.op ((Equiv.refl _) (Sum.inr ())) - DW'.opAlgHom 1) ^ 1) v) ∈
        (maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 DW'.ML) := by
    intro v
    rw [pow_one, map_one, LinearMap.sub_apply, Module.End.one_apply, map_sub]
    have : DWp'.op ((Equiv.refl _) (Sum.inr ())) v = diamondL (L0 N r qv * qq qv) (Hq N r qv) 𝒪 u v := rfl
    rw [this, hdiaW, sub_self]
    exact Submodule.zero_mem _
  obtain ⟨eW, heW⟩ := CohCarrier.HeckeData.exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem hk
    DW' DWp' (Equiv.refl _) (fun g => rfl) (fun g => rfl) 1 (by rw [map_one]; rfl) 1 hnilW

  set σV := sigmaV S N r qv hq hqS hqL with hσV
  set σW := sigmaW S N r qv with hσW
  set ι := iDegL (L0 N r qv) (L0 N r qv * qq qv) (HR N r (Fin.init qv)) (Hq N r qv) 1 𝒪 𝒪 (h1 N r qv)
    with hι
  set j := jDegL (L0 N r qv) (L0 N r qv * qq qv) (HR N r (Fin.init qv)) (Hq N r qv) 1 𝒪 𝒪 (h1 N r qv)
    with hj
  have hqne : ∀ i : Fin t, qv i.castSucc ≠ qq qv := by
    intro i h
    apply hqL
    have hd : qv i.castSucc ∣ level N r (Fin.init qv) := dvd_level_q N r (Fin.init qv) i
    rwa [h] at hd
  have hθVW : ∀ g : GC (level N r qv) S t ⊕ Unit,
      DWp'.θbar (σW (Sum.inl g)) = DVp'.θbar (σV (Sum.inl g)) := by
    rintro ((⟨ℓ, hℓ, hℓS, hℓL⟩ | i) | ⟨⟩) <;> rfl
  have hιg : ∀ g : GC (level N r qv) S t ⊕ Unit,
      ι ∘ₗ DVp'.op (σV (Sum.inl g)) = DWp'.op (σW (Sum.inl g)) ∘ₗ ι := by
    rintro ((⟨ℓ, hℓ, hℓS, hℓL⟩ | i) | ⟨⟩)
    · haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      have hℓLq : ¬ ℓ ∣ L0 N r qv * qq qv := level_eq N r qv ▸ hℓL
      exact iDegL_heckeTL_of_not_dvd (L0 N r qv) (qq qv) (HR N r (Fin.init qv)) (Hq N r qv) (h1 N r qv)
        𝒪 ℓ hℓ hℓLq
    · exact iDegL_heckeTL_of_dvd (L0 N r qv) (qq qv) (HR N r (Fin.init qv)) (Hq N r qv) (h1 N r qv)
        𝒪 (qv i.castSucc) (dvd_level_q N r (Fin.init qv) i)
    · exact iDegL_diamondL (L0 N r qv) (qq qv) (HR N r (Fin.init qv)) (Hq N r qv) (h1 N r qv) 𝒪 u
  have hjg : ∀ g : GC (level N r qv) S t ⊕ Unit,
      j ∘ₗ DWp'.op (σW (Sum.inl g)) = DVp'.op (σV (Sum.inl g)) ∘ₗ j := by
    rintro ((⟨ℓ, hℓ, hℓS, hℓL⟩ | i) | ⟨⟩)
    · haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      have hℓLq : ¬ ℓ ∣ L0 N r qv * qq qv := level_eq N r qv ▸ hℓL
      exact jDegL_heckeTL_of_not_dvd (L0 N r qv) (qq qv) (HR N r (Fin.init qv)) (Hq N r qv) (h1 N r qv)
        𝒪 ℓ hℓ hℓLq
    · exact jDegL_heckeTL_of_dvd (L0 N r qv) (qq qv) (HR N r (Fin.init qv)) (Hq N r qv) (h1 N r qv)
        𝒪 (qv i.castSucc) (dvd_level_q N r (Fin.init qv) i)
        ((Nat.coprime_primes (hq i.castSucc) (hq (Fin.last t))).mpr (hqne i))
    · exact jDegL_diamondL (L0 N r qv) (qq qv) (HR N r (Fin.init qv)) (Hq N r qv) (h1 N r qv) 𝒪 u
  have hwg : ∀ g : GC (level N r qv) S t ⊕ Unit,
      w * DWp'.op (σW (Sum.inl g)) = DWp'.op (σW (Sum.inl g)) * w := by
    rintro ((⟨ℓ, hℓ, hℓS, hℓL⟩ | i) | ⟨⟩)
    · exact hwT ℓ hℓ (TWStepData.ne_of_not_dvd_level N r qv hℓL)
    · exact hwT (qv i.castSucc) (hq i.castSucc) (hqne i)
    · exact hwd u
  have hdV : IsUnit (DVp'.op (σV (Sum.inl (Sum.inr ())))) :=
    isUnit_diamondL (L0 N r qv) (HR N r (Fin.init qv)) 𝒪 _
  have hdW : IsUnit (DWp'.op (σW (Sum.inl (Sum.inr ())))) :=
    isUnit_diamondL (L0 N r qv * qq qv) (Hq N r qv) 𝒪 u

  set aq := θ (CuspForm.heckeAlgebra.T (hq (Fin.last t)) (not_dvd_of_not_dvd_level N r (Fin.init qv) hqL)
    hqS) with haq
  have hT : DVp'.θbar (σV (Sum.inr ())) = α (Fin.last t) + (aq - α (Fin.last t)) := by
    rw [add_sub_cancel]; rfl
  have hαβ : α (Fin.last t) * (aq - α (Fin.last t)) = 1 := by
    have h := hα.1
    rw [hq1] at h
    linear_combination -h
  have hne : α (Fin.last t) ≠ aq - α (Fin.last t) := by
    intro h
    apply hα.2
    linear_combination h
  obtain ⟨e₁, he₁⟩ :=
    CohCarrier.HeckeData.exists_linearEquiv_ML_of_degeneracy_atkinLehner_identities hk DVp' DWp' σV σW
      hθVW ι j w hιg hjg hwg (qq qv) (Sum.inr ()) hdV hdW h₁ h₂ h₃ h₄ h₅ hq1 rfl (α (Fin.last t))
      (aq - α (Fin.last t)) rfl hT hαβ hne

  have hεX' : ∀ (g : CuspForm.TWLevel.Gen (level N r qv) S (t + 1)) (x : DWs.ML),
      ε ((MvPolynomial.X g : DWs.FreeAlg) • x) = (MvPolynomial.X g : DW'.FreeAlg) • ε x := hεX
  have heW' : ∀ (g : CuspForm.TWLevel.Gen (level N r qv) S (t + 1)) (y : DW'.ML),
      eW.symm ((MvPolynomial.X g : DW'.FreeAlg) • y) =
        (MvPolynomial.X (Sum.inl g) : DWp'.FreeAlg) • eW.symm y := by
    intro g y
    apply eW.injective
    have h := heW g (eW.symm y)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [LinearEquiv.apply_symm_apply]
    exact h.symm
  have heV' : ∀ (g : CuspForm.TWLevel.Gen (level N r (Fin.init qv)) S t) (x : DVp'.ML),
      eV ((MvPolynomial.X (Sum.inl g) : DVp'.FreeAlg) • x) = (MvPolynomial.X g : DV.FreeAlg) • eV x :=
    heV
  refine ⟨((ε.trans eW.symm).trans e₁).trans eV, ?_, ?_⟩
  · intro ℓ hℓ hℓS hℓL hℓL' x
    have key : ∀ y : DWp'.ML,
        e₁ ((MvPolynomial.X (Sum.inl (CuspForm.TWLevel.Gen.T ℓ hℓ hℓS hℓL)) : DWp'.FreeAlg) • y) =
          (MvPolynomial.X (Sum.inl (CuspForm.TWLevel.Gen.T ℓ hℓ hℓS hℓL')) : DVp'.FreeAlg) • e₁ y :=
      fun y => he₁ (Sum.inl (GC.T ℓ hℓ hℓS hℓL)) y
    show eV (e₁ (eW.symm (ε ((MvPolynomial.X (CuspForm.TWLevel.Gen.T ℓ hℓ hℓS hℓL) : DWs.FreeAlg) • x)))) =
      (MvPolynomial.X (CuspForm.TWLevel.Gen.T ℓ hℓ hℓS hℓL') : DV.FreeAlg) • eV (e₁ (eW.symm (ε x)))
    rw [hεX', heW', key, heV']
  · intro i x
    have key : ∀ y : DWp'.ML,
        e₁ ((MvPolynomial.X (Sum.inl (CuspForm.TWLevel.Gen.U (Fin.castSucc i))) : DWp'.FreeAlg) • y) =
          (MvPolynomial.X (Sum.inl (CuspForm.TWLevel.Gen.U i)) : DVp'.FreeAlg) • e₁ y :=
      fun y => he₁ (Sum.inl (GC.U i)) y
    have s1 := hεX' (CuspForm.TWLevel.Gen.U (Fin.castSucc i)) x
    have s2 := heW' (CuspForm.TWLevel.Gen.U (Fin.castSucc i)) (ε x)
    have s3 := key (eW.symm (ε x))
    have s4 := heV' (CuspForm.TWLevel.Gen.U i) (e₁ (eW.symm (ε x)))
    show eV (e₁ (eW.symm (ε ((MvPolynomial.X (CuspForm.TWLevel.Gen.U (Fin.castSucc i)) : DWs.FreeAlg) • x)))) =
      (MvPolynomial.X (CuspForm.TWLevel.Gen.U i) : DV.FreeAlg) • eV (e₁ (eW.symm (ε x)))
    exact (congrArg (fun z => eV (e₁ (eW.symm z))) s1).trans
      ((congrArg (fun z => eV (e₁ z)) s2).trans ((congrArg eV s3).trans s4))

end TWStepMain
p2m_reactivate "P2MW.S_CuspForm_TWLevel_exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq.TWStepGeo P2MW.S_CuspForm_TWLevel_exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq.TWStepTransport"

end
p2m_reactivate "P2MW.S_CuspForm_TWLevel_exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq.TWStepGeo P2MW.S_CuspForm_TWLevel_exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq.TWStepTransport"

open IsLocalRing CuspForm.TWLevel in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪]

    (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]

    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)

    {t : ℕ} (qv : Fin (t + 1) → ℕ) (hq : ∀ i, (qv i).Prime) (hqS : qv (Fin.last t) ∉ S)
    (hqL : ¬ qv (Fin.last t) ∣ level N r (Fin.init qv))
    (hq1 : ((qv (Fin.last t) : ℕ) : ResidueField 𝒪) = 1)

    (α : Fin (t + 1) → ResidueField 𝒪)
    (hα : α (Fin.last t) ^ 2 -
          θ (CuspForm.heckeAlgebra.T (hq (Fin.last t))
            (not_dvd_of_not_dvd_level N r (Fin.init qv) hqL) hqS) * α (Fin.last t) +
            (qv (Fin.last t) : ResidueField 𝒪) = 0 ∧
      2 * α (Fin.last t) ≠
        θ (CuspForm.heckeAlgebra.T (hq (Fin.last t))
          (not_dvd_of_not_dvd_level N r (Fin.init qv) hqL) hqS))

    (hc₁ : haveI : ∀ i, NeZero (qv i) := fun i => ⟨(hq i).ne_zero⟩
      OpComm N r qv S 𝒪 (HR N r qv))
    (hc₀ : haveI : ∀ i, NeZero (Fin.init qv i) := fun i => ⟨(hq i.castSucc).ne_zero⟩
      OpComm N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv))) :
    haveI : ∀ i, NeZero (qv i) := fun i => ⟨(hq i).ne_zero⟩
    haveI : ∀ i, NeZero (Fin.init qv i) := fun i => ⟨(hq i.castSucc).ne_zero⟩

    (∀ (u : (ZMod (level N r qv))ˣ) (v : Carrier N r qv 𝒪 (HR N r qv)),
      (heckeData N r qv S 𝒪 (HR N r qv) θ α hc₁).toML
          (CohCarrier.diamondL (level N r qv) (HR N r qv) 𝒪 u v) =
        (heckeData N r qv S 𝒪 (HR N r qv) θ α hc₁).toML v) →
    (∀ (u : (ZMod (level N r (Fin.init qv)))ˣ) (v : Carrier N r (Fin.init qv) 𝒪 (HR N r (Fin.init qv))),
      (heckeData N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) θ (Fin.init α) hc₀).toML
          (CohCarrier.diamondL (level N r (Fin.init qv)) (HR N r (Fin.init qv)) 𝒪 u v) =
        (heckeData N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) θ (Fin.init α) hc₀).toML v) →
    ∃ e : ML N r qv S 𝒪 (HR N r qv) θ α hc₁ ≃ₗ[𝒪]
        ML N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) θ (Fin.init α) hc₀,

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv)
          (hℓL' : ¬ ℓ ∣ level N r (Fin.init qv)) (x : ML N r qv S 𝒪 (HR N r qv) θ α hc₁),
        e ((MvPolynomial.X (Gen.T ℓ hℓ hℓS hℓL) :
            (heckeData N r qv S 𝒪 (HR N r qv) θ α hc₁).FreeAlg) • x) =
          (MvPolynomial.X (Gen.T ℓ hℓ hℓS hℓL') :
            (heckeData N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) θ (Fin.init α) hc₀).FreeAlg) •
            e x) ∧

      (∀ (i : Fin t) (x : ML N r qv S 𝒪 (HR N r qv) θ α hc₁),
        e ((MvPolynomial.X (Gen.U i.castSucc) :
            (heckeData N r qv S 𝒪 (HR N r qv) θ α hc₁).FreeAlg) • x) =
          (MvPolynomial.X (Gen.U i) :
            (heckeData N r (Fin.init qv) S 𝒪 (HR N r (Fin.init qv)) θ (Fin.init α) hc₀).FreeAlg) •
            e x) :=
  haveI : ∀ i, NeZero (qv i) := fun i => ⟨(hq i).ne_zero⟩
  haveI : ∀ i, NeZero (Fin.init qv i) := fun i => ⟨(hq i.castSucc).ne_zero⟩
  fun hdia₁ hdia₀ => TWStepMain.main S N r θ qv hq hqS hqL hq1 α hα hc₁ hc₀ hdia₁ hdia₀

end S_CuspForm_TWLevel_exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq
end P2MW
export P2MW.S_CuspForm_TWLevel_exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq (solution)
