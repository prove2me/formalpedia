-- Prove2me | solution 1 for CuspForm.IsNormalizedEigenform.exists_heckeAlgebraChar_raisedLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/4065cb42-a0a0-5c86-997e-ee192ecaa65d

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_EigenformCoefficientRing
import Definitions.Def_FreyPackage_ModMCarrier_OldSublattice
import Theorems.Thm_CuspForm_IsNormalizedEigenform_heckeTLin_apply_eq_qCoeff_smul
import Theorems.Thm_CuspForm_IsNormalizedEigenform_primeCoeffsIntegral_of_neZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNormalizedEigenform_exists_heckeAlgebraChar_raisedLevel
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false

noncomputable section

namespace SolRaisedLevelHeckeChar

open ModularForm

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def eigenSubring (R : Subalgebra ℤ ℂ) (v : V) : Subring (Module.End ℂ V) where
  carrier := {t | ∃ c : ℂ, c ∈ R ∧ t v = c • v}
  mul_mem' := by
    rintro s t ⟨a, ha, hs⟩ ⟨b, hb, ht⟩
    refine ⟨a * b, mul_mem ha hb, ?_⟩
    rw [Module.End.mul_apply, ht, map_smul, hs, smul_smul, mul_comm]
  one_mem' := ⟨1, one_mem R, by rw [Module.End.one_apply, one_smul]⟩
  add_mem' := by
    rintro s t ⟨a, ha, hs⟩ ⟨b, hb, ht⟩
    exact ⟨a + b, add_mem ha hb, by rw [LinearMap.add_apply, hs, ht, add_smul]⟩
  zero_mem' := ⟨0, zero_mem R, by rw [LinearMap.zero_apply, zero_smul]⟩
  neg_mem' := by
    rintro s ⟨a, ha, hs⟩
    exact ⟨-a, neg_mem ha, by rw [LinearMap.neg_apply, hs, neg_smul]⟩

def eigenSubalgebra (R : Subalgebra ℤ ℂ) (v : V) : Subalgebra ℤ (Module.End ℂ V) :=
  subalgebraOfSubring (eigenSubring R v)

variable (R : Subalgebra ℤ ℂ) {v : V}

theorem mem_eigenSubalgebra_iff {t : Module.End ℂ V} :
    t ∈ eigenSubalgebra R v ↔ ∃ c : ℂ, c ∈ R ∧ t v = c • v :=
  mem_subalgebraOfSubring

theorem exists_eigenvalue (t : eigenSubalgebra R v) :
    ∃ c : R, (t : Module.End ℂ V) v = (c : ℂ) • v := by
  obtain ⟨c, hc, h⟩ := (mem_eigenSubalgebra_iff R).mp t.2
  exact ⟨⟨c, hc⟩, h⟩

def eigenvalue (t : eigenSubalgebra R v) : R :=
  (exists_eigenvalue R t).choose

theorem apply_eq_eigenvalue_smul (t : eigenSubalgebra R v) :
    (t : Module.End ℂ V) v = (eigenvalue R t : ℂ) • v :=
  (exists_eigenvalue R t).choose_spec

variable {R}

theorem coe_eigenvalue_eq_of_apply_eq_smul (hv : v ≠ 0) {t : eigenSubalgebra R v} {c : ℂ}
    (h : (t : Module.End ℂ V) v = c • v) : (eigenvalue R t : ℂ) = c :=
  smul_left_injective ℂ hv ((apply_eq_eigenvalue_smul R t).symm.trans h)

variable (R)

def eigenChar (hv : v ≠ 0) : eigenSubalgebra R v →+* R where
  toFun := eigenvalue R
  map_one' := by
    apply Subtype.ext
    rw [OneMemClass.coe_one]
    apply coe_eigenvalue_eq_of_apply_eq_smul hv
    rw [OneMemClass.coe_one, Module.End.one_apply, one_smul]
  map_mul' s t := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul]
    apply coe_eigenvalue_eq_of_apply_eq_smul hv
    rw [MulMemClass.coe_mul, Module.End.mul_apply, apply_eq_eigenvalue_smul R t, map_smul,
      apply_eq_eigenvalue_smul R s, smul_smul, mul_comm]
  map_zero' := by
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero]
    apply coe_eigenvalue_eq_of_apply_eq_smul hv
    rw [ZeroMemClass.coe_zero, LinearMap.zero_apply, zero_smul]
  map_add' s t := by
    apply Subtype.ext
    rw [AddMemClass.coe_add]
    apply coe_eigenvalue_eq_of_apply_eq_smul hv
    rw [AddMemClass.coe_add, LinearMap.add_apply, apply_eq_eigenvalue_smul R t,
      apply_eq_eigenvalue_smul R s, add_smul]

theorem eigenChar_apply (hv : v ≠ 0) (t : eigenSubalgebra R v) :
    eigenChar R hv t = eigenvalue R t := rfl

theorem coe_eigenChar_eq_of_apply_eq_smul (hv : v ≠ 0) {t : eigenSubalgebra R v} {c : ℂ}
    (h : (t : Module.End ℂ V) v = c • v) : (eigenChar R hv t : ℂ) = c :=
  coe_eigenvalue_eq_of_apply_eq_smul hv h

end Generic

section RaisedLevel

open FreyPackage.ModMCarrier

variable {N q' : ℕ} [NeZero (N * q')]

def raise (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    CuspForm (CongruenceSubgroup.Gamma0 (N * q')) 2 :=
  levelInclusionLin (dvd_mul_right N q') 2 f

@[scoped simp] theorem coe_raise (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ⇑(raise (q' := q') f) = ⇑f := rfl

theorem raise_ne_zero {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    (hf : CuspForm.IsNormalizedEigenform f) : raise (q' := q') f ≠ 0 := by
  intro h
  have h1 := hf.qCoeff_one
  have hcoe : (⇑f : UpperHalfPlane → ℂ) = 0 := by
    rw [← coe_raise (q' := q') f, h]; rfl
  rw [hcoe, ModularFormClass.qCoeff, UpperHalfPlane.qExpansion_zero, map_zero] at h1
  exact zero_ne_one h1

theorem heckeTLin_raise {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    (hf : CuspForm.IsNormalizedEigenform f) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ N * q') :
    CuspForm.heckeTLin 2 hℓ hℓM (raise f) = ModularFormClass.qCoeff f ℓ • raise f := by
  have hℓN : ¬ ℓ ∣ N := fun h => hℓM (h.mul_right q')
  apply DFunLike.coe_injective
  have hN := congrArg DFunLike.coe
    (CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul N f hf ℓ hℓ hℓN)
  rw [CuspForm.coe_heckeTLin_apply, CuspForm.IsGLPos.coe_smul] at hN
  change ⇑(CuspForm.heckeTLin 2 hℓ hℓM (raise f)) = ⇑(ModularFormClass.qCoeff f ℓ • raise (q' := q') f)
  rw [CuspForm.coe_heckeTLin_apply, CuspForm.IsGLPos.coe_smul, coe_raise]
  exact hN

theorem heckeAlgebra_le_eigenSubalgebra [NeZero N] {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    (hf : CuspForm.IsNormalizedEigenform f) :
    CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'}
      ≤ eigenSubalgebra (integralClosure ℤ ℂ) (raise (q' := q') f) := by
  refine Algebra.adjoin_le ?_
  rintro T (⟨ℓ, hℓ, hℓM, -, rfl⟩ | ⟨q, hqM, -, hqS, rfl⟩)
  · obtain ⟨a, ha⟩ := CuspForm.IsNormalizedEigenform.primeCoeffsIntegral_of_neZero hf ⟨ℓ, hℓ⟩
    refine (mem_eigenSubalgebra_iff _).mpr ⟨ModularFormClass.qCoeff f ℓ, ?_, ?_⟩
    · rw [← ha]; exact a.2
    · exact heckeTLin_raise hf hℓ hℓM
  · exact absurd hqM hqS

end RaisedLevel

end SolRaisedLevelHeckeChar
p2m_reactivate "P2MW.S_CuspForm_IsNormalizedEigenform_exists_heckeAlgebraChar_raisedLevel.SolRaisedLevelHeckeChar"

open SolRaisedLevelHeckeChar in
theorem solution
    {N q' : ℕ} [NeZero N] (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) [NeZero (N * q')]
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : CuspForm.IsNormalizedEigenform f) :
    ∃ χ₁ : CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'} →+* integralClosure ℤ ℂ,
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ N * q'),
        ((χ₁ (CuspForm.heckeAlgebra.T hℓ hℓM hℓM) : integralClosure ℤ ℂ) : ℂ)
          = ModularFormClass.qCoeff f ℓ := by
  have hv : raise (q' := q') f ≠ 0 := raise_ne_zero hf
  have hle := heckeAlgebra_le_eigenSubalgebra (q' := q') hf
  refine ⟨(eigenChar (integralClosure ℤ ℂ) hv).comp (Subalgebra.inclusion hle).toRingHom, ?_⟩
  intro ℓ hℓ hℓM
  change ((eigenChar (integralClosure ℤ ℂ) hv
      (Subalgebra.inclusion hle (CuspForm.heckeAlgebra.T hℓ hℓM hℓM)) : integralClosure ℤ ℂ) : ℂ)
    = ModularFormClass.qCoeff f ℓ
  exact coe_eigenChar_eq_of_apply_eq_smul (integralClosure ℤ ℂ) hv (heckeTLin_raise hf hℓ hℓM)

end
p2m_reactivate "P2MW.S_CuspForm_IsNormalizedEigenform_exists_heckeAlgebraChar_raisedLevel.SolRaisedLevelHeckeChar"

end S_CuspForm_IsNormalizedEigenform_exists_heckeAlgebraChar_raisedLevel
end P2MW
export P2MW.S_CuspForm_IsNormalizedEigenform_exists_heckeAlgebraChar_raisedLevel (solution)
