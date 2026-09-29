-- Prove2me | solution 1 for CuspForm.exists_isNormalizedEigenform_of_isMaximal_heckeAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/138a475a-b6f6-5459-ba5a-a078ab331141

import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_annihilator_le_of_isPrime
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_isNormalizedEigenform_of_isMaximal_heckeAlgebra
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false

noncomputable section

namespace P2mS17DS611

variable {M : ℕ} [NeZero M]

abbrev S2 (M : ℕ) : Type := CuspForm (CongruenceSubgroup.Gamma0 M) 2

theorem exists_apply_eq_smul (S : Set ℕ) {f : S2 M} (hf : f.IsNormalizedEigenform)
    (t : CuspForm.heckeAlgebra M 2 S) : ∃ c : ℂ, (t : Module.End ℂ (S2 M)) f = c • f := by
  obtain ⟨t, ht⟩ := t
  change t ∈ Algebra.adjoin ℤ (CuspForm.heckeGenerators M 2 S) at ht
  have key := (CuspForm.isNormalizedEigenform_iff_heckeTLin f).mp hf
  induction ht using Algebra.adjoin_induction with
  | mem T hTmem =>
    rcases hTmem with ⟨ℓ, hℓ, hℓN, _, rfl⟩ | ⟨ℓ, hℓN, hℓ, _, rfl⟩
    · exact ⟨ModularFormClass.qCoeff f ℓ, (key.2 ℓ hℓ).1 hℓN⟩
    · exact ⟨ModularFormClass.qCoeff f ℓ, (key.2 ℓ hℓ).2 hℓN⟩
  | algebraMap n =>
    refine ⟨(n : ℂ), ?_⟩
    change (algebraMap ℤ (Module.End ℂ (S2 M)) n) f = (n : ℂ) • f
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply, Int.cast_smul_eq_zsmul]
  | add S T _ _ ihS ihT =>
    obtain ⟨c, hc⟩ := ihS
    obtain ⟨d, hd⟩ := ihT
    exact ⟨c + d, by rw [LinearMap.add_apply, hc, hd, add_smul]⟩
  | mul S T _ _ ihS ihT =>
    obtain ⟨c, hc⟩ := ihS
    obtain ⟨d, hd⟩ := ihT
    exact ⟨c * d, by rw [Module.End.mul_apply, hd, map_smul, hc, smul_smul, mul_comm]⟩

theorem ne_zero_of_isNormalizedEigenform {f : S2 M} (hf : f.IsNormalizedEigenform) : f ≠ 0 := by
  intro h0
  have h1 := hf.qCoeff_one
  rw [h0, CuspForm.coe_zero] at h1
  simp [ModularFormClass.qCoeff, UpperHalfPlane.qExpansion_zero] at h1

theorem smul_left_injective' {f : S2 M} (hf0 : f ≠ 0) {c d : ℂ} (h : c • f = d • f) : c = d := by
  have h1 : (c - d) • f = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h1 with h2 | h2
  · exact sub_eq_zero.mp h2
  · exact absurd h2 hf0

def eigenScalar (S : Set ℕ) {f : S2 M} (hf : f.IsNormalizedEigenform) (t : CuspForm.heckeAlgebra M 2 S) : ℂ :=
  Classical.choose (exists_apply_eq_smul S hf t)

theorem apply_eq_eigenScalar_smul (S : Set ℕ) {f : S2 M} (hf : f.IsNormalizedEigenform)
    (t : CuspForm.heckeAlgebra M 2 S) : (t : Module.End ℂ (S2 M)) f = eigenScalar S hf t • f :=
  Classical.choose_spec (exists_apply_eq_smul S hf t)

theorem eigenScalar_eq_of_apply_eq_smul (S : Set ℕ) {f : S2 M} (hf : f.IsNormalizedEigenform)
    (t : CuspForm.heckeAlgebra M 2 S) {c : ℂ} (h : (t : Module.End ℂ (S2 M)) f = c • f) :
    eigenScalar S hf t = c :=
  smul_left_injective' (ne_zero_of_isNormalizedEigenform hf) ((apply_eq_eigenScalar_smul S hf t).symm.trans h)

def eigenCharC (S : Set ℕ) {f : S2 M} (hf : f.IsNormalizedEigenform) : CuspForm.heckeAlgebra M 2 S →+* ℂ where
  toFun := eigenScalar S hf
  map_one' := eigenScalar_eq_of_apply_eq_smul S hf 1 (by rw [Subalgebra.coe_one, Module.End.one_apply, one_smul])
  map_mul' s t := by
    apply eigenScalar_eq_of_apply_eq_smul S hf
    rw [Subalgebra.coe_mul, Module.End.mul_apply, apply_eq_eigenScalar_smul S hf t, map_smul,
      apply_eq_eigenScalar_smul S hf s, smul_smul, mul_comm]
  map_zero' := eigenScalar_eq_of_apply_eq_smul S hf 0 (by rw [Subalgebra.coe_zero, LinearMap.zero_apply, zero_smul])
  map_add' s t := by
    apply eigenScalar_eq_of_apply_eq_smul S hf
    rw [Subalgebra.coe_add, LinearMap.add_apply, apply_eq_eigenScalar_smul S hf s,
      apply_eq_eigenScalar_smul S hf t, add_smul]

theorem apply_eq_eigenCharC_smul (S : Set ℕ) {f : S2 M} (hf : f.IsNormalizedEigenform)
    (t : CuspForm.heckeAlgebra M 2 S) : (t : Module.End ℂ (S2 M)) f = eigenCharC S hf t • f :=
  apply_eq_eigenScalar_smul S hf t

theorem eigenCharC_T (S : Set ℕ) {f : S2 M} (hf : f.IsNormalizedEigenform)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ S) :
    eigenCharC S hf (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff f ℓ := by
  apply eigenScalar_eq_of_apply_eq_smul S hf
  rw [CuspForm.heckeAlgebra.coe_T]
  exact (((CuspForm.isNormalizedEigenform_iff_heckeTLin f).mp hf).2 ℓ hℓ).1 hℓM

theorem isIntegral_eigenCharC' (S : Set ℕ) {f : S2 M} (hf : f.IsNormalizedEigenform)
    (t : CuspForm.heckeAlgebra M 2 S) : IsIntegral ℤ (eigenCharC S hf t) := by
  haveI := CuspForm.moduleFinite_heckeAlgebra_two M S
  have ht : IsIntegral ℤ t := Algebra.IsIntegral.isIntegral t
  exact ht.map (eigenCharC S hf).toIntAlgHom

def eigenCharZbar (S : Set ℕ) {f : S2 M} (hf : f.IsNormalizedEigenform) :
    CuspForm.heckeAlgebra M 2 S →+* integralClosure ℤ ℂ :=
  (eigenCharC S hf).codRestrict (integralClosure ℤ ℂ)
    (fun t => show IsIntegral ℤ (eigenCharC S hf t) from isIntegral_eigenCharC' S hf t)

@[scoped simp] theorem coe_eigenCharZbar (S : Set ℕ) {f : S2 M} (hf : f.IsNormalizedEigenform)
    (t : CuspForm.heckeAlgebra M 2 S) : (eigenCharZbar S hf t : ℂ) = eigenCharC S hf t := rfl

end P2mS17DS611
p2m_reactivate "P2MW.S_CuspForm_exists_isNormalizedEigenform_of_isMaximal_heckeAlgebra.P2mS17DS611"

open P2mS17DS611 in
theorem solution (N : ℕ) [NeZero N]
    (S : Set ℕ) (𝔪 : Ideal (CuspForm.heckeAlgebra N 2 S)) (h𝔪 : 𝔪.IsMaximal) :
    ∃ (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (𝔐 : Ideal (integralClosure ℤ ℂ)),
      g.IsNormalizedEigenform ∧ 𝔐.IsMaximal ∧
      ∀ t : CuspForm.heckeAlgebra N 2 S, ∃ a : integralClosure ℤ ℂ,
        (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) g = (a : ℂ) • g ∧
        (t ∈ 𝔪 → a ∈ 𝔐) := by
  haveI := h𝔪
  obtain ⟨g, hg, hann⟩ :=
    CuspForm.exists_isNormalizedEigenform_annihilator_le_of_isPrime S 𝔪 h𝔪.isPrime
  let χ : CuspForm.heckeAlgebra N 2 S →+* integralClosure ℤ ℂ := eigenCharZbar S hg
  have hker : RingHom.ker χ ≤ 𝔪 := by
    intro t ht
    apply hann t
    have h0 : (χ t : ℂ) = 0 := by rw [RingHom.mem_ker.mp ht]; rfl
    rw [apply_eq_eigenCharC_smul S hg t, ← coe_eigenCharZbar, h0, zero_smul]
  letI : Algebra (CuspForm.heckeAlgebra N 2 S) (integralClosure ℤ ℂ) := χ.toAlgebra
  haveI : IsScalarTower ℤ (CuspForm.heckeAlgebra N 2 S) (integralClosure ℤ ℂ) :=
    IsScalarTower.of_algebraMap_eq fun n => by
      simp [RingHom.algebraMap_toAlgebra]
  haveI : Algebra.IsIntegral (CuspForm.heckeAlgebra N 2 S) (integralClosure ℤ ℂ) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := ℤ) x).tower_top⟩
  have hker' : RingHom.ker (algebraMap (CuspForm.heckeAlgebra N 2 S) (integralClosure ℤ ℂ)) ≤ 𝔪 := hker
  obtain ⟨𝔐, h𝔐, hcomap⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral 𝔪 hker'
  refine ⟨g, 𝔐, hg, h𝔐, fun t => ⟨χ t, ?_, fun ht => ?_⟩⟩
  · rw [coe_eigenCharZbar]; exact apply_eq_eigenCharC_smul S hg t
  · have : t ∈ 𝔐.comap (algebraMap (CuspForm.heckeAlgebra N 2 S) (integralClosure ℤ ℂ)) := by
      rw [hcomap]; exact ht
    exact this

end
end S_CuspForm_exists_isNormalizedEigenform_of_isMaximal_heckeAlgebra
end P2MW
export P2MW.S_CuspForm_exists_isNormalizedEigenform_of_isMaximal_heckeAlgebra (solution)
