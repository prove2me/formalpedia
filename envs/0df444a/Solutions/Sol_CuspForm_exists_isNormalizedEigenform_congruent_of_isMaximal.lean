-- Prove2me | solution 1 for CuspForm.exists_isNormalizedEigenform_congruent_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/7c5b5d6c-c62b-5130-a3c0-9482ab43e924

import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_FLTPrelim_ModularRep
import Theorems.Thm_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra
import Theorems.Thm_CuspForm_HasIntegralStructure_moduleFree_heckeAlgebra
import Theorems.Thm_DeligneSerre_exists_minimalPrime_le
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra_integralClosure
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeT
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_ker_le_of_isPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_isNormalizedEigenform_congruent_of_isMaximal

theorem solution {N : ℕ} [NeZero N]
    (hN : CuspForm.HasIntegralStructure N 2)
    (𝔪₁ : Ideal (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N})) (h𝔪₁ : 𝔪₁.IsMaximal)
    {p : ℕ} (hp𝔪 : (p : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁) :
    ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (_ : f.IsNormalizedEigenform)
      (𝔪' : Ideal (integralClosure ℤ ℂ)), 𝔪'.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪' ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (b : ℤ),
        CuspForm.heckeAlgebra.T hℓ hℓN hℓN - (b : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁ →
        ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          a - (b : integralClosure ℤ ℂ) ∈ 𝔪' := by
  classical

  haveI : Module.Finite ℤ (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) :=
    CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra hN (by norm_num) _
  haveI : Module.Free ℤ (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) :=
    CuspForm.HasIntegralStructure.moduleFree_heckeAlgebra hN (by norm_num) _
  haveI : Module.IsTorsionFree ℤ (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) := inferInstance

  obtain ⟨𝔭, h𝔭min, h𝔭le, h𝔭char⟩ := DeligneSerre.exists_minimalPrime_le 𝔪₁ h𝔪₁.isPrime
  obtain ⟨f, hf, hann⟩ := CuspForm.exists_isNormalizedEigenform_ker_le_of_isPrime hN 𝔭 h𝔭min.1.1 h𝔭char

  obtain ⟨χ, hχ⟩ :=
    CuspForm.IsNormalizedEigenform.exists_ringHom_heckeAlgebra_integralClosure hN hf {ℓ | ℓ ∣ N}
  have hkerχ : RingHom.ker χ ≤ 𝔪₁ := by
    intro t ht
    refine h𝔭le (hann t ?_)
    rw [hχ t, RingHom.mem_ker.mp ht]
    simp

  letI : Algebra (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) (integralClosure ℤ ℂ) := χ.toAlgebra
  haveI : IsScalarTower ℤ (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) (integralClosure ℤ ℂ) := by
    refine IsScalarTower.of_algebraMap_eq fun n => ?_
    show algebraMap ℤ (integralClosure ℤ ℂ) n = χ (algebraMap ℤ (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) n)
    simp only [eq_intCast, map_intCast]
  haveI : Algebra.IsIntegral (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) (integralClosure ℤ ℂ) := by
    constructor
    intro x
    exact IsIntegral.tower_top (R := ℤ) (integralClosure.isIntegral x)
  haveI := h𝔪₁
  obtain ⟨𝔪', h𝔪'max, h𝔪'comap⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := integralClosure ℤ ℂ) 𝔪₁
      (by rw [RingHom.algebraMap_toAlgebra]; exact hkerχ)
  have hmem : ∀ t ∈ 𝔪₁, χ t ∈ 𝔪' := by
    intro t ht
    have hcomap : t ∈ 𝔪'.comap (algebraMap (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) (integralClosure ℤ ℂ)) := by
      rw [h𝔪'comap]; exact ht
    rwa [Ideal.mem_comap, RingHom.algebraMap_toAlgebra] at hcomap
  refine ⟨f, hf, 𝔪', h𝔪'max, ?_, ?_⟩
  ·
    have := hmem _ hp𝔪
    rwa [map_natCast] at this
  ·
    intro ℓ hℓ hℓN b hTb
    refine ⟨χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓN), ?_, ?_⟩
    ·
      have hTf : ((CuspForm.heckeAlgebra.T hℓ hℓN hℓN : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) :
          Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = ModularFormClass.qCoeff f ℓ • f := by
        apply DFunLike.coe_injective
        rw [CuspForm.heckeAlgebra.coe_T]
        show ⇑(CuspForm.heckeTLin 2 hℓ hℓN f) = ⇑(ModularFormClass.qCoeff f ℓ • f)
        rw [CuspForm.coe_heckeTLin_apply, CuspForm.IsGLPos.coe_smul]
        exact (((CuspForm.isNormalizedEigenform_iff_heckeT f).mp hf).2 ℓ hℓ).1 hℓN
      have h2 := hχ (CuspForm.heckeAlgebra.T hℓ hℓN hℓN)
      rw [hTf] at h2
      have hsub : (ModularFormClass.qCoeff f ℓ - (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓN) : ℂ)) • f = 0 := by
        rw [sub_smul, h2, sub_self]
      rcases smul_eq_zero.mp hsub with h0 | h0
      · exact (sub_eq_zero.mp h0).symm
      · exact absurd h0 hf.ne_zero
    · have h := hmem _ hTb
      have e : χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓN - (b : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}))
          = χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓN) - (b : integralClosure ℤ ℂ) := by
        rw [RingHom.map_sub, map_intCast]
      rwa [e] at h

end S_CuspForm_exists_isNormalizedEigenform_congruent_of_isMaximal
end P2MW
export P2MW.S_CuspForm_exists_isNormalizedEigenform_congruent_of_isMaximal (solution)
