-- Prove2me | solution 1 for CuspForm.exists_qIntegral_eisenstein_eigen_mod_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e38ffb6c-bf1c-5ad0-a2bd-5f790d55160b

import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralLattice
import Theorems.Thm_CuspForm_exists_ringHom_zmod_of_eisenstein_injective
import Theorems.Thm_CuspForm_exists_qIntegral_qCoeff_apply_one_eq_of_hasIntegralBasis
import Theorems.Thm_CuspForm_exists_mem_heckeAlgebra_qCoeff_apply_one_eq
import Theorems.Thm_ModularCurve_heckeProj_surjective
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Data.ZMod.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_qIntegral_eisenstein_eigen_mod_of_injective

set_option autoImplicit false

noncomputable section

open ModularCurve

namespace S09RCMain

private theorem one_mem_strictPeriods (N : ℕ) :
    (1 : ℝ) ∈ Subgroup.strictPeriods
      (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)) := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples 1

private theorem qCoeff_sub {N : ℕ} (g₁ g₂ : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(g₁ - g₂)) n
      = ModularFormClass.qCoeff g₁ n - ModularFormClass.qCoeff g₂ n := by
  simp only [ModularFormClass.qCoeff, CuspForm.coe_sub,
    ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods N) g₁ g₂, map_sub]

private theorem qCoeff_zsmul {N : ℕ} (c : ℤ) (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (n : ℕ) :
    ModularFormClass.qCoeff (⇑(c • g)) n = (c : ℂ) * ModularFormClass.qCoeff g n := by
  have h : (c • g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) = (c : ℂ) • g :=
    (Int.cast_smul_eq_zsmul ℂ c g).symm
  rw [h]
  simp only [ModularFormClass.qCoeff]
  rw [CuspForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N) (c : ℂ) g, map_smul,
    smul_eq_mul]

private theorem qCoeff_heckeTLin_eq {N : ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeTLin 2 hℓ hℓN g) n
      = ModularFormClass.qCoeff g (n * ℓ)
        + if ℓ ∣ n then (ℓ : ℂ) * ModularFormClass.qCoeff g (n / ℓ) else 0 := by
  rw [CuspForm.coe_heckeTLin_apply]
  rw [ModularFormClass.qCoeff_heckeT g (one_mem_strictPeriods N) hℓ.ne_zero n]
  rw [ModularForm.coeffHeckeT_apply]
  simp only [show (2 : ℤ) - 1 = 1 by norm_num, zpow_one]

private theorem qCoeff_heckeULin_eq {N : ℕ} [NeZero N] {q : ℕ} (hq0 : q ≠ 0) (hqN : q ∣ N)
    (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeULin 2 hqN g) n
      = ModularFormClass.qCoeff g (n * q) := by
  rw [CuspForm.coe_heckeULin_apply]
  rw [ModularFormClass.qCoeff_heckeU g (one_mem_strictPeriods N) hq0 n]
  rfl

private theorem coe_algebraMap_apply (N : ℕ) [NeZero N] (c : ℤ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ((algebraMap ℤ (CuspForm.heckeAlgebra N 2 ∅) c : CuspForm.heckeAlgebra N 2 ∅) :
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = c • f := by
  rw [show ((algebraMap ℤ (CuspForm.heckeAlgebra N 2 ∅) c : CuspForm.heckeAlgebra N 2 ∅) :
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))
      = algebraMap ℤ (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) c from rfl]
  simp only [algebraMap_int_eq, Int.coe_castRingHom, Module.End.intCast_apply]

private theorem dvd_of_qCoeff_eq (p m : ℕ) [Fact p.Prime]
    (χ : CuspForm.heckeAlgebra p 2 ∅ →+* ZMod m)
    (hχI : ∀ i ∈ Ideal.map (heckeProj p) (eisensteinIdeal p), χ i = 0)
    (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2)
    (hRC2 : ∀ t : CuspForm.heckeAlgebra p 2 ∅, ∀ c : ℤ,
      (c : ℂ) = ModularFormClass.qCoeff
        ((t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2)) f) 1 →
      (c : ZMod m) = χ t)
    (n : ℕ) (hn : n ≠ 0) (g : HeckeAlg) (hg : g ∈ eisensteinIdeal p) (c : ℤ)
    (hc : (c : ℂ) = ModularFormClass.qCoeff
      ((heckeProj p g : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2)) f) n) :
    (m : ℤ) ∣ c := by
  obtain ⟨t, ht, hT1⟩ := CuspForm.exists_mem_heckeAlgebra_qCoeff_apply_one_eq p n hn
  obtain ⟨τ, hτ⟩ := ModularCurve.heckeProj_surjective p ⟨t, ht⟩
  have hx : τ * g ∈ eisensteinIdeal p := Ideal.mul_mem_left _ τ hg
  have hc1 : (c : ℂ) = ModularFormClass.qCoeff
      ((heckeProj p (τ * g) : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2)) f)
        1 := by
    rw [map_mul, hτ, Subalgebra.coe_mul, Module.End.mul_apply,
      show ((⟨t, ht⟩ : CuspForm.heckeAlgebra p 2 ∅) :
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2)) = t from rfl,
      hT1]
    exact hc
  have h5 := hRC2 (heckeProj p (τ * g)) c hc1
  rw [hχI _ (Ideal.mem_map_of_mem _ hx)] at h5
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd c m).mp h5

end S09RCMain

namespace CuspForm p2m_export "CuspForm" "sub_apply IsGLPos.coe_smul coe_sub coe_smul heckeAlgebra heckeAlgebra.coe_T heckeAlgebra.coe_U heckeTLin heckeULin coe_heckeTLin_apply coe_heckeULin_apply qIntegralSet HasIntegralBasis exists_ringHom_zmod_of_eisenstein_injective exists_qIntegral_qCoeff_apply_one_eq_of_hasIntegralBasis exists_mem_heckeAlgebra_qCoeff_apply_one_eq" end CuspForm
p2m_open_scoped "CuspForm" in

private theorem CuspForm.exists_qIntegral_eisenstein_eigen_mod_of_injective
    (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (hIB : CuspForm.HasIntegralBasis p)
    (hinj : ∀ c : ℤ, algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅) c ∈
      Ideal.map (heckeProj p) (eisensteinIdeal p) ⊔
        Ideal.span {((m : ℕ) : CuspForm.heckeAlgebra p 2 ∅)} → (m : ℤ) ∣ c) :
    ∃ f ∈ CuspForm.qIntegralSet p, ∃ af : ℕ → ℤ,
      (∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) ∧
      IsCoprime (af 1) (m : ℤ) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ, n ≠ 0 →
        (m : ℤ) ∣ af (n * ℓ) + (if ℓ ∣ n then (ℓ : ℤ) * af (n / ℓ) else 0) - (1 + ℓ) * af n) ∧
      (∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af (n * p) - af n) := by
  have pP : p.Prime := Fact.out
  haveI : NeZero m := ⟨by omega⟩

  obtain ⟨χ, hχI, -⟩ := CuspForm.exists_ringHom_zmod_of_eisenstein_injective p m hm hinj

  obtain ⟨f, hf, hRC2⟩ := CuspForm.exists_qIntegral_qCoeff_apply_one_eq_of_hasIntegralBasis
    p m hIB χ.toAddMonoidHom.toIntLinearMap
  have hRC2' : ∀ t : CuspForm.heckeAlgebra p 2 ∅, ∀ c : ℤ,
      (c : ℂ) = ModularFormClass.qCoeff
        ((t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2)) f) 1 →
      (c : ZMod m) = χ t := hRC2

  have hf' : ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ (⊥ : Subring ℂ) := hf
  choose af haf using fun n => Subring.mem_bot.mp (hf' n)
  refine ⟨f, hf, af, haf, ?_, ?_, ?_⟩
  ·
    have hone : ((af 1 : ℤ) : ℂ) = ModularFormClass.qCoeff
        (((1 : CuspForm.heckeAlgebra p 2 ∅) :
          Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2)) f) 1 := haf 1
    have h5 := hRC2' 1 (af 1) hone
    rw [map_one] at h5
    obtain ⟨k, hk⟩ : (m : ℤ) ∣ af 1 - 1 := by
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp ?_
      push_cast
      rw [h5]
      ring
    exact ⟨1, -k, by linear_combination hk⟩
  ·
    intro ℓ hℓ hℓp n hn
    have hℓdvd : ¬ ℓ ∣ p := fun hd => hℓp ((Nat.prime_dvd_prime_iff_eq hℓ pP).mp hd)
    have hg : heckeGen ⟨ℓ, hℓ⟩ - MvPolynomial.C (1 + (ℓ : ℤ)) ∈ eisensteinIdeal p := by
      refine heckeGen_sub_mem_eigenIdeal _ _ _ ?_
      rw [eisensteinSystem_of_not_dvd (N := p) (ℓ := ⟨ℓ, hℓ⟩) hℓdvd]
      simp only [algebraMap_int_eq, Int.coe_castRingHom, Int.cast_id]
    refine S09RCMain.dvd_of_qCoeff_eq p m χ hχI f hRC2' n hn _ hg _ ?_
    rw [map_sub, heckeProj_heckeGen_of_not_dvd ⟨ℓ, hℓ⟩ hℓdvd, heckeProj_C,
      Subalgebra.coe_sub, LinearMap.sub_apply, CuspForm.heckeAlgebra.coe_T,
      S09RCMain.coe_algebraMap_apply, S09RCMain.qCoeff_sub,
      S09RCMain.qCoeff_heckeTLin_eq hℓ hℓdvd f n, S09RCMain.qCoeff_zsmul]
    split_ifs
    · push_cast
      rw [haf (n * ℓ), haf (n / ℓ), haf n]
    · push_cast
      rw [haf (n * ℓ), haf n]
  ·
    intro n hn
    have hg : heckeGen ⟨p, pP⟩ - MvPolynomial.C 1 ∈ eisensteinIdeal p := by
      refine heckeGen_sub_mem_eigenIdeal _ _ _ ?_
      rw [eisensteinSystem_of_dvd (N := p) (ℓ := ⟨p, pP⟩) (dvd_refl p)]
      exact map_one _
    refine S09RCMain.dvd_of_qCoeff_eq p m χ hχI f hRC2' n hn _ hg _ ?_
    rw [map_sub, heckeProj_heckeGen_of_dvd ⟨p, pP⟩ (dvd_refl p), heckeProj_C,
      Subalgebra.coe_sub, LinearMap.sub_apply, CuspForm.heckeAlgebra.coe_U,
      S09RCMain.coe_algebraMap_apply, S09RCMain.qCoeff_sub,
      S09RCMain.qCoeff_heckeULin_eq pP.ne_zero (dvd_refl p) f n, S09RCMain.qCoeff_zsmul]
    push_cast
    rw [haf (n * p), haf n]
    ring

theorem solution (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (hIB : CuspForm.HasIntegralBasis p)
    (hinj : ∀ c : ℤ, algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅) c ∈
      Ideal.map (heckeProj p) (eisensteinIdeal p) ⊔
        Ideal.span {((m : ℕ) : CuspForm.heckeAlgebra p 2 ∅)} → (m : ℤ) ∣ c) :
    ∃ f ∈ CuspForm.qIntegralSet p, ∃ af : ℕ → ℤ,
      (∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) ∧
      IsCoprime (af 1) (m : ℤ) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ, n ≠ 0 →
        (m : ℤ) ∣ af (n * ℓ) + (if ℓ ∣ n then (ℓ : ℤ) * af (n / ℓ) else 0) - (1 + ℓ) * af n) ∧
      (∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af (n * p) - af n) :=
  CuspForm.exists_qIntegral_eisenstein_eigen_mod_of_injective p m hm hIB hinj

end

end S_CuspForm_exists_qIntegral_eisenstein_eigen_mod_of_injective
end P2MW
export P2MW.S_CuspForm_exists_qIntegral_eisenstein_eigen_mod_of_injective (solution)
