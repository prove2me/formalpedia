-- Prove2me | solution 1 for CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c4375f46-16d9-5e6d-ae6d-6927da22c70d

import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Theorems.Thm_CuspForm_heckeTLin_apply_eq_smul_iff
import Theorems.Thm_CuspForm_heckeULin_apply_eq_smul_iff
import Theorems.Thm_ModularForm_eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero
import Theorems.Thm_CuspForm_qCoeff_zero
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Theorems.Thm_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed
import Theorems.Thm_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra
import Theorems.Thm_CuspForm_HasIntegralStructure_exists_ne_zero_forall_apply_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_HasIntegralStructure_exists_isNormalizedEigenform_qCoeff_eq

noncomputable section

open ModularForm ModularFormClass

namespace FrobChareqC2

variable {N : ℕ} {k : ℤ}

theorem hΓ (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)).strictPeriods :=
  CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N

theorem qCoeff_zero' (n : ℕ) : qCoeff ⇑(0 : CuspForm (CongruenceSubgroup.Gamma0 N) k) n = 0 := by
  simp only [qCoeff, CuspForm.coe_zero]
  rw [UpperHalfPlane.qExpansion_zero, map_zero]

theorem qCoeff_smul (c : ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    qCoeff ⇑(c • f) n = c * qCoeff ⇑f n := by
  have h1 : ⇑(c • f) = c • ⇑f := by ext z; simp
  simp only [qCoeff, h1]
  rw [ModularForm.qExpansion_smul one_pos (hΓ N) c f]
  simp

end FrobChareqC2

p2m_open "P2MW.S_CuspForm_HasIntegralStructure_exists_isNormalizedEigenform_qCoeff_eq.FrobChareqC2 CuspForm ModularForm.CuspForm"

namespace FrobChareqC2

theorem qCoeff_heckeTLin_one {N : ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (c : ℂ)
    (h : CuspForm.heckeTLin 2 hℓ hℓN f = c • f) : qCoeff ⇑f ℓ = c * qCoeff ⇑f 1 := by
  have := ((CuspForm.heckeTLin_apply_eq_smul_iff 2 hℓ hℓN f c).mp h) 1
  have h1 : ¬ ℓ ∣ 1 := fun hd => hℓ.one_lt.ne' (Nat.dvd_one.mp hd)
  rw [coeffHeckeT_apply, one_mul, if_neg h1, add_zero] at this
  exact this

theorem qCoeff_heckeULin_one {N : ℕ} [NeZero N] {q : ℕ} (hqN : q ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (c : ℂ)
    (h : CuspForm.heckeULin 2 hqN f = c • f) : qCoeff ⇑f q = c * qCoeff ⇑f 1 := by
  have := ((CuspForm.heckeULin_apply_eq_smul_iff 2 hqN f c).mp h) 1
  rw [coeffHeckeU_apply, one_mul] at this
  exact this

theorem C2_7a {N : ℕ} [NeZero N] (hN : HasIntegralStructure N 2) (χ : heckeAlgebra N 2 ∅ →+* ℂ) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
        ModularFormClass.qCoeff f ℓ = χ (heckeAlgebra.T hℓ hℓN (Set.notMem_empty ℓ))) ∧
      ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N),
        ModularFormClass.qCoeff f q = χ (heckeAlgebra.U hq hqN (Set.notMem_empty q)) := by
  obtain ⟨g, hg0, hg⟩ := CuspForm.HasIntegralStructure.exists_ne_zero_forall_apply_eq_smul hN one_le_two χ

  classical
  let c : ℕ → ℂ := fun p => if hp : p.Prime then
    (if hpN : p ∣ N then χ (heckeAlgebra.U hp hpN (Set.notMem_empty p))
      else χ (heckeAlgebra.T hp hpN (Set.notMem_empty p))) else 0
  have hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), CuspForm.heckeTLin 2 hℓ hℓN g = c ℓ • g := by
    intro ℓ hℓ hℓN
    have := hg (heckeAlgebra.T hℓ hℓN (Set.notMem_empty ℓ))
    rw [heckeAlgebra.coe_T] at this
    rw [this]; simp only [c, dif_pos hℓ, dif_neg hℓN]
  have hU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N), CuspForm.heckeULin 2 hqN g = c q • g := by
    intro q hq hqN
    have := hg (heckeAlgebra.U hq hqN (Set.notMem_empty q))
    rw [heckeAlgebra.coe_U] at this
    rw [this]; simp only [c, dif_pos hq, dif_pos hqN]

  set a₁ := qCoeff ⇑g 1 with ha₁
  have ha₁0 : a₁ ≠ 0 := by
    intro h0
    apply hg0
    have hcoefT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n, coeffHeckeT 2 p (qCoeff ⇑g) n = c p * qCoeff ⇑g n :=
      fun p hp hpN => (CuspForm.heckeTLin_apply_eq_smul_iff 2 hp hpN g (c p)).mp (hT p hp hpN)
    have hcoefU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n, coeffHeckeU p (qCoeff ⇑g) n = c p * qCoeff ⇑g n :=
      fun p hp hpN => (CuspForm.heckeULin_apply_eq_smul_iff 2 hpN g (c p)).mp (hU p hp hpN)
    have hzero : ∀ n, n ≠ 0 → qCoeff ⇑g n = 0 :=
      ModularForm.eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero 2 N (qCoeff ⇑g) c hcoefT hcoefU h0
    refine ModularFormClass.eq_of_forall_qCoeff_eq (hΓ N) fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [CuspForm.qCoeff_zero, CuspForm.qCoeff_zero]
    · rw [hzero n hn.ne']
      exact (qCoeff_zero' (N := N) (k := 2) n).symm

  refine ⟨a₁⁻¹ • g, ?_, ?_, ?_⟩
  · rw [CuspForm.isNormalizedEigenform_iff_heckeTLin]
    refine ⟨by rw [qCoeff_smul, ← ha₁, inv_mul_cancel₀ ha₁0], fun p hp => ⟨fun hpN => ?_, fun hpN => ?_⟩⟩
    · rw [map_smul, hT p hp hpN, smul_comm, qCoeff_smul, qCoeff_heckeTLin_one hp hpN g (c p) (hT p hp hpN),
        ← ha₁, mul_comm a₁⁻¹, mul_assoc, mul_inv_cancel₀ ha₁0, mul_one]
    · rw [map_smul, hU p hp hpN, smul_comm, qCoeff_smul, qCoeff_heckeULin_one hpN g (c p) (hU p hp hpN),
        ← ha₁, mul_comm a₁⁻¹, mul_assoc, mul_inv_cancel₀ ha₁0, mul_one]
  · intro ℓ hℓ hℓN
    rw [qCoeff_smul, qCoeff_heckeTLin_one hℓ hℓN g (c ℓ) (hT ℓ hℓ hℓN), ← ha₁, mul_comm a₁⁻¹, mul_assoc,
      mul_inv_cancel₀ ha₁0, mul_one]
    simp only [c, dif_pos hℓ, dif_neg hℓN]
  · intro q hq hqN
    rw [qCoeff_smul, qCoeff_heckeULin_one hqN g (c q) (hU q hq hqN), ← ha₁, mul_comm a₁⁻¹, mul_assoc,
      mul_inv_cancel₀ ha₁0, mul_one]
    simp only [c, dif_pos hq, dif_pos hqN]

end FrobChareqC2

theorem solution {N : ℕ} [NeZero N] (hN : CuspForm.HasIntegralStructure N 2) {S : Set ℕ} (χ : CuspForm.heckeAlgebra N 2 S →+* ℂ) : ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform ∧ (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), ModularFormClass.qCoeff f ℓ = χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) ∧ ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S), ModularFormClass.qCoeff f q = χ (CuspForm.heckeAlgebra.U hq hqN hqS) := by
  haveI : Module.Finite ℤ (heckeAlgebra N 2 ∅) := CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra hN one_le_two ∅
  let ι : heckeAlgebra N 2 S →ₐ[ℤ] heckeAlgebra N 2 ∅ :=
    Subalgebra.inclusion (heckeAlgebra_mono (Set.empty_subset S))
  letI : Algebra (heckeAlgebra N 2 S) (heckeAlgebra N 2 ∅) := ι.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (heckeAlgebra N 2 S) (heckeAlgebra N 2 ∅) :=
    ⟨fun x => by
      have h := (Algebra.IsIntegral.isIntegral (R := ℤ) x).map_of_comp_eq
        (algebraMap ℤ (heckeAlgebra N 2 S)) (RingHom.id (heckeAlgebra N 2 ∅)) (RingHom.ext_int _ _)
      rwa [RingHom.id_apply] at h⟩
  have hker : RingHom.ker (algebraMap (heckeAlgebra N 2 S) (heckeAlgebra N 2 ∅)) ≤ RingHom.ker χ := by
    have hinj : Function.Injective ι := Subalgebra.inclusion_injective _
    have : RingHom.ker (algebraMap (heckeAlgebra N 2 S) (heckeAlgebra N 2 ∅)) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).mp hinj
    rw [this]
    exact bot_le
  obtain ⟨ψ, hψ⟩ := RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed χ hker
  have hψι : ∀ t : heckeAlgebra N 2 S, ψ (ι t) = χ t := fun t => by
    rw [← hψ]
    rfl
  obtain ⟨f, hf, hfT, hfU⟩ := C2_7a hN ψ
  refine ⟨f, hf, fun ℓ hℓ hℓN hℓS => ?_, fun q hq hqN hqS => ?_⟩
  · rw [hfT ℓ hℓ hℓN, ← hψι]
    rfl
  · rw [hfU q hq hqN, ← hψι]
    rfl

end

end S_CuspForm_HasIntegralStructure_exists_isNormalizedEigenform_qCoeff_eq
end P2MW
export P2MW.S_CuspForm_HasIntegralStructure_exists_isNormalizedEigenform_qCoeff_eq (solution)
