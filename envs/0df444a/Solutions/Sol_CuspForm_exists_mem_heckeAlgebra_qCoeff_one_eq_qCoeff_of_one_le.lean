-- Prove2me | solution 1 for CuspForm.exists_mem_heckeAlgebra_qCoeff_one_eq_qCoeff_of_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/7239ae94-290b-5b9a-aa37-123b36d8c2db

import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_mem_heckeAlgebra_qCoeff_one_eq_qCoeff_of_one_le

set_option autoImplicit false

namespace QExtrInt

open Module CongruenceSubgroup ModularFormClass UpperHalfPlane

private theorem one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma0 N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
      Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples _

variable {N' : ℕ} {k : ℤ}

private theorem qCoeff_add (f g : CuspForm (Gamma0 N') k) (n : ℕ) :
    qCoeff (⇑(f + g)) n = qCoeff (⇑f) n + qCoeff (⇑g) n := by
  have hf := ModularFormClass.analyticAt_cuspFunction_zero f one_pos
    (one_mem_strictPeriods_Gamma0 N')
  have hg := ModularFormClass.analyticAt_cuspFunction_zero g one_pos
    (one_mem_strictPeriods_Gamma0 N')
  simp only [qCoeff, CuspForm.coe_add, qExpansion_add hf hg, map_add]

private theorem qCoeff_smul (c : ℂ) (f : CuspForm (Gamma0 N') k) (n : ℕ) :
    qCoeff (⇑(c • f)) n = c * qCoeff (⇑f) n := by
  have hf := ModularFormClass.analyticAt_cuspFunction_zero f one_pos
    (one_mem_strictPeriods_Gamma0 N')
  simp only [qCoeff, CuspForm.IsGLPos.coe_smul, qExpansion_smul hf c, PowerSeries.coeff_smul,
    smul_eq_mul]

private noncomputable def qCoeffL (N' : ℕ) (k : ℤ) (n : ℕ) : CuspForm (Gamma0 N') k →ₗ[ℂ] ℂ where
  toFun f := qCoeff (⇑f) n
  map_add' f g := qCoeff_add f g n
  map_smul' c f := by simpa using qCoeff_smul c f n

@[scoped simp] private theorem qCoeffL_apply (n : ℕ) (f : CuspForm (Gamma0 N') k) :
    qCoeffL N' k n f = qCoeff (⇑f) n := rfl

private theorem qCoeff_sub (f g : CuspForm (Gamma0 N') k) (n : ℕ) :
    qCoeff (⇑(f - g)) n = qCoeff (⇑f) n - qCoeff (⇑g) n := by
  rw [← qCoeffL_apply n, ← qCoeffL_apply n f, ← qCoeffL_apply n g, map_sub]

private theorem qCoeff_heckeTLin {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N')
    (f : CuspForm (Gamma0 N') k) (m : ℕ) :
    qCoeff (⇑(CuspForm.heckeTLin k hℓ hℓN f)) m =
      qCoeff (⇑f) (m * ℓ) + if ℓ ∣ m then (ℓ : ℂ) ^ (k - 1) * qCoeff (⇑f) (m / ℓ) else 0 := by
  rw [CuspForm.coe_heckeTLin_apply, ModularFormClass.qCoeff_heckeT f
    (one_mem_strictPeriods_Gamma0 N') hℓ.ne_zero m, ModularForm.coeffHeckeT_apply]

private theorem qCoeff_heckeULin [NeZero N'] {q : ℕ} (hq : q.Prime) (hqN : q ∣ N')
    (f : CuspForm (Gamma0 N') k) (m : ℕ) :
    qCoeff (⇑(CuspForm.heckeULin k hqN f)) m = qCoeff (⇑f) (m * q) := by
  rw [CuspForm.coe_heckeULin_apply, ModularFormClass.qCoeff_heckeU f
    (one_mem_strictPeriods_Gamma0 N') hq.ne_zero m, ModularForm.coeffHeckeU_apply]

private theorem exists_heckeOp (N' : ℕ) [NeZero N'] (k : ℤ) (hk : 1 ≤ k) (n : ℕ) (hn : 0 < n) :
    ∃ t ∈ CuspForm.heckeAlgebra N' k (∅ : Set ℕ),
      ∀ f : CuspForm (Gamma0 N') k, qCoeff (⇑(t f)) 1 = qCoeff (⇑f) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases eq_or_ne n 1 with rfl | hn1
  · exact ⟨1, Subalgebra.one_mem _, fun f => rfl⟩
  obtain ⟨ℓ, hℓ, m, rfl⟩ := Nat.exists_prime_and_dvd hn1
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hmn : m < ℓ * m := lt_mul_left hm hℓ.one_lt
  obtain ⟨tm, htm, htm'⟩ := ih m hmn hm
  by_cases hℓN : ℓ ∣ N'
  · refine ⟨tm * CuspForm.heckeULin k hℓN,
      mul_mem htm (CuspForm.heckeULin_mem_heckeAlgebra hℓ hℓN (by simp)), fun f => ?_⟩
    rw [Module.End.mul_apply, htm', qCoeff_heckeULin hℓ hℓN, mul_comm]
  · by_cases hℓm : ℓ ∣ m
    · obtain ⟨r, hr⟩ := hℓm
      have hr0 : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; simp [hr] at hm)
      have hrm : r ≤ m := by rw [hr]; exact Nat.le_mul_of_pos_left r hℓ.pos
      obtain ⟨tr, htr, htr'⟩ := ih r (lt_of_le_of_lt hrm hmn) hr0
      have hcast : (((ℓ ^ (k - 1).toNat : ℕ) : ℤ) : ℂ) = (ℓ : ℂ) ^ (k - 1) := by
        push_cast
        rw [← zpow_natCast, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ k - 1)]
      refine ⟨tm * CuspForm.heckeTLin k hℓ hℓN - ((ℓ ^ (k - 1).toNat : ℕ) : ℤ) • tr,
        sub_mem (mul_mem htm (CuspForm.heckeTLin_mem_heckeAlgebra hℓ hℓN (by simp)))
          (Subalgebra.smul_mem _ htr _), fun f => ?_⟩
      have hdiv : m / ℓ = r := by rw [hr, Nat.mul_div_cancel_left r hℓ.pos]
      have hsmul : qCoeff (⇑(((((ℓ ^ (k - 1).toNat : ℕ) : ℤ) • tr) f))) 1 =
          (ℓ : ℂ) ^ (k - 1) * qCoeff (⇑f) r := by
        rw [LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul ℂ, qCoeff_smul, htr', hcast]
      rw [LinearMap.sub_apply, qCoeff_sub, Module.End.mul_apply, htm',
        qCoeff_heckeTLin hℓ hℓN, if_pos ⟨r, hr⟩, hdiv, hsmul, mul_comm m ℓ]
      ring
    · refine ⟨tm * CuspForm.heckeTLin k hℓ hℓN,
        mul_mem htm (CuspForm.heckeTLin_mem_heckeAlgebra hℓ hℓN (by simp)), fun f => ?_⟩
      rw [Module.End.mul_apply, htm', qCoeff_heckeTLin hℓ hℓN, if_neg hℓm, add_zero, mul_comm]

end QExtrInt
p2m_reactivate "P2MW.S_CuspForm_exists_mem_heckeAlgebra_qCoeff_one_eq_qCoeff_of_one_le.QExtrInt"

theorem solution (N : ℕ) [NeZero N] (k : ℤ) (hk : 1 ≤ k)
    (n : ℕ) (hn : 0 < n) :
    ∃ t ∈ CuspForm.heckeAlgebra N k (∅ : Set ℕ),
      ∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) k,
        ModularFormClass.qCoeff (t f) 1 = ModularFormClass.qCoeff f n :=
  QExtrInt.exists_heckeOp N k hk n hn

end S_CuspForm_exists_mem_heckeAlgebra_qCoeff_one_eq_qCoeff_of_one_le
end P2MW
export P2MW.S_CuspForm_exists_mem_heckeAlgebra_qCoeff_one_eq_qCoeff_of_one_le (solution)
