-- Prove2me | solution 1 for CuspForm.exists_mem_heckeAlgebra_qCoeff_apply_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e879a2a0-191c-5249-9bd6-a6ccc0c13f3f

import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_HeckeAlgebra
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_mem_heckeAlgebra_qCoeff_apply_one_eq
set_option autoImplicit false
noncomputable section
open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

namespace S09RC

private theorem one_mem_strictPeriods (p : ℕ) :
    (1 : ℝ) ∈ ((Gamma0 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine Subgroup.mem_map.mpr ⟨ModularGroup.T, ?_, ?_⟩
  · rw [Gamma0_mem]
    simp [ModularGroup.T]
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom,
        Matrix.SpecialLinearGroup.mapGL]

variable {p : ℕ}

private theorem qCoeff_zero (j : ℕ) :
    ModularFormClass.qCoeff (0 : CuspForm (Gamma0 p) 2) j = 0 := by
  simp only [ModularFormClass.qCoeff, CuspForm.coe_zero, qExpansion_zero, map_zero]

private theorem qCoeff_add (g h : CuspForm (Gamma0 p) 2) (j : ℕ) :
    ModularFormClass.qCoeff (⇑(g + h)) j =
      ModularFormClass.qCoeff g j + ModularFormClass.qCoeff h j := by
  simp only [ModularFormClass.qCoeff, CuspForm.coe_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods p) g h, map_add]

private theorem qCoeff_sub (g h : CuspForm (Gamma0 p) 2) (j : ℕ) :
    ModularFormClass.qCoeff (⇑(g - h)) j =
      ModularFormClass.qCoeff g j - ModularFormClass.qCoeff h j := by
  simp only [ModularFormClass.qCoeff, CuspForm.coe_sub,
    ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods p) g h, map_sub]

private theorem qCoeff_natCast_mul_apply (m : ℕ)
    (u : Module.End ℂ (CuspForm (Gamma0 p) 2)) (g : CuspForm (Gamma0 p) 2) (j : ℕ) :
    ModularFormClass.qCoeff (((m : Module.End ℂ (CuspForm (Gamma0 p) 2)) * u) g) j =
      (m : ℂ) * ModularFormClass.qCoeff (u g) j := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, zero_mul, LinearMap.zero_apply, qCoeff_zero, Nat.cast_zero, zero_mul]
  | succ m ih =>
    rw [Nat.cast_add_one, add_mul, one_mul, LinearMap.add_apply, qCoeff_add, ih,
      Nat.cast_add_one, add_mul, one_mul]

end S09RC

namespace CuspForm p2m_export "CuspForm" "sub_apply coe_zero zero_apply coe_sub ext add_apply coe_add heckeTLin heckeULin coe_heckeTLin_apply coe_heckeULin_apply heckeAlgebra heckeTLin_mem_heckeAlgebra heckeULin_mem_heckeAlgebra" end CuspForm
p2m_open_scoped "CuspForm" in
private theorem CuspForm.exists_mem_heckeAlgebra_qCoeff_apply_one_eq (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : n ≠ 0) : ∃ t ∈ CuspForm.heckeAlgebra p 2 ∅, ∀ f : CuspForm (CongruenceSubgroup.Gamma0 p) 2, ModularFormClass.qCoeff (t f) 1 = ModularFormClass.qCoeff f n := by
  have hp : p.Prime := Fact.out
  revert hn
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn
    rcases eq_or_ne n 1 with rfl | hn1
    · exact ⟨1, one_mem _, fun f => by rw [Module.End.one_apply]⟩
    · obtain ⟨ℓ, hℓeq⟩ : ∃ l : ℕ, l = n.minFac := ⟨_, rfl⟩
      have hℓ : ℓ.Prime := by rw [hℓeq]; exact Nat.minFac_prime hn1
      have hdvd : ℓ ∣ n := by rw [hℓeq]; exact Nat.minFac_dvd n
      have hn' : n = n / ℓ * ℓ := (Nat.div_mul_cancel hdvd).symm
      have hn'0 : n / ℓ ≠ 0 :=
        Nat.div_ne_zero_iff.mpr ⟨hℓ.pos.ne', Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd⟩
      have hn'lt : n / ℓ < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hℓ.one_lt
      obtain ⟨t', ht'mem, ht'⟩ := IH (n / ℓ) hn'lt hn'0
      rcases eq_or_ne ℓ p with hcase | hℓp
      ·
        have hidx : n / ℓ * p = n := by rw [← hcase]; exact hn'.symm
        refine ⟨t' * CuspForm.heckeULin 2 dvd_rfl,
          mul_mem ht'mem
            (CuspForm.heckeULin_mem_heckeAlgebra hp dvd_rfl (Set.notMem_empty p)),
          fun f => ?_⟩
        rw [Module.End.mul_apply, ht' (CuspForm.heckeULin 2 dvd_rfl f),
          CuspForm.coe_heckeULin_apply,
          ModularFormClass.qCoeff_heckeU f (S09RC.one_mem_strictPeriods p) hp.pos.ne' (n / ℓ),
          ModularForm.coeffHeckeU_apply, hidx]
      ·
        have hℓN : ¬ ℓ ∣ p := fun hd => hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp hd)
        by_cases hc : ℓ ∣ n / ℓ
        ·
          have hn''0 : n / ℓ / ℓ ≠ 0 :=
            Nat.div_ne_zero_iff.mpr ⟨hℓ.pos.ne', Nat.le_of_dvd (Nat.pos_of_ne_zero hn'0) hc⟩
          have hn''lt : n / ℓ / ℓ < n := lt_of_le_of_lt (Nat.div_le_self _ _) hn'lt
          obtain ⟨t'', ht''mem, ht''⟩ := IH (n / ℓ / ℓ) hn''lt hn''0
          refine ⟨t' * CuspForm.heckeTLin 2 hℓ hℓN -
              (ℓ : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2)) * t'',
            sub_mem
              (mul_mem ht'mem
                (CuspForm.heckeTLin_mem_heckeAlgebra hℓ hℓN (Set.notMem_empty ℓ)))
              (mul_mem (Subalgebra.natCast_mem _ ℓ) ht''mem),
            fun f => ?_⟩
          rw [LinearMap.sub_apply, S09RC.qCoeff_sub, Module.End.mul_apply,
            ht' (CuspForm.heckeTLin 2 hℓ hℓN f), CuspForm.coe_heckeTLin_apply,
            ModularFormClass.qCoeff_heckeT f (S09RC.one_mem_strictPeriods p) hℓ.pos.ne' (n / ℓ),
            ModularForm.coeffHeckeT_of_dvd 2 hc, S09RC.qCoeff_natCast_mul_apply, ht'' f, ← hn']
          have hexp : ((2 : ℤ) - 1) = 1 := by norm_num
          rw [hexp, zpow_one, add_sub_cancel_right]
        · refine ⟨t' * CuspForm.heckeTLin 2 hℓ hℓN,
            mul_mem ht'mem
              (CuspForm.heckeTLin_mem_heckeAlgebra hℓ hℓN (Set.notMem_empty ℓ)),
            fun f => ?_⟩
          rw [Module.End.mul_apply, ht' (CuspForm.heckeTLin 2 hℓ hℓN f),
            CuspForm.coe_heckeTLin_apply,
            ModularFormClass.qCoeff_heckeT f (S09RC.one_mem_strictPeriods p) hℓ.pos.ne' (n / ℓ),
            ModularForm.coeffHeckeT_of_not_dvd 2 hc, ← hn']

theorem solution : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : n ≠ 0), ∃ t ∈ CuspForm.heckeAlgebra p 2 ∅, ∀ f : CuspForm (CongruenceSubgroup.Gamma0 p) 2, ModularFormClass.qCoeff (t f) 1 = ModularFormClass.qCoeff f n :=
  @CuspForm.exists_mem_heckeAlgebra_qCoeff_apply_one_eq

end
end S_CuspForm_exists_mem_heckeAlgebra_qCoeff_apply_one_eq
end P2MW
export P2MW.S_CuspForm_exists_mem_heckeAlgebra_qCoeff_apply_one_eq (solution)
