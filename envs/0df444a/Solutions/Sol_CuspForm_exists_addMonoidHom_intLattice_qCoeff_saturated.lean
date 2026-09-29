-- Prove2me | solution 1 for CuspForm.exists_addMonoidHom_intLattice_qCoeff_saturated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/71b78294-cf91-5f5d-9519-b29477b819e9

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_QCoeffLinear

import Theorems.Thm_CuspForm_mem_intLattice_iff
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_addMonoidHom_intLattice_qCoeff_saturated

set_option autoImplicit false

open CongruenceSubgroup

theorem solution (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ a : ↥(CuspForm.intLattice N k) →+ (ℕ → ℤ),
      (∀ (f : ↥(CuspForm.intLattice N k)) (n : ℕ),
        ((a f n : ℤ) : ℂ) = ModularFormClass.qCoeff (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) n) ∧
      Function.Injective a ∧
      ∀ (m : ℤ) (f : ↥(CuspForm.intLattice N k)), (∀ n, m ∣ a f n) →
        ∃ g : ↥(CuspForm.intLattice N k), f = m • g := by
  classical

  have hex : ∀ (f : ↥(CuspForm.intLattice N k)) (n : ℕ), ∃ m : ℤ,
      ModularFormClass.qCoeff (f : CuspForm (Gamma0 N) k) n = (m : ℂ) :=
    fun f n => (CuspForm.mem_intLattice_iff (f : CuspForm (Gamma0 N) k)).mp f.2 n
  choose c hc using hex
  have hlin : ∀ (f : CuspForm (Gamma0 N) k) (n : ℕ),
      ModularFormClass.qCoeff f n = CuspForm.qCoeffLinear N k n f := fun _ _ => rfl
  let a : ↥(CuspForm.intLattice N k) →+ (ℕ → ℤ) :=
    { toFun := fun f n => c f n
      map_zero' := by
        funext n
        apply Int.cast_injective (α := ℂ)
        rw [← hc, Pi.zero_apply, Int.cast_zero, Submodule.coe_zero, hlin, map_zero]
      map_add' := fun f g => by
        funext n
        apply Int.cast_injective (α := ℂ)
        rw [← hc, Pi.add_apply, Int.cast_add, ← hc, ← hc, Submodule.coe_add, hlin, hlin, hlin, map_add] }
  have ha : ∀ (f : ↥(CuspForm.intLattice N k)) (n : ℕ),
      ((a f n : ℤ) : ℂ) = ModularFormClass.qCoeff (f : CuspForm (Gamma0 N) k) n := fun f n => (hc f n).symm
  refine ⟨a, ha, ?_, ?_⟩
  · intro f g h
    apply Subtype.ext
    apply ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods_Gamma0 N)
    intro n
    have := congrFun h n
    rw [← ha, ← ha]
    exact congrArg (Int.cast : ℤ → ℂ) this
  · intro m f hm
    by_cases hm0 : m = 0
    · subst hm0
      refine ⟨0, ?_⟩
      rw [zero_smul]
      apply Subtype.ext
      apply ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods_Gamma0 N)
      intro n
      obtain ⟨d, hd⟩ := hm n
      rw [← ha, hd, zero_mul, Int.cast_zero, Submodule.coe_zero, hlin, map_zero]
    · choose d hd using hm

      let g0 : CuspForm (Gamma0 N) k := ((m : ℂ)⁻¹) • (f : CuspForm (Gamma0 N) k)
      have hg0 : ∀ n, ModularFormClass.qCoeff g0 n = ((d n : ℤ) : ℂ) := by
        intro n
        have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
        rw [hlin, map_smul, ← hlin, ← ha, hd, smul_eq_mul, Int.cast_mul]
        field_simp
      have hg0mem : g0 ∈ CuspForm.intLattice N k := (CuspForm.mem_intLattice_iff g0).mpr fun n => ⟨d n, hg0 n⟩
      refine ⟨⟨g0, hg0mem⟩, Subtype.ext ?_⟩
      show (f : CuspForm (Gamma0 N) k) = m • g0
      have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
      rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul, mul_inv_cancel₀ hmC, one_smul]

end S_CuspForm_exists_addMonoidHom_intLattice_qCoeff_saturated
end P2MW
export P2MW.S_CuspForm_exists_addMonoidHom_intLattice_qCoeff_saturated (solution)
