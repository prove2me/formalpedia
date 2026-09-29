-- Prove2me | solution 1 for CuspForm.IsNormalizedEigenform.exists_integralClosure_coe_eq_qCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e90cb273-a861-5c38-80bb-1e523c8470e7

import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_IntegralStructure
import Theorems.Thm_IsIntegral_of_mem_span_of_apply_eq_smul
import Theorems.Thm_exists_integralClosure_coe_eq_of_isIntegral
import Theorems.Thm_CuspForm_intLattice_fg
import Theorems.Thm_CuspForm_mem_intLattice_of_coe_eq_heckeT
import Theorems.Thm_CuspForm_mem_intLattice_of_coe_eq_heckeU
import Theorems.Thm_CuspForm_exists_coe_eq_heckeT
import Theorems.Thm_CuspForm_exists_coe_eq_heckeU
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_coeffHecke
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNormalizedEigenform_exists_integralClosure_coe_eq_qCoeff

noncomputable section

open scoped ModularForm

namespace W3E

variable {N : ℕ}

local notation "S2" N => CuspForm (CongruenceSubgroup.Gamma0 N) 2

theorem hΓ (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)).strictPeriods :=
  CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N

def hk (N p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  if p ∣ N then ModularForm.heckeU 2 p f else ModularForm.heckeT 2 p f

theorem hk_add (N p : ℕ) (f g : UpperHalfPlane → ℂ) : hk N p (f + g) = hk N p f + hk N p g := by
  unfold hk; split_ifs
  · exact ModularForm.heckeU_add 2 p f g
  · exact ModularForm.heckeT_add 2 p f g

theorem hk_smul (N p : ℕ) (c : ℂ) (f : UpperHalfPlane → ℂ) : hk N p (c • f) = c • hk N p f := by
  unfold hk; split_ifs
  · exact ModularForm.heckeU_smul 2 p c f
  · exact ModularForm.heckeT_smul 2 p c f

def ck (N p : ℕ) (a : ℕ → ℂ) : ℕ → ℂ :=
  if p ∣ N then ModularForm.coeffHeckeU p a else ModularForm.coeffHeckeT 2 p a

theorem qCoeff_hk (N : ℕ) {p : ℕ} (hp : p ≠ 0) (g : S2 N) (n : ℕ) :
    ModularFormClass.qCoeff (hk N p ⇑g) n = ck N p (ModularFormClass.qCoeff ⇑g) n := by
  unfold hk ck; split_ifs
  · exact ModularFormClass.qCoeff_heckeU g (hΓ N) hp n
  · exact ModularFormClass.qCoeff_heckeT g (hΓ N) hp n

theorem qCoeff_smul (c : ℂ) (f : S2 N) (n : ℕ) :
    ModularFormClass.qCoeff ⇑(c • f) n = c * ModularFormClass.qCoeff ⇑f n := by
  have han := ModularFormClass.analyticAt_cuspFunction_zero f one_pos (hΓ N)
  unfold ModularFormClass.qCoeff
  rw [CuspForm.IsGLPos.coe_smul, UpperHalfPlane.qExpansion_smul han, map_smul, smul_eq_mul]

theorem qCoeff_zero_one : ModularFormClass.qCoeff ⇑(0 : S2 N) 1 = 0 := by
  have := qCoeff_smul (N := N) 0 0 1
  rwa [zero_smul, zero_mul] at this

variable [NeZero N]

theorem exists_coe_eq_hk (f : S2 N) {p : ℕ} (hp : p.Prime) : ∃ g : S2 N, ⇑g = hk N p ⇑f := by
  unfold hk; split_ifs with h
  · exact CuspForm.exists_coe_eq_heckeU f h
  · exact CuspForm.exists_coe_eq_heckeT f hp h

def opFun (N : ℕ) [NeZero N] (p : ℕ) (f : S2 N) : S2 N :=
  if hp : p.Prime then Classical.choose (exists_coe_eq_hk f hp) else 0

theorem coe_opFun {p : ℕ} (hp : p.Prime) (f : S2 N) : ⇑(opFun N p f) = hk N p ⇑f := by
  unfold opFun; rw [dif_pos hp]; exact Classical.choose_spec (exists_coe_eq_hk f hp)

theorem opFun_of_not_prime {p : ℕ} (hp : ¬ p.Prime) (f : S2 N) : opFun N p f = 0 := by
  unfold opFun; rw [dif_neg hp]

def op (N : ℕ) [NeZero N] (p : ℕ) : Module.End ℂ (S2 N) where
  toFun := opFun N p
  map_add' f g := by
    by_cases hp : p.Prime
    · exact DFunLike.ext' (by
        rw [CuspForm.coe_add, coe_opFun hp, coe_opFun hp, coe_opFun hp, CuspForm.coe_add, hk_add])
    · simp [opFun_of_not_prime hp]
  map_smul' c f := by
    by_cases hp : p.Prime
    · exact DFunLike.ext' (by
        rw [RingHom.id_apply, CuspForm.IsGLPos.coe_smul, coe_opFun hp, coe_opFun hp,
          CuspForm.IsGLPos.coe_smul, hk_smul])
    · simp [opFun_of_not_prime hp]

theorem op_apply (p : ℕ) (f : S2 N) : op N p f = opFun N p f := rfl

theorem qCoeff_op {p : ℕ} (hp : p.Prime) (f : S2 N) (n : ℕ) :
    ModularFormClass.qCoeff ⇑(op N p f) n = ck N p (ModularFormClass.qCoeff ⇑f) n := by
  rw [op_apply, coe_opFun hp, qCoeff_hk N hp.ne_zero]

theorem op_mem_intLattice {p : ℕ} (hp : p.Prime) (x : S2 N) (hx : x ∈ CuspForm.intLattice N 2) :
    op N p x ∈ CuspForm.intLattice N 2 := by
  have hcoe : ⇑(op N p x) = hk N p ⇑x := by rw [op_apply, coe_opFun hp]
  unfold hk at hcoe
  split_ifs at hcoe with h
  · exact CuspForm.mem_intLattice_of_coe_eq_heckeU hp.ne_zero hcoe hx
  · exact CuspForm.mem_intLattice_of_coe_eq_heckeT (by norm_num) hp.ne_zero hcoe hx

theorem op_apply_eq_smul {f : S2 N} (hf : f.IsNormalizedEigenform) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    op N ℓ f = ModularFormClass.qCoeff ⇑f ℓ • f := by
  obtain ⟨-, heig⟩ := (CuspForm.isNormalizedEigenform_iff_coeffHecke f).mp hf
  obtain ⟨hT, hU⟩ := heig ℓ hℓ
  apply ModularFormClass.eq_of_forall_qCoeff_eq (hΓ N)
  intro n
  rw [qCoeff_op hℓ, qCoeff_smul]
  unfold ck; split_ifs with h
  · exact hU h n
  · exact hT h n

theorem exists_integralClosure_coe_eq_qCoeff (hN : CuspForm.HasIntegralStructure N 2) {f : S2 N}
    (hf : f.IsNormalizedEigenform) (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ := by
  apply exists_integralClosure_coe_eq_of_isIntegral
  have hv : f ∈ Submodule.span ℂ ((CuspForm.intLattice N 2 : Submodule ℤ (S2 N)) : Set (S2 N)) := by
    unfold CuspForm.HasIntegralStructure at hN
    rw [hN]; exact Submodule.mem_top
  have hv0 : f ≠ 0 := by
    rintro rfl
    have h1 := hf.qCoeff_one
    rw [qCoeff_zero_one] at h1
    exact zero_ne_one h1
  exact IsIntegral.of_mem_span_of_apply_eq_smul (CuspForm.intLattice N 2) (CuspForm.intLattice_fg N 2)
    (op N ℓ) (fun x hx => op_mem_intLattice hℓ x hx) hv hv0 (op_apply_eq_smul hf hℓ)

end W3E

end

theorem solution {N : ℕ} [NeZero N] (hN : CuspForm.HasIntegralStructure N 2)
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform) (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ :=
  W3E.exists_integralClosure_coe_eq_qCoeff hN hf ℓ hℓ

end S_CuspForm_IsNormalizedEigenform_exists_integralClosure_coe_eq_qCoeff
end P2MW
export P2MW.S_CuspForm_IsNormalizedEigenform_exists_integralClosure_coe_eq_qCoeff (solution)
