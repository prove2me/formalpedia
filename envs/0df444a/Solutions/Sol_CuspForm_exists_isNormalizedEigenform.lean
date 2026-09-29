-- Prove2me | solution 1 for CuspForm.exists_isNormalizedEigenform
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c5b5ffaf-0a1f-5452-876c-822d6597f3d8

import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Theorems.Thm_CuspForm_exists_coe_eq_heckeT
import Theorems.Thm_CuspForm_exists_coe_eq_heckeU
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_ModularForm_coeffHeckeT_comm
import Theorems.Thm_ModularForm_coeffHeckeT_coeffHeckeU_comm
import Theorems.Thm_ModularForm_coeffHeckeU_comm
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Theorems.Thm_CuspForm_qCoeff_zero
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_coeffHecke
import Theorems.Thm_Module_End_exists_forall_apply_eq_smul_of_pairwise_commute
import Theorems.Thm_ModularForm_eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero
import Theorems.Thm_ModularForm_coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_isNormalizedEigenform

noncomputable section

open scoped ModularForm

namespace W27

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

theorem ck_comm (N : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (a : ℕ → ℂ) :
    ck N p (ck N q a) = ck N q (ck N p a) := by
  have hco : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  unfold ck; split_ifs with h1 h2
  · exact ModularForm.coeffHeckeU_comm p q a
  · exact (ModularForm.coeffHeckeT_coeffHeckeU_comm 2 hco.symm a).symm
  · exact ModularForm.coeffHeckeT_coeffHeckeU_comm 2 hco a
  · exact ModularForm.coeffHeckeT_comm 2 hco a

theorem ck_smul (N p : ℕ) (c : ℂ) (a : ℕ → ℂ) : ck N p (c • a) = c • ck N p a := by
  unfold ck; split_ifs
  · exact ModularForm.coeffHeckeU_smul p c a
  · exact ModularForm.coeffHeckeT_smul 2 p c a

theorem qCoeff_smul (c : ℂ) (f : S2 N) (n : ℕ) :
    ModularFormClass.qCoeff ⇑(c • f) n = c * ModularFormClass.qCoeff ⇑f n := by
  have han := ModularFormClass.analyticAt_cuspFunction_zero f one_pos (hΓ N)
  unfold ModularFormClass.qCoeff
  rw [CuspForm.IsGLPos.coe_smul, UpperHalfPlane.qExpansion_smul han, map_smul, smul_eq_mul]

theorem qCoeff_zero' (n : ℕ) : ModularFormClass.qCoeff ⇑(0 : S2 N) n = 0 := by
  have := qCoeff_smul (N := N) 0 0 n
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

theorem qCoeff_op {p : ℕ} (hp : p.Prime) (f : S2 N) :
    ModularFormClass.qCoeff ⇑(op N p f) = ck N p (ModularFormClass.qCoeff ⇑f) := by
  funext n
  rw [op_apply, coe_opFun hp, qCoeff_hk N hp.ne_zero]

theorem op_commute (p q : ℕ) : Commute (op N p) (op N q) := by
  by_cases hp : p.Prime
  swap
  · have : op N p = 0 := LinearMap.ext fun f => by rw [op_apply, opFun_of_not_prime hp]; rfl
    rw [this]; exact Commute.zero_left _
  by_cases hq : q.Prime
  swap
  · have : op N q = 0 := LinearMap.ext fun f => by rw [op_apply, opFun_of_not_prime hq]; rfl
    rw [this]; exact Commute.zero_right _
  rcases eq_or_ne p q with rfl | hpq
  · exact Commute.refl _
  refine LinearMap.ext fun f => ?_
  show op N p (op N q f) = op N q (op N p f)
  apply ModularFormClass.eq_of_forall_qCoeff_eq (hΓ N)
  intro n
  have h1 := congrFun (qCoeff_op hp (op N q f)) n
  have h2 := congrFun (qCoeff_op hq (op N p f)) n
  rw [h1, h2, qCoeff_op hq f, qCoeff_op hp f, ck_comm N hp hq hpq]

theorem exists_isNormalizedEigenform (h : ∃ g : S2 N, g ≠ 0) : ∃ f : S2 N, f.IsNormalizedEigenform := by
  classical
  haveI : FiniteDimensional ℂ (S2 N) := CuspForm.finiteDimensional_Gamma0 N 2
  obtain ⟨g, hg⟩ := h
  haveI : Nontrivial (S2 N) := nontrivial_of_ne g 0 hg

  obtain ⟨f₀, hf₀, heig⟩ := Module.End.exists_forall_apply_eq_smul_of_pairwise_commute (op N)
    (fun p q _ => op_commute p q)
  choose c hc using heig
  set a : ℕ → ℂ := ModularFormClass.qCoeff ⇑f₀ with ha

  have hck : ∀ p : ℕ, p.Prime → ∀ n, ck N p a n = c p * a n := by
    intro p hp n
    have := congrFun (qCoeff_op hp f₀) n
    rw [hc p] at this
    rw [← this, qCoeff_smul]
  have hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT 2 p a n = c p * a n := by
    intro p hp hpN n; have := hck p hp n; unfold ck at this; rwa [if_neg hpN] at this
  have hU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p a n = c p * a n := by
    intro p hp hpN n; have := hck p hp n; unfold ck at this; rwa [if_pos hpN] at this

  have ha1 : a 1 ≠ 0 := by
    intro h1
    apply hf₀
    apply ModularFormClass.eq_of_forall_qCoeff_eq (hΓ N)
    intro n
    rw [qCoeff_zero']
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact CuspForm.qCoeff_zero f₀
    · exact ModularForm.eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero 2 N a c hT hU h1 n hn.ne'

  set f : S2 N := (a 1)⁻¹ • f₀ with hf
  have hqf : ∀ n, ModularFormClass.qCoeff ⇑f n = (a 1)⁻¹ * a n := fun n => qCoeff_smul _ _ n
  have hqf' : ModularFormClass.qCoeff ⇑f = (a 1)⁻¹ • a := funext fun n => by rw [hqf n]; rfl
  have hf1 : ModularFormClass.qCoeff ⇑f 1 = 1 := by rw [hqf 1, inv_mul_cancel₀ ha1]
  have hT' : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
      ModularForm.coeffHeckeT 2 p (ModularFormClass.qCoeff ⇑f) n = c p * ModularFormClass.qCoeff ⇑f n := by
    intro p hp hpN n
    rw [hqf', ModularForm.coeffHeckeT_smul, Pi.smul_apply, hT p hp hpN n, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul]
    ring
  have hU' : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ,
      ModularForm.coeffHeckeU p (ModularFormClass.qCoeff ⇑f) n = c p * ModularFormClass.qCoeff ⇑f n := by
    intro p hp hpN n
    rw [hqf', ModularForm.coeffHeckeU_smul, Pi.smul_apply, hU p hp hpN n, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul]
    ring
  have hcp : ∀ p : ℕ, p.Prime → c p = ModularFormClass.qCoeff ⇑f p :=
    ModularForm.coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one 2 N _ c hT' hU' hf1
  refine ⟨f, (CuspForm.isNormalizedEigenform_iff_coeffHecke f).mpr ⟨hf1, fun p hp => ⟨?_, ?_⟩⟩⟩
  · intro hpN n; rw [hT' p hp hpN n, hcp p hp]
  · intro hpN n; rw [hU' p hp hpN n, hcp p hp]

end W27

end

theorem solution {N : ℕ} [NeZero N]
    (h : ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2, g ≠ 0) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform :=
  W27.exists_isNormalizedEigenform h

end S_CuspForm_exists_isNormalizedEigenform
end P2MW
export P2MW.S_CuspForm_exists_isNormalizedEigenform (solution)
