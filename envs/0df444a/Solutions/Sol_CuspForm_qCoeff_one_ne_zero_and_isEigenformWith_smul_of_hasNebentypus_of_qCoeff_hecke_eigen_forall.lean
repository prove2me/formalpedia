-- Prove2me | solution 1 for CuspForm.qCoeff_one_ne_zero_and_isEigenformWith_smul_of_hasNebentypus_of_qCoeff_hecke_eigen_forall
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/850a90c7-7f20-5b5d-bf5f-4a66203cb952

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_qCoeff_zero_eq_zero_gamma1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_qCoeff_one_ne_zero_and_isEigenformWith_smul_of_hasNebentypus_of_qCoeff_hecke_eigen_forall

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularForm UpperHalfPlane Filter Function
open scoped ModularForm UpperHalfPlane MatrixGroups

namespace NormaliseEigenformG3b

variable {N : ℕ}

section Toolkit

variable [NeZero N] {k : ℤ}

private theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  simp [Gamma1_mem, ModularGroup.T]

@[local simp] private theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

private theorem periodic_of_slash_T {F : ℍ → ℂ}
    (h : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) = F) :
    Periodic (F ∘ ofComplex) 1 := by
  have hT : ∀ τ : ℍ, F ((1 : ℝ) +ᵥ τ) = F τ := by
    intro τ
    have := congrFun h τ
    change (F ∣[k] ModularGroup.T) τ = F τ at this
    rw [SL_slash_apply] at this
    rw [← modular_T_smul]
    rw [← this]
    simp [denom, ModularGroup.T]
  intro w
  by_cases hw : 0 < w.im
  · have : 0 < (w + 1).im := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    convert hT ⟨w, hw⟩ using 2
    ext
    simp [add_comm]
  · have hw : w.im ≤ 0 := le_of_not_gt hw
    have : (w + 1).im ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

private theorem sl_slash (f : ℍ → ℂ) (γ : SL(2, ℤ)) :
    f ∣[k] γ = f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) := rfl

omit [NeZero N] in
private theorem slash_mem (g : CuspForm (Gamma1 N) k) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) :
    (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑g :=
  SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ)

private structure Reg (F : ℍ → ℂ) : Prop where
  per : Periodic (F ∘ ofComplex) 1
  hol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F
  bdd : IsBoundedAtImInfty F

private theorem reg_coe (g : CuspForm (Gamma1 N) k) : Reg (⇑g : ℍ → ℂ) :=
  ⟨periodic_of_slash_T (slash_mem g (T_mem_Gamma1 N)), CuspFormClass.holo g,
    ModularFormClass.bdd_at_infty g⟩

private theorem Reg.smul {F : ℍ → ℂ} (h : Reg F) (c : ℂ) : Reg (c • F) := by
  refine ⟨?_, h.hol.const_smul c, h.bdd.smul c⟩
  intro w
  have := h.per w
  simp only [comp_apply, Pi.smul_apply] at this ⊢
  rw [this]

private theorem Reg.analyticAt {F : ℍ → ℂ} (h : Reg F) : AnalyticAt ℂ (cuspFunction 1 F) 0 :=
  analyticAt_cuspFunction_zero one_pos h.per h.hol h.bdd

end Toolkit

section Main

variable [NeZero N] {k : ℤ}

private theorem qCoeff_smul_coe (c : ℂ) (g : CuspForm (Gamma1 N) k) (n : ℕ) :
    ModularFormClass.qCoeff (c • (⇑g : ℍ → ℂ)) n = c * ModularFormClass.qCoeff (⇑g) n := by
  rw [ModularFormClass.qCoeff, ModularFormClass.qCoeff, qExpansion_smul (reg_coe g).analyticAt,
    map_smul, smul_eq_mul]

private theorem qCoeff_smul (c : ℂ) (g : CuspForm (Gamma1 N) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(c • g)) n = c * ModularFormClass.qCoeff (⇑g) n := by
  rw [CuspForm.IsGLPos.coe_smul]
  exact qCoeff_smul_coe c g n

private theorem eq_zero_of_forall_qCoeff_eq_zero (g : CuspForm (Gamma1 N) k)
    (h : ∀ n : ℕ, ModularFormClass.qCoeff (⇑g) n = 0) : g = 0 := by
  have r₁ := reg_coe g
  have r₂ : Reg ((0 : ℂ) • (⇑g : ℍ → ℂ)) := r₁.smul 0
  have key := UpperHalfPlane.eq_of_forall_qCoeff_eq r₁.per r₁.hol r₁.bdd r₂.per r₂.hol r₂.bdd
    (fun n => by rw [qCoeff_smul_coe, zero_mul]; exact h n)
  apply DFunLike.coe_injective
  change (⇑g : ℍ → ℂ) = ⇑(0 : CuspForm (Gamma1 N) k)
  rw [CuspForm.coe_zero, key, zero_smul]

omit [NeZero N] in

private theorem qCoeff_eq_zero_of_qCoeff_one_eq_zero (ε : DirichletCharacter ℂ N)
    (g : CuspForm (Gamma1 N) k) (b : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
      ModularFormClass.qCoeff g (p * n) +
          ε (p : ZMod N) * (p : ℂ) ^ (k - 1) *
            (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
        b p * ModularFormClass.qCoeff g n)
    (hU : ∀ q : ℕ, q.Prime → q ∣ N → ∀ n : ℕ,
      ModularFormClass.qCoeff g (q * n) = b q * ModularFormClass.qCoeff g n)
    (h1 : ModularFormClass.qCoeff g 1 = 0) : ∀ n : ℕ, ModularFormClass.qCoeff g n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · exact CuspForm.qCoeff_zero_eq_zero_gamma1 g
    · exact h1
  · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    obtain ⟨m, rfl⟩ := hpn
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hmlt : m < p * m := lt_mul_of_one_lt_left hm0 hp.one_lt
    have ham : ModularFormClass.qCoeff g m = 0 := ih m hmlt
    by_cases hpN : p ∣ N
    · rw [hU p hp hpN m, ham, mul_zero]
    · have h := hT p hp hpN m
      have hdiv : (if p ∣ m then ModularFormClass.qCoeff g (m / p) else 0) = 0 := by
        split_ifs with hpm
        · exact ih _ (lt_of_le_of_lt (Nat.div_le_self m p) hmlt)
        · rfl
      rw [hdiv, ham, mul_zero, mul_zero, add_zero] at h
      exact h

private theorem main (ε : DirichletCharacter ℂ N)
    (g : CuspForm (Gamma1 N) k) (hg0 : g ≠ 0) (hε : CuspForm.HasNebentypus ε g)
    (b : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
      ModularFormClass.qCoeff g (p * n) +
          ε (p : ZMod N) * (p : ℂ) ^ (k - 1) *
            (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
        b p * ModularFormClass.qCoeff g n)
    (hU : ∀ q : ℕ, q.Prime → q ∣ N → ∀ n : ℕ,
      ModularFormClass.qCoeff g (q * n) = b q * ModularFormClass.qCoeff g n) :
    ModularFormClass.qCoeff g 1 ≠ 0 ∧
      CuspForm.IsEigenformWith ε ((ModularFormClass.qCoeff g 1)⁻¹ • g) ∧
      ∀ p : ℕ, p.Prime →
        ModularFormClass.qCoeff ((ModularFormClass.qCoeff g 1)⁻¹ • g) p = b p := by
  set a₁ : ℂ := ModularFormClass.qCoeff g 1 with ha₁
  have ha1 : a₁ ≠ 0 := fun h0 =>
    hg0 (eq_zero_of_forall_qCoeff_eq_zero g (qCoeff_eq_zero_of_qCoeff_one_eq_zero ε g b hT hU h0))

  have hap : ∀ p : ℕ, p.Prime → ModularFormClass.qCoeff g p = b p * a₁ := by
    intro p hp
    by_cases hpN : p ∣ N
    · have := hU p hp hpN 1
      rwa [mul_one] at this
    · have := hT p hp hpN 1
      rwa [mul_one, if_neg (fun h => hp.ne_one (Nat.dvd_one.mp h)), mul_zero, add_zero] at this
  have hh : ∀ n : ℕ, ModularFormClass.qCoeff (⇑(a₁⁻¹ • g)) n = a₁⁻¹ * ModularFormClass.qCoeff (⇑g) n :=
    qCoeff_smul a₁⁻¹ g

  have hhp : ∀ p : ℕ, p.Prime → ModularFormClass.qCoeff (⇑(a₁⁻¹ • g)) p = b p := by
    intro p hp
    rw [hh, hap p hp, mul_comm (b p) a₁, ← mul_assoc, inv_mul_cancel₀ ha1, one_mul]
  refine ⟨ha1, ?_, hhp⟩
  unfold CuspForm.IsEigenformWith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hh, inv_mul_cancel₀ ha1]
  · intro p hp hpN n
    rw [hhp p hp, hh, hh, hh]
    have h := hT p hp hpN n
    by_cases hpn : p ∣ n
    · rw [if_pos hpn] at h ⊢
      linear_combination a₁⁻¹ * h
    · rw [if_neg hpn] at h ⊢
      linear_combination a₁⁻¹ * h
  · intro q hq hqN n
    rw [hhp q hq, hh, hh]
    linear_combination a₁⁻¹ * hU q hq hqN n
  · intro γ hγ τ
    have h := hε γ hγ τ
    rw [CuspForm.IsGLPos.coe_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, h]
    ring

end Main

end NormaliseEigenformG3b

end

open scoped MatrixGroups ModularForm in

theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M)
    (g : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hg0 : g ≠ 0) (hε : CuspForm.HasNebentypus ε g)
    (b : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
      ModularFormClass.qCoeff g (p * n) +
          ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
            (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
        b p * ModularFormClass.qCoeff g n)
    (hU : ∀ q : ℕ, q.Prime → q ∣ M → ∀ n : ℕ,
      ModularFormClass.qCoeff g (q * n) = b q * ModularFormClass.qCoeff g n) :
    ModularFormClass.qCoeff g 1 ≠ 0 ∧
      CuspForm.IsEigenformWith ε ((ModularFormClass.qCoeff g 1)⁻¹ • g) ∧
      ∀ p : ℕ, p.Prime →
        ModularFormClass.qCoeff ((ModularFormClass.qCoeff g 1)⁻¹ • g) p = b p :=
  NormaliseEigenformG3b.main ε g hg0 hε b hT hU

end S_CuspForm_qCoeff_one_ne_zero_and_isEigenformWith_smul_of_hasNebentypus_of_qCoeff_hecke_eigen_forall
end P2MW
export P2MW.S_CuspForm_qCoeff_one_ne_zero_and_isEigenformWith_smul_of_hasNebentypus_of_qCoeff_hecke_eigen_forall (solution)
