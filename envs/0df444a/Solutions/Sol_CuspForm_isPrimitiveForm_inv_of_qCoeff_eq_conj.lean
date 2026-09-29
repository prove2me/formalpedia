-- Prove2me | solution 1 for CuspForm.isPrimitiveForm_inv_of_qCoeff_eq_conj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/dc547138-8246-5727-8ea0-6dc9a816211f

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_CuspForm_exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_isPrimitiveForm_inv_of_qCoeff_eq_conj

set_option autoImplicit false

open CongruenceSubgroup ModularFormClass UpperHalfPlane Function
open scoped MatrixGroups ComplexConjugate

noncomputable section

namespace ConjPrimitiveForm

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ M).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

theorem periodic (f : CuspForm (Γ₁ℝ M) k) : Periodic (⇑f ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods M)

theorem bdd (f : CuspForm (Γ₁ℝ M) k) : IsBoundedAtImInfty (⇑f) := by
  haveI : Fact (IsCusp OnePoint.infty (Γ₁ℝ M)) :=
    ⟨(Γ₁ℝ M).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods M)⟩
  exact ModularFormClass.bdd_at_infty f

theorem eq_of_qCoeff_eq (f₁ f₂ : CuspForm (Γ₁ℝ M) k) (h : ∀ n : ℕ, qCoeff f₁ n = qCoeff f₂ n) :
    f₁ = f₂ :=
  DFunLike.ext' (UpperHalfPlane.eq_of_forall_qCoeff_eq (periodic f₁) f₁.holo' (bdd f₁)
    (periodic f₂) f₂.holo' (bdd f₂) h)

theorem qCoeff_zero_fun (n : ℕ) : qCoeff (0 : ℍ → ℂ) n = 0 := by
  rw [qCoeff, UpperHalfPlane.qExpansion_zero, map_zero]

theorem eq_zero_of_qCoeff (f : CuspForm (Γ₁ℝ M) k) (h : ∀ n : ℕ, qCoeff f n = 0) : f = 0 :=
  eq_of_qCoeff_eq f 0 (fun n => by rw [h n, CuspForm.coe_zero, qCoeff_zero_fun])

theorem conj_natCast_zpow (p : ℕ) (m : ℤ) : conj ((p : ℂ) ^ m) = (p : ℂ) ^ m := by
  rw [map_zpow₀, Complex.conj_natCast]

theorem conj_intCast (n : ℤ) : conj (n : ℂ) = n := map_intCast _ n

theorem conj_dirichlet [NeZero M] (ε : DirichletCharacter ℂ M) (a : ZMod M) :
    conj (ε a) = ε⁻¹ a := by
  have := MulChar.star_apply' ε a
  rwa [RCLike.star_def] at this

theorem conj_ite (P : Prop) [Decidable P] (a : ℂ) :
    conj (if P then a else 0) = if P then conj a else 0 := by
  split_ifs <;> simp

theorem conj_hecke_rel [NeZero M] (ε : DirichletCharacter ℂ M) (a : ℕ → ℂ) (p : ℕ) (lam : ℂ)
    (h : ∀ n : ℕ, a (p * n) + ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then a (n / p) else 0) = lam * a n) (n : ℕ) :
    conj (a (p * n)) + ε⁻¹ (p : ZMod M) * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then conj (a (n / p)) else 0) = conj lam * conj (a n) := by
  have := congrArg conj (h n)
  rw [map_add, map_mul, map_mul, map_mul, conj_dirichlet, conj_natCast_zpow, conj_ite] at this
  exact this

def conjNeg (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1], by
    rw [Matrix.det_fin_two_of]
    have := Matrix.det_fin_two γ.1
    rw [γ.2] at this
    linear_combination (-1 : ℤ) * this⟩

@[scoped simp] theorem conjNeg_apply_00 (γ : SL(2, ℤ)) : (conjNeg γ) 0 0 = γ 0 0 := rfl
@[scoped simp] theorem conjNeg_apply_01 (γ : SL(2, ℤ)) : (conjNeg γ) 0 1 = -γ 0 1 := rfl
@[scoped simp] theorem conjNeg_apply_10 (γ : SL(2, ℤ)) : (conjNeg γ) 1 0 = -γ 1 0 := rfl
@[scoped simp] theorem conjNeg_apply_11 (γ : SL(2, ℤ)) : (conjNeg γ) 1 1 = γ 1 1 := rfl

theorem conjNeg_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : conjNeg γ ∈ Gamma0 M := by
  rw [Gamma0_mem] at hγ ⊢
  simp [hγ]

def negConj (τ : ℍ) : ℍ := ⟨-conj (τ : ℂ), by simpa using τ.im_pos⟩

@[scoped simp] theorem coe_negConj (τ : ℍ) : ((negConj τ : ℍ) : ℂ) = -conj (τ : ℂ) := rfl

theorem coe_sl_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ • τ : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) /
      (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

theorem coe_conjNeg_smul_negConj (γ : SL(2, ℤ)) (τ : ℍ) :
    ((conjNeg γ • negConj τ : ℍ) : ℂ) = -conj ((γ • τ : ℍ) : ℂ) := by
  rw [coe_sl_smul, coe_sl_smul, map_div₀]
  simp only [conjNeg_apply_00, conjNeg_apply_01, conjNeg_apply_10, conjNeg_apply_11, coe_negConj,
    Int.cast_neg, map_add, map_mul, conj_intCast]
  have e1 : ((γ 0 0 : ℤ) : ℂ) * -conj (τ : ℂ) + -((γ 0 1 : ℤ) : ℂ) =
      -(((γ 0 0 : ℤ) : ℂ) * conj (τ : ℂ) + ((γ 0 1 : ℤ) : ℂ)) := by ring
  have e2 : -((γ 1 0 : ℤ) : ℂ) * -conj (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) =
      ((γ 1 0 : ℤ) : ℂ) * conj (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by ring
  rw [e1, e2, neg_div]

theorem hasNebentypus_inv_of_conj [NeZero M] {ε : DirichletCharacter ℂ M}
    {f f' : CuspForm (Γ₁ℝ M) k} (hf : CuspForm.HasNebentypus ε f)
    (hf' : ∀ τ τ' : ℍ, (τ' : ℂ) = -conj (τ : ℂ) → f' τ = conj (f τ')) :
    CuspForm.HasNebentypus ε⁻¹ f' := by
  intro γ hγ τ
  have h1 : f' (γ • τ) = conj (f (conjNeg γ • negConj τ)) :=
    hf' (γ • τ) (conjNeg γ • negConj τ) (coe_conjNeg_smul_negConj γ τ)
  have h2 := hf (conjNeg γ) (conjNeg_mem_Gamma0 hγ) (negConj τ)
  have h3 : f' τ = conj (f (negConj τ)) := hf' τ (negConj τ) rfl
  rw [h1, h2, map_mul, map_mul, conjNeg_apply_11, conjNeg_apply_10, conj_dirichlet, ← h3,
    map_zpow₀, map_add, map_mul]
  simp only [Int.cast_neg, map_neg, conj_intCast, coe_negConj, Complex.conj_conj,
    neg_mul_neg]

variable [NeZero M]

theorem main (ε : DirichletCharacter ℂ M) (g : CuspForm (Γ₁ℝ M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) (g' : CuspForm (Γ₁ℝ M) k)
    (hg' : ∀ n : ℕ, qCoeff g' n = conj (qCoeff g n)) :
    CuspForm.IsPrimitiveForm ε⁻¹ g' := by

  obtain ⟨g'', hpt, hcoef⟩ := CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj M k g
  have hgg : g' = g'' := eq_of_qCoeff_eq g' g'' (fun n => by rw [hg', hcoef])
  subst hgg
  have heig := hg.isEigenformWith
  refine ⟨⟨?_, ?_, ?_, hasNebentypus_inv_of_conj heig.hasNebentypus hpt⟩, ?_⟩
  · rw [hg', heig.qCoeff_one, map_one]
  · intro p hp hpM n
    have := conj_hecke_rel (k := k) ε (fun n => qCoeff g n) p (qCoeff g p)
      (heig.hecke_of_not_dvd hp hpM) n
    rw [hg', hg', hg', hg']
    exact this
  · intro ℓ hℓ hℓM n
    rw [hg', hg', hg', heig.hecke_of_dvd hℓ hℓM n, map_mul]
  ·
    intro M' hM' hne hocc
    haveI : NeZero M' := ⟨fun h0 => NeZero.ne M (zero_dvd_iff.1 (h0 ▸ hM'))⟩
    obtain ⟨ε', h', hh'0, hh'neb, S, hS⟩ := hocc
    obtain ⟨h'', hpt'', hcoef''⟩ :=
      CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj M' k h'
    apply hg.not_eigenpacketOccursAt hM' hne
    refine ⟨ε'⁻¹, h'', ?_, hasNebentypus_inv_of_conj hh'neb hpt'', S, fun p hp hpS => ⟨?_, ?_⟩⟩
    · intro h0
      apply hh'0
      apply eq_zero_of_qCoeff
      intro n
      have := hcoef'' n
      rw [h0, CuspForm.coe_zero, qCoeff_zero_fun] at this
      have := congrArg conj this
      rwa [map_zero, Complex.conj_conj, eq_comm] at this
    · have h1 : ε' (p : ZMod M') = ε⁻¹ (p : ZMod M) := (hS p hp hpS).1
      show ε'⁻¹ (p : ZMod M') = ε (p : ZMod M)
      rw [MulChar.inv_apply_eq_inv', h1, MulChar.inv_apply_eq_inv', inv_inv]
    · intro n
      have hrel := (hS p hp hpS).2
      have := conj_hecke_rel (k := k) ε' (fun n => qCoeff h' n) p (qCoeff g' p) hrel n
      rw [hcoef'', hcoef'', hcoef'']
      rw [hg', Complex.conj_conj] at this
      exact this

end ConjPrimitiveForm
p2m_reactivate "P2MW.S_CuspForm_isPrimitiveForm_inv_of_qCoeff_eq_conj.ConjPrimitiveForm"

end
p2m_reactivate "P2MW.S_CuspForm_isPrimitiveForm_inv_of_qCoeff_eq_conj.ConjPrimitiveForm"

open scoped MatrixGroups in
theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) (g' : CuspForm (Gamma1 M) k)
    (hg' : ∀ n : ℕ, ModularFormClass.qCoeff g' n = starRingEnd ℂ (ModularFormClass.qCoeff g n)) :
    CuspForm.IsPrimitiveForm ε⁻¹ g' :=
  ConjPrimitiveForm.main ε g hg g' hg'

end S_CuspForm_isPrimitiveForm_inv_of_qCoeff_eq_conj
end P2MW
export P2MW.S_CuspForm_isPrimitiveForm_inv_of_qCoeff_eq_conj (solution)
