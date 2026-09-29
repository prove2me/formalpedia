-- Prove2me | solution 1 for CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/539c2598-28bc-5421-a0d0-9d90199365e4

import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_Module_End_exists_forall_apply_eq_smul_of_pairwise_commute
import Theorems.Thm_ModularForm_eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero
import Theorems.Thm_ModularForm_coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_coeffHecke
import Theorems.Thm_CuspForm_heckeTLin_comm
import Theorems.Thm_CuspForm_heckeTLin_heckeULin_comm
import Theorems.Thm_CuspForm_heckeULin_comm
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_qCoeff_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul

theorem solution {N : ℕ} [NeZero N]
    {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg : g ≠ 0) (a : ℕ → ℂ) (S : Set ℕ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S →
      CuspForm.heckeTLin 2 hℓ hℓN g = a ℓ • g) :
    ∃ h : CuspForm (CongruenceSubgroup.Gamma0 N) 2, h.IsNormalizedEigenform ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → ModularFormClass.qCoeff h ℓ = a ℓ := by
  classical

  have hΓ := CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N
  haveI : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
    CuspForm.finiteDimensional_Gamma0 N 2

  have qCoeff_smul : ∀ (c : ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (n : ℕ),
      ModularFormClass.qCoeff ⇑(c • f) n = c * ModularFormClass.qCoeff ⇑f n := by
    intro c f n
    have han := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
    unfold ModularFormClass.qCoeff
    rw [CuspForm.IsGLPos.coe_smul, UpperHalfPlane.qExpansion_smul han, map_smul, smul_eq_mul]
  have qCoeff_zero' : ∀ n : ℕ,
      ModularFormClass.qCoeff ⇑(0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2) n = 0 := by
    intro n
    have := qCoeff_smul 0 g n
    rwa [zero_smul, zero_mul] at this

  let T : Nat.Primes → Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) := fun p =>
    if hpN : (p : ℕ) ∣ N then CuspForm.heckeULin 2 hpN else CuspForm.heckeTLin 2 p.2 hpN
  have hT_of_not_dvd : ∀ (p : Nat.Primes) (hpN : ¬ (p : ℕ) ∣ N),
      T p = CuspForm.heckeTLin 2 p.2 hpN := fun p hpN => by
    simp only [T, dif_neg hpN]
  have hT_of_dvd : ∀ (p : Nat.Primes) (hpN : (p : ℕ) ∣ N),
      T p = CuspForm.heckeULin 2 hpN := fun p hpN => by
    simp only [T, dif_pos hpN]
  have hcomm : ∀ p q : Nat.Primes, Commute (T p) (T q) := by
    intro p q
    by_cases hp : (p : ℕ) ∣ N <;> by_cases hq : (q : ℕ) ∣ N
    · rw [hT_of_dvd p hp, hT_of_dvd q hq]; exact CuspForm.heckeULin_comm 2 hp hq
    · rw [hT_of_dvd p hp, hT_of_not_dvd q hq]
      exact (CuspForm.heckeTLin_heckeULin_comm 2 q.2 hq hp).symm
    · rw [hT_of_not_dvd p hp, hT_of_dvd q hq]
      exact CuspForm.heckeTLin_heckeULin_comm 2 p.2 hp hq
    · rw [hT_of_not_dvd p hp, hT_of_not_dvd q hq]; exact CuspForm.heckeTLin_comm 2 p.2 hp q.2 hq

  let W : Submodule ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
    ⨅ (ℓ : Nat.Primes) (hℓN : ¬ (ℓ : ℕ) ∣ N) (_ : (ℓ : ℕ) ∉ S),
      Module.End.eigenspace (CuspForm.heckeTLin 2 ℓ.2 hℓN) (a ℓ)
  have mem_W : ∀ x, x ∈ W ↔ ∀ (ℓ : Nat.Primes) (hℓN : ¬ (ℓ : ℕ) ∣ N), (ℓ : ℕ) ∉ S →
      CuspForm.heckeTLin 2 ℓ.2 hℓN x = a ℓ • x := by
    intro x
    simp only [W, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hgW : g ∈ W := (mem_W g).2 fun ℓ hℓN hℓS => hT ℓ ℓ.2 hℓN hℓS

  have hWT : ∀ (p : Nat.Primes), ∀ x ∈ W, T p x ∈ W := by
    intro p x hx
    rw [mem_W] at hx ⊢
    intro ℓ hℓN hℓS
    have hc := hcomm ℓ p
    rw [hT_of_not_dvd ℓ hℓN] at hc
    have := LinearMap.congr_fun hc.eq x
    simp only [Module.End.mul_apply] at this
    rw [this, hx ℓ hℓN hℓS, map_smul]
  let T' : Nat.Primes → Module.End ℂ W := fun p => (T p).restrict (hWT p)
  have hcomm' : Pairwise fun p q => Commute (T' p) (T' q) := by
    intro p q _
    refine LinearMap.ext fun x => Subtype.ext ?_
    have := LinearMap.congr_fun (hcomm p q).eq (x : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    simpa only [Module.End.mul_apply, T', LinearMap.restrict_coe_apply] using this
  haveI : Nontrivial W := ⟨⟨⟨g, hgW⟩, 0, fun h => hg (congrArg Subtype.val h)⟩⟩

  obtain ⟨v, hv0, hv⟩ := Module.End.exists_forall_apply_eq_smul_of_pairwise_commute T' hcomm'
  set h₀ : CuspForm (CongruenceSubgroup.Gamma0 N) 2 := (v : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    with hh₀
  have hh₀0 : h₀ ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hh₀W : h₀ ∈ W := v.2
  choose c hc using hv
  have hc' : ∀ p : Nat.Primes, T p h₀ = c p • h₀ := fun p => by
    have := congrArg Subtype.val (hc p)
    simpa only [T', LinearMap.restrict_coe_apply, Submodule.coe_smul] using this

  let cc : ℕ → ℂ := fun p => if hp : p.Prime then c ⟨p, hp⟩ else 0
  have hcc : ∀ (p : ℕ) (hp : p.Prime), cc p = c ⟨p, hp⟩ := fun p hp => by simp only [cc, dif_pos hp]

  have hcoeffT : ∀ (d : ℂ) (p : ℕ), p.Prime → ¬ p ∣ N → ∀ n : ℕ,
      ModularForm.coeffHeckeT 2 p (ModularFormClass.qCoeff ⇑(d • h₀)) n
        = cc p * ModularFormClass.qCoeff ⇑(d • h₀) n := by
    intro d p hp hpN n
    have e := hc' ⟨p, hp⟩
    rw [hT_of_not_dvd ⟨p, hp⟩ hpN] at e
    have e2 : CuspForm.heckeTLin 2 hp hpN (d • h₀) = c ⟨p, hp⟩ • (d • h₀) := by
      rw [map_smul, e, smul_comm]
    have e3 := congrArg (fun F : CuspForm (CongruenceSubgroup.Gamma0 N) 2 =>
      ModularFormClass.qCoeff ⇑F n) e2
    simp only [CuspForm.coe_heckeTLin_apply] at e3
    rw [ModularFormClass.qCoeff_heckeT (d • h₀) hΓ hp.ne_zero n, qCoeff_smul] at e3
    rw [hcc p hp]
    exact e3
  have hcoeffU : ∀ (d : ℂ) (p : ℕ), p.Prime → p ∣ N → ∀ n : ℕ,
      ModularForm.coeffHeckeU p (ModularFormClass.qCoeff ⇑(d • h₀)) n
        = cc p * ModularFormClass.qCoeff ⇑(d • h₀) n := by
    intro d p hp hpN n
    have e := hc' ⟨p, hp⟩
    rw [hT_of_dvd ⟨p, hp⟩ hpN] at e
    have e2 : CuspForm.heckeULin 2 hpN (d • h₀) = c ⟨p, hp⟩ • (d • h₀) := by
      rw [map_smul, e, smul_comm]
    have e3 := congrArg (fun F : CuspForm (CongruenceSubgroup.Gamma0 N) 2 =>
      ModularFormClass.qCoeff ⇑F n) e2
    simp only [CuspForm.coe_heckeULin_apply] at e3
    rw [ModularFormClass.qCoeff_heckeU (d • h₀) hΓ hp.ne_zero n, qCoeff_smul] at e3
    rw [hcc p hp]
    exact e3

  have h1 : ModularFormClass.qCoeff ⇑h₀ 1 ≠ 0 := by
    intro h10
    apply hh₀0
    have hall := ModularForm.eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero 2 N
      (ModularFormClass.qCoeff ⇑((1 : ℂ) • h₀)) cc
      (fun p hp hpN n => hcoeffT 1 p hp hpN n) (fun p hp hpN n => hcoeffU 1 p hp hpN n)
      (by rw [one_smul]; exact h10)
    rw [one_smul] at hall
    refine ModularFormClass.eq_of_forall_qCoeff_eq hΓ fun n => ?_
    rw [qCoeff_zero']
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact CuspForm.qCoeff_zero h₀
    · exact hall n hn.ne'

  set d : ℂ := (ModularFormClass.qCoeff ⇑h₀ 1)⁻¹ with hd
  set h : CuspForm (CongruenceSubgroup.Gamma0 N) 2 := d • h₀ with hhd
  have hb1 : ModularFormClass.qCoeff ⇑h 1 = 1 := by
    rw [hhd, qCoeff_smul, hd, inv_mul_cancel₀ h1]
  have hev := ModularForm.coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one 2 N
    (ModularFormClass.qCoeff ⇑h) cc (fun p hp hpN n => hcoeffT d p hp hpN n)
    (fun p hp hpN n => hcoeffU d p hp hpN n) hb1
  refine ⟨h, ?_, ?_⟩
  · rw [CuspForm.isNormalizedEigenform_iff_coeffHecke]
    refine ⟨hb1, fun p hp => ⟨fun hpN n => ?_, fun hpN n => ?_⟩⟩
    · rw [hcoeffT d p hp hpN n, hev p hp]
    · rw [hcoeffU d p hp hpN n, hev p hp]
  · intro ℓ hℓ hℓN hℓS

    have e1 : CuspForm.heckeTLin 2 hℓ hℓN h₀ = a ℓ • h₀ := (mem_W h₀).1 hh₀W ⟨ℓ, hℓ⟩ hℓN hℓS
    have e2 := hc' ⟨ℓ, hℓ⟩
    rw [hT_of_not_dvd ⟨ℓ, hℓ⟩ hℓN] at e2
    have e3 : (a ℓ - c ⟨ℓ, hℓ⟩) • h₀ = 0 := by rw [sub_smul, ← e1, ← e2, sub_self]
    have hac : a ℓ = c ⟨ℓ, hℓ⟩ := by
      rcases smul_eq_zero.mp e3 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hh₀0
    rw [← hev ℓ hℓ, hcc ℓ hℓ, hac]

end S_CuspForm_exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul
end P2MW
export P2MW.S_CuspForm_exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul (solution)
