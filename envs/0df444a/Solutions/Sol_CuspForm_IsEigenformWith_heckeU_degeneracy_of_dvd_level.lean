-- Prove2me | solution 1 for CuspForm.IsEigenformWith.heckeU_degeneracy_of_dvd_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d1d0f23b-09c5-5fe9-b409-cef6034c9cdd

import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_UpperHalfPlane_qCoeff_heckeU
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import Theorems.Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_ModularForm_mdifferentiable_heckeU
import Theorems.Thm_ModularForm_isBoundedAtImInfty_heckeU
import Theorems.Thm_ModularForm_periodic_heckeU_comp_ofComplex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level

set_option autoImplicit false

noncomputable section

namespace CuspForm
p2m_export "CuspForm" "sub_apply add_apply IsEigenformWith"
namespace M4cStrings
p2m_open "CuspForm"

open Complex Function Filter
p2m_open "UpperHalfPlane~I"
open scoped Real MatrixGroups ModularForm Manifold Topology
open ModularForm ModularFormClass

private theorem qCoeff_const_smul {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty f) (c : ℂ) (n : ℕ) : qCoeff (c • f) n = c * qCoeff f n := by
  simp only [qCoeff]
  rw [UpperHalfPlane.qExpansion_smul (analyticAt_cuspFunction_zero one_pos hper hhol hbdd)]
  simp

private theorem qCoeff_add {f g : ℍ → ℂ} (hfper : Periodic (f ∘ ofComplex) 1) (hfhol : MDiff f)
    (hfbdd : IsBoundedAtImInfty f) (hgper : Periodic (g ∘ ofComplex) 1) (hghol : MDiff g)
    (hgbdd : IsBoundedAtImInfty g) (n : ℕ) : qCoeff (f + g) n = qCoeff f n + qCoeff g n := by
  simp only [qCoeff]
  rw [UpperHalfPlane.qExpansion_add (analyticAt_cuspFunction_zero one_pos hfper hfhol hfbdd)
    (analyticAt_cuspFunction_zero one_pos hgper hghol hgbdd)]
  simp

private theorem qCoeff_sub {f g : ℍ → ℂ} (hfper : Periodic (f ∘ ofComplex) 1) (hfhol : MDiff f)
    (hfbdd : IsBoundedAtImInfty f) (hgper : Periodic (g ∘ ofComplex) 1) (hghol : MDiff g)
    (hgbdd : IsBoundedAtImInfty g) (n : ℕ) : qCoeff (f - g) n = qCoeff f n - qCoeff g n := by
  simp only [qCoeff]
  rw [UpperHalfPlane.qExpansion_sub (analyticAt_cuspFunction_zero one_pos hfper hfhol hfbdd)
    (analyticAt_cuspFunction_zero one_pos hgper hghol hgbdd)]
  simp

private theorem periodic_const_smul {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (c : ℂ) :
    Periodic ((c • f) ∘ ofComplex) 1 := fun z ↦ by
  simpa using congrArg (c * ·) (hper z)

private theorem periodic_add {f g : ℍ → ℂ} (hf : Periodic (f ∘ ofComplex) 1) (hg : Periodic (g ∘ ofComplex) 1) :
    Periodic ((f + g) ∘ ofComplex) 1 := fun z ↦ by
  have h1 := hf z
  have h2 := hg z
  simp only [comp_apply, Pi.add_apply] at h1 h2 ⊢
  rw [h1, h2]

private theorem periodic_sub {f g : ℍ → ℂ} (hf : Periodic (f ∘ ofComplex) 1) (hg : Periodic (g ∘ ofComplex) 1) :
    Periodic ((f - g) ∘ ofComplex) 1 := fun z ↦ by
  have h1 := hf z
  have h2 := hg z
  simp only [comp_apply, Pi.sub_apply] at h1 h2 ⊢
  rw [h1, h2]

private theorem reg_gamma1 {N : ℕ} {k : ℤ} (h : CuspForm (CongruenceSubgroup.Gamma1 N) k) :
    Periodic (⇑h ∘ ofComplex) 1 ∧ MDiff (⇑h : ℍ → ℂ) ∧ IsBoundedAtImInfty (⇑h : ℍ → ℂ) := by
  have hΓ : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]
    exact AddSubgroup.mem_zmultiples 1
  refine ⟨SlashInvariantFormClass.periodic_comp_ofComplex h hΓ, ModularFormClass.holo h, ?_⟩
  haveI : Fact (IsCusp OnePoint.infty (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  exact ModularFormClass.bdd_at_infty h

private theorem main
    (M : ℕ) [NeZero M] (k : ℤ) {L : ℕ} [NeZero L] (hLM : L ∣ M)
    {εL : DirichletCharacter ℂ L} {g : CuspForm (CongruenceSubgroup.Gamma1 L) k}
    (hg : CuspForm.IsEigenformWith εL g)
    (G : ℕ → CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hG : ∀ d : ℕ, d ∣ M / L → ∀ τ : UpperHalfPlane, G d τ = g (ModularForm.heckeDiagMatrix d • τ))
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) {d : ℕ} (hd : d ∣ M / L) :
    (q ∣ d → ModularForm.heckeU k q ⇑(G d) = ⇑(G (d / q))) ∧
    (¬ q ∣ d → q ∣ L → ModularForm.heckeU k q ⇑(G d) = ModularFormClass.qCoeff g q • ⇑(G d)) ∧
    (¬ q ∣ d → ¬ q ∣ L →
      ModularForm.heckeU k q ⇑(G d) =
        ModularFormClass.qCoeff g q • ⇑(G d) -
          (εL (q : ZMod L) * (q : ℂ) ^ (k - 1)) • ⇑(G (d * q))) := by
  classical
  have hq0 : q ≠ 0 := hq.ne_zero
  obtain ⟨e, he⟩ := hLM
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hMLe : M / L = e := by rw [he, Nat.mul_div_cancel_left _ hL0]
  have he0 : e ≠ 0 := by rintro rfl; exact NeZero.ne M (by rw [he, mul_zero])
  have hd0 : d ≠ 0 := fun h0 => he0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hMLe ▸ hd))

  obtain ⟨gper, ghol, gbdd⟩ := reg_gamma1 g
  have hb : ∀ {d' : ℕ}, d' ∣ M / L → d' ≠ 0 → ∀ m : ℕ,
      qCoeff (⇑(G d')) m = if d' ∣ m then qCoeff (⇑g) (m / d') else 0 := by
    intro d' hd' hd'0 m
    rw [show (⇑(G d') : ℍ → ℂ) = fun τ => g (ModularForm.heckeDiagMatrix d' • τ) from funext (hG d' hd')]
    exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul gper ghol gbdd hd'0 m
  obtain ⟨hper, hhol, hbdd⟩ := reg_gamma1 (G d)
  have hUper := ModularForm.periodic_heckeU_comp_ofComplex hper k q
  have hUhol := ModularForm.mdifferentiable_heckeU hhol k q
  have hUbdd := ModularForm.isBoundedAtImInfty_heckeU hbdd k q
  have hqU : ∀ m : ℕ, qCoeff (ModularForm.heckeU k q ⇑(G d)) m = qCoeff ⇑(G d) (m * q) := fun m => by
    rw [UpperHalfPlane.qCoeff_heckeU hper hhol hbdd k hq0 m, ModularForm.coeffHeckeU_apply]
  refine ⟨fun hqd => ?_, fun hqd hqL => ?_, fun hqd hqL => ?_⟩
  ·
    obtain ⟨d', rfl⟩ := hqd
    have hd'0 : d' ≠ 0 := fun h => hd0 (by rw [h, mul_zero])
    have hdq : q * d' / q = d' := Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hq0)
    have hd' : d' ∣ M / L := (Dvd.intro_left q rfl).trans hd
    obtain ⟨h'per, h'hol, h'bdd⟩ := reg_gamma1 (G (q * d' / q))
    refine UpperHalfPlane.eq_of_forall_qCoeff_eq hUper hUhol hUbdd h'per h'hol h'bdd fun m => ?_
    rw [hqU m, hb hd hd0, hdq, hb hd' hd'0]
    by_cases hdm : d' ∣ m
    · obtain ⟨m', rfl⟩ := hdm
      rw [if_pos ⟨m', by ring⟩, if_pos ⟨m', rfl⟩, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd'0),
        show d' * m' * q / (q * d') = m' from by
          rw [show d' * m' * q = (q * d') * m' from by ring, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]]
    · rw [if_neg hdm, if_neg (fun h => hdm ?_)]

      obtain ⟨t, ht⟩ := h
      refine ⟨t, Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hq0) ?_⟩
      calc m * q = q * d' * t := ht
        _ = d' * t * q := by ring
  ·
    have hcop : Nat.Coprime q d := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqd
    refine UpperHalfPlane.eq_of_forall_qCoeff_eq hUper hUhol hUbdd (periodic_const_smul hper _)
      (hhol.const_smul _) (hbdd.const_smul_left _) fun m => ?_
    rw [hqU m, qCoeff_const_smul hper hhol hbdd, hb hd hd0, hb hd hd0]
    by_cases hdm : d ∣ m
    · obtain ⟨m', rfl⟩ := hdm
      rw [if_pos ⟨m' * q, by ring⟩, if_pos ⟨m', rfl⟩, mul_assoc,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0),
        mul_comm m' q]
      exact hg.hecke_of_dvd hq hqL m'
    · rw [if_neg (fun h => hdm ((Nat.Coprime.dvd_mul_right hcop.symm).mp h)), if_neg hdm, mul_zero]
  ·
    have hcop : Nat.Coprime q d := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqd
    have hqe : q ∣ e := by
      have : q ∣ L * e := he ▸ hqM
      exact ((Nat.Prime.dvd_mul hq).mp this).resolve_left hqL
    have hdq : d * q ∣ M / L := by
      rw [hMLe] at hd ⊢
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop.symm hd hqe
    have hdq0 : d * q ≠ 0 := mul_ne_zero hd0 hq0
    obtain ⟨h'per, h'hol, h'bdd⟩ := reg_gamma1 (G (d * q))
    set c : ℂ := εL (q : ZMod L) * (q : ℂ) ^ (k - 1) with hc
    refine UpperHalfPlane.eq_of_forall_qCoeff_eq hUper hUhol hUbdd
      (periodic_sub (periodic_const_smul hper _) (periodic_const_smul h'per _))
      ((hhol.const_smul _).sub (h'hol.const_smul _))
      ((hbdd.const_smul_left _).sub (h'bdd.const_smul_left _)) fun m => ?_
    rw [hqU m, qCoeff_sub (periodic_const_smul hper _) (hhol.const_smul _) (hbdd.const_smul_left _)
        (periodic_const_smul h'per _) (h'hol.const_smul _) (h'bdd.const_smul_left _),
      qCoeff_const_smul hper hhol hbdd, qCoeff_const_smul h'per h'hol h'bdd, hb hd hd0, hb hd hd0, hb hdq hdq0]
    by_cases hdm : d ∣ m
    · obtain ⟨m', rfl⟩ := hdm
      have key := hg.hecke_of_not_dvd hq hqL m'
      rw [if_pos ⟨m' * q, by ring⟩, if_pos ⟨m', rfl⟩, mul_assoc,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0),
        mul_comm m' q]
      by_cases hqm' : q ∣ m'
      · rw [if_pos (mul_dvd_mul_left d hqm'),
          show d * m' / (d * q) = m' / q from Nat.mul_div_mul_left _ _ (Nat.pos_of_ne_zero hd0)]
        rw [if_pos hqm'] at key
        rw [← key, hc]
        ring
      · rw [if_neg (fun h => hqm' ?_)]
        · rw [if_neg hqm'] at key
          rw [← key]
          ring
        · exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hd0)).mp h
    · rw [if_neg (fun h => hdm ((Nat.Coprime.dvd_mul_right hcop.symm).mp h)), if_neg hdm,
        if_neg (fun h => hdm ((dvd_mul_right d q).trans h))]
      ring

end CuspForm.M4cStrings

end

open scoped MatrixGroups ModularForm in

theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) {L : ℕ} [NeZero L] (hLM : L ∣ M)
    {εL : DirichletCharacter ℂ L} {g : CuspForm (CongruenceSubgroup.Gamma1 L) k}
    (hg : CuspForm.IsEigenformWith εL g)
    (G : ℕ → CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hG : ∀ d : ℕ, d ∣ M / L → ∀ τ : UpperHalfPlane, G d τ = g (ModularForm.heckeDiagMatrix d • τ))
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) {d : ℕ} (hd : d ∣ M / L) :
    (q ∣ d → ModularForm.heckeU k q ⇑(G d) = ⇑(G (d / q))) ∧
    (¬ q ∣ d → q ∣ L → ModularForm.heckeU k q ⇑(G d) = ModularFormClass.qCoeff g q • ⇑(G d)) ∧
    (¬ q ∣ d → ¬ q ∣ L →
      ModularForm.heckeU k q ⇑(G d) =
        ModularFormClass.qCoeff g q • ⇑(G d) -
          (εL (q : ZMod L) * (q : ℂ) ^ (k - 1)) • ⇑(G (d * q))) :=
  CuspForm.M4cStrings.main M k hLM hg G hG hq hqM hd

end S_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level
end P2MW
export P2MW.S_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level (solution)
