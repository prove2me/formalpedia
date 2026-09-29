-- Prove2me | solution 1 for CuspForm.IsEigenformWith.heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c073341a-16d2-5441-8864-4916c28e050b

import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_UpperHalfPlane_qCoeff_heckeU
import Theorems.Thm_UpperHalfPlane_qCoeff_heckeT
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import Theorems.Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_ModularForm_mdifferentiable_heckeU
import Theorems.Thm_ModularForm_isBoundedAtImInfty_heckeU
import Theorems.Thm_ModularForm_periodic_heckeU_comp_ofComplex
import Theorems.Thm_ModularForm_mdifferentiable_heckeT
import Theorems.Thm_ModularForm_isBoundedAtImInfty_heckeT
import Theorems.Thm_ModularForm_periodic_heckeT_comp_ofComplex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul

set_option autoImplicit false

noncomputable section

namespace CuspForm
p2m_export "CuspForm" "sub_apply add_apply IsEigenformWith"
namespace M4bOld
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
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) {d : ℕ} (hd : d ∣ M / L) :
    ModularForm.heckeU k ℓ ⇑(G d) + εL (ℓ : ZMod L) • ((⇑(G d)) ∣[k] ModularForm.heckeDiagMatrix ℓ) =
      ModularFormClass.qCoeff g ℓ • ⇑(G d) := by
  classical
  have hℓ0 : ℓ ≠ 0 := hℓ.ne_zero
  have hML : M / L ≠ 0 := by
    obtain ⟨e, he⟩ := hLM
    rw [he, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne L))]
    rintro rfl
    exact NeZero.ne M (by rw [he, mul_zero])
  have hd0 : d ≠ 0 := fun h0 => hML (Nat.eq_zero_of_zero_dvd (h0 ▸ hd))
  have hℓL : ¬ ℓ ∣ L := fun h => hℓM (h.trans hLM)
  have hℓd : ¬ ℓ ∣ d := fun h => hℓM ((h.trans hd).trans (Nat.div_dvd_of_dvd hLM))
  have hcop : Nat.Coprime ℓ d := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓd

  obtain ⟨hper, hhol, hbdd⟩ := reg_gamma1 (G d)
  obtain ⟨gper, ghol, gbdd⟩ := reg_gamma1 g

  have hcoe : (⇑(G d) : ℍ → ℂ) = fun τ => g (ModularForm.heckeDiagMatrix d • τ) := funext (hG d hd)
  have hb : ∀ m : ℕ, qCoeff (⇑(G d)) m = if d ∣ m then qCoeff (⇑g) (m / d) else 0 := by
    intro m
    rw [hcoe]
    exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul gper ghol gbdd hd0 m

  have hD : (⇑(G d)) ∣[k] ModularForm.heckeDiagMatrix ℓ
      = ModularForm.heckeT k ℓ ⇑(G d) - ModularForm.heckeU k ℓ ⇑(G d) := by
    rw [ModularForm.heckeT_eq_heckeU_add, add_sub_cancel_left]

  have hUper := ModularForm.periodic_heckeU_comp_ofComplex hper k ℓ
  have hUhol := ModularForm.mdifferentiable_heckeU hhol k ℓ
  have hUbdd := ModularForm.isBoundedAtImInfty_heckeU hbdd k ℓ
  have hTper := ModularForm.periodic_heckeT_comp_ofComplex hper k ℓ
  have hThol := ModularForm.mdifferentiable_heckeT hhol k ℓ
  have hTbdd := ModularForm.isBoundedAtImInfty_heckeT hbdd k ℓ
  have hDper : Periodic (((⇑(G d)) ∣[k] ModularForm.heckeDiagMatrix ℓ) ∘ ofComplex) 1 := by
    rw [hD]; exact periodic_sub hTper hUper
  have hDhol : MDiff ((⇑(G d)) ∣[k] ModularForm.heckeDiagMatrix ℓ) := by
    rw [hD]; exact hThol.sub hUhol
  have hDbdd : IsBoundedAtImInfty ((⇑(G d)) ∣[k] ModularForm.heckeDiagMatrix ℓ) := by
    rw [hD]; exact hTbdd.sub hUbdd
  set c : ℂ := εL (ℓ : ZMod L) with hc
  have hcDper := periodic_const_smul hDper c
  have hcDhol := hDhol.const_smul c
  have hcDbdd : IsBoundedAtImInfty (c • ((⇑(G d)) ∣[k] ModularForm.heckeDiagMatrix ℓ)) :=
    hDbdd.const_smul_left c

  refine UpperHalfPlane.eq_of_forall_qCoeff_eq (periodic_add hUper hcDper) (hUhol.add hcDhol)
    (hUbdd.add hcDbdd) (periodic_const_smul hper _) (hhol.const_smul _) (hbdd.const_smul_left _)
    fun n => ?_
  have hqU : qCoeff (ModularForm.heckeU k ℓ ⇑(G d)) n = qCoeff ⇑(G d) (n * ℓ) := by
    rw [UpperHalfPlane.qCoeff_heckeU hper hhol hbdd k hℓ0 n, ModularForm.coeffHeckeU_apply]
  have hqT : qCoeff (ModularForm.heckeT k ℓ ⇑(G d)) n
      = qCoeff ⇑(G d) (n * ℓ)
        + (if ℓ ∣ n then (ℓ : ℂ) ^ (k - 1) * qCoeff ⇑(G d) (n / ℓ) else 0) := by
    rw [UpperHalfPlane.qCoeff_heckeT hper hhol hbdd k hℓ0 n, ModularForm.coeffHeckeT_apply]
  have hqD : qCoeff ((⇑(G d)) ∣[k] ModularForm.heckeDiagMatrix ℓ) n
      = (if ℓ ∣ n then (ℓ : ℂ) ^ (k - 1) * qCoeff ⇑(G d) (n / ℓ) else 0) := by
    rw [hD, qCoeff_sub hTper hThol hTbdd hUper hUhol hUbdd, hqT, hqU, add_sub_cancel_left]
  rw [qCoeff_add hUper hUhol hUbdd hcDper hcDhol hcDbdd, qCoeff_const_smul hDper hDhol hDbdd,
    qCoeff_const_smul hper hhol hbdd, hqU, hqD]

  by_cases hdn : d ∣ n
  · obtain ⟨m, rfl⟩ := hdn
    have e1 : qCoeff ⇑(G d) (d * m * ℓ) = qCoeff ⇑g (m * ℓ) := by
      rw [hb, if_pos ⟨m * ℓ, by ring⟩, mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
    have e2 : qCoeff ⇑(G d) (d * m) = qCoeff ⇑g m := by
      rw [hb, if_pos ⟨m, rfl⟩, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
    have key := hg.hecke_of_not_dvd hℓ hℓL m
    rw [mul_comm ℓ m] at key
    by_cases hℓm : ℓ ∣ m
    · have e3 : qCoeff ⇑(G d) (d * m / ℓ) = qCoeff ⇑g (m / ℓ) := by
        rw [Nat.mul_div_assoc d hℓm, hb, if_pos ⟨m / ℓ, rfl⟩,
          Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
      rw [if_pos (hℓm.mul_left d), e1, e2, e3]
      rw [if_pos hℓm] at key
      rw [← key]
      ring
    · have hℓdm : ¬ ℓ ∣ d * m := fun h => hℓm ((Nat.Coprime.dvd_mul_left hcop).mp h)
      rw [if_neg hℓdm, e1, e2]
      rw [if_neg hℓm] at key
      rw [← key]
      ring
  · have e1 : qCoeff ⇑(G d) (n * ℓ) = 0 := by
      rw [hb, if_neg (fun h => hdn ((Nat.Coprime.dvd_mul_right hcop.symm).mp h))]
    have e2 : qCoeff ⇑(G d) n = 0 := by rw [hb, if_neg hdn]
    have e3 : (if ℓ ∣ n then (ℓ : ℂ) ^ (k - 1) * qCoeff ⇑(G d) (n / ℓ) else 0) = 0 := by
      split_ifs with hℓn
      · rw [hb, if_neg (fun h' => hdn (h'.trans (Nat.div_dvd_of_dvd hℓn))), mul_zero]
      · rfl
    rw [e1, e2, e3]
    ring

end CuspForm.M4bOld

end

open scoped MatrixGroups ModularForm in

theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) {L : ℕ} [NeZero L] (hLM : L ∣ M)
    {εL : DirichletCharacter ℂ L} {g : CuspForm (CongruenceSubgroup.Gamma1 L) k}
    (hg : CuspForm.IsEigenformWith εL g)
    (G : ℕ → CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hG : ∀ d : ℕ, d ∣ M / L → ∀ τ : UpperHalfPlane, G d τ = g (ModularForm.heckeDiagMatrix d • τ))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) {d : ℕ} (hd : d ∣ M / L) :
    ModularForm.heckeU k ℓ ⇑(G d) + εL (ℓ : ZMod L) • ((⇑(G d)) ∣[k] ModularForm.heckeDiagMatrix ℓ) =
      ModularFormClass.qCoeff g ℓ • ⇑(G d) :=
  CuspForm.M4bOld.main M k hLM hg G hG hℓ hℓM hd

end S_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul
end P2MW
export P2MW.S_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul (solution)
