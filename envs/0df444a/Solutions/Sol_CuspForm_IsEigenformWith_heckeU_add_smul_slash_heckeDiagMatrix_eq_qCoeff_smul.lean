-- Prove2me | solution 1 for CuspForm.IsEigenformWith.heckeU_add_smul_slash_heckeDiagMatrix_eq_qCoeff_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/cc216a89-dd4e-5969-93c9-6bb19f4d3a0f

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_ModularForm_HeckeOperator

import Theorems.Thm_UpperHalfPlane_qCoeff_heckeU
import Theorems.Thm_UpperHalfPlane_qCoeff_heckeT
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
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

namespace P2MW.S_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_eq_qCoeff_smul

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

noncomputable section

namespace Ws41
namespace L7b

open Complex Function Filter
p2m_open "UpperHalfPlane~I"
open scoped Real MatrixGroups ModularForm Manifold Topology
open ModularForm ModularFormClass

theorem qCoeff_const_smul {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty f) (c : ℂ) (n : ℕ) : qCoeff (c • f) n = c * qCoeff f n := by
  simp only [qCoeff]
  rw [UpperHalfPlane.qExpansion_smul (analyticAt_cuspFunction_zero one_pos hper hhol hbdd)]
  simp

theorem qCoeff_add {f g : ℍ → ℂ} (hfper : Periodic (f ∘ ofComplex) 1) (hfhol : MDiff f)
    (hfbdd : IsBoundedAtImInfty f) (hgper : Periodic (g ∘ ofComplex) 1) (hghol : MDiff g)
    (hgbdd : IsBoundedAtImInfty g) (n : ℕ) : qCoeff (f + g) n = qCoeff f n + qCoeff g n := by
  simp only [qCoeff]
  rw [UpperHalfPlane.qExpansion_add (analyticAt_cuspFunction_zero one_pos hfper hfhol hfbdd)
    (analyticAt_cuspFunction_zero one_pos hgper hghol hgbdd)]
  simp

theorem qCoeff_sub {f g : ℍ → ℂ} (hfper : Periodic (f ∘ ofComplex) 1) (hfhol : MDiff f)
    (hfbdd : IsBoundedAtImInfty f) (hgper : Periodic (g ∘ ofComplex) 1) (hghol : MDiff g)
    (hgbdd : IsBoundedAtImInfty g) (n : ℕ) : qCoeff (f - g) n = qCoeff f n - qCoeff g n := by
  simp only [qCoeff]
  rw [UpperHalfPlane.qExpansion_sub (analyticAt_cuspFunction_zero one_pos hfper hfhol hfbdd)
    (analyticAt_cuspFunction_zero one_pos hgper hghol hgbdd)]
  simp

theorem periodic_const_smul {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (c : ℂ) :
    Periodic ((c • f) ∘ ofComplex) 1 := fun z ↦ by
  simpa using congrArg (c * ·) (hper z)

theorem periodic_add {f g : ℍ → ℂ} (hf : Periodic (f ∘ ofComplex) 1) (hg : Periodic (g ∘ ofComplex) 1) :
    Periodic ((f + g) ∘ ofComplex) 1 := fun z ↦ by
  have h1 := hf z
  have h2 := hg z
  simp only [comp_apply, Pi.add_apply] at h1 h2 ⊢
  rw [h1, h2]

theorem periodic_sub {f g : ℍ → ℂ} (hf : Periodic (f ∘ ofComplex) 1) (hg : Periodic (g ∘ ofComplex) 1) :
    Periodic ((f - g) ∘ ofComplex) 1 := fun z ↦ by
  have h1 := hf z
  have h2 := hg z
  simp only [comp_apply, Pi.sub_apply] at h1 h2 ⊢
  rw [h1, h2]

end Ws41.L7b

end

open Ws41.L7b in
theorem solution
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith ε h) {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) :
    ModularForm.heckeU 2 p ⇑h + ε (p : ZMod M) • ((⇑h) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p)
      = ModularFormClass.qCoeff h p • ⇑h := by
  classical
  have hp0 : p ≠ 0 := hp.ne_zero

  have hΓ : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]
    exact AddSubgroup.mem_zmultiples 1
  have hper : Function.Periodic (⇑h ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex h hΓ
  have hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ⇑h :=
    ModularFormClass.holo h
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty ⇑h := by
    haveI : Fact (IsCusp OnePoint.infty (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ))) :=
      ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ⟩
    exact ModularFormClass.bdd_at_infty h

  have hD : (⇑h) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p
      = ModularForm.heckeT 2 p ⇑h - ModularForm.heckeU 2 p ⇑h := by
    rw [ModularForm.heckeT_eq_heckeU_add, add_sub_cancel_left]

  have hUper := ModularForm.periodic_heckeU_comp_ofComplex hper 2 p
  have hUhol := ModularForm.mdifferentiable_heckeU hhol 2 p
  have hUbdd := ModularForm.isBoundedAtImInfty_heckeU hbdd 2 p
  have hTper := ModularForm.periodic_heckeT_comp_ofComplex hper 2 p
  have hThol := ModularForm.mdifferentiable_heckeT hhol 2 p
  have hTbdd := ModularForm.isBoundedAtImInfty_heckeT hbdd 2 p
  have hDper : Function.Periodic (((⇑h) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p) ∘ UpperHalfPlane.ofComplex) 1 := by
    rw [hD]; exact periodic_sub hTper hUper
  have hDhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      ((⇑h) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p) := by
    rw [hD]; exact hThol.sub hUhol
  have hDbdd : UpperHalfPlane.IsBoundedAtImInfty ((⇑h) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p) := by
    rw [hD]; exact hTbdd.sub hUbdd
  set c : ℂ := ε (p : ZMod M) with hc
  have hcDper := periodic_const_smul hDper c
  have hcDhol := hDhol.const_smul c
  have hcDbdd : UpperHalfPlane.IsBoundedAtImInfty (c • ((⇑h) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p)) :=
    hDbdd.const_smul_left c

  refine UpperHalfPlane.eq_of_forall_qCoeff_eq (periodic_add hUper hcDper) (hUhol.add hcDhol)
    (hUbdd.add hcDbdd) (periodic_const_smul hper _) (hhol.const_smul _) (hbdd.const_smul_left _)
    fun n => ?_
  have hqU : ModularFormClass.qCoeff (ModularForm.heckeU 2 p ⇑h) n = ModularFormClass.qCoeff ⇑h (n * p) := by
    rw [UpperHalfPlane.qCoeff_heckeU hper hhol hbdd 2 hp0 n, ModularForm.coeffHeckeU_apply]
  have hqT : ModularFormClass.qCoeff (ModularForm.heckeT 2 p ⇑h) n
      = ModularFormClass.qCoeff ⇑h (n * p)
        + (if p ∣ n then (p : ℂ) ^ ((2 : ℤ) - 1) * ModularFormClass.qCoeff ⇑h (n / p) else 0) := by
    rw [UpperHalfPlane.qCoeff_heckeT hper hhol hbdd 2 hp0 n, ModularForm.coeffHeckeT_apply]
  have hqD : ModularFormClass.qCoeff ((⇑h) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p) n
      = (if p ∣ n then (p : ℂ) ^ ((2 : ℤ) - 1) * ModularFormClass.qCoeff ⇑h (n / p) else 0) := by
    rw [hD, qCoeff_sub hTper hThol hTbdd hUper hUhol hUbdd, hqT, hqU, add_sub_cancel_left]
  rw [qCoeff_add hUper hUhol hUbdd hcDper hcDhol hcDbdd, qCoeff_const_smul hDper hDhol hDbdd,
    qCoeff_const_smul hper hhol hbdd, hqU, hqD]
  have key := hh.hecke_of_not_dvd hp hpM n
  rw [mul_comm p n] at key
  rw [← key]
  split_ifs <;> ring

end S_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_eq_qCoeff_smul
end P2MW
export P2MW.S_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_eq_qCoeff_smul (solution)
