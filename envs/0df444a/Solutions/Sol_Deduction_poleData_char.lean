-- Prove2me | solution 1 for Deduction.poleData_char
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:29.996194+00:00
-- url     : https://prove2.me/submissions/1e6908a6-d38f-43f8-9738-df9f095cbadd

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LogDerivLocal
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LFunctionConj
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_CharFamilyLFunctionNeZeroOfOneLeRe
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mellinGchiOfNeOne
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mellinGchiModOne
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_measurableGchi
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_GchiGrowth
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_GchiConj
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_poleData
import Theorems.Thm_Deduction_poleData_abstract
import Theorems.Thm_Deduction_poleData_change
import Theorems.Thm_Deduction_mellin_Gchi_modOne
import Theorems.Thm_Deduction_mellin_Gchi_of_ne_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (adm : N = 1 ∨ χ ≠ 1) :
    ∃ Φ : ℂ → ℂ,
      (∀ s : ℂ, 2 < s.re → Φ s = ∫ u in Ioi (0 : ℝ), Gchi χ (Real.exp u) * cexp (-s * u)) ∧
      (∀ ρ, ρ ≠ 0 → DirichletCharacter.LFunction χ ρ ≠ 0 → AnalyticAt ℂ Φ ρ) ∧
      (∀ ρ, ρ ≠ 0 → ∃ m : ℕ, (m = 0 ↔ DirichletCharacter.LFunction χ ρ ≠ 0) ∧
        ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
        ∀ᶠ s in 𝓝[≠] ρ, Φ s = (m : ℂ) * (-1 / (ρ * (ρ - 1))) / (s - ρ) + h s) ∧
      (∀ z, ∀ᶠ w in 𝓝[≠] z, DirichletCharacter.LFunction χ w ≠ 0) := by
  by_cases hχ : χ = 1
  · have hN : N = 1 := adm.resolve_right (fun h => h hχ)
    subst hN
    simp only [DirichletCharacter.LFunction_modOne_eq]
    set g : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1 with hg_def
    have hg_ne : ∀ w : ℂ, w ≠ 1 → g w = (w - 1) * riemannZeta w := by
      intro w hw
      simp [g, Function.update_apply, hw]
    have hg1 : g 1 = 1 := by simp [g]
    have hg : Differentiable ℂ g := by
      rw [← differentiableOn_univ,
        ← differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
      refine ⟨?_, ?_⟩
      · intro z hz
        have hz1 : z ≠ 1 := by simpa using hz
        apply DifferentiableAt.differentiableWithinAt
        have hev : g =ᶠ[𝓝 z] fun s => (s - 1) * riemannZeta s := by
          filter_upwards [isOpen_compl_singleton.mem_nhds hz1] with w hw
          exact hg_ne w hw
        have hd : DifferentiableAt ℂ (fun s => (s - 1) * riemannZeta s) z :=
          DifferentiableAt.mul (by fun_prop) (differentiableAt_riemannZeta hz1)
        exact hd.congr_of_eventuallyEq hev
      · simpa only [g, continuousAt_update_same] using riemannZeta_residue_one
    have hderiv1 : deriv g 1 = Real.eulerMascheroniConstant := by
      have hd : HasDerivAt g (deriv g 1) 1 := (hg 1).hasDerivAt
      rw [hasDerivAt_iff_tendsto_slope] at hd
      refine tendsto_nhds_unique hd (tendsto_riemannZeta_sub_one_div.congr' ?_)
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs1 : s ≠ 1 := hs
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      rw [slope_def_field, hg_ne s hs1, hg1]
      field_simp
    have hderiv : ∀ s : ℂ, s ≠ 1 →
        deriv g s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
      intro s hs1
      have hev : g =ᶠ[𝓝 s] fun s => (s - 1) * riemannZeta s := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with w hw
        exact hg_ne w hw
      rw [hev.deriv_eq]
      have h1 : HasDerivAt (fun s : ℂ => s - 1) 1 s := (hasDerivAt_id s).sub_const 1
      have h2 : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
        (differentiableAt_riemannZeta hs1).hasDerivAt
      have h3 : HasDerivAt (fun s : ℂ => (s - 1) * riemannZeta s)
          (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s := h1.mul h2
      rw [h3.deriv]
      ring
    have hgz : ∀ w : ℂ, g w ≠ 0 ↔ riemannZeta w ≠ 0 := by
      intro w
      by_cases hw : w = 1
      · subst hw
        rw [hg1]
        exact ⟨fun _ => riemannZeta_one_ne_zero, fun _ => one_ne_zero⟩
      · rw [hg_ne w hw]
        have hw' : w - 1 ≠ 0 := sub_ne_zero.mpr hw
        constructor
        · intro h hz
          exact h (by rw [hz, mul_zero])
        · intro h
          exact mul_ne_zero hw' h
    obtain ⟨Φ, h1, h2, h3, h4⟩ := poleData_abstract g hg (by rw [hg1]; exact one_ne_zero) 1
    refine ⟨Φ, ?_, ?_, ?_, ?_⟩
    · intro s hs
      have hs1 : s ≠ 1 := by
        intro h
        rw [h] at hs
        norm_num at hs
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      have hs0 : s ≠ 0 := by
        intro h
        rw [h] at hs
        norm_num at hs
      have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
      rw [h1 s hs1, poleData_change, mellin_Gchi_modOne χ s (by linarith), hderiv s hs1,
        hg_ne s hs1, hderiv1, hg1]
      congr 1
      field_simp
      ring
    · intro ρ hρ hL
      exact h2 ρ hρ ((hgz ρ).mpr hL)
    · intro ρ hρ
      obtain ⟨m, hm, rest⟩ := h3 ρ hρ
      exact ⟨m, hm.trans (hgz ρ), rest⟩
    · intro z
      filter_upwards [h4 z] with w hw
      exact (hgz w).mp hw
  · obtain ⟨Φ, h1, h2, h3, h4⟩ := poleData_abstract (DirichletCharacter.LFunction χ)
      (DirichletCharacter.differentiable_LFunction hχ)
      (DirichletCharacter.LFunction_apply_one_ne_zero hχ) 0
    refine ⟨Φ, ?_, h2, h3, h4⟩
    intro s hs
    have hs1 : s ≠ 1 := by
      intro h
      rw [h] at hs
      norm_num at hs
    rw [h1 s hs1, poleData_change, mellin_Gchi_of_ne_one χ hχ s (by linarith), zero_mul, add_zero]
end Deduction
