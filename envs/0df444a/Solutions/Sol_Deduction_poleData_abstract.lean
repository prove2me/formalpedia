-- Prove2me | solution 1 for Deduction.poleData_abstract
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:04.409629+00:00
-- url     : https://prove2.me/submissions/a04fbfbb-cb75-473f-b34e-e5753de8ca20

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
import Theorems.Thm_Deduction_poleData_dslope
import Theorems.Thm_Deduction_logDeriv_local


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
theorem _root_.solution (g : ℂ → ℂ) (hg : Differentiable ℂ g) (h1 : g 1 ≠ 0) (k : ℂ) :
    ∃ Φ : ℂ → ℂ,
      (∀ s, s ≠ 1 → Φ s =
        -(deriv g s / g s - s * (deriv g 1 / g 1) + k * (1 - s)) / (s * (s - 1))) ∧
      (∀ ρ, ρ ≠ 0 → g ρ ≠ 0 → AnalyticAt ℂ Φ ρ) ∧
      (∀ ρ, ρ ≠ 0 → ∃ m : ℕ, (m = 0 ↔ g ρ ≠ 0) ∧ ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
        ∀ᶠ s in 𝓝[≠] ρ, Φ s = (m : ℂ) * (-1 / (ρ * (ρ - 1))) / (s - ρ) + h s) ∧
      (∀ z, ∀ᶠ w in 𝓝[≠] z, g w ≠ 0) := by
  have hA : ∀ z, AnalyticAt ℂ g z := fun z => hg.analyticAt z
  have hnz : ∀ z, ¬ ∀ᶠ w in 𝓝 z, g w = 0 := by
    intro z hz
    have hon : AnalyticOnNhd ℂ g Set.univ := fun w _ => hA w
    have hzero := hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ z) hz
    exact h1 (hzero (Set.mem_univ 1))
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = deriv g 1 / g 1 := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℂ → ℂ, N = fun s => deriv g s / g s - s * c + k * (1 - s) := ⟨_, rfl⟩
  have hNs : ∀ s, N s = deriv g s / g s - s * c + k * (1 - s) := fun s => by rw [hN]
  have hN1 : N 1 = 0 := by rw [hNs, hc]; ring
  have hUo : IsOpen {s | g s ≠ 0} := isOpen_ne_fun hg.continuous continuous_const
  have hNd : DifferentiableOn ℂ N {s | g s ≠ 0} := by
    intro s hs
    have hd : DifferentiableAt ℂ (deriv g) s := (hA s).deriv.differentiableAt
    have hd2 : DifferentiableAt ℂ (fun s => deriv g s / g s - s * c + k * (1 - s)) s :=
      ((hd.div (hA s).differentiableAt hs).sub (differentiableAt_id.mul (differentiableAt_const c))).add
        ((differentiableAt_const k).mul ((differentiableAt_const 1).sub differentiableAt_id))
    rw [hN]
    exact hd2.differentiableWithinAt
  have hDd : DifferentiableOn ℂ (dslope N 1) {s | g s ≠ 0} :=
    (differentiableOn_dslope (hUo.mem_nhds h1)).mpr hNd
  have hPhi : ∀ s, s ≠ 1 → -(dslope N 1 s) / s =
      -(deriv g s / g s - s * (deriv g 1 / g 1) + k * (1 - s)) / (s * (s - 1)) := by
    intro s hs
    rw [dslope_of_ne _ hs, slope_def_field, hN1, hNs, ← hc]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hPan : ∀ ρ, ρ ≠ 0 → g ρ ≠ 0 → AnalyticAt ℂ (fun s => -(dslope N 1 s) / s) ρ := by
    intro ρ hρ hgρ
    exact (hDd.analyticAt (hUo.mem_nhds hgρ)).neg.div analyticAt_id hρ
  refine ⟨fun s => -(dslope N 1 s) / s, hPhi, hPan, ?_, ?_⟩
  · intro ρ hρ
    by_cases hgρ : g ρ = 0
    · have hρ1 : ρ ≠ 1 := fun h => h1 (h ▸ hgρ)
      obtain ⟨m, hm0, -, h0, hh0, hev⟩ := logDeriv_local (hA ρ) (hnz ρ)
      have hr : AnalyticAt ℂ (fun s : ℂ => 1 / (s * (s - 1))) ρ :=
        analyticAt_const.div (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
          (mul_ne_zero hρ (sub_ne_zero.mpr hρ1))
      have hq := poleData_dslope hr
      refine ⟨m, hm0, fun s => -((m : ℂ) * dslope (fun s : ℂ => 1 / (s * (s - 1))) ρ s)
          - (h0 s - s * c + k * (1 - s)) * (1 / (s * (s - 1))), ?_, ?_⟩
      · exact ((analyticAt_const.mul hq).neg).sub
          (((hh0.sub (analyticAt_id.mul analyticAt_const)).add
            (analyticAt_const.mul (analyticAt_const.sub analyticAt_id))).mul hr)
      · have hne0 : ∀ᶠ s in 𝓝[≠] ρ, s ≠ 0 :=
          nhdsWithin_le_nhds (isOpen_ne.mem_nhds hρ)
        have hne1 : ∀ᶠ s in 𝓝[≠] ρ, s ≠ 1 :=
          nhdsWithin_le_nhds (isOpen_ne.mem_nhds hρ1)
        have hneρ : ∀ᶠ s in 𝓝[≠] ρ, s ≠ ρ := self_mem_nhdsWithin
        filter_upwards [hev, hne0, hne1, hneρ] with s hs hs0 hs1 hsρ
        rw [hPhi s hs1, hs, dslope_of_ne _ hsρ, slope_def_field, ← hc]
        simp only [div_eq_mul_inv, mul_inv]
        ring
    · refine ⟨0, by simp [hgρ], fun s => -(dslope N 1 s) / s, hPan ρ hρ hgρ, ?_⟩
      exact Filter.Eventually.of_forall (fun s => by simp)
  · intro z
    rcases (hA z).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd h (hnz z)
    · exact h
end Deduction
