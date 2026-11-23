-- Prove2me | solution 1 for Deduction.logDeriv_local
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:20.70885+00:00
-- url     : https://prove2.me/submissions/6d2df5d5-6c77-4419-9b5a-eed51b7d0ebf

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LogDerivLocal

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
theorem _root_.solution {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ) (hne : ¬ ∀ᶠ s in 𝓝 ρ, f s = 0) :
    ∃ m : ℕ, (m = 0 ↔ f ρ ≠ 0) ∧ (m : ℕ∞) = analyticOrderAt f ρ ∧ ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, deriv f s / f s = (m : ℂ) / (s - ρ) + h s := by
  have htop : analyticOrderAt f ρ ≠ ⊤ := fun h => hne (analyticOrderAt_eq_top.mp h)
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_ne_top.mp htop
  set m := analyticOrderNatAt f ρ with hm
  refine ⟨m, ?_, Nat.cast_analyticOrderNatAt htop, fun s => deriv g s / g s,
    hg.deriv.div hg hg0, ?_⟩
  · rw [← hf.analyticOrderAt_eq_zero, ← Nat.cast_analyticOrderNatAt htop]
    exact Nat.cast_eq_zero.symm
  · have hev : ∀ᶠ s in 𝓝 ρ, (∀ᶠ z in 𝓝 s, f z = (z - ρ) ^ m • g z) ∧ g s ≠ 0 ∧ AnalyticAt ℂ g s :=
      (Filter.Eventually.eventually_nhds hfg).and
        ((hg.continuousAt.eventually_ne hg0).and hg.eventually_analyticAt)
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with s hs hsne
    obtain ⟨hs1, hs2, hs3⟩ := hs
    have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr hsne
    have hd : HasDerivAt (fun z => (z - ρ) ^ m * g z)
        (↑m * (s - ρ) ^ (m - 1) * 1 * g s + (s - ρ) ^ m * deriv g s) s :=
      (((hasDerivAt_id' s).sub_const ρ).pow m).mul hs3.differentiableAt.hasDerivAt
    have e1 : deriv f s = deriv (fun z => (z - ρ) ^ m * g z) s := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hs1] with z hz
      rw [hz, smul_eq_mul]
    have e2 : f s = (s - ρ) ^ m * g s := by simpa only [smul_eq_mul] using hs1.self_of_nhds
    rw [e1, hd.deriv, e2]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0]
      simp
    · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, pow_succ]
      field_simp
end Deduction
