-- Prove2me | solution 1 for ChatterjeeSamuelson1983.thm2_linked_odes_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T05:35:44.590422+00:00
-- url     : https://prove2.me/submissions/42c42b11-27bf-4c5b-af41-32d9d2138aa4

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_LinkedODE_RegularBelief
import Definitions.Def_ChatterjeeSamuelson_LinkedODE_ClassA
import Definitions.Def_ChatterjeeSamuelson_Shared_IsEquilibrium
import Theorems.Thm_ChatterjeeSamuelson_LinkedODE_linked_differential_equations

open MeasureTheory ProbabilityTheory Set ChatterjeeSamuelson ChatterjeeSamuelson.LinkedODE

theorem solution (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (μb μs : Measure ℝ) (loS hiS loB hiB : ℝ) (fb fs S B : ℝ → ℝ)
    (hμb : RegularBelief μb loS hiS fb) (hμs : RegularBelief μs loB hiB fs)
    (hEq : Shared.IsEquilibrium k μb μs loS hiS loB hiB S B)
    (hS : ClassA S loS hiS) (hB : ClassA B loB hiB) :
    (∀ a c y : ℝ, loS ≤ a → c ≤ hiS → y ∈ Ioo a c → StrictMonoOn S (Ioo a c) →
      ∀ x ∈ Icc loB hiB, B x = S y → (∀ x' ∈ Icc loB hiB, B x' = S y → x' = x) →
        k * cdf μb y * deriv S y + fb y * S y = x * fb y) ∧
    (∀ a c x : ℝ, loB ≤ a → c ≤ hiB → x ∈ Ioo a c → StrictMonoOn B (Ioo a c) →
      ∀ y ∈ Icc loS hiS, S y = B x → (∀ y' ∈ Icc loS hiS, S y' = B x → y' = y) →
        (1 - k) * (1 - cdf μs x) * deriv B x - fs x * B x = -(y * fs x)) := by
  obtain ⟨h1, h2⟩ := linked_differential_equations k hk0 hk1 μb μs loS hiS loB hiB fb fs S B
    hμb hμs hEq hS hB
  exact ⟨fun a c y ha hc hy hm x hx he _ => h1 a c y ha hc hy hm x hx he,
    fun a c x ha hc hx hm y hy he _ => h2 a c x ha hc hx hm y hy he⟩
