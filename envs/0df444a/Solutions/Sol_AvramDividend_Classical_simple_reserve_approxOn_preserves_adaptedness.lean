-- Prove2me | solution 1 for AvramDividend.Classical.simple_reserve_approxOn_preserves_adaptedness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:17:12.394127+00:00
-- url     : https://prove2.me/submissions/9fafcc68-3cdd-4f0e-bdab-cb82e6731649


import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (m' : MeasurableSpace Ω)
    (Z : Ω → ℝ)
    (hZ : Measurable[m'] Z) (hZm : Measurable Z)
    (s : Set ℝ) (y₀ : ℝ) (hy₀ : y₀ ∈ s) (n : ℕ) :
    Measurable[m'] (fun ω =>
      (SimpleFunc.approxOn Z hZm s y₀ hy₀ n) ω) := by
  let A : SimpleFunc ℝ ℝ :=
    SimpleFunc.approxOn (id : ℝ → ℝ) measurable_id s y₀ hy₀ n
  have hmeas : Measurable[m'] (A ∘ Z) :=
    A.measurable.comp hZ
  have hrepr :
      (fun ω => (SimpleFunc.approxOn Z hZm s y₀ hy₀ n) ω) =
        A ∘ Z := by
    have hc := SimpleFunc.approxOn_comp
      (f := (id : ℝ → ℝ)) measurable_id (g := Z) hZm
      hy₀ n
    funext ω
    have h := congrArg (fun a : SimpleFunc Ω ℝ => a ω) hc
    simpa only [A, SimpleFunc.coe_comp, Function.comp_def, id_eq]
      using h
  rw [hrepr]
  exact hmeas

