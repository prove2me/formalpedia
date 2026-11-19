-- Prove2me | solution 1 for EnvyFreeCake104.Divide.cutAnswer_cell_spec__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-18T19:14:33.618556+00:00
-- url     : https://prove2.me/submissions/d4388bd3-e4f5-49b6-869c-89303befcd25

import Definitions.Def_EnvyFreeCake104_Divide_Query
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

theorem solution {ι : Type} (V : ι → Valuation) (i : ι) :
    ∀ (a b r : ℝ), 0 ≤ a → a ≤ b → b ≤ 1 →
      0 ≤ r → r ≤ (V i).value (Set.Ico a b) →
      a ≤ cutAnswer V i a r ∧ cutAnswer V i a r ≤ b ∧
      (V i).value (Set.Ico a (cutAnswer V i a r)) = r ∧
      ∀ z : ℝ, z ∈ Set.Icc a b →
        r ≤ (V i).value (Set.Ico a z) → cutAnswer V i a r ≤ z := by
  intro a b r ha hab hb hr hrb
  let f : ℝ → ℝ := fun y ↦ (V i).value (Set.Icc a y)
  have hformula (y : ℝ) (hy : y ≤ 1) :
      f y = ∫ x in Set.Icc a y, (V i).density x := by
    have hs : Set.Icc a y ⊆ Set.Icc (0 : ℝ) 1 :=
      fun x hx ↦ ⟨ha.trans hx.1, hx.2.trans hy⟩
    change (∫ x in Set.Icc a y ∩ Set.Icc (0 : ℝ) 1, (V i).density x) = _
    rw [Set.inter_eq_left.mpr hs]
  have hhalf (y : ℝ) (hy : y ≤ 1) : f y = (V i).value (Set.Ico a y) := by
    have hs : Set.Ico a y ⊆ Set.Icc (0 : ℝ) 1 :=
      fun x hx ↦ ⟨ha.trans hx.1, hx.2.le.trans hy⟩
    rw [hformula y hy, Valuation.value, Set.inter_eq_left.mpr hs]
    exact MeasureTheory.integral_Icc_eq_integral_Ico
  have hf : ContinuousOn f (Set.Icc a 1) := by
    have hi : MeasureTheory.IntegrableOn (V i).density (Set.Icc a 1) :=
      (V i).integrable.mono_set (fun x hx ↦ ⟨ha.trans hx.1, hx.2⟩)
    apply (intervalIntegral.continuousOn_primitive_Icc hi).congr
    intro y hy
    exact hformula y hy.2
  have hfa : f a = 0 := by
    rw [hformula a (hab.trans hb)]
    simp
  -- Every crossing has an exact-value point preceding it, including when r = 0.
  have hcross (z : ℝ) (hz : z ∈ Set.Icc a 1) (hrz : r ≤ f z) :
      ∃ y ∈ Set.Icc a z, f y = r := by
    have hcont : ContinuousOn f (Set.Icc a z) :=
      hf.mono (fun x hx ↦ ⟨hx.1, hx.2.trans hz.2⟩)
    apply intermediate_value_Icc hz.1 hcont
    exact ⟨by simpa [hfa] using hr, hrz⟩
  let S : Set ℝ := {y | y ∈ Set.Icc a 1 ∧ f y = r}
  have hclosed : IsClosed S := by
    change IsClosed (Set.Icc a 1 ∩ f ⁻¹' {r})
    exact hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hcompact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hclosed (fun y hy ↦ hy.1)
  obtain ⟨y, hy, hyr⟩ := hcross b ⟨hab, hb⟩ (by rwa [hhalf b hb])
  have hyS : y ∈ S := ⟨⟨hy.1, hy.2.trans hb⟩, hyr⟩
  have hleast : IsLeast S (sInf S) := hcompact.isLeast_sInf ⟨y, hyS⟩
  have hcut : cutAnswer V i a r = sInf S := rfl
  rw [hcut]
  refine ⟨hleast.1.1.1, (hleast.2 hyS).trans hy.2, ?_, ?_⟩
  · rw [← hhalf (sInf S) hleast.1.1.2]
    exact hleast.1.2
  · intro z hz hrz
    obtain ⟨w, hw, hwr⟩ :=
      hcross z ⟨hz.1, hz.2.trans hb⟩ (by rwa [hhalf z (hz.2.trans hb)])
    exact (hleast.2 ⟨⟨hw.1, hw.2.trans (hz.2.trans hb)⟩, hwr⟩).trans hw.2
