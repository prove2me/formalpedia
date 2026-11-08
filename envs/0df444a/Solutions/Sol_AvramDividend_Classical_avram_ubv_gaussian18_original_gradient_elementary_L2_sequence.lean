-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian18_original_gradient_elementary_L2_sequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T21:56:16.239576+00:00
-- url     : https://prove2.me/submissions/adf71bf7-c774-4ac8-b823-b4f9e175b298

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian17_original_masked_gradient_MemLp
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_elementary_predictable_L2_dense

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter TopologicalSpace AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    [IsFiniteMeasure μ] (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      X.σ * (if Y p ∈ Icc u v then deriv w (Y p) else 0)
    let T : Set (Set (ℝ≥0 × Ω)) :=
      {A | (∃ B : Set Ω, MeasurableSet[𝓕.rightCont 0] B ∧
                 A = ({0} ×ˢ B)) ∨
           (∃ t : ℝ≥0, ∃ B : Set Ω, MeasurableSet[𝓕.rightCont t] B ∧
                 A = (Ioi t ×ˢ B))}
    let S : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
      {z | ∃ (A : Set (ℝ≥0 × Ω))
          (hA : A ∈ insert univ (insert ∅ T))
          (hm : MeasurableSet[𝓕.rightCont.predictable] A) (hfinite : μ A ≠ ⊤),
          indicatorConstLp (2 : ℝ≥0∞) hm hfinite (1 : ℝ) = z}
    ∃ e : ℕ → Lp ℝ (2 : ℝ≥0∞) μ,
      (∀ n, e n ∈ Submodule.span ℝ S) ∧
      Tendsto e atTop (𝓝 ((avram_ubv_gaussian17_original_masked_gradient_MemLp
        X x D hD w a b u v hw hau huv hvb μ hμ).toLp G)) := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let G : ℝ≥0 × Ω → ℝ := fun p =>
    X.σ * (if Y p ∈ Icc u v then deriv w (Y p) else 0)
  let f : Lp ℝ (2 : ℝ≥0∞) μ :=
    (avram_ubv_gaussian17_original_masked_gradient_MemLp
      X x D hD w a b u v hw hau huv hvb μ hμ).toLp G
  have hDense := avram_ubv_gaussian10_original_elementary_predictable_L2_dense
    (𝓕 := 𝓕.rightCont) (mProd := 𝓕.rightCont.predictable) rfl μ
  have hf : f ∈ (Submodule.span ℝ
      {z : Lp ℝ (2 : ℝ≥0∞) μ |
        ∃ (A : Set (ℝ≥0 × Ω))
          (hA : A ∈ insert univ (insert ∅
            {T | (∃ B, MeasurableSet[𝓕.rightCont 0] B ∧ T = ({0} ×ˢ B)) ∨
                 (∃ t, ∃ B, MeasurableSet[𝓕.rightCont t] B ∧ T = (Ioi t ×ˢ B))}))
          (hm : MeasurableSet[𝓕.rightCont.predictable] A) (hfinite : μ A ≠ ⊤),
          indicatorConstLp (2 : ℝ≥0∞) hm hfinite (1 : ℝ) = z}).topologicalClosure :=
    hDense f
  rcases (mem_closure_iff_seq_limit).mp (show f ∈ closure _ from hf) with
    ⟨e, he, hlim⟩
  exact ⟨e, he, hlim⟩
