-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_signed_plus_one_grid_strong_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:00:58.668105+00:00
-- url     : https://prove2.me/submissions/533b0040-af32-446d-9bb6-e883860ac213

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_bounded_negative_test_grid_l2_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_signed_finite_sum_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_eventual_finite_envelope_strong_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-! Original signed Lévy meshes converge strongly in L¹ when their genuine a.e. limit is known. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → ENNReal) (M : ENNReal) (hM : M ≠ ⊤)
    (hf : ∀ y : ℝ, f y ≤ if y ≤ -ε then M else 0)
    (g : ℝ → ℝ) (hg : ∀ y, ‖g y‖ₑ ≤ f y)
    (h : ℕ → ℝ) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hY : ∀ n ω, Y n ω = ∑ i ∈ Finset.range (n + 1),
      g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (h n)) ω -
        X.X ((i : ℝ≥0) * Real.toNNReal (h n)) ω))
    (hmesh : Tendsto h atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hhor : ∀ᶠ n : ℕ in atTop, ((n + 1 : ℕ) : ℝ) * h n ≤ T)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    MemLp Z 1 P ∧
      Tendsto (fun n => eLpNorm (Y n - Z) 1 P) atTop (nhds 0) := by
  obtain ⟨C, hC, hgrid⟩ :=
    avram_p2_original_bounded_negative_test_grid_l2_bound
      X ε hε T hT f M hM hf
  let K : ENNReal :=
    M ^ 2 * (ENNReal.ofReal (C * T) + (ENNReal.ofReal (C * T)) ^ 2)
  have hK : K ≠ ⊤ := by
    have hct : ENNReal.ofReal (C * T) ≠ ⊤ := ENNReal.ofReal_ne_top
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top hM)
      (ENNReal.add_ne_top.mpr ⟨hct, ENNReal.pow_ne_top hct⟩)
  let G : ℕ → Ω → ENNReal := fun n ω =>
    ∑ i ∈ Finset.range (n + 1),
      f (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (h n)) ω -
        X.X ((i : ℝ≥0) * Real.toNNReal (h n)) ω)
  have hEventual : ∀ᶠ n : ℕ in atTop,
      (∫⁻ ω, (G n ω) ^ 2 ∂P) ≤ K := by
    filter_upwards [hmesh.eventually hgrid, hhor] with n hsmall htime
    exact hsmall (n + 1) htime
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEventual
  apply avram_p2_j_ui_eventual_finite_envelope_strong_L1
    P Y Z G K N hK hm
  · intro n
    exact Eventually.of_forall (fun ω => by
      rw [hY n ω]
      exact avram_p2_j_ui_signed_finite_sum_envelope
        (Finset.range (n + 1))
        (fun i => g (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (h n)) ω -
          X.X ((i : ℝ≥0) * Real.toNNReal (h n)) ω))
        (fun i => f (X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (h n)) ω -
          X.X ((i : ℝ≥0) * Real.toNNReal (h n)) ω))
        (fun i hi => hg _))
  · intro n hn
    simpa [ENNReal.rpow_natCast] using hN n hn
  · exact hae
