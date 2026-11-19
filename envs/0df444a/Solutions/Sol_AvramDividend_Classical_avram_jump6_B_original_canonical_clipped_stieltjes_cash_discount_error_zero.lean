-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_canonical_clipped_stieltjes_cash_discount_error_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:42:38.789561+00:00
-- url     : https://prove2.me/submissions/b26f7cae-00d0-4cd1-b158-bed170131fdf

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_public_canonical_strict_stieltjes_real_error_sandwich
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_NNReal_grid_exact_mesh_width_and_limit
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_discount_mesh_error_tends_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_grid_reaches_bounded_clock_every_mesh
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (t : ℝ≥0) (n : ℕ) (ht : t ≤ (n : ℝ≥0))
    (hStrict : (t : ℝ≥0∞) < ruinTime X x D ω) :
    let N : ℕ → ℕ := fun j => (n + 1) * (j + 1)
    let v : ℕ → ℕ → ℝ≥0 := fun j i =>
      min ((i : ℝ≥0) * ((1 : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0))) t
    Tendsto (fun j : ℕ =>
      ∑ i ∈ Finset.range (N j),
        ((∫⁻ r in paymentTimes (ruinTime X x D ω) ∩
            Ioc (v j i : ℝ) (v j (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * r)))
            ∂(dividendMeasure D ω)).toReal -
          Real.exp (-(q * (v j (i + 1) : ℝ))) *
            (rightLimit D (v j (i + 1)) ω - rightLimit D (v j i) ω)))
      atTop (𝓝 (0 : ℝ)) := by
  let N : ℕ → ℕ := fun j => (n+1)*(j+1)
  let v : ℕ → ℕ → ℝ≥0 := fun j i => min ((i : ℝ≥0) * ((1 : ℝ≥0) / ((j+1 : ℕ) : ℝ≥0))) t
  let err : ℕ → ℝ := (fun j : ℕ =>
      ∑ i ∈ Finset.range (N j),
        ((∫⁻ r in paymentTimes (ruinTime X x D ω) ∩
            Ioc (v j i : ℝ) (v j (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * r)))
            ∂(dividendMeasure D ω)).toReal -
          Real.exp (-(q * (v j (i + 1) : ℝ))) *
            (rightLimit D (v j (i + 1)) ω - rightLimit D (v j i) ω)))

  have hBounds (j : ℕ) :
      0 ≤ err j ∧
      err j ≤ (q / ((j : ℝ) + 1)) *
         (rightLimit D t ω - rightLimit D 0 ω) := by
    simpa [N, v, err] using
      (AvramDividend.Classical.avram_jump6_B_public_canonical_strict_stieltjes_real_error_sandwich
        X x C D hD ω q hq t n ht hStrict j)
  have hDelta : Tendsto (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1))
      atTop (nhds (0 : ℝ)) :=
    AvramDividend.Classical.avram_jump6_B_canonical_NNReal_grid_exact_mesh_width_and_limit.2
  have hUpper : Tendsto
      (fun j : ℕ =>
        (q * (rightLimit D t ω - rightLimit D 0 ω)) *
          ((1 : ℝ) / ((j : ℝ) + 1))) atTop (nhds (0 : ℝ)) := by
    convert tendsto_const_nhds.mul hDelta using 1 <;> simp
  have hTarget : Tendsto err atTop (nhds (0 : ℝ)) := by
    apply Filter.Tendsto.squeeze
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)) hUpper
    . intro j
      exact (hBounds j).1
    . intro j
      calc
        err j ≤ (q / ((j : ℝ) + 1)) *
            (rightLimit D t ω - rightLimit D 0 ω) := (hBounds j).2
        _ = (q * (rightLimit D t ω - rightLimit D 0 ω)) *
              ((1 : ℝ) / ((j : ℝ) + 1)) := by ring
  simpa [err, N, v] using hTarget
