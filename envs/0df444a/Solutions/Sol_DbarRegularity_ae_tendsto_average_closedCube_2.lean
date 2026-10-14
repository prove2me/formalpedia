-- Prove2me | solution 2 for DbarRegularity.ae_tendsto_average_closedCube
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T23:53:31.425851+00:00
-- url     : https://prove2.me/submissions/33596f5e-c6fb-462d-81ee-b87aef3a4d0b

import Definitions.Def_DbarRegularity_Setting
import Mathlib.MeasureTheory.Covering.Differentiation
import Mathlib.MeasureTheory.Covering.Vitali
import Theorems.Thm_DbarRegularity_interior_closedCube
import Theorems.Thm_DbarRegularity_isClosed_closedCube
import Theorems.Thm_DbarRegularity_dist_le_of_mem_closedCube
import Theorems.Thm_DbarRegularity_volume_closedBall_le_cube
import Theorems.Thm_DbarRegularity_volume_closedCube



namespace DbarRegularity

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal

theorem ae_tendsto_average_closedCube' {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : EuclideanSpace ℝ (Fin d) → E}
    (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, ∀ {ι : Type*} {l : Filter ι} (a : ι → EuclideanSpace ℝ (Fin d)) (s : ι → ℝ),
      Tendsto s l (𝓝[>] 0) → (∀ᶠ j in l, x ∈ closedCube (a j) (s j)) →
      Tendsto (fun j => ⨍ y in closedCube (a j) (s j), f y) l (𝓝 (f x)) := by
  set C : ℝ≥0 := Real.toNNReal ((6 * Real.sqrt d) ^ d + 3 ^ d) with hCdef
  have hC1 : ENNReal.ofReal (3 ^ d) ≤ (C : ℝ≥0∞) :=
    ENNReal.ofReal_le_ofReal (by have := pow_nonneg (by positivity : (0:ℝ) ≤ 6 * Real.sqrt d) d; linarith)
  have hC2 : ENNReal.ofReal ((6 * Real.sqrt d) ^ d) ≤ (C : ℝ≥0∞) :=
    ENNReal.ofReal_le_ofReal (by have := pow_nonneg (by norm_num : (0:ℝ) ≤ 3) d; linarith)
  have hdbl : ∀ x : EuclideanSpace ℝ (Fin d), ∃ᶠ r in 𝓝[>] (0:ℝ),
      volume (closedBall x (3 * r)) ≤ C * volume (closedBall x r) := by
    intro x
    refine Eventually.frequently ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [Measure.addHaar_closedBall_mul volume x (by norm_num : (0:ℝ) ≤ 3) hr.le,
      Measure.addHaar_closedBall_center volume x r, finrank_euclideanSpace_fin]
    gcongr
  let v := Vitali.vitaliFamily (volume : Measure (EuclideanSpace ℝ (Fin d))) C hdbl
  filter_upwards [v.ae_tendsto_average hf] with x hx
  intro ι l a s hs hmem
  have hpos : ∀ᶠ j in l, 0 < s j := hs self_mem_nhdsWithin
  have hs0 : Tendsto s l (𝓝 0) := hs.mono_right nhdsWithin_le_nhds
  refine hx.comp (v.tendsto_filterAt_iff.2 ⟨?_, ?_⟩)
  · filter_upwards [hpos, hmem] with j hj hxj
    refine ⟨isClosed_closedCube _ _, ?_, Real.sqrt d * s j, ?_, ?_⟩
    · rw [interior_closedCube]
      refine ⟨WithLp.toLp 2 fun i => a j i + s j / 2, fun i => ?_⟩
      simp only [PiLp.toLp_apply]
      constructor <;> linarith
    · exact fun y hy => mem_closedBall.2 (dist_le_of_mem_closedCube hxj hy)
    · refine (volume_closedBall_le_cube x).trans ?_
      rw [volume_closedCube, ← ENNReal.ofReal_pow hj.le, ← ENNReal.ofReal_pow (by positivity),
        show (2 * (3 * (Real.sqrt d * s j))) ^ d = (6 * Real.sqrt d) ^ d * s j ^ d by ring,
        ENNReal.ofReal_mul (by positivity)]
      gcongr
  · intro ε hε
    have hlt : ∀ᶠ j in l, s j < ε / (Real.sqrt d + 1) :=
      hs0 (Iio_mem_nhds (by positivity))
    filter_upwards [hlt, hmem, hpos] with j h1 h2 h3 y hy
    rw [mem_closedBall]
    refine (dist_le_of_mem_closedCube h2 hy).trans ?_
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith

end DbarRegularity

open DbarRegularity

open MeasureTheory Filter Topology

theorem solution {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : EuclideanSpace ℝ (Fin d) → E}
    (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, ∀ {ι : Type*} {l : Filter ι} (a : ι → EuclideanSpace ℝ (Fin d)) (s : ι → ℝ),
      Tendsto s l (𝓝[>] 0) → (∀ᶠ j in l, x ∈ closedCube (a j) (s j)) →
      Tendsto (fun j => ⨍ y in closedCube (a j) (s j), f y) l (𝓝 (f x)) :=
  ae_tendsto_average_closedCube' hf
