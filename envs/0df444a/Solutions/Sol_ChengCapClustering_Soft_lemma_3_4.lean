-- Prove2me | solution 1 for ChengCapClustering.Soft.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-26T11:24:28.478796+00:00
-- url     : https://prove2.me/submissions/2c4f84e8-6d58-4615-b58a-4a406b47f8d9

import Mathlib
import Definitions.Def_ChengCapClustering_Soft_Clustering

universe u v

open ChengCapClustering ChengCapClustering.Soft

namespace P2MHole01_25bd8837
/-- Scalar identity: `(1 / b) * b ^ w = b ^ (w - 1)` for `b > 0`. -/
lemma p2m_hole_scalar {b : ℝ} (hb : 0 < b) (w : ℝ) : (1 / b) * b ^ w = b ^ (w - 1) := by
  rw [Real.rpow_sub hb, Real.rpow_one]
  field_simp [hb.ne']

/-- For `z ≥ 1` and `u, v ≥ 0`:
`(u + v) ^ z ≤ 3 ^ (z - 1) * u ^ z + (3 / 2) ^ (z - 1) * v ^ z`. -/
lemma p2m_hole_conv {z u v : ℝ} (hz : 1 ≤ z) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (u + v) ^ z ≤ (3 : ℝ) ^ (z - 1) * u ^ z + (3 / 2 : ℝ) ^ (z - 1) * v ^ z := by
  have hconv : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ ↦ t ^ z) := convexOn_rpow hz
  obtain ⟨_, hconv'⟩ := hconv
  have h3u : (3 : ℝ) * u ∈ Set.Ici 0 := (Set.mem_Ici).mpr (by positivity)
  have h32v : (3 / 2 : ℝ) * v ∈ Set.Ici 0 := (Set.mem_Ici).mpr (by positivity)
  have hcvx : (fun t : ℝ ↦ t ^ z) ((1 / 3 : ℝ) • (3 * u) + (2 / 3 : ℝ) • ((3 / 2 : ℝ) * v)) ≤
      (1 / 3 : ℝ) • (fun t : ℝ ↦ t ^ z) (3 * u) + (2 / 3 : ℝ) • (fun t : ℝ ↦ t ^ z) ((3 / 2 : ℝ) * v) :=
    hconv' h3u h32v (a := (1 / 3 : ℝ)) (b := (2 / 3 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hcomb : ((1 / 3 : ℝ) • (3 * u) + (2 / 3 : ℝ) • ((3 / 2 : ℝ) * v) : ℝ) = u + v := by
    rw [smul_eq_mul, smul_eq_mul]
    ring
  have hseg : (u + v) ^ z ≤ (1 / 3 : ℝ) * ((3 : ℝ) * u) ^ z + (2 / 3 : ℝ) * ((3 / 2 : ℝ) * v) ^ z := by
    calc
      (u + v) ^ z = ((1 / 3 : ℝ) • (3 * u) + (2 / 3 : ℝ) • ((3 / 2 : ℝ) * v)) ^ z := by
        simp only [hcomb]
      _ ≤ (1 / 3 : ℝ) • (fun t : ℝ ↦ t ^ z) (3 * u) + (2 / 3 : ℝ) • (fun t : ℝ ↦ t ^ z) ((3 / 2 : ℝ) * v) :=
        hcvx
      _ = (1 / 3 : ℝ) * ((3 : ℝ) * u) ^ z + (2 / 3 : ℝ) * ((3 / 2 : ℝ) * v) ^ z := by
        simp [smul_eq_mul]
  have hA : (1 / 3 : ℝ) * ((3 : ℝ) * u) ^ z = (3 : ℝ) ^ (z - 1) * u ^ z := by
    calc
      (1 / 3 : ℝ) * ((3 : ℝ) * u) ^ z = (1 / 3 : ℝ) * (3 ^ z * u ^ z) := by
        rw [Real.mul_rpow (by norm_num : 0 ≤ (3 : ℝ)) hu]
      _ = ((1 / 3 : ℝ) * 3 ^ z) * u ^ z := by ring
      _ = (3 : ℝ) ^ (z - 1) * u ^ z := by rw [p2m_hole_scalar (by norm_num : 0 < (3 : ℝ)) z]
  have hB : (2 / 3 : ℝ) * ((3 / 2 : ℝ) * v) ^ z = (3 / 2 : ℝ) ^ (z - 1) * v ^ z := by
    calc
      (2 / 3 : ℝ) * ((3 / 2 : ℝ) * v) ^ z = (2 / 3 : ℝ) * ((3 / 2 : ℝ) ^ z * v ^ z) := by
        rw [Real.mul_rpow (by norm_num : 0 ≤ (3 / 2 : ℝ)) hv]
      _ = ((2 / 3 : ℝ) * (3 / 2 : ℝ) ^ z) * v ^ z := by ring
      _ = (3 / 2 : ℝ) ^ (z - 1) * v ^ z := by
        rw [show (2 / 3 : ℝ) = 1 / (3 / 2 : ℝ) by norm_num, p2m_hole_scalar (by norm_num : 0 < (3 / 2 : ℝ)) z]
  rw [hA, hB] at hseg
  exact hseg

theorem solution {V : Type u} [inst : MetricSpace V] (z : ℝ) (hz : (1 : ℝ) ≤ z) (x a y : V) :
  dist x y ^ z ≤ (3 : ℝ) ^ (z - (1 : ℝ)) * dist x a ^ z + (3 / 2 : ℝ) ^ (z - (1 : ℝ)) * dist a y ^ z := by
  set u := dist x a with hu
  set v := dist a y with hv
  have hu0 : 0 ≤ u := by
    rw [hu]
    exact dist_nonneg
  have hv0 : 0 ≤ v := by
    rw [hv]
    exact dist_nonneg
  have hxay : 0 ≤ dist x y := by
    exact dist_nonneg
  have htri : dist x y ≤ u + v := by
    rw [hu, hv]
    exact dist_triangle x a y
  have hmon : dist x y ^ z ≤ (u + v) ^ z := Real.rpow_le_rpow hxay htri (by linarith)
  have hseg : (u + v) ^ z ≤ (3 : ℝ) ^ (z - 1) * u ^ z + (3 / 2 : ℝ) ^ (z - 1) * v ^ z :=
    p2m_hole_conv hz hu0 hv0
  calc
    dist x y ^ z ≤ (u + v) ^ z := hmon
    _ ≤ (3 : ℝ) ^ (z - 1) * u ^ z + (3 / 2 : ℝ) ^ (z - 1) * v ^ z := hseg
    _ = (3 : ℝ) ^ (z - (1 : ℝ)) * dist x a ^ z + (3 / 2 : ℝ) ^ (z - (1 : ℝ)) * dist a y ^ z := by
      rw [hu, hv]
end P2MHole01_25bd8837

-- riskiest
/-- Pointwise triangle bound, the content of Lemma 3.4: for any three points `x, a, y` of a
metric space and any `z ≥ 1`,
`dist x y ^ z ≤ 3^{z−1} · dist x a ^ z + (3/2)^{z−1} · dist a y ^ z`.
Proof idea: triangle inequality `dist x y ≤ dist x a + dist a y`, then the scalar convexity
fact `3^{z−1} w^z + (3/2)^{z−1} (1−w)^z ≥ 1` on `[0,1]` (convex, minimum `1` at `w = 2/3`)
with `w = dist x a / (dist x a + dist a y)`; the case `dist x a + dist a y = 0` is trivial. -/
theorem h_pointwise {V : Type u} [MetricSpace V] (z : ℝ) (hz : 1 ≤ z) (x a y : V) :
    dist x y ^ z ≤ (3 : ℝ) ^ (z - 1) * dist x a ^ z + ((3 : ℝ) / 2) ^ (z - 1) * dist a y ^ z := by
  (first | exact P2MHole01_25bd8837.solution z hz x a y | (apply P2MHole01_25bd8837.solution <;> assumption))

/-- Lemma 3.4 (Triangle bound), printed p. 8 / PDF p. 10: every block, with any representative and
any slot locations, is `(3^{z−1}, (3/2)^{z−1})`-movable. -/
theorem solution (V : Type u) [MetricSpace V] (z : ℝ) (hz : 1 ≤ z) (F : Set V) {ι : Type v}
    (Q : Finset ι) (pt : ι → V) (a : V) :
    IsMovable z ((3 : ℝ) ^ (z - 1)) (((3 : ℝ) / 2) ^ (z - 1)) F Q pt a := by
  dsimp only [IsMovable]
  refine ⟨?_, ?_, ?_⟩
  · -- 1 ≤ 3^{z−1} since z − 1 ≥ 0
    exact Real.one_le_rpow (by norm_num) (sub_nonneg.mpr hz)
  · -- 0 ≤ (3/2)^{z−1}
    exact Real.rpow_nonneg (by norm_num) (z - 1)
  · -- any bijection works (take `Q.equivFin`): the bound is termwise
    intro y hy
    refine ⟨Q.equivFin, ?_⟩
    have hm : (3 : ℝ) ^ (z - 1) * ∑ q ∈ Q, dist (pt q) a ^ z =
        (3 : ℝ) ^ (z - 1) * ∑ i ∈ Q.attach, dist (pt ↑i) a ^ z := by
      rw [← Finset.sum_attach]
    rw [hm, Finset.sum_coe_sort_eq_attach, Finset.sum_coe_sort_eq_attach,
        Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => h_pointwise z hz (pt i) a (y (Q.equivFin i)))
