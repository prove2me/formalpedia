-- Prove2me | solution 1 for DbarRegularity.dyadic_closedCube_subset
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T23:42:25.986977+00:00
-- url     : https://prove2.me/submissions/4e7537e4-9908-4a55-8568-d625525a3355

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Covering.Differentiation
import Mathlib.MeasureTheory.Covering.Vitali



namespace DbarRegularity

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal

theorem closedCube_eq_preimage {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    closedCube a s = (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)) ⁻¹'
      Icc (fun i => a i) (fun i => a i + s) := by
  ext x
  simp [closedCube, Pi.le_def, forall_and]

theorem volume_closedCube {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    volume (closedCube a s) = ENNReal.ofReal s ^ d := by
  rw [closedCube_eq_preimage, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  simp

theorem interior_closedCube {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    interior (closedCube a s) = {x | ∀ i, a i < x i ∧ x i < a i + s} := by
  have h : closedCube a s = (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹'
      (Set.pi univ fun i => Icc (a i) (a i + s)) := by
    ext x; simp [closedCube, PiLp.homeomorph, Pi.le_def, forall_and]
  rw [h, ← Homeomorph.preimage_interior, interior_pi_set finite_univ]
  ext x; simp [PiLp.homeomorph]

theorem isClosed_closedCube {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    IsClosed (closedCube a s) := by
  rw [closedCube_eq_preimage]
  exact isClosed_Icc.preimage (PiLp.continuous_ofLp 2 _)

end DbarRegularity

namespace DbarRegularity

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal

theorem dist_le_of_mem_closedCube {d : ℕ} {a x y : EuclideanSpace ℝ (Fin d)} {s : ℝ}
    (hx : x ∈ closedCube a s) (hy : y ∈ closedCube a s) : dist y x ≤ Real.sqrt d * s := by
  have hc : ∀ i, dist (y i) (x i) ^ 2 ≤ s ^ 2 := by
    intro i
    have h1 := hx i; have h2 := hy i
    rw [Real.dist_eq, sq_abs]
    nlinarith
  rw [EuclideanSpace.dist_eq]
  calc Real.sqrt (∑ i, dist (y i) (x i) ^ 2) ≤ Real.sqrt (∑ _i : Fin d, s ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => hc i)
    _ = Real.sqrt d * s := by
        rcases Nat.eq_zero_or_pos d with rfl | hd
        · simp
        · have hs : 0 ≤ s := by
            have h1 := hx ⟨0, hd⟩; linarith
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hs]

theorem volume_closedBall_le_cube {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) {ρ : ℝ} :
    volume (closedBall x ρ) ≤ ENNReal.ofReal (2 * ρ) ^ d := by
  rw [← volume_closedCube (WithLp.toLp 2 fun i => x i - ρ)]
  refine measure_mono fun y hy i => ?_
  have h := (PiLp.dist_apply_le y x i).trans (mem_closedBall.1 hy)
  rw [Real.dist_eq, abs_le] at h
  simp only [PiLp.toLp_apply]
  constructor <;> linarith

theorem ae_tendsto_average_closedCube {d : ℕ} {E : Type*} [NormedAddCommGroup E]
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

theorem dyadic_closedCube_subset {d : ℕ} {h H : ℝ} (hh : 0 < h) {N : ℕ} (hH : H = N * h)
    (z w : Fin d → ℤ)
    (hne : (interior (closedCube (WithLp.toLp 2 fun i => (z i : ℝ) * h) h) ∩
      interior (closedCube (WithLp.toLp 2 fun i => (w i : ℝ) * H) H)).Nonempty) :
    closedCube (WithLp.toLp 2 fun i => (z i : ℝ) * h) h ⊆
      closedCube (WithLp.toLp 2 fun i => (w i : ℝ) * H) H := by
  obtain ⟨y, hy1, hy2⟩ := hne
  rw [interior_closedCube] at hy1 hy2
  intro x hx i
  have a := hy1 i
  have b := hy2 i
  have c := hx i
  simp only [PiLp.toLp_apply] at a b c ⊢
  subst hH
  have h1 : w i * (N : ℤ) < z i + 1 := by
    have : ((w i : ℝ) * N) * h < ((z i : ℝ) + 1) * h := by linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hh.le
  have h2 : z i < (w i + 1) * (N : ℤ) := by
    have : (z i : ℝ) * h < ((w i : ℝ) + 1) * N * h := by linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hh.le
  have h1' : ((w i : ℝ) * N) ≤ z i := by exact_mod_cast (show w i * (N : ℤ) ≤ z i by omega)
  have h2' : (z i : ℝ) + 1 ≤ ((w i : ℝ) + 1) * N := by
    exact_mod_cast (show z i + 1 ≤ (w i + 1) * (N : ℤ) by omega)
  have e1 := mul_le_mul_of_nonneg_right h1' hh.le
  have e2 := mul_le_mul_of_nonneg_right h2' hh.le
  constructor <;> nlinarith

end DbarRegularity

open DbarRegularity

theorem solution {d : ℕ} {h H : ℝ} (hh : 0 < h) {N : ℕ} (hH : H = N * h)
    (z w : Fin d → ℤ)
    (hne : (interior (closedCube (WithLp.toLp 2 fun i => (z i : ℝ) * h) h) ∩
      interior (closedCube (WithLp.toLp 2 fun i => (w i : ℝ) * H) H)).Nonempty) :
    closedCube (WithLp.toLp 2 fun i => (z i : ℝ) * h) h ⊆
      closedCube (WithLp.toLp 2 fun i => (w i : ℝ) * H) H :=
  dyadic_closedCube_subset hh hH z w hne
