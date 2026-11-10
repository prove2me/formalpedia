-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_annulus15_finite_weight_L2_of_physical_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T17:34:31.389055+00:00
-- url     : https://prove2.me/submissions/a10039b3-22e8-4d90-a759-5a2fcbdc8eba

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators
noncomputable section
/-- Finite deterministic-weight L² isometry from physical moment certificates. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [DecidableEq ι] (s : Finset ι) (Y : ι → Ω → ℝ) (a r : ι → ℝ)
    (hDiag : ∀ i ∈ s, Integrable (fun ω => (Y i ω) ^ 2) P ∧
      (∫ ω, (Y i ω) ^ 2 ∂P) = r i)
    (hOff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Integrable (fun ω => Y i ω * Y j ω) P ∧
      (∫ ω, Y i ω * Y j ω ∂P) = 0) :
    Integrable (fun ω => (∑ i ∈ s, a i * Y i ω) ^ 2) P ∧
    (∫ ω, (∑ i ∈ s, a i * Y i ω) ^ 2 ∂P) =
      ∑ i ∈ s, (a i) ^ 2 * r i := by
  classical
  let K : ι → ι → Ω → ℝ := fun i j ω => (a i * a j) * (Y i ω * Y j ω)
  have hK (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      Integrable (K i j) P := by
    by_cases hij : i = j
    · subst j
      simpa only [K, pow_two] using ((hDiag i hi).1.const_mul (a i * a i))
    · exact (hOff i hi j hj hij).1.const_mul (a i * a j)
  have hInner (i : ι) (hi : i ∈ s) :
      Integrable (fun ω => ∑ j ∈ s, K i j ω) P :=
    integrable_finset_sum s (fun j hj => hK i hi j hj)
  have hDouble : Integrable (fun ω => ∑ i ∈ s, ∑ j ∈ s, K i j ω) P :=
    integrable_finset_sum s hInner
  have hPoly (ω : Ω) :
      (∑ i ∈ s, a i * Y i ω) ^ 2 = ∑ i ∈ s, ∑ j ∈ s, K i j ω := by
    calc
      _ = (∑ i ∈ s, a i * Y i ω) *
          (∑ j ∈ s, a j * Y j ω) := pow_two _
      _ = ∑ i ∈ s, ∑ j ∈ s, K i j ω := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [K]
        ring
  have hKI (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      (∫ ω, K i j ω ∂P) = if i = j then (a i) ^ 2 * r i else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [if_pos rfl]
      calc
        (∫ ω, K i i ω ∂P) =
            (a i * a i) * (∫ ω, (Y i ω) ^ 2 ∂P) := by
          rw [integral_const_mul]
          congr 1
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun ω => by ring)
        _ = (a i) ^ 2 * r i := by rw [(hDiag i hi).2]; ring
    · simp only [if_neg hij]
      change (∫ ω, (a i * a j) * (Y i ω * Y j ω) ∂P) = 0
      rw [integral_const_mul, (hOff i hi j hj hij).2, mul_zero]
  constructor
  · exact hDouble.congr (Filter.Eventually.of_forall (fun ω => (hPoly ω).symm))
  · calc
      (∫ ω, (∑ i ∈ s, a i * Y i ω) ^ 2 ∂P) =
          (∫ ω, ∑ i ∈ s, ∑ j ∈ s, K i j ω ∂P) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hPoly
      _ = ∑ i ∈ s, ∑ j ∈ s, (∫ ω, K i j ω ∂P) := by
            rw [integral_finset_sum s hInner]
            apply Finset.sum_congr rfl
            intro i hi
            rw [integral_finset_sum s (fun j hj => hK i hi j hj)]
      _ = ∑ i ∈ s, (a i) ^ 2 * r i := by
            apply Finset.sum_congr rfl
            intro i hi
            calc
              _ = ∑ j ∈ s, if i = j then (a i) ^ 2 * r i else 0 :=
                Finset.sum_congr rfl (fun j hj => hKI i hi j hj)
              _ = (a i) ^ 2 * r i := by simp [Finset.sum_ite_eq', hi]
