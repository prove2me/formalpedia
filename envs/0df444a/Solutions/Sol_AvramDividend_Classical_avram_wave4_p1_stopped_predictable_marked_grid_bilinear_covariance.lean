-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_stopped_predictable_marked_grid_bilinear_covariance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:08:17.866483+00:00
-- url     : https://prove2.me/submissions/761fd1a4-2523-408c-8fa0-e4f291b983f7

import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_stopped_predictable_marked_finite_grid_l2_isometry
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators
/-- Polarize the actual stopped finite-grid marked-Poisson L² isometry.
The three mark profiles are f, g, f+g, with filtration-relative joint
past/future independence for each of their full accumulated prefixes. -/
theorem solution {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure E) [IsProbabilityMeasure ν] (H : ℕ → Ω → ℝ) (τ : Ω → ℕ) (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E) (r : ℕ → ℝ≥0) (F : Fin 3 → ℕ → E → ℝ) (hFadd : ∀ i z, F 2 i z = F 0 i z + F 1 i z) (hKm : ∀ i, Measurable (K i)) (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) μ) (hYm : ∀ i n, Measurable (Y i n)) (hYL : ∀ i n, HasLaw (Y i n) ν μ) (hYi : ∀ i, iIndepFun (Y i) μ) (hCountMarks : ∀ i, IndepFun (K i) (fun ω (n : ℕ) => Y i n ω) μ) (hWm : ∀ i, Measurable (fun ω => if i < τ ω then H i ω else 0)) (hW2 : ∀ i, Integrable (fun ω => (if i < τ ω then H i ω else 0) ^ 2) μ) (hPast : ∀ i, IndepFun (fun ω => if i < τ ω then H i ω else 0) (fun ω => (K i ω, fun n : ℕ => Y i n ω)) μ) (hFm : ∀ a i, Measurable (F a i)) (hFI : ∀ a i, Integrable (F a i) ν) (hF2 : ∀ a i, MemLp (F a i) 2 ν) (hIncMeas : ∀ a i, Measurable (fun ω => (if i < τ ω then H i ω else 0) * ((∑ n ∈ Finset.range (K i ω), F a i (Y i n ω)) - (r i : ℝ) * ∫ z, F a i z ∂ν))) (hPrefixMeas : ∀ a i, Measurable (fun ω => ∑ j ∈ Finset.range i, (if j < τ ω then H j ω else 0) * ((∑ n ∈ Finset.range (K j ω), F a j (Y j n ω)) - (r j : ℝ) * ∫ z, F a j z ∂ν))) (hJointPast : ∀ a i, IndepFun (fun ω => ((∑ j ∈ Finset.range i, (if j < τ ω then H j ω else 0) * ((∑ n ∈ Finset.range (K j ω), F a j (Y j n ω)) - (r j : ℝ) * ∫ z, F a j z ∂ν)), if i < τ ω then H i ω else 0)) (fun ω => (K i ω, fun n : ℕ => Y i n ω)) μ) (m : ℕ) : let S : Fin 3 → Ω → ℝ := fun a ω => ∑ i ∈ Finset.range m, (if i < τ ω then H i ω else 0) * ((∑ n ∈ Finset.range (K i ω), F a i (Y i n ω)) - (r i : ℝ) * ∫ z, F a i z ∂ν)
    Integrable (fun ω => S 0 ω * S 1 ω) μ ∧ (∫ ω, S 0 ω * S 1 ω ∂μ) = ∑ i ∈ Finset.range m, (∫ ω, (if i < τ ω then H i ω else 0) ^ 2 ∂μ) * ((r i : ℝ) * ∫ z, F 0 i z * F 1 i z ∂ν) := by
  classical
  let W : ℕ → Ω → ℝ := fun i ω => if i < τ ω then H i ω else 0
  let Z : Fin 3 → ℕ → Ω → ℝ := fun a i ω => W i ω * ((∑ n ∈ Finset.range (K i ω), F a i (Y i n ω)) - (r i : ℝ) * ∫ z, F a i z ∂ν)
  let S : Fin 3 → Ω → ℝ := fun a ω => ∑ i ∈ Finset.range m, Z a i ω
  change Integrable (fun ω => S 0 ω * S 1 ω) μ ∧ (∫ ω, S 0 ω * S 1 ω ∂μ) = ∑ i ∈ Finset.range m, (∫ ω, W i ω ^ 2 ∂μ) * ((r i : ℝ) * ∫ z, F 0 i z * F 1 i z ∂ν)
  have hIso (a : Fin 3) : Integrable (fun ω => S a ω ^ 2) μ ∧ (∫ ω, S a ω ^ 2 ∂μ) = ∑ i ∈ Finset.range m, (∫ ω, W i ω ^ 2 ∂μ) * ((r i : ℝ) * ∫ z, F a i z ^ 2 ∂ν) := by
    exact avram_wave4_p1_stopped_predictable_marked_finite_grid_l2_isometry
      μ ν H τ K Y r (F a) hKm hKlaw hYm hYL hYi
      hCountMarks hWm hW2 hPast (hFm a) (hFI a) (hF2 a)
      (hIncMeas a) (hPrefixMeas a) (hJointPast a) m
  have hMeanAdd (i : ℕ) : (∫ z, F 2 i z ∂ν) = (∫ z, F 0 i z ∂ν) + (∫ z, F 1 i z ∂ν) := by
    calc
      _ = (∫ z, F 0 i z + F 1 i z ∂ν) := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact hFadd i z
      _ = _ := by
        simpa only [Pi.add_apply] using integral_add (hFI 0 i) (hFI 1 i)
  have hZadd (i : ℕ) (ω : Ω) : Z 2 i ω = Z 0 i ω + Z 1 i ω := by
    have hMarks : (∑ n ∈ Finset.range (K i ω), F 2 i (Y i n ω)) = (∑ n ∈ Finset.range (K i ω), F 0 i (Y i n ω)) + (∑ n ∈ Finset.range (K i ω), F 1 i (Y i n ω)) := by
      calc
        _ = ∑ n ∈ Finset.range (K i ω),
              (F 0 i (Y i n ω) + F 1 i (Y i n ω)) := by
                apply Finset.sum_congr rfl
                intro n hn
                exact hFadd i (Y i n ω)
        _ = _ := Finset.sum_add_distrib
    dsimp [Z]
    rw [hMarks, hMeanAdd i]
    ring
  have hSadd (ω : Ω) : S 2 ω = S 0 ω + S 1 ω := by
    change (∑ i ∈ Finset.range m, Z 2 i ω) =
      (∑ i ∈ Finset.range m, Z 0 i ω) +
        (∑ i ∈ Finset.range m, Z 1 i ω)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact hZadd i ω
  have hProductPoint : (fun ω => S 0 ω * S 1 ω) = (fun ω => (1 / 2 : ℝ) * ((S 2 ω) ^ 2 - (S 0 ω) ^ 2 - (S 1 ω) ^ 2)) := by
    funext ω
    rw [hSadd ω]
    ring
  have hProductInt : Integrable (fun ω => S 0 ω * S 1 ω) μ := by
    rw [hProductPoint]
    exact (((hIso 2).1.sub (hIso 0).1).sub (hIso 1).1).const_mul (1 / 2 : ℝ)
  have hMark (i : ℕ) : (∫ z, F 2 i z ^ 2 ∂ν) - (∫ z, F 0 i z ^ 2 ∂ν) - (∫ z, F 1 i z ^ 2 ∂ν) = 2 * (∫ z, F 0 i z * F 1 i z ∂ν) := by
    have hFG : Integrable (fun z => F 0 i z * F 1 i z) ν := by
      have h := (hF2 0 i).integrable_mul (hF2 1 i)
      have hEq : (fun z => F 0 i z * F 1 i z) =
          (F 0 i) * (F 1 i) := by
        funext z
        rfl
      rw [hEq]
      exact h
    have h0 : Integrable (fun z => F 0 i z ^ 2) ν :=
      (memLp_two_iff_integrable_sq (hFm 0 i).aestronglyMeasurable).1 (hF2 0 i)
    have h1 : Integrable (fun z => F 1 i z ^ 2) ν :=
      (memLp_two_iff_integrable_sq (hFm 1 i).aestronglyMeasurable).1 (hF2 1 i)
    have hDouble : Integrable (fun z => (2 : ℝ) * (F 0 i z * F 1 i z)) ν :=
      hFG.const_mul 2
    have hInner :
        (∫ z, F 0 i z ^ 2 + 2 * (F 0 i z * F 1 i z) ∂ν) =
          (∫ z, F 0 i z ^ 2 ∂ν) +
            (∫ z, (2 : ℝ) * (F 0 i z * F 1 i z) ∂ν) := by
      simpa only [Pi.add_apply] using integral_add h0 hDouble
    have hOuter :
        (∫ z, (F 0 i z ^ 2 + 2 * (F 0 i z * F 1 i z)) +
            F 1 i z ^ 2 ∂ν) =
          (∫ z, F 0 i z ^ 2 + 2 * (F 0 i z * F 1 i z) ∂ν) +
            (∫ z, F 1 i z ^ 2 ∂ν) := by
      simpa only [Pi.add_apply] using integral_add (h0.add hDouble) h1
    have hExpand : (∫ z, F 2 i z ^ 2 ∂ν) = (∫ z, F 0 i z ^ 2 ∂ν) + 2 * (∫ z, F 0 i z * F 1 i z ∂ν) + (∫ z, F 1 i z ^ 2 ∂ν) := by
      calc
        _ = (∫ z, (F 0 i z ^ 2 + (2 : ℝ) *
             (F 0 i z * F 1 i z)) + F 1 i z ^ 2 ∂ν) := by
          apply integral_congr_ae
          filter_upwards [] with z
          rw [hFadd i z]
          ring
        _ = _ := by
          rw [hOuter, hInner, integral_const_mul]
    rw [hExpand]
    ring
  constructor
  · exact hProductInt
  · have hPolar :
        (∫ ω, S 0 ω * S 1 ω ∂μ) =
          (1 / 2 : ℝ) *
            ((∫ ω, S 2 ω ^ 2 ∂μ) -
              (∫ ω, S 0 ω ^ 2 ∂μ) -
                (∫ ω, S 1 ω ^ 2 ∂μ)) := by
      have hOuterSub :
          (∫ ω, (S 2 ω ^ 2 - S 0 ω ^ 2) - S 1 ω ^ 2 ∂μ) =
            (∫ ω, S 2 ω ^ 2 - S 0 ω ^ 2 ∂μ) -
              (∫ ω, S 1 ω ^ 2 ∂μ) := by
        simpa only [Pi.sub_apply] using
          integral_sub ((hIso 2).1.sub (hIso 0).1) (hIso 1).1
      have hInnerSub :
          (∫ ω, S 2 ω ^ 2 - S 0 ω ^ 2 ∂μ) =
            (∫ ω, S 2 ω ^ 2 ∂μ) -
              (∫ ω, S 0 ω ^ 2 ∂μ) := by
        simpa only [Pi.sub_apply] using integral_sub (hIso 2).1 (hIso 0).1
      rw [hProductPoint, integral_const_mul, hOuterSub, hInnerSub]
    rw [hPolar, (hIso 2).2, (hIso 0).2, (hIso 1).2]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = (∫ ω, W i ω ^ 2 ∂μ) * (r i : ℝ) *
            ((1 / 2 : ℝ) *
              ((∫ z, F 2 i z ^ 2 ∂ν) -
                (∫ z, F 0 i z ^ 2 ∂ν) -
                  (∫ z, F 1 i z ^ 2 ∂ν))) := by ring
      _ = _ := by
        rw [hMark i]
        ring