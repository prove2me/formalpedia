-- Prove2me | solution 1 for BFWFluidLimit.integral_sum_sq_average_add_le
-- status  : ACCEPTED   (prove)
-- author  : @wfe2017
-- created : 2026-11-20T11:13:53.435952+00:00
-- url     : https://prove2.me/submissions/4a08a694-b131-457d-adf0-1e8a315b8cbf

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic
set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace BFWFluidLimit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- A past-measurable square-integrable random variable is orthogonal to a
square-integrable innovation whose conditional expectation given that past is zero. -/
theorem integral_mul_eq_zero_of_condExp_eq_zero [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfmeas : AEStronglyMeasurable[m] f μ)
    (hgzero : μ[g | m] =ᵐ[μ] 0) :
    ∫ ω, f ω * g ω ∂μ = 0 := by
  calc
    ∫ ω, f ω * g ω ∂μ = ∫ ω, μ[f * g | m] ω ∂μ :=
      (integral_condExp hm).symm
    _ = ∫ ω, f ω * μ[g | m] ω ∂μ :=
      integral_congr_ae (condExp_mul_of_aestronglyMeasurable_left
        hfmeas (hf.integrable_mul hg) (hg.integrable (by norm_num)))
    _ = ∫ ω, (0 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hgzero] with ω hω
      simp [hω]
    _ = 0 := by simp

/-- Pythagoras for a finite collection of pairwise orthogonal real random variables. -/
theorem integral_sq_finsetSum_eq_sum_integral_sq {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Ω → ℝ) (hf : ∀ i ∈ s, MemLp (f i) 2 μ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∫ ω, f i ω * f j ω ∂μ = 0) :
    ∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂μ = ∑ i ∈ s, ∫ ω, (f i ω) ^ 2 ∂μ := by
  calc
    ∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂μ =
        ∫ ω, ∑ i ∈ s, ∑ j ∈ s, f i ω * f j ω ∂μ := by
      congr 1
      funext ω
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ i ∈ s, ∑ j ∈ s, ∫ ω, f i ω * f j ω ∂μ := by
      rw [integral_finsetSum s (f := fun i ω => ∑ j ∈ s, f i ω * f j ω)
        (fun i hi => integrable_finsetSum s
          (f := fun j ω => f i ω * f j ω)
          (fun j hj => (hf i hi).integrable_mul (hf j hj)))]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum s (fun j hj => (hf i hi).integrable_mul (hf j hj))
    _ = ∑ i ∈ s, ∫ ω, (f i ω) ^ 2 ∂μ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single i]
      · simp only [pow_two]
      · intro j hj hji
        exact horth i hi j hj hji.symm
      · intro h
        exact (h hi).elim

/-- The empirical mean of orthogonal innovations with uniformly bounded second
moments has mean square at most `C / K`. No independence is assumed here. -/
theorem integral_sq_average_le (K : ℕ) (hK : 0 < K) (f : ℕ → Ω → ℝ)
    (hf : ∀ i < K, MemLp (f i) 2 μ)
    (horth : ∀ i < K, ∀ j < K, i ≠ j → ∫ ω, f i ω * f j ω ∂μ = 0)
    (C : ℝ) (hbound : ∀ i < K, ∫ ω, (f i ω) ^ 2 ∂μ ≤ C) :
    ∫ ω, ((∑ i ∈ Finset.range K, f i ω) / K) ^ 2 ∂μ ≤ C / K := by
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  simp_rw [div_pow]
  rw [integral_div,
    integral_sq_finsetSum_eq_sum_integral_sq (Finset.range K) f
      (by simpa using hf) (by simpa using horth)]
  calc
    (∑ i ∈ Finset.range K, ∫ ω, (f i ω) ^ 2 ∂μ) / (K : ℝ) ^ 2
        ≤ ((K : ℝ) * C) / (K : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      calc
        ∑ i ∈ Finset.range K, ∫ ω, (f i ω) ^ 2 ∂μ
            ≤ ∑ _i ∈ Finset.range K, C :=
          Finset.sum_le_sum (fun i hi => hbound i (Finset.mem_range.mp hi))
        _ = (K : ℝ) * C := by simp
    _ = C / K := by field_simp

/-- Conditional mean-zero innovations satisfy the orthogonality assumptions
needed above. `past j` is the information available before innovation `j`.
Earlier innovations must be measurable with respect to that information. -/
theorem integral_sq_average_martingaleDifference_le [IsFiniteMeasure μ]
    (K : ℕ) (hK : 0 < K) (z : ℕ → Ω → ℝ)
    (past : ℕ → MeasurableSpace Ω) (hpast : ∀ j < K, past j ≤ mΩ)
    (hz : ∀ i < K, MemLp (z i) 2 μ)
    (hadapted : ∀ i < K, ∀ j < K, i < j → AEStronglyMeasurable[past j] (z i) μ)
    (hzero : ∀ j < K, μ[z j | past j] =ᵐ[μ] 0)
    (C : ℝ) (hbound : ∀ i < K, ∫ ω, (z i ω) ^ 2 ∂μ ≤ C) :
    ∫ ω, ((∑ i ∈ Finset.range K, z i ω) / K) ^ 2 ∂μ ≤ C / K := by
  apply integral_sq_average_le K hK z hz _ C hbound
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact integral_mul_eq_zero_of_condExp_eq_zero (hpast j hj)
      (hz i hi) (hz j hj) (hadapted i hi j hj hlt) (hzero j hj)
  · have h := integral_mul_eq_zero_of_condExp_eq_zero (hpast i hi)
      (hz j hj) (hz i hi) (hadapted j hj i hi hgt) (hzero i hi)
    simpa only [mul_comm] using h

/-- Two components can be estimated separately even when they are mutually
dependent. This is the factor-two estimate used for exploration initialization. -/
theorem integral_sq_add_le_two {f g : Ω → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) :
    ∫ ω, (f ω + g ω) ^ 2 ∂μ ≤
      2 * ((∫ ω, (f ω) ^ 2 ∂μ) + ∫ ω, (g ω) ^ 2 ∂μ) := by
  calc
    ∫ ω, (f ω + g ω) ^ 2 ∂μ
        ≤ ∫ ω, 2 * ((f ω) ^ 2 + (g ω) ^ 2) ∂μ := by
      apply integral_mono (hf.add hg).integrable_sq
        ((hf.integrable_sq.add hg.integrable_sq).const_mul 2)
      intro ω
      exact add_sq_le
    _ = 2 * ((∫ ω, (f ω) ^ 2 ∂μ) + ∫ ω, (g ω) ^ 2 ∂μ) := by
      rw [integral_const_mul, integral_add hf.integrable_sq hg.integrable_sq]

/-- A sum of two separately orthogonal arrays has an `O(1/K)` initialization
bound. Cross-orthogonality between the arrays is deliberately not required. -/
theorem integral_sq_average_add_le (K : ℕ) (hK : 0 < K)
    (a z : ℕ → Ω → ℝ)
    (ha : ∀ i < K, MemLp (a i) 2 μ)
    (hz : ∀ i < K, MemLp (z i) 2 μ)
    (haorth : ∀ i < K, ∀ j < K, i ≠ j → ∫ ω, a i ω * a j ω ∂μ = 0)
    (hzorth : ∀ i < K, ∀ j < K, i ≠ j → ∫ ω, z i ω * z j ω ∂μ = 0)
    (A Z : ℝ)
    (habound : ∀ i < K, ∫ ω, (a i ω) ^ 2 ∂μ ≤ A)
    (hzbound : ∀ i < K, ∫ ω, (z i ω) ^ 2 ∂μ ≤ Z) :
    ∫ ω, ((∑ i ∈ Finset.range K, (a i ω + z i ω)) / K) ^ 2 ∂μ
      ≤ 2 * (A + Z) / K := by
  have haavg : MemLp (fun ω => (∑ i ∈ Finset.range K, a i ω) / K) 2 μ := by
    simpa [div_eq_mul_inv] using
      (memLp_finsetSum (Finset.range K)
        (fun i hi => ha i (Finset.mem_range.mp hi))).mul_const (K : ℝ)⁻¹
  have hzavg : MemLp (fun ω => (∑ i ∈ Finset.range K, z i ω) / K) 2 μ := by
    simpa [div_eq_mul_inv] using
      (memLp_finsetSum (Finset.range K)
        (fun i hi => hz i (Finset.mem_range.mp hi))).mul_const (K : ℝ)⁻¹
  simp_rw [Finset.sum_add_distrib, add_div]
  calc
    ∫ ω, ((∑ i ∈ Finset.range K, a i ω) / K +
        (∑ i ∈ Finset.range K, z i ω) / K) ^ 2 ∂μ
        ≤ 2 * ((∫ ω, ((∑ i ∈ Finset.range K, a i ω) / K) ^ 2 ∂μ) +
          ∫ ω, ((∑ i ∈ Finset.range K, z i ω) / K) ^ 2 ∂μ) :=
      integral_sq_add_le_two haavg hzavg
    _ ≤ 2 * (A / K + Z / K) := by
      gcongr
      · exact integral_sq_average_le K hK a ha haorth A habound
      · exact integral_sq_average_le K hK z hz hzorth Z hzbound
    _ = 2 * (A + Z) / K := by ring

/-- The same initialization estimate for a finite vector, expressed as a sum
of coordinate squares (the squared Euclidean norm). -/
theorem integral_sum_sq_average_add_le {d : Type*} [Fintype d]
    (K : ℕ) (hK : 0 < K) (a z : d → ℕ → Ω → ℝ)
    (ha : ∀ j i, i < K → MemLp (a j i) 2 μ)
    (hz : ∀ j i, i < K → MemLp (z j i) 2 μ)
    (haorth : ∀ j i, i < K → ∀ l, l < K → i ≠ l →
      ∫ ω, a j i ω * a j l ω ∂μ = 0)
    (hzorth : ∀ j i, i < K → ∀ l, l < K → i ≠ l →
      ∫ ω, z j i ω * z j l ω ∂μ = 0)
    (A Z : d → ℝ)
    (habound : ∀ j i, i < K → ∫ ω, (a j i ω) ^ 2 ∂μ ≤ A j)
    (hzbound : ∀ j i, i < K → ∫ ω, (z j i ω) ^ 2 ∂μ ≤ Z j) :
    ∫ ω, (∑ j, ((∑ i ∈ Finset.range K, (a j i ω + z j i ω)) / K) ^ 2) ∂μ
      ≤ 2 * (∑ j, (A j + Z j)) / K := by
  classical
  have havg (j : d) : MemLp
      (fun ω => (∑ i ∈ Finset.range K, (a j i ω + z j i ω)) / K) 2 μ := by
    simpa [div_eq_mul_inv] using
      (memLp_finsetSum (Finset.range K)
        (fun i hi => (ha j i (Finset.mem_range.mp hi)).add
          (hz j i (Finset.mem_range.mp hi)))).mul_const (K : ℝ)⁻¹
  rw [integral_finsetSum Finset.univ (fun j _ => (havg j).integrable_sq)]
  calc
    ∑ j, ∫ ω, ((∑ i ∈ Finset.range K, (a j i ω + z j i ω)) / K) ^ 2 ∂μ
        ≤ ∑ j, 2 * (A j + Z j) / K := by
      apply Finset.sum_le_sum
      intro j _
      exact integral_sq_average_add_le K hK (a j) (z j) (ha j) (hz j)
        (haorth j) (hzorth j) (A j) (Z j) (habound j) (hzbound j)
    _ = 2 * (∑ j, (A j + Z j)) / K := by
      rw [← Finset.sum_div, Finset.mul_sum]

end BFWFluidLimit
open BFWFluidLimit
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
theorem solution {d : Type*} [Fintype d]
    (K : ℕ) (hK : 0 < K) (a z : d → ℕ → Ω → ℝ)
    (ha : ∀ j i, i < K → MemLp (a j i) 2 μ)
    (hz : ∀ j i, i < K → MemLp (z j i) 2 μ)
    (haorth : ∀ j i, i < K → ∀ l, l < K → i ≠ l →
      ∫ ω, a j i ω * a j l ω ∂μ = 0)
    (hzorth : ∀ j i, i < K → ∀ l, l < K → i ≠ l →
      ∫ ω, z j i ω * z j l ω ∂μ = 0)
    (A Z : d → ℝ)
    (habound : ∀ j i, i < K → ∫ ω, (a j i ω) ^ 2 ∂μ ≤ A j)
    (hzbound : ∀ j i, i < K → ∫ ω, (z j i ω) ^ 2 ∂μ ≤ Z j) :
    ∫ ω, (∑ j, ((∑ i ∈ Finset.range K, (a j i ω + z j i ω)) / K) ^ 2) ∂μ
      ≤ 2 * (∑ j, (A j + Z j)) / K := by
  exact BFWFluidLimit.integral_sum_sq_average_add_le K hK a z ha hz haorth hzorth A Z habound hzbound
