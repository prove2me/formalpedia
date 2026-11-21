-- Prove2me | solution 1 for FulfillFlex.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T03:16:24.623074+00:00
-- url     : https://prove2.me/submissions/9664f3b0-5368-45d9-b45d-527642163e74

import Mathlib

open MeasureTheory ProbabilityTheory

set_option maxHeartbeats 2000000

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hL2 : MemLp (X 0) 2 P) (T : ℕ) :
    Integrable (fun ω => max (∑ i ∈ Finset.range T, X i ω - T * ∫ ω', X 0 ω' ∂P) 0) P ∧
      ∫ ω, max (∑ i ∈ Finset.range T, X i ω - T * ∫ ω', X 0 ω' ∂P) 0 ∂P
        ≤ 1 / 2 * √(T : ℝ) * √(Var[X 0; P]) := by
  classical
  set μ : ℝ := ∫ ω, X 0 ω ∂P with hμ
  have hXi_memLp : ∀ i, MemLp (X i) 2 P := fun i => (hident i).memLp_iff.mpr hL2
  have hXi_int : ∀ i, Integrable (X i) P := fun i => (hXi_memLp i).integrable (by norm_num)
  have hXi_ae : ∀ i, AEMeasurable (X i) P := fun i => (hXi_memLp i).aemeasurable
  have hmean_eq : ∀ i, ∫ ω, X i ω ∂P = μ := fun i => (hident i).integral_eq
  -- the centred sum
  set S : Ω → ℝ := fun ω => ∑ i ∈ Finset.range T, X i ω - (T : ℝ) * μ with hS
  have hfn_eq : (∑ i ∈ Finset.range T, X i) = fun ω => ∑ i ∈ Finset.range T, X i ω := by
    funext ω
    exact Finset.sum_apply ω _ _
  have hsum_ae : AEMeasurable (fun ω => ∑ i ∈ Finset.range T, X i ω) P := by
    have h := Finset.aemeasurable_sum (Finset.range T) (f := X) (fun i _ => hXi_ae i)
    rwa [hfn_eq] at h
  have hsum_int : Integrable (fun ω => ∑ i ∈ Finset.range T, X i ω) P :=
    integrable_finset_sum _ (fun i _ => hXi_int i)
  have hS_ae : AEMeasurable S P := by
    rw [hS]
    exact hsum_ae.sub aemeasurable_const
  have hS_int : Integrable S P := by
    rw [hS]
    exact hsum_int.sub (integrable_const _)
  have hS_memLp : MemLp S 2 P := by
    rw [hS]
    have h1 : MemLp (fun ω => ∑ i ∈ Finset.range T, X i ω) 2 P := by
      have h := memLp_finsetSum' (s := Finset.range T) (f := X) (fun i _ => hXi_memLp i)
      rwa [hfn_eq] at h
    exact h1.sub (memLp_const _)
  -- expectation of S vanishes
  have hES : ∫ ω, S ω ∂P = 0 := by
    rw [hS]
    rw [integral_sub hsum_int (integrable_const _)]
    rw [integral_finsetSum (Finset.range T) (fun i _ => hXi_int i)]
    simp only [hmean_eq]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp
  -- variance of S
  have hVarS : variance S P = (T : ℝ) * variance (X 0) P := by
    have h1 : variance (fun ω => (∑ i ∈ Finset.range T, X i ω) - (T : ℝ) * μ) P
        = variance (fun ω => ∑ i ∈ Finset.range T, X i ω) P :=
      variance_sub_const hsum_ae.aestronglyMeasurable _
    have h2 : variance (fun ω => ∑ i ∈ Finset.range T, X i ω) P
        = ∑ i ∈ Finset.range T, variance (X i) P := by
      have h := IndepFun.variance_sum (μ := P) (s := Finset.range T) (X := X)
        (fun i _ => hXi_memLp i) (fun i _ j _ hij => hindep.indepFun hij)
      rw [← h]
      refine variance_congr (Filter.Eventually.of_forall (fun ω => ?_))
      exact (Finset.sum_apply ω _ _).symm
    have h3 : ∑ i ∈ Finset.range T, variance (X i) P
        = ∑ _i ∈ Finset.range T, variance (X 0) P :=
      Finset.sum_congr rfl (fun i _ => (hident i).variance_eq)
    have h4 : ∑ _i ∈ Finset.range T, variance (X 0) P = (T : ℝ) * variance (X 0) P := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc variance S P
        = variance (fun ω => (∑ i ∈ Finset.range T, X i ω) - (T : ℝ) * μ) P := by rw [hS]
      _ = variance (fun ω => ∑ i ∈ Finset.range T, X i ω) P := h1
      _ = ∑ i ∈ Finset.range T, variance (X i) P := h2
      _ = ∑ _i ∈ Finset.range T, variance (X 0) P := h3
      _ = (T : ℝ) * variance (X 0) P := h4
  -- second moment equals the variance
  have hES2 : ∫ ω, S ω ^ 2 ∂P = (T : ℝ) * variance (X 0) P := by
    have h := variance_eq_integral (X := S) hS_ae
    rw [hES] at h
    simp only [sub_zero] at h
    rw [hVarS] at h
    exact h.symm
  have hAbs_int : Integrable (fun ω => |S ω|) P := hS_int.abs
  have hSq_int : Integrable (fun ω => S ω ^ 2) P := hS_memLp.integrable_sq
  -- E|S| = 2 E S⁺
  have hAbsEq : ∫ ω, |S ω| ∂P = 2 * ∫ ω, max (S ω) 0 ∂P := by
    have h := integral_abs_eq_two_mul_integral_posPart_sub_integral hS_int
    rw [hES] at h
    have hpos : (fun ω => (S ω)⁺) = fun ω => max (S ω) 0 := by
      funext ω; rfl
    rw [hpos] at h
    simpa using h
  -- Cauchy-Schwarz via convexity of the square
  have hcs : (∫ ω, |S ω| ∂P) ^ 2 ≤ ∫ ω, S ω ^ 2 ∂P := by
    have hconv := ConvexOn.map_integral_le (μ := P) (s := Set.Ici (0 : ℝ))
      (f := fun ω => |S ω|) (g := fun x : ℝ => x ^ 2)
      (convexOn_pow 2) (continuousOn_pow (s := Set.Ici (0 : ℝ)) 2) isClosed_Ici
      (Filter.Eventually.of_forall (fun ω => Set.mem_Ici.mpr (abs_nonneg _)))
      hAbs_int
      (by
        have h : (fun ω => |S ω| ^ 2) = fun ω => S ω ^ 2 := by
          funext ω; rw [sq_abs]
        rw [Function.comp_def, h]
        exact hSq_int)
    simpa [Function.comp_def, sq_abs] using hconv
  have hAbs_nonneg : 0 ≤ ∫ ω, |S ω| ∂P := integral_nonneg (fun ω => abs_nonneg _)
  have hSqrt : ∫ ω, |S ω| ∂P ≤ √((T : ℝ) * variance (X 0) P) := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [← hES2]
    exact hcs
  refine ⟨?_, ?_⟩
  · -- integrability of the positive part
    refine Integrable.mono' hAbs_int ?_ ?_
    · exact (hS_ae.max aemeasurable_const).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      have h : max (S ω) 0 ≤ |S ω| := max_le (le_abs_self (S ω)) (abs_nonneg (S ω))
      simpa only [hS] using h
  · -- value bound
    have hgoal : (fun ω => max (∑ i ∈ Finset.range T, X i ω - T * ∫ ω', X 0 ω' ∂P) 0)
        = fun ω => max (S ω) 0 := by
      funext ω
      simp only [hS, hμ]
    rw [hgoal]
    have h1 : ∫ ω, max (S ω) 0 ∂P = 1 / 2 * ∫ ω, |S ω| ∂P := by
      rw [hAbsEq]; ring
    have h2 : (1 : ℝ) / 2 * ∫ ω, |S ω| ∂P
        ≤ 1 / 2 * √(T : ℝ) * √(Var[X 0; P]) := by
      have h3 : √((T : ℝ) * variance (X 0) P) = √(T : ℝ) * √(variance (X 0) P) := by
        rw [Real.sqrt_mul (show (0 : ℝ) ≤ (T : ℝ) by positivity)]
      have h4 : √(variance (X 0) P) = √(Var[X 0; P]) := rfl
      rw [← h4]
      nlinarith [hSqrt, Real.sqrt_nonneg (T : ℝ), Real.sqrt_nonneg (variance (X 0) P)]
    rw [h1]
    exact h2
