-- Prove2me | solution 1 for DetANN.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-14T01:01:44.192294+00:00
-- url     : https://prove2.me/submissions/10dab743-86fd-466b-a9d4-59f67de7e5f6

import Mathlib

open MeasureTheory

namespace DetANNLemma34Aux

variable {Ω F : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The bias–variance decomposition `E‖v − X‖² = ‖v − EX‖² + E‖X − EX‖²`. -/
theorem bias_var (X : Ω → F) (hX : MemLp X 2 μ) (v : F) :
    ∫ ω, ‖v - X ω‖ ^ 2 ∂μ = ‖v - ∫ ω, X ω ∂μ‖ ^ 2 + ∫ ω, ‖X ω - ∫ ω', X ω' ∂μ‖ ^ 2 ∂μ := by
  set m := ∫ ω, X ω ∂μ
  have hXi : Integrable X μ := hX.integrable (by norm_num)
  have hY : MemLp (fun ω => X ω - m) 2 μ := hX.sub (memLp_const m)
  have hYi : Integrable (fun ω => X ω - m) μ := hY.integrable (by norm_num)
  have hYsq : Integrable (fun ω => ‖X ω - m‖ ^ 2) μ := hY.integrable_norm_pow (by norm_num)
  have hinner : Integrable (fun ω => inner ℝ (v - m) (X ω - m)) μ := hYi.const_inner (v - m)
  have hpt : ∀ ω, ‖v - X ω‖ ^ 2 =
      ‖v - m‖ ^ 2 - 2 * inner ℝ (v - m) (X ω - m) + ‖X ω - m‖ ^ 2 := by
    intro ω
    have : v - X ω = (v - m) - (X ω - m) := by abel
    rw [this, norm_sub_sq_real]
  simp_rw [hpt]
  have h0 : ∫ ω, inner ℝ (v - m) (X ω - m) ∂μ = 0 := by
    rw [integral_inner hYi, integral_sub hXi (integrable_const m)]
    simp [m]
  have hA : Integrable (fun ω => ‖v - m‖ ^ 2 - 2 * inner ℝ (v - m) (X ω - m)) μ :=
    (integrable_const _).sub (hinner.const_mul 2)
  rw [integral_add hA hYsq, integral_sub (integrable_const _) (hinner.const_mul 2),
    integral_const_mul, h0]
  simp

end DetANNLemma34Aux

open DetANNLemma34Aux in
theorem solution {Ω F : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (X : Ω → F) (hX : MemLp X 2 μ) :
    ∫ ω, ‖X ω - ∫ ω', X ω' ∂μ‖ ^ 2 ∂μ = (1 / 2) * ∫ p, ‖X p.1 - X p.2‖ ^ 2 ∂(μ.prod μ) ∧
      ∀ v : F, ∫ ω, ‖v - X ω‖ ^ 2 ∂μ =
        ‖v - ∫ ω, X ω ∂μ‖ ^ 2 + ∫ ω, ‖X ω - ∫ ω', X ω' ∂μ‖ ^ 2 ∂μ := by
  refine ⟨?_, fun v => bias_var X hX v⟩
  set m := ∫ ω, X ω ∂μ
  set V := ∫ ω, ‖X ω - m‖ ^ 2 ∂μ
  have hY : MemLp (fun ω => X ω - m) 2 μ := hX.sub (memLp_const m)
  have hYsq : Integrable (fun ω => ‖X ω - m‖ ^ 2) μ := hY.integrable_norm_pow (by norm_num)
  -- inner integrals
  have hin : ∀ x, ∫ y, ‖X x - X y‖ ^ 2 ∂μ = ‖X x - m‖ ^ 2 + V := fun x => bias_var X hX (X x)
  have hinI : ∀ x, Integrable (fun y => ‖X x - X y‖ ^ 2) μ := fun x =>
    ((memLp_const (X x)).sub hX).integrable_norm_pow (by norm_num)
  have hmeas : AEStronglyMeasurable (fun p : Ω × Ω => ‖X p.1 - X p.2‖ ^ 2) (μ.prod μ) := by
    have h1 : AEStronglyMeasurable (fun p : Ω × Ω => X p.1) (μ.prod μ) := hX.1.comp_fst
    have h2 : AEStronglyMeasurable (fun p : Ω × Ω => X p.2) (μ.prod μ) := hX.1.comp_snd
    exact ((h1.sub h2).norm).pow 2
  have hint : Integrable (fun p : Ω × Ω => ‖X p.1 - X p.2‖ ^ 2) (μ.prod μ) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨Filter.Eventually.of_forall hinI, ?_⟩
    have : (fun x => ∫ y, ‖‖X x - X y‖ ^ 2‖ ∂μ) = fun x => ‖X x - m‖ ^ 2 + V := by
      funext x; simp only [norm_pow, norm_norm]; exact hin x
    rw [this]; exact hYsq.add (integrable_const V)
  rw [integral_prod _ hint]
  simp_rw [hin]
  rw [integral_add hYsq (integrable_const V)]
  simp; ring
