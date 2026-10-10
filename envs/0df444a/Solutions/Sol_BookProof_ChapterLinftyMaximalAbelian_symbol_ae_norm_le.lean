-- Prove2me | solution 1 for BookProof.ChapterLinftyMaximalAbelian.symbol_ae_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:35:58.766783+00:00
-- url     : https://prove2.me/submissions/44fbd88b-95bb-46cc-b746-38f9390ffdb2

-- Generated from ChapterLinftyMaximalAbelian.lean — solution of BookProof.ChapterLinftyMaximalAbelian.symbol_ae_norm_le
import Mathlib
import Definitions.Def_ChapterLinftyMaximalAbelian
import Theorems.Thm_BookProof_ChapterLinftyMaximalAbelian_stronglyMeasurable_symbol
import Theorems.Thm_BookProof_ChapterLinftyMaximalAbelian_symbol_mul
import Theorems.Thm_BookProof_ChapterLinftyMaximalAbelian_multOp_indicator_oneLp
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMaximalAbelian



noncomputable section

open MeasureTheory ENNReal Complex


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

set_option maxHeartbeats 1000000 in
theorem solution {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} (hT : CommutesWithMultOps T) :
    ∀ᵐ x ∂μ, ‖symbol T x‖ ≤ ‖T‖ := by

  set c : ℝ := ‖T‖ with hc
  -- for each `n`, the set where `‖ψ‖ ≥ c + 1/(n+1)` is null
  have key : ∀ n : ℕ, μ {x | c + 1 / (n + 1 : ℝ) ≤ ‖symbol T x‖} = 0 := by
    intro n
    set ε : ℝ := 1 / (n + 1 : ℝ) with hε
    have hεpos : 0 < ε := by positivity
    set s : Set α := {x | c + ε ≤ ‖symbol T x‖} with hsdef
    have hs : MeasurableSet s := by
      have : Measurable fun x => ‖symbol T x‖ :=
        (stronglyMeasurable_symbol T).measurable.norm
      exact measurableSet_le measurable_const this
    set φ : α → ℂ := s.indicator fun _ => (1 : ℂ) with hφdef
    have hφ : MemLp φ ⊤ μ := (memLp_top_const (1 : ℂ)).indicator hs
    set u : Lp ℂ 2 μ := multOp φ hφ (oneLp μ) with hu
    have hu_eq : u = indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ) :=
      multOp_indicator_oneLp hs 1
    have hnorm_u : ‖u‖ = μ.real s ^ (1 / (2 : ℝ)) := by
      rw [hu_eq, norm_indicatorConstLp (by norm_num) (by norm_num)]
      simp
    -- the lower bound: `|T u| ≥ (c+ε)·1_s` pointwise
    have hlow : ‖indicatorConstLp 2 hs (measure_ne_top μ s) ((c + ε : ℝ) : ℂ)‖ ≤ ‖T u‖ := by
      refine Lp.norm_le_norm_of_ae_le ?_
      filter_upwards [indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs)
          (hμs := measure_ne_top μ s) (c := ((c + ε : ℝ) : ℂ)), symbol_mul hT φ hφ] with x h1 h2
      rw [h1, h2]
      by_cases hx : x ∈ s
      · have hmem : c + ε ≤ ‖symbol T x‖ := hx
        have hnn : (0 : ℝ) ≤ c + ε := by rw [hc]; positivity
        rw [Set.indicator_of_mem hx, hφdef, Set.indicator_of_mem hx, one_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
        exact hmem
      · simp [Set.indicator_of_notMem hx, hφdef]
    have hupper : ‖T u‖ ≤ c * μ.real s ^ (1 / (2 : ℝ)) := by
      calc ‖T u‖ ≤ ‖T‖ * ‖u‖ := T.le_opNorm u
        _ = c * μ.real s ^ (1 / (2 : ℝ)) := by rw [hnorm_u]
    have hlow' : (c + ε) * μ.real s ^ (1 / (2 : ℝ)) ≤ c * μ.real s ^ (1 / (2 : ℝ)) := by
      have := hlow.trans hupper
      rwa [norm_indicatorConstLp (by norm_num) (by norm_num), Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
    have hzero : μ.real s ^ (1 / (2 : ℝ)) ≤ 0 := by nlinarith [hεpos]
    have hpow : μ.real s ^ (1 / (2 : ℝ)) = 0 :=
      le_antisymm hzero (Real.rpow_nonneg (measureReal_nonneg) _)
    have : μ.real s = 0 := by
      by_contra h
      have hpos : 0 < μ.real s := lt_of_le_of_ne measureReal_nonneg (Ne.symm h)
      exact absurd hpow (ne_of_gt (Real.rpow_pos_of_pos hpos _))
    exact (measureReal_eq_zero_iff (measure_ne_top μ s)).mp this
  -- union over `n`
  have : μ {x | ¬ ‖symbol T x‖ ≤ c} = 0 := by
    have hsub : {x | ¬ ‖symbol T x‖ ≤ c}
        ⊆ ⋃ n : ℕ, {x | c + 1 / (n + 1 : ℝ) ≤ ‖symbol T x‖} := by
      intro x hx
      simp only [Set.mem_setOf_eq, not_le] at hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      exact Set.mem_iUnion.mpr ⟨n, by simp only [Set.mem_setOf_eq]; linarith⟩
    exact measure_mono_null hsub (measure_iUnion_null key)
  simpa [ae_iff] using this
