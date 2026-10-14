-- Prove2me | solution 1 for BookProof.NsScalarVectorCurry.isSliceOf_curryLI
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:27:07.569635+00:00
-- url     : https://prove2.me/submissions/4ae8b14b-edc9-47a6-9d6f-0bdd736292d1

-- Generated from ChapterNsScalarVectorCurry.lean — solution of BookProof.NsScalarVectorCurry.isSliceOf_curryLI
import Mathlib
import Definitions.Def_ChapterNsScalarVectorCurry
import Theorems.Thm_BookProof_NsScalarVectorCurry_eLpNorm_two_sq
import Theorems.Thm_BookProof_NsScalarVectorCurry_eLpNorm_two_sq_prime
import Theorems.Thm_BookProof_NsScalarVectorCurry_lintegral_eLpNorm_slice_sq
import Theorems.Thm_BookProof_NsScalarVectorCurry_enn_tendsto_zero_of_sq
import Theorems.Thm_BookProof_NsScalarVectorCurry_ae_tendsto_zero_of_tsum_lintegral_ne_top
import Theorems.Thm_BookProof_NsScalarVectorCurry_isSliceOf_fibTensor
open BookProof.NsScalarVectorCurry



open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate


noncomputable section

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}
variable [SigmaFinite μ] [SigmaFinite ν]

set_option maxHeartbeats 1000000 in
theorem solution (f : Lp (Lp ℂ 2 ν) 2 μ) : IsSliceOf f (curryLI f) := by

  classical
  -- a sequence of elements of the dense span, converging to `f` fast
  have hmem : ∀ k : ℕ, ∃ v ∈ Set.range (fibTensor (μ := μ) (ν := ν)),
      dist f v < (1 / 2 : ℝ) ^ k := fun k =>
    Metric.mem_closure_iff.1 (denseRange_fibTensor f) _ (by positivity)
  choose w hw hwdist using hmem
  have hwslice : ∀ k, IsSliceOf (w k) (curryLI (w k)) := by
    intro k
    obtain ⟨t, ht⟩ := hw k
    have h := isSliceOf_fibTensor t
    rw [ht] at h
    rwa [← curryLI_fibTensor t, ht] at h
  -- the two error functions, in the fibred and in the scalar picture
  set φ₁ : ℕ → V → ℝ≥0∞ := fun k x => ‖((w k - f : Lp (Lp ℂ 2 ν) 2 μ) : V → Lp ℂ 2 ν) x‖ₑ
    with hφ₁
  set φ₂ : ℕ → V → ℝ≥0∞ := fun k x =>
    eLpNorm (fun y => ((curryLI (w k) - curryLI f : Lp ℂ 2 (μ.prod ν)) : V × W → ℂ) (x, y)) 2 ν
    with hφ₂
  have hnorm : ∀ k, ‖w k - f‖ₑ ^ 2 ≤ (ENNReal.ofReal ((1 / 2 : ℝ) ^ 2)) ^ k := by
    intro k
    have h1 : ‖w k - f‖ ≤ (1 / 2 : ℝ) ^ k := by
      rw [← dist_eq_norm, dist_comm]
      exact (hwdist k).le
    have h2 : ‖w k - f‖ₑ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal h1
    calc ‖w k - f‖ₑ ^ 2 ≤ (ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) ^ 2 := by gcongr
      _ = (ENNReal.ofReal ((1 / 2 : ℝ) ^ 2)) ^ k := by
          rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_pow (by norm_num),
            ← pow_mul, ← pow_mul, Nat.mul_comm]
  have hgeom : ∑' k : ℕ, (ENNReal.ofReal ((1 / 2 : ℝ) ^ 2)) ^ k ≠ ∞ := by
    rw [ENNReal.tsum_geometric]
    refine ENNReal.inv_ne_top.2 ?_
    have hlt : ENNReal.ofReal ((1 / 2 : ℝ) ^ 2) < 1 := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      exact ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.2 (by norm_num)
    exact tsub_pos_of_lt hlt |>.ne'
  -- the fibred error tends to zero almost everywhere
  have hint₁ : ∀ k, ∫⁻ x, (φ₁ k x) ^ 2 ∂μ = ‖w k - f‖ₑ ^ 2 := by
    intro k
    rw [Lp.enorm_def, eLpNorm_two_sq_prime]
  have hmeas₁ : ∀ k, AEMeasurable (fun x => (φ₁ k x) ^ 2) μ := fun k =>
    (((Lp.aestronglyMeasurable (w k - f)).enorm :
      AEMeasurable (fun x => ‖((w k - f : Lp (Lp ℂ 2 ν) 2 μ) : V → Lp ℂ 2 ν) x‖ₑ) μ).pow_const _)
  have htend₁ : ∀ᵐ x ∂μ, Filter.Tendsto (fun k => φ₁ k x) Filter.atTop (nhds 0) := by
    have := ae_tendsto_zero_of_tsum_lintegral_ne_top (ρ := μ) (fun k x => (φ₁ k x) ^ 2) hmeas₁ ?_
    · filter_upwards [this] with x hx using enn_tendsto_zero_of_sq hx
    · refine ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum fun k => ?_)
      rw [hint₁ k]
      exact hnorm k
  -- the scalar error tends to zero almost everywhere
  have hint₂ : ∀ k, ∫⁻ x, (φ₂ k x) ^ 2 ∂μ = ‖w k - f‖ₑ ^ 2 := by
    intro k
    rw [show (fun x => (φ₂ k x) ^ 2) = fun x =>
        (eLpNorm (fun y => ((curryLI (w k) - curryLI f : Lp ℂ 2 (μ.prod ν)) : V × W → ℂ) (x, y))
          2 ν) ^ 2 from rfl,
      lintegral_eLpNorm_slice_sq _ (Lp.aestronglyMeasurable _), ← Lp.enorm_def,
      ← map_sub curryLI (w k) f, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
      curryLI.norm_map]
  have hmeas₂ : ∀ k, AEMeasurable (fun x => (φ₂ k x) ^ 2) μ := by
    intro k
    have hF : AEMeasurable (fun z : V × W =>
        ‖((curryLI (w k) - curryLI f : Lp ℂ 2 (μ.prod ν)) : V × W → ℂ) z‖ₑ ^ (2 : ℝ))
        (μ.prod ν) :=
      ((Lp.aestronglyMeasurable _).enorm).pow_const _
    have := hF.lintegral_prod_right'
    refine this.congr ?_
    filter_upwards with x
    rw [show (φ₂ k x) ^ 2 =
        (eLpNorm (fun y => ((curryLI (w k) - curryLI f : Lp ℂ 2 (μ.prod ν)) : V × W → ℂ) (x, y))
          2 ν) ^ 2 from rfl, eLpNorm_two_sq]
  have htend₂ : ∀ᵐ x ∂μ, Filter.Tendsto (fun k => φ₂ k x) Filter.atTop (nhds 0) := by
    have := ae_tendsto_zero_of_tsum_lintegral_ne_top (ρ := μ) (fun k x => (φ₂ k x) ^ 2) hmeas₂ ?_
    · filter_upwards [this] with x hx using enn_tendsto_zero_of_sq hx
    · refine ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum fun k => ?_)
      rw [hint₂ k]
      exact hnorm k
  -- the countably many almost-everywhere facts, collected
  have hsubouter : ∀ᵐ x ∂μ, ∀ k : ℕ,
      ((w k - f : Lp (Lp ℂ 2 ν) 2 μ) : V → Lp ℂ 2 ν) x
        = (w k : V → Lp ℂ 2 ν) x - (f : V → Lp ℂ 2 ν) x := by
    rw [ae_all_iff]
    exact fun k => Lp.coeFn_sub (w k) f
  have hsliceall : ∀ᵐ x ∂μ, ∀ k : ℕ,
      ((w k : V → Lp ℂ 2 ν) x : W → ℂ)
        =ᵐ[ν] fun y => (curryLI (w k) : V × W → ℂ) (x, y) := by
    rw [ae_all_iff]
    exact hwslice
  have hsubinner : ∀ᵐ x ∂μ, ∀ k : ℕ, ∀ᵐ y ∂ν,
      ((curryLI (w k) - curryLI f : Lp ℂ 2 (μ.prod ν)) : V × W → ℂ) (x, y)
        = (curryLI (w k) : V × W → ℂ) (x, y) - (curryLI f : V × W → ℂ) (x, y) := by
    rw [ae_all_iff]
    exact fun k => Measure.ae_ae_of_ae_prod (Lp.coeFn_sub (curryLI (w k)) (curryLI f))
  have hslicemeas : ∀ᵐ x ∂μ,
      AEStronglyMeasurable (fun y => (curryLI f : V × W → ℂ) (x, y)) ν :=
    (Lp.aestronglyMeasurable (curryLI f)).prodMk_left
  filter_upwards [htend₁, htend₂, hsubouter, hsliceall, hsubinner, hslicemeas]
    with x hx₁ hx₂ hxsub hxslice hxsubin hxmeas
  -- at such an `x` the two pictures differ by nothing
  set A : W → ℂ := ((f : V → Lp ℂ 2 ν) x : W → ℂ) with hA
  set C : W → ℂ := fun y => (curryLI f : V × W → ℂ) (x, y) with hC
  have hAmeas : AEStronglyMeasurable A ν := Lp.aestronglyMeasurable _
  have hzero : eLpNorm (A - C) 2 ν = 0 := by
    refine le_antisymm ?_ zero_le
    have hle : ∀ k : ℕ, eLpNorm (A - C) 2 ν ≤ φ₁ k x + φ₂ k x := by
      intro k
      set B : W → ℂ := ((w k : V → Lp ℂ 2 ν) x : W → ℂ) with hB
      have hBmeas : AEStronglyMeasurable B ν := Lp.aestronglyMeasurable _
      have hsplit : A - C = (A - B) + (B - C) := by funext y; simp
      have h1 : eLpNorm (A - B) 2 ν = φ₁ k x := by
        have hval : φ₁ k x
            = ‖((w k : V → Lp ℂ 2 ν) x) - ((f : V → Lp ℂ 2 ν) x)‖ₑ := by
          simp only [hφ₁, hxsub k]
        rw [hval, Lp.enorm_def, eLpNorm_sub_comm A B]
        refine eLpNorm_congr_ae ?_
        filter_upwards [Lp.coeFn_sub ((w k : V → Lp ℂ 2 ν) x) ((f : V → Lp ℂ 2 ν) x)]
          with y hy
        simp only [Pi.sub_apply, hA, hB]
        rw [hy]
        simp
      have h2 : eLpNorm (B - C) 2 ν = φ₂ k x := by
        simp only [hφ₂]
        refine eLpNorm_congr_ae ?_
        filter_upwards [hxslice k, hxsubin k] with y hy hy2
        simp only [Pi.sub_apply, hB, hC]
        rw [hy2, hy]
      calc eLpNorm (A - C) 2 ν
          = eLpNorm ((A - B) + (B - C)) 2 ν := by rw [← hsplit]
        _ ≤ eLpNorm (A - B) 2 ν + eLpNorm (B - C) 2 ν :=
            eLpNorm_add_le (hAmeas.sub hBmeas) (hBmeas.sub hxmeas) (by norm_num)
        _ = φ₁ k x + φ₂ k x := by rw [h1, h2]
    have hlim : Filter.Tendsto (fun k => φ₁ k x + φ₂ k x) Filter.atTop (nhds 0) := by
      simpa using hx₁.add hx₂
    exact ge_of_tendsto' hlim hle
  have := (eLpNorm_eq_zero_iff (hAmeas.sub hxmeas) (by norm_num)).1 hzero
  filter_upwards [this] with y hy
  have : A y - C y = 0 := hy
  linear_combination (norm := ring_nf) this
