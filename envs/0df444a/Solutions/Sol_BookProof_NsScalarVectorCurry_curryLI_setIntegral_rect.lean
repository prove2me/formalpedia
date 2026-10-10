-- Prove2me | solution 1 for BookProof.NsScalarVectorCurry.curryLI_setIntegral_rect
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:12.656355+00:00
-- url     : https://prove2.me/submissions/e5427a61-083f-45db-a3d8-1a8ddcf4583c

-- Generated from ChapterNsScalarVectorCurry.lean — solution of BookProof.NsScalarVectorCurry.curryLI_setIntegral_rect
import Mathlib
import Definitions.Def_ChapterNsScalarVectorCurry
import Theorems.Thm_BookProof_NsScalarVectorCurry_curryLI_indicator_prod
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
theorem solution (f : Lp (Lp ℂ 2 ν) 2 μ) {s : Set V} {t : Set W}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hνt : ν t ≠ ∞)
    (hst : (μ.prod ν) (s ×ˢ t) ≠ ∞) :
    ∫ z in s ×ˢ t, (curryLI f : V × W → ℂ) z ∂(μ.prod ν)
      = ∫ x in s, (∫ y in t, ((f : V → Lp ℂ 2 ν) x : W → ℂ) y ∂ν) ∂μ := by

  have hinner : inner ℂ (curryLI (fibMk (indicatorConstLp 2 hs hμs (1 : ℂ))
        (indicatorConstLp 2 ht hνt (1 : ℂ)))) (curryLI f)
      = inner ℂ (fibMk (indicatorConstLp 2 hs hμs (1 : ℂ)) (indicatorConstLp 2 ht hνt (1 : ℂ))) f :=
    curryLI.inner_map_map _ _
  rw [curryLI_indicator_prod hs ht hμs hνt hst,
    L2.inner_indicatorConstLp_one (𝕜 := ℂ) (hs.prod ht) hst (curryLI f), L2.inner_def] at hinner
  rw [hinner]
  have hcongr : ∀ᵐ x ∂μ, inner ℂ ((fibMk (indicatorConstLp 2 hs hμs (1 : ℂ))
        (indicatorConstLp 2 ht hνt (1 : ℂ)) : V → Lp ℂ 2 ν) x) ((f : V → Lp ℂ 2 ν) x)
      = s.indicator (fun x => ∫ y in t, ((f : V → Lp ℂ 2 ν) x : W → ℂ) y ∂ν) x := by
    filter_upwards [coeFn_fibMk (indicatorConstLp 2 hs hμs (1 : ℂ))
        (indicatorConstLp 2 ht hνt (1 : ℂ)),
      indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs) (hμs := hμs) (c := (1 : ℂ))]
      with x h1 h2
    rw [h1, h2, inner_smul_left, L2.inner_indicatorConstLp_one (𝕜 := ℂ) ht hνt]
    by_cases hx : x ∈ s <;> simp [hx]
  rw [integral_congr_ae hcongr, integral_indicator hs]
