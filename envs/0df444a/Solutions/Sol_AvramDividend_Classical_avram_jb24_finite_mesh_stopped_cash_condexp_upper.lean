-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb24_finite_mesh_stopped_cash_condexp_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:27:56.487573+00:00
-- url     : https://prove2.me/submissions/94812e42-58af-4aa3-a865-583fc10a1188

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jb23_dominated_two_channel_initial_centering_L1
import Theorems.Thm_AvramDividend_Classical_avram_jb24_stopped_cash_limit_upper_from_two_noises
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Direct conditional budget from dominated centred original stopped noise limits. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (b : ℝ) (F MG MJ BG BJ : Ω → ℝ)
    (G J E : ℕ → Ω → ℝ)
    (hFI : Integrable F P)
    (hGI : ∀ k, Integrable (G k) P)
    (hJI : ∀ k, Integrable (J k) P)
    (hGconv : ∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (MG ω)))
    (hJconv : ∀ᵐ ω ∂P, Tendsto (fun k => J k ω) atTop (𝓝 (MJ ω)))
    (hEconv : ∀ᵐ ω ∂P, Tendsto (fun k => E k ω) atTop (𝓝 (0 : ℝ)))
    (hBG : Integrable BG P) (hBJ : Integrable BJ P)
    (hGdom : ∀ k, ∀ᵐ ω ∂P, ‖G k ω‖ ≤ BG ω)
    (hJdom : ∀ k, ∀ᵐ ω ∂P, ‖J k ω‖ ≤ BJ ω)
    (hGzero : ∀ k, P[G k | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)))
    (hJzero : ∀ k, P[J k | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)))
    (hUpper : ∀ k, ∀ᵐ ω ∂P,
      F ω ≤ b + G k ω + J k ω + E k ω) :
    Integrable MG P ∧ Integrable MJ P ∧
    P[MG | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
    P[MJ | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
    P[F | 𝓕.rightCont 0] ≤ᵐ[P] (fun _ : Ω => b) := by
  have hLimit :=
    avram_jb23_dominated_two_channel_initial_centering_L1
      G J MG MJ BG BJ hGI hJI hGconv hJconv
      hBG hBJ hGdom hJdom hGzero hJzero
  have hPath :=
    avram_jb24_stopped_cash_limit_upper_from_two_noises
      b F MG MJ G J E hGconv hJconv hEconv hUpper
  refine ⟨hLimit.1, hLimit.2.2.1,
    hLimit.2.1, hLimit.2.2.2, ?_⟩
  let m : MeasurableSpace Ω := 𝓕.rightCont 0
  have hBI : Integrable (fun _ : Ω => b) P := integrable_const b
  have hAI : Integrable (fun ω : Ω => b + MG ω) P :=
    hBI.add hLimit.1
  have hGI' : Integrable (fun ω : Ω => b + MG ω + MJ ω) P :=
    hAI.add hLimit.2.2.1
  have hmono := condExp_mono hFI hGI' hPath (m := m)
  have hfirst := condExp_add hBI hLimit.1 m
  have hsecond := condExp_add hAI hLimit.2.2.1 m
  have hc : P[(fun _ : Ω => b) | m] = (fun _ : Ω => b) :=
    condExp_const (𝓕.rightCont.le 0) b
  filter_upwards [hmono, hfirst, hsecond, hLimit.2.1, hLimit.2.2.2]
    with ω hm hf hs hg hj
  change P[MG | m] ω = 0 at hg
  change P[MJ | m] ω = 0 at hj
  have hfun1 : ((fun z : Ω => b + MG z) + MJ) =
      (fun z : Ω => b + MG z + MJ z) := by
    funext z
    rfl
  have hfun2 : ((fun _ : Ω => b) + MG) =
      (fun z : Ω => b + MG z) := by
    funext z
    rfl
  have hs' :
      P[(fun z : Ω => b + MG z + MJ z) | m] ω =
        P[(fun z : Ω => b + MG z) | m] ω + P[MJ | m] ω := by
    rw [hfun1] at hs
    simpa only [Pi.add_apply] using hs
  have hf' :
      P[(fun z : Ω => b + MG z) | m] ω =
        P[(fun _ : Ω => b) | m] ω + P[MG | m] ω := by
    rw [hfun2] at hf
    simpa only [Pi.add_apply] using hf
  calc
    P[F | m] ω ≤ P[(fun z : Ω => b + MG z + MJ z) | m] ω := hm
    _ = P[(fun z : Ω => b + MG z) | m] ω + P[MJ | m] ω := hs'
    _ = (P[(fun _ : Ω => b) | m] ω + P[MG | m] ω) +
        P[MJ | m] ω := by rw [hf']
    _ = b := by simpa [hc, hg, hj]
