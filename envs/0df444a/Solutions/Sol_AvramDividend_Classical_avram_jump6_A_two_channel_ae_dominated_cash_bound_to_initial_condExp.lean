-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_two_channel_ae_dominated_cash_bound_to_initial_condExp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:08:02.612332+00:00
-- url     : https://prove2.me/submissions/006ab5a3-dff6-4b81-b489-9b2e18ea1816

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jb23_dominated_two_channel_initial_centering_L1
import Theorems.Thm_AvramDividend_Classical_avram_a07_condexp_upper_of_two_centered_noises
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {Flt : Filtration ℝ≥0 mOmega}
    (F : Omega → ℝ) (b : ℝ)
    (G J E : ℕ → Omega → ℝ)
    (MG MJ BG BJ : Omega → ℝ)
    (hFI : Integrable F P)
    (hGI : ∀ k, Integrable (G k) P)
    (hJI : ∀ k, Integrable (J k) P)
    (hGconv : ∀ᵐ omega ∂P,
      Tendsto (fun k => G k omega) atTop (𝓝 (MG omega)))
    (hJconv : ∀ᵐ omega ∂P,
      Tendsto (fun k => J k omega) atTop (𝓝 (MJ omega)))
    (hEconv : ∀ᵐ omega ∂P,
      Tendsto (fun k => E k omega) atTop (𝓝 (0 : ℝ)))
    (hBG : Integrable BG P) (hBJ : Integrable BJ P)
    (hGdom : ∀ k, ∀ᵐ omega ∂P, ‖G k omega‖ ≤ BG omega)
    (hJdom : ∀ k, ∀ᵐ omega ∂P, ‖J k omega‖ ≤ BJ omega)
    (hG0 : ∀ k, P[G k | Flt.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)))
    (hJ0 : ∀ k, P[J k | Flt.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)))
    (hLedger : ∀ᵐ omega ∂P, ∀ k,
      F omega ≤ b + G k omega + J k omega + E k omega) :
    ∀ᵐ omega ∂P, P[F | Flt.rightCont 0] omega ≤ b := by
  obtain ⟨hMGI, hMG0, hMJI, hMJ0⟩ :=
    avram_jb23_dominated_two_channel_initial_centering_L1
      G J MG MJ BG BJ hGI hJI hGconv hJconv
      hBG hBJ hGdom hJdom hG0 hJ0
  have hUpper : ∀ᵐ omega ∂P, F omega ≤ b + MG omega + MJ omega := by
    filter_upwards [hGconv, hJconv, hEconv, hLedger]
      with omega hGc hJc hEc hCash
    have hLim : Tendsto
        (fun k => b + G k omega + J k omega + E k omega)
        atTop (𝓝 (b + MG omega + MJ omega)) := by
      convert ((tendsto_const_nhds.add hGc).add hJc).add hEc using 1 <;> simp
    exact ge_of_tendsto hLim (Filter.Eventually.of_forall hCash)
  exact avram_a07_condexp_upper_of_two_centered_noises
    b F MG MJ hFI hMGI hMJI hMG0 hMJ0 hUpper
