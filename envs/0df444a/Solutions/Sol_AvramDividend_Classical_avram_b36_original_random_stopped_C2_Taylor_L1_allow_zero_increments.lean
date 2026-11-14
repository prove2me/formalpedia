-- Prove2me | solution 1 for AvramDividend.Classical.avram_b36_original_random_stopped_C2_Taylor_L1_allow_zero_increments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:48:35.0797+00:00
-- url     : https://prove2.me/submissions/30a4ed8a-6a3e-4bc2-800b-75033085743a

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_preleft_C2_taylor_remainder_modulus
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_random_stopped_compact_mesh_energy_L1
import Theorems.Thm_AvramDividend_Classical_avram_b35_original_physical_C2_Taylor_zero_increment_cell_filter_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True stopped physical Taylor L1 error with zero increments allowed. -/
theorem solution
    {Omega : Type*} [mOmega : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration ℝ≥0 mOmega}
    (X : SpectrallyNegativeLevy P F)
    (x : ℝ) (D : ℝ≥0 → Omega → ℝ) (hD : IsDividendStrategy F D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (A : Set Omega) (S : Finset ℕ)
        (s t : ℕ → Omega → ℝ≥0),
        let z : Omega → ℕ → ℝ := fun omega i =>
          Function.leftLim (fun u : ℝ≥0 =>
            x + X.X u omega - rightLimit D u omega) (s i omega)
        let g : Omega → ℕ → ℝ := fun omega i =>
          X.X (t i omega) omega - X.X (s i omega) omega -
            (((t i omega : ℝ) - (s i omega : ℝ)) * X.c)
        let Q : Omega → ℝ := fun omega => ∑ i ∈ S, (g omega i) ^ 2
        let R : Omega → ℝ := fun omega => ∑ i ∈ S,
          (w (z omega i + g omega i) -
            taylorWithinEval w 1
              (Set.uIcc (z omega i) (z omega i + g omega i))
              (z omega i) (z omega i + g omega i) -
            (iteratedDeriv 2 w (z omega i) * (g omega i) ^ 2) / 2)
        (∀ i ∈ S, IsStoppingTime F.rightCont
          (fun omega => (s i omega : WithTop ℝ≥0))) →
        (∀ i ∈ S, IsStoppingTime F.rightCont
          (fun omega => (t i omega : WithTop ℝ≥0))) →
        (∀ᵐ omega ∂(P.restrict A), ∀ i ∈ S,
          z omega i ∈ Icc a b ∧ z omega i + g omega i ∈ Icc a b ∧
          dist (z omega i + g omega i) (z omega i) < delta) →
        AEStronglyMeasurable (fun omega => |R omega|) (P.restrict A) →
        IntegrableOn (fun omega => |R omega|) A P ∧
        (∫ omega in A, |R omega| ∂P) ≤
          eps * (∫ omega in A, Q omega ∂P) := by
  classical
  obtain ⟨delta, hdelta, hMod⟩ :=
    avram_ubv_gauss13_localise_original_preleft_C2_taylor_remainder_modulus
      X x D hD C w hw a b ha hab hbcap eps heps
  refine ⟨delta, hdelta, ?_⟩
  intro A S s t
  dsimp only
  intro hs ht hBand hRMeas
  let z : Omega → ℕ → ℝ := fun omega i =>
    Function.leftLim (fun u : ℝ≥0 =>
      x + X.X u omega - rightLimit D u omega) (s i omega)
  let g : Omega → ℕ → ℝ := fun omega i =>
    X.X (t i omega) omega - X.X (s i omega) omega -
      (((t i omega : ℝ) - (s i omega : ℝ)) * X.c)
  let Q : Omega → ℝ := fun omega => ∑ i ∈ S, (g omega i) ^ 2
  let e : Omega → ℕ → ℝ := fun omega i =>
    w (z omega i + g omega i) -
      taylorWithinEval w 1
        (Set.uIcc (z omega i) (z omega i + g omega i))
        (z omega i) (z omega i + g omega i) -
      (iteratedDeriv 2 w (z omega i) * (g omega i) ^ 2) / 2
  let R : Omega → ℝ := fun omega => ∑ i ∈ S, e omega i
  have hWeak : ∀ᵐ omega ∂(P.restrict A), ∀ i ∈ S,
      z omega i ∈ Icc a b ∧ z omega i + g omega i ∈ Icc a b := by
    filter_upwards [hBand] with omega hω i hi
    exact ⟨(hω i hi).1, (hω i hi).2.1⟩
  have hQI : IntegrableOn Q A P :=
    avram_b27_original_random_stopped_compact_mesh_energy_L1
      X x D a b hab A S s t hs ht hWeak
  have hPoint : ∀ᵐ omega ∂(P.restrict A),
      |R omega| ≤ eps * Q omega := by
    filter_upwards [hBand] with omega hω
    have hCell (i : ℕ) (hi : i ∈ S) :
        |e omega i| ≤ eps * (g omega i) ^ 2 := by
      rcases hω i hi with ⟨hz, hy, hd⟩
      by_cases hg : g omega i = 0
      · simp [e, hg, taylorWithinEval_self]
      · have hne : z omega i ≠ z omega i + g omega i := by
          intro h
          apply hg
          linarith
        have h := hMod omega (s i omega) (z omega i + g omega i)
          hz hy hne hd
        simpa only [e, z, add_sub_cancel_left] using h
    calc
      |R omega| ≤ ∑ i ∈ S, |e omega i| := by
        simpa only [R] using
          (Finset.abs_sum_le_sum_abs (fun i => e omega i) S)
      _ ≤ ∑ i ∈ S, eps * (g omega i) ^ 2 := by
        apply Finset.sum_le_sum
        exact fun i hi => hCell i hi
      _ = eps * Q omega := by simp [Q, Finset.mul_sum]
  have hRI : IntegrableOn (fun omega => |R omega|) A P :=
    Integrable.mono' (hQI.const_mul eps) hRMeas (by
      filter_upwards [hPoint] with omega hω
      simpa [Real.norm_eq_abs] using hω)
  refine ⟨hRI, ?_⟩
  have hI := integral_mono_ae hRI (hQI.const_mul eps) hPoint
  simpa only [integral_const_mul] using hI
