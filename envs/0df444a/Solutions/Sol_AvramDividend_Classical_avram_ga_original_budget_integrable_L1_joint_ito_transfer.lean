-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_budget_integrable_L1_joint_ito_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T14:07:41.028975+00:00
-- url     : https://prove2.me/submissions/b57e2dad-2169-45da-867f-d600b7e8e8b5

import Mathlib
open MeasureTheory Filter Topology Set
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (hA : MeasurableSet A)
    (F N Occ : Ω → ℝ) (M B : ℕ → Ω → ℝ) (x Γ c : ℝ)
    (hFI : Integrable F P) (hMI : ∀ m, Integrable (M m) P)
    (hOI : Integrable Occ (P.restrict A))
    (hNI : Integrable N P)
    (hBI : ∀ m, Integrable (fun ω => |B m ω|) P)
    (hPath : ∀ᵐ ω ∂(P.restrict A),
      F ω - x ≤ N ω + Γ + c * Occ ω)
    (hNlim : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hBlim : Tendsto (fun m => ∫ ω, |B m ω| ∂P)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω in A,
      max ((F ω - x) - M m ω - (Γ + c * Occ ω) - B m ω)
        (0 : ℝ) ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  let E : ℕ → Ω → ℝ := fun m ω =>
    (F ω - x) - M m ω - (Γ + c * Occ ω) - B m ω
  have hDI (m : ℕ) :
      Integrable (fun ω => |N ω - M m ω|) (P.restrict A) :=
    ((hNI.sub (hMI m)).abs).restrict
  have hBI' (m : ℕ) :
      Integrable (fun ω => |B m ω|) (P.restrict A) :=
    (hBI m).restrict
  have hBound (m : ℕ) :
      ∀ᵐ ω ∂(P.restrict A),
        max (E m ω) (0 : ℝ) ≤
          |N ω - M m ω| + |B m ω| := by
    filter_upwards [hPath] with ω hω
    change max ((F ω - x) - M m ω - (Γ + c * Occ ω) - B m ω)
      (0 : ℝ) ≤ |N ω - M m ω| + |B m ω|
    apply max_le
    · calc
        (F ω - x) - M m ω - (Γ + c * Occ ω) - B m ω ≤
            (N ω - M m ω) - B m ω := by linarith
        _ ≤ |N ω - M m ω| + |B m ω| := by
          linarith [le_abs_self (N ω - M m ω),
            neg_le_abs (B m ω)]
    · exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hBRestr (m : ℕ) :
      (∫ ω in A, |B m ω| ∂P) ≤ (∫ ω, |B m ω| ∂P) := by
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun ω => abs_nonneg (B m ω)))
      (hBI m)
  have hUpper (m : ℕ) :
      (∫ ω in A, max (E m ω) (0 : ℝ) ∂P) ≤
        (∫ ω in A, |N ω - M m ω| ∂P) +
          (∫ ω, |B m ω| ∂P) := by
    by_cases hEI : Integrable (fun ω => max (E m ω) (0 : ℝ))
        (P.restrict A)
    · have hMono :
          (∫ ω in A, max (E m ω) (0 : ℝ) ∂P) ≤
          (∫ ω in A, |N ω - M m ω| + |B m ω| ∂P) :=
        integral_mono_ae hEI ((hDI m).add (hBI' m)) (hBound m)
      rw [integral_add (hDI m) (hBI' m)] at hMono
      linarith [hBRestr m]
    · rw [integral_undef hEI]
      exact add_nonneg
        (integral_nonneg (fun ω => abs_nonneg (N ω - M m ω)))
        (integral_nonneg (fun ω => abs_nonneg (B m ω)))
  have hLim :
      Tendsto (fun m : ℕ =>
        ∫ ω in A, max (E m ω) (0 : ℝ) ∂P)
        atTop (nhds (0 : ℝ)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds (by simpa only [add_zero] using hNlim.add hBlim)
    · intro m
      exact integral_nonneg (fun ω => le_max_right (E m ω) (0 : ℝ))
    · exact hUpper
  exact hLim
