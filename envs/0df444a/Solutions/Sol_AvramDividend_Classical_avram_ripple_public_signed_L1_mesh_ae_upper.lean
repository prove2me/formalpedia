-- Prove2me | solution 1 for AvramDividend.Classical.avram_ripple_public_signed_L1_mesh_ae_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:24:35.437801+00:00
-- url     : https://prove2.me/submissions/b71eb7c3-cdc1-49bd-ad38-4a20a3b8094c

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω)
    (F Z : Ω → ℝ) (M R : ℕ → Ω → ℝ) (c : ℝ)
    (hGI : Integrable (fun ω => max (F ω - c - Z ω) 0) (P.restrict A))
    (hMI : ∀ m, Integrable (fun ω => |M m ω - Z ω|) (P.restrict A))
    (hRI : ∀ m, Integrable (fun ω => |R m ω|) (P.restrict A))
    (hPath : ∀ m, ∀ᵐ ω ∂(P.restrict A), F ω - c ≤ M m ω + R m ω)
    (hML1 : Tendsto (fun m => ∫ ω in A, |M m ω - Z ω| ∂P)
      atTop (nhds (0 : ℝ)))
    (hRL1 : Tendsto (fun m => ∫ ω in A, |R m ω| ∂P)
      atTop (nhds (0 : ℝ))) :
    ∀ᵐ ω ∂(P.restrict A), F ω - c ≤ Z ω := by
  let G : Ω → ℝ := fun ω => max (F ω - c - Z ω) 0
  have hg (ω : Ω) : 0 ≤ G ω := le_max_right _ _
  have hBound (m : ℕ) :
      (∫ ω in A, G ω ∂P) ≤
        (∫ ω in A, |M m ω - Z ω| ∂P) +
          (∫ ω in A, |R m ω| ∂P) := by
    rw [← integral_add (hMI m) (hRI m)]
    apply integral_mono_ae hGI ((hMI m).add (hRI m))
    filter_upwards [hPath m] with ω hω
    change max (F ω - c - Z ω) 0 ≤
      |M m ω - Z ω| + |R m ω|
    apply max_le
    · have h₁ := le_abs_self (M m ω - Z ω)
      have h₂ := le_abs_self (R m ω)
      linarith
    · exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hlim :
      Tendsto (fun _ : ℕ => ∫ ω in A, G ω ∂P)
        atTop (nhds (0 : ℝ)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds (by simpa only [add_zero] using hML1.add hRL1)
    · intro m
      exact integral_nonneg hg
    · exact hBound
  have hzero : (∫ ω in A, G ω ∂P) = 0 :=
    tendsto_const_nhds_iff.mp hlim
  have hAe : G =ᵐ[P.restrict A] (fun _ => (0 : ℝ)) :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall hg) hGI).mp hzero
  filter_upwards [hAe] with ω hω
  change max (F ω - c - Z ω) 0 = 0 at hω
  linarith [le_max_left (F ω - c - Z ω) (0 : ℝ)]
