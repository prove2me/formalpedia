-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB23_integrable_L1_positive_excess_to_ae_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:46:34.958271+00:00
-- url     : https://prove2.me/submissions/3c7ca7f7-8e00-4ba7-9fbf-a3af74bec1c7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB22_abstract_L1_positive_excess_to_ae_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (F N B : Ω → ℝ) (M : ℕ → Ω → ℝ)
    (hFI : IntegrableOn F A P) (hNI : IntegrableOn N A P)
    (hBI : IntegrableOn B A P) (hMI : ∀ m, IntegrableOn (M m) A P)
    (hEL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P) atTop (𝓝 (0 : ℝ)))
    (hR : Tendsto (fun m => ∫ ω in A, max (F ω - M m ω - B ω) 0 ∂P) atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂(P.restrict A), F ω ≤ N ω + B ω := by
  classical
  have hPos (S : Ω → ℝ) (hS : IntegrableOn S A P) :
      IntegrableOn (fun ω => max (S ω) 0) A P := by
    have hRep : IntegrableOn (fun ω => (1 / 2 : ℝ) * (S ω + |S ω|)) A P :=
      (hS.add hS.abs).const_mul (1 / 2 : ℝ)
    convert hRep using 1
    ext ω
    rcases le_total 0 (S ω) with hs | hs
    · rw [max_eq_left hs, abs_of_nonneg hs]
      ring
    · rw [max_eq_right hs, abs_of_nonpos hs]
      ring
  have hI : IntegrableOn (fun ω => max (F ω - N ω - B ω) 0) A P :=
    hPos (fun ω => F ω - N ω - B ω) ((hFI.sub hNI).sub hBI)
  have hIM (m : ℕ) : IntegrableOn (fun ω => max (F ω - M m ω - B ω) 0) A P :=
    hPos (fun ω => F ω - M m ω - B ω) ((hFI.sub (hMI m)).sub hBI)
  have hDI (m : ℕ) : IntegrableOn (fun ω => |N ω - M m ω|) A P :=
    (hNI.sub (hMI m)).abs
  exact AvramDividend.Classical.avram_gbB22_abstract_L1_positive_excess_to_ae_bound
    P A F N B M hI hIM hDI hEL1 hR
