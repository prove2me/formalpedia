-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_rateone_size2_count_one_at_first_mark
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:59:12.846894+00:00
-- url     : https://prove2.me/submissions/3a333f11-05bc-4c77-899c-484f6e1206ba

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_strictMono_arrival
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (τ Y : ℕ → Ω → ℝ)
    (hJ : IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      (Measure.dirac (-2 : ℝ)) μ) :
    ∀ᵐ ω ∂μ, jumpCount (fun n => arrival τ n ω) (arrival τ 0 ω) = 1 := by
  have hMono : ∀ᵐ ω ∂μ, StrictMono (fun n => arrival τ n ω) :=
    IsCompoundPoissonDriver.ae_strictMono_arrival hJ (by norm_num)
  filter_upwards [hMono] with ω hω
  let T : ℕ → ℝ := fun n => arrival τ n ω
  have h01 : T 0 < T 1 := hω (by omega : (0 : ℕ) < 1)
  have hle : jumpCount T (T 0) ≤ 1 := by
    exact Nat.sInf_le (show 1 ∈ {n : ℕ | T 0 < T n} from h01)
  have hge : 1 ≤ jumpCount T (T 0) := by
    have hmem : jumpCount T (T 0) ∈ {n : ℕ | T 0 < T n} :=
      Nat.sInf_mem (show Set.Nonempty {n : ℕ | T 0 < T n} from ⟨1, h01⟩)
    have hnz : jumpCount T (T 0) ≠ 0 := by
      intro hz
      change T 0 < T (jumpCount T (T 0)) at hmem
      rw [hz] at hmem
      exact (lt_irrefl _) hmem
    omega
  exact Nat.le_antisymm hle hge
