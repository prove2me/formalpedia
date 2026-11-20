-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_size2_compoundPoisson_equals_negative_two_at_first_arrival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:30:59.172943+00:00
-- url     : https://prove2.me/submissions/f5952674-c968-443e-aae8-49df8d5a2c35

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_strictMono_arrival
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (τ Y : ℕ → Ω → ℝ)
    (hJ : IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      (Measure.dirac (-2 : ℝ)) μ) :
    ∀ᵐ ω ∂μ,
      compoundPoisson (0 : ℝ) τ Y (arrival τ 0 ω) ω = -2 := by
  letI : IsProbabilityMeasure μ := hJ.indep.isProbabilityMeasure
  have hMarks : ∀ᵐ ω ∂μ, ∀ n : ℕ, Y n ω = (-2 : ℝ) :=
    (ae_all_iff).2 (fun n => (hJ.law_mark n).ae_eq_of_dirac)
  have hMono : ∀ᵐ ω ∂μ, StrictMono (fun n => arrival τ n ω) :=
    IsCompoundPoissonDriver.ae_strictMono_arrival hJ (by norm_num)
  filter_upwards [hMarks, hMono] with ω hMark hω
  let T : ℕ → ℝ := fun n => arrival τ n ω
  have h01 : T 0 < T 1 := hω (by omega : (0 : ℕ) < 1)
  have hle : jumpCount T (T 0) ≤ 1 :=
    Nat.sInf_le (show 1 ∈ {n : ℕ | T 0 < T n} from h01)
  have hmem : jumpCount T (T 0) ∈ {n : ℕ | T 0 < T n} :=
    Nat.sInf_mem (show Set.Nonempty {n : ℕ | T 0 < T n} from ⟨1, h01⟩)
  have hge : 1 ≤ jumpCount T (T 0) := by
    have hnz : jumpCount T (T 0) ≠ 0 := by
      intro hz
      change T 0 < T (jumpCount T (T 0)) at hmem
      rw [hz] at hmem
      exact (lt_irrefl _) hmem
    omega
  have hNum : jumpCount (fun n => arrival τ n ω) (arrival τ 0 ω) = 1 :=
    Nat.le_antisymm hle hge
  simp [compoundPoisson, piecewisePath, hMark, hNum,
    Finset.sum_const, nsmul_eq_mul]
