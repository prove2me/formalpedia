-- Prove2me | solution 1 for Formalism.HermitianLattices.ExplicitEstimates.mean_log_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:48.046366+00:00
-- url     : https://prove2.me/submissions/6e935690-eb9f-4a4d-ae5a-84e7f902350b

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_IntegralMultipleNormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ColumnParametrizationOffDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ExplicitEstimates
open Finset
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (hookF)
namespace Formalism.HermitianLattices.ExplicitEstimates
theorem _root_.solution : MeanLogExplicit := by
  intro d k h v hd hk hv hpos hcol
  have hdpos : (0:ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hXpos : ∀ τ, 0 < ∑ c, h τ c := by
    intro τ
    exact Finset.sum_pos (fun c _ => hpos τ c) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hcol' : ∀ c, ∑ τ, h τ c ≤ d * ((k:ℝ) ^ 2 * (2 * v) ^ 2) := by
    intro c
    have h1 := hcol c
    rw [div_le_iff₀ hdpos] at h1
    linarith
  have hT : ∑ τ, ∑ c, h τ c ≤ d * ((k:ℝ) ^ 3 * (2 * v) ^ 2) := by
    rw [Finset.sum_comm]
    have h1 : ∑ c : Fin k, ∑ τ : Fin d, h τ c ≤ ∑ c : Fin k, ((d:ℝ) * ((k:ℝ) ^ 2 * (2 * v) ^ 2)) :=
      Finset.sum_le_sum (fun c _ => hcol' c)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    calc _ ≤ _ := h1
      _ = _ := by ring
  have hTpos : 0 < ∑ τ, ∑ c, h τ c :=
    Finset.sum_pos (fun τ _ => hXpos τ) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (∑ τ, ∑ c, h τ c) / d := ⟨_, rfl⟩
  have hMpos : 0 < M := by rw [hM]; exact div_pos hTpos hdpos
  have hstep : ∀ τ, Real.log (∑ c, h τ c) ≤ Real.log M + (∑ c, h τ c) / M - 1 := by
    intro τ
    have h1 := Real.log_le_sub_one_of_pos (div_pos (hXpos τ) hMpos)
    rw [Real.log_div (hXpos τ).ne' hMpos.ne'] at h1
    linarith
  have hsum1 : ∑ τ, Real.log (∑ c, h τ c) ≤ ∑ τ : Fin d, (Real.log M + (∑ c, h τ c) / M - 1) :=
    Finset.sum_le_sum (fun τ _ => hstep τ)
  have hsum2 : ∑ τ : Fin d, (Real.log M + (∑ c, h τ c) / M - 1)
      = d * Real.log M + (∑ τ, ∑ c, h τ c) / M - d := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hsum3 : (∑ τ, ∑ c, h τ c) / M = d := by
    have h1 := hTpos.ne'
    have h2 := hdpos.ne'
    rw [hM]
    field_simp
  have hMle : M ≤ (k:ℝ) ^ 3 * (2 * v) ^ 2 := by
    rw [hM, div_le_iff₀ hdpos]
    linarith
  have hlog := Real.log_le_log hMpos hMle
  have hfin := mul_le_mul_of_nonneg_left hlog hdpos.le
  rw [div_le_iff₀ hdpos]
  linarith
end Formalism.HermitianLattices.ExplicitEstimates
