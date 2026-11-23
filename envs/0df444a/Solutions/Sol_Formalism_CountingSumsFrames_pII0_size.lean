-- Prove2me | solution 1 for Formalism.CountingSumsFrames.pII0_size
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:13.773344+00:00
-- url     : https://prove2.me/submissions/77b5e672-4b9a-44fc-be33-f1c6039a524e

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSizeBoundsHolds
import Theorems.Thm_Formalism_CountingSumsFrames_pII0_basic
import Theorems.Thm_Formalism_CountingSumsFrames_sizeBound_frame_le
import Theorems.Thm_Formalism_CountingSumsFrames_sizeBound_multiplicity_le
import Theorems.Thm_Formalism_CountingSumsFrames_sizeBound_count_le
import Theorems.Thm_Formalism_CountingSumsFrames_sizeBound_card_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CountingSumsFrames
open Real
namespace Formalism.CountingSumsFrames
theorem _root_.solution (CE p r N N₁ Nₛ k Q c' Y al : ℝ) (hCE : 0 ≤ CE) (hp : 0 ≤ p) (hpQ : p ≤ Q)
    (hQ : 1 ≤ Q) (hr : 2 ≤ r) (hrN1 : r ≤ N₁) (hN1 : N₁ ^ 2 ≤ r * N) (hk : N₁ + 3 * r ≤ k)
    (hNs0 : 0 ≤ Nₛ) (hNs1 : Nₛ ≤ N₁) (hNs2 : Nₛ ≤ 2 * N) (hc : 1 ≤ c') (hY : 0 ≤ Y)
    (hal0 : 0 ≤ al) (hal : al ≤ 1 + r * k * Q) :
    32 * p * Y * k ^ 2 * Nₛ * Q ^ 2 *
        (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') + 1)
      ≤ 32 * (2 * CE + 7) * (k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y) := by
  obtain ⟨hrN, hk8, hN1r⟩ := pII0_basic r N N₁ k hr hrN1 hN1 hk
  have hN0 : 0 ≤ N := by linarith
  set S := (2 * Q + 3) * c' + k * Q + c' * al + 3 * c' with hS
  have hS0 : 0 ≤ S := by
    have : 0 ≤ c' * al := by nlinarith
    nlinarith
  have hS3 : S ≤ 3 * r * k * c' * Q := sizeBound_multiplicity_le r k Q c' al hQ hr hk8 hc hal
  have h1 := sizeBound_frame_le r N N₁ Nₛ k hr hrN1 hN1 hk8 hN0 hNs1 hNs2
  have h3 := sizeBound_count_le r N N₁ Nₛ (by linarith) hN1 hNs1
  have h4 := sizeBound_card_le r N Nₛ k Q c' hr (by linarith) hQ hc hN0 hNs2
  set M := k * r ^ 2 * N * Q ^ 2 * c' with hM
  have hQ2 : Q ≤ Q ^ 2 := by nlinarith
  have a1 : Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2) ≤ 2 * CE * M := by
    have : Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2) = (CE * c' * Q ^ 2) * (Nₛ * (N₁ + r * k)) := by ring
    rw [this]
    have hcq : 0 ≤ CE * c' * Q ^ 2 := by positivity
    calc (CE * c' * Q ^ 2) * (Nₛ * (N₁ + r * k)) ≤ (CE * c' * Q ^ 2) * (2 * r ^ 2 * N * k) :=
          mul_le_mul_of_nonneg_left h1 hcq
      _ = 2 * CE * M := by rw [hM]; ring
  have a2 : Nₛ * ((N₁ + 1) * S) ≤ 6 * M := by
    have e : Nₛ * ((N₁ + 1) * S) = (Nₛ * (N₁ + 1)) * S := by ring
    rw [e]
    have hr0 : 0 ≤ 2 * r * N := by positivity
    calc (Nₛ * (N₁ + 1)) * S ≤ (2 * r * N) * S := mul_le_mul_of_nonneg_right h3 hS0
      _ ≤ (2 * r * N) * (3 * r * k * c' * Q) := mul_le_mul_of_nonneg_left hS3 hr0
      _ = 6 * (k * r ^ 2 * N * Q * c') := by ring
      _ ≤ 6 * M := by
        rw [hM]
        have : 0 ≤ k * r ^ 2 * N * c' := by positivity
        nlinarith
  have a3 : Nₛ ≤ M := by rw [hM]; linarith [h4, show r ^ 2 * N * k * c' * Q ^ 2 = k * r ^ 2 * N * Q ^ 2 * c' by ring]
  have hX : Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1) ≤ (2 * CE + 7) * M := by
    have : Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1)
        = Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2) + Nₛ * ((N₁ + 1) * S) + Nₛ := by ring
    rw [this]; linarith
  have hB : 0 ≤ 32 * Y * k ^ 2 * Q ^ 2 := by positivity
  have hpX : p * (Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1)) ≤ Q * ((2 * CE + 7) * M) := by
    have hX0 : 0 ≤ Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1) := by
      have : 0 ≤ CE * c' * (N₁ + r * k) * Q ^ 2 := by
        have : 0 ≤ N₁ + r * k := by nlinarith
        positivity
      have : 0 ≤ (N₁ + 1) * S := mul_nonneg (by linarith) hS0
      positivity
    calc p * _ ≤ Q * (Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1)) :=
          mul_le_mul_of_nonneg_right hpQ hX0
      _ ≤ Q * ((2 * CE + 7) * M) := mul_le_mul_of_nonneg_left hX (by linarith)
  calc 32 * p * Y * k ^ 2 * Nₛ * Q ^ 2 * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1)
      = (32 * Y * k ^ 2 * Q ^ 2) * (p * (Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1))) := by ring
    _ ≤ (32 * Y * k ^ 2 * Q ^ 2) * (Q * ((2 * CE + 7) * M)) := mul_le_mul_of_nonneg_left hpX hB
    _ = 32 * (2 * CE + 7) * (k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y) := by rw [hM]; ring
end Formalism.CountingSumsFrames
