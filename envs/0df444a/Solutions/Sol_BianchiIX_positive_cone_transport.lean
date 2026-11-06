-- Prove2me | solution 1 for BianchiIX.positive_cone_transport
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:03:46.595785+00:00
-- url     : https://prove2.me/submissions/8c5100b2-4240-4331-8f7f-59d0d4930109

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


/-- Positive radial normalization transports a cone and adds the logarithmic phase errors. -/
theorem solution (D : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
    {w : Fin 3 → ℝ} {a b : Fin 2 → ℝ} {L : ℝ} (hw0 : 0 < w 0)
    (hw : ∀ i : Fin 2, |w i.succ| ≤ a i * w 0)
    (H : ∀ z : Fin 3 → ℝ, z 0 = 1 → (∀ i : Fin 2, |z i.succ| ≤ a i) →
      0 < D z 0 ∧ |Real.log (D z 0)| ≤ L ∧ ∀ i : Fin 2, |D z i.succ| ≤ b i * D z 0) :
    0 < D w 0 ∧ |Real.log (D w 0)| ≤ |Real.log (w 0)| + L ∧
      ∀ i : Fin 2, |D w i.succ| ≤ b i * D w 0 := by
  let z := (w 0)⁻¹ • w
  have hz0 : z 0 = 1 := inv_mul_cancel₀ hw0.ne'
  have hz (i : Fin 2) : |z i.succ| ≤ a i := by
    change |(w 0)⁻¹ * w i.succ| ≤ a i
    rw [abs_mul, abs_of_pos (inv_pos.mpr hw0)]
    calc
      _ ≤ (w 0)⁻¹ * (a i * w 0) := mul_le_mul_of_nonneg_left (hw i) (inv_nonneg.mpr hw0.le)
      _ = _ := by field_simp
  obtain ⟨hp, hl, hc⟩ := H z hz0 hz
  have hwz : w = w 0 • z := by
    dsimp only [z]
    rw [smul_smul, mul_inv_cancel₀ hw0.ne', one_smul]
  have hd (i : Fin 3) : D w i = w 0 * D z i := by
    calc
      _ = D (w 0 • z) i := congrArg (fun q => D q i) hwz
      _ = _ := by rw [map_smul]; rfl
  refine ⟨by rw [hd]; exact mul_pos hw0 hp, ?_, ?_⟩
  · rw [hd, Real.log_mul hw0.ne' hp.ne']
    exact (abs_add_le _ _).trans (add_le_add le_rfl hl)
  · intro i
    rw [hd, abs_mul, abs_of_pos hw0, hd]
    exact (mul_le_mul_of_nonneg_left (hc i) hw0.le).trans_eq (by ring)
