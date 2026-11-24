-- Prove2me | solution 1 for BSLambda.Numerics.neg_log_one_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:29:12.844736+00:00
-- url     : https://prove2.me/submissions/0c2c1e9d-4b7b-4f84-9f9f-bf4afc386e21

module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
namespace BSLambda.Numerics
theorem _root_.solution {y : ℝ} (hy : y < 1) : -Real.log (1 - y) ≤ y / (1 - y) := by
  have hpos : (0 : ℝ) < 1 - y := sub_pos.mpr hy
  have h : (1 - y)⁻¹ - 1 = y / (1 - y) := by rw [← one_div, div_sub_one hpos.ne', sub_sub_cancel]
  linarith [Real.one_sub_inv_le_log_of_pos hpos]
end BSLambda.Numerics
