-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz2.term_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:22.590806+00:00
-- url     : https://prove2.me/submissions/a5628ed0-1a8b-4fcc-b308-6e8e7029b261

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz2
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz2
theorem _root_.solution (M N : ℕ) (hM : 3 ≤ M) (hN : 1 ≤ N) :
    1 / ((N : ℝ) + 1) ^ M ≤
      4 / 2 ^ M * (1 / ((N : ℝ) * (N + 1)) - 1 / (((N : ℝ) + 1) * (N + 2))) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hM
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : 4 / (2 : ℝ) ^ (3 + t) * (1 / ((N : ℝ) * (N + 1)) - 1 / (((N : ℝ) + 1) * (N + 2)))
      = 1 / (2 ^ t * ((N : ℝ) * (N + 1) * (N + 2))) := by
    rw [pow_add]
    field_simp
    ring
  rw [h1]
  apply one_div_le_one_div_of_le (by positivity)
  rw [pow_add, mul_comm]
  have h2 : (2 : ℝ) ^ t ≤ ((N : ℝ) + 1) ^ t := pow_le_pow_left₀ (by norm_num) (by linarith) t
  have h3 : (N : ℝ) * (N + 1) * (N + 2) ≤ ((N : ℝ) + 1) ^ 3 := by nlinarith
  exact mul_le_mul h3 h2 (by positivity) (by positivity)
end Formalism.FourierDecayAlt.P.Sz2
