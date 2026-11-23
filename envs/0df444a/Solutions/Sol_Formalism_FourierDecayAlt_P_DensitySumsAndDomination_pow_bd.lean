-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DensitySumsAndDomination.pow_bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:45.262803+00:00
-- url     : https://prove2.me/submissions/4130075c-e9df-48c6-b83b-e57e1b03c240

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DensitySumsAndDomination

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexInnerProductSpace ComplexOrder ComplexConjugate
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DensitySumsAndDomination
namespace Formalism.FourierDecayAlt.P.DensitySumsAndDomination
theorem _root_.solution (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (((m : ℕ) : ℝ) ^ n)⁻¹ ≤ 4 * ((2 : ℝ) ^ n)⁻¹ * (((m : ℕ) : ℝ) ^ 2)⁻¹ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hm' : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpk : (2 : ℝ) ^ k ≤ (m : ℝ) ^ k := by gcongr
  have hL : ((m : ℝ) ^ (2 + k))⁻¹ = ((m : ℝ) ^ 2)⁻¹ * ((m : ℝ) ^ k)⁻¹ := by
    rw [pow_add, mul_inv]
  have hR : 4 * ((2 : ℝ) ^ (2 + k))⁻¹ * ((m : ℝ) ^ 2)⁻¹ = ((m : ℝ) ^ 2)⁻¹ * ((2 : ℝ) ^ k)⁻¹ := by
    rw [pow_add, mul_inv]
    first
      | ring
      | (norm_num; ring)
  rw [hL, hR]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hpk) (by positivity)
end Formalism.FourierDecayAlt.P.DensitySumsAndDomination
