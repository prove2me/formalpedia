-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.corollary_consequence_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:14.311368+00:00
-- url     : https://prove2.me/submissions/f9f9d04e-87e5-4b1f-bc77-f4161e3a8281

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_corollary_upper_estimate_holds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_corollary_lower_estimate_holds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_corollary_mass_estimate_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
open scoped ENNReal
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.MomentBound₂ := by
  intro Ω _ μ _ r q l H0 R T hm hpos hH0 hR hT h0 hc hl
  have hH0' : (0:ℝ) ≤ H0 := by linarith
  have hM1 : (1:ℝ) ≤ max 1 R := le_max_left _ _
  have hMR : R ≤ max 1 R := le_max_right _ _
  have hH1 : 0 < H0 * max 1 R ^ r := by positivity
  have hab : ∀ a, ∫⁻ ω, ENNReal.ofReal (l a ω ^ (2 * q)) ∂μ ≤ ENNReal.ofReal ((H0 * max 1 R ^ r) ^ (2 * q)) ∧
      ∫⁻ ω, ENNReal.ofReal ((l a ω)⁻¹ ^ (2 * q)) ∂μ ≤ ENNReal.ofReal ((H0 * max 1 R ^ r) ^ (2 * q)) := by
    intro a
    have ha : a.val ≤ r := Nat.lt_succ_iff.1 a.isLt
    constructor
    · refine (corollary_upper_estimate_holds Ω μ r q l H0 R hm hpos hH0' hR h0 hc a).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [mul_pow, ← pow_mul]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc R ^ (2 * q * a.val) ≤ max 1 R ^ (2 * q * a.val) := pow_le_pow_left₀ hR hMR _
        _ ≤ max 1 R ^ (r * (2 * q)) := pow_le_pow_right₀ hM1 (by
            rw [mul_comm r]; exact Nat.mul_le_mul_left _ ha)
    · refine (corollary_lower_estimate_holds Ω μ r q l T R hm hpos hT hR hl hc a).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [mul_pow, ← pow_mul]
      calc R ^ (2 * q * (r - a.val)) ≤ max 1 R ^ (2 * q * (r - a.val)) := pow_le_pow_left₀ hR hMR _
        _ ≤ max 1 R ^ (r * (2 * q)) := pow_le_pow_right₀ hM1 (by
            rw [mul_comm r]; exact Nat.mul_le_mul_left _ (by omega))
        _ ≤ H0 ^ (2 * q) * max 1 R ^ (r * (2 * q)) :=
            le_mul_of_one_le_left (by positivity) (one_le_pow₀ hH0)
  refine ⟨hab, fun la hla => ?_⟩
  exact corollary_mass_estimate_holds Ω μ r q l _ la hm hpos hH1 hla (fun a => (hab a).1) (fun a => (hab a).2)
end Formalism.HermitianLatticeCounting.P
