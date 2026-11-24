-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.principal_character_orthogonality_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:45:02.975431+00:00
-- url     : https://prove2.me/submissions/02b843f3-7aff-49df-b4d6-ca07b309796f

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszAPOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (q a : ℕ) [NeZero q] (ha : Nat.Coprime a q) (x : ℝ) :
    ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * (if χ = 1 then (x : ℂ) else 0) = (x : ℂ) := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a q).mpr ha
  rw [← hu, ZMod.inv_coe_unit]
  simp [mul_ite, mul_zero, Finset.sum_ite_eq', MulChar.one_apply (Units.isUnit _)]
end Formalism.ZeroFreeDirichlet
