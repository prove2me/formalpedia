-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx3.norm_B
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:49:48.193956+00:00
-- url     : https://prove2.me/submissions/72600608-ac63-463a-a39d-a64875b2a3bb

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx3
namespace Formalism.FourierDecayAlt.P.Jx3
theorem _root_.solution (hN : S6.NormIdl) (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ)
    (hg : 0 < g) : (FractionalIdeal.absNorm (S6.idl E g 0 (-(ν + 1))) : ℝ) =
      ((S6.rd E ^ (-(ν + 1))) ^ S6.deg E) ^ 2 := by
  have h := hN E g 0 (-(ν + 1)) hg
  rw [zpow_zero, one_mul] at h
  rw [← h, Real.sq_sqrt]
  exact_mod_cast (FractionalIdeal.absNorm_nonneg _)
end Formalism.FourierDecayAlt.P.Jx3
