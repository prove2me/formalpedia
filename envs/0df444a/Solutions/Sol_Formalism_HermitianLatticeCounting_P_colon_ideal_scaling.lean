-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.colon_ideal_scaling
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:42.411717+00:00
-- url     : https://prove2.me/submissions/250913cb-16d2-4958-9ab4-749c9704f92e

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ColonScale := by
  intro E _ _ U _ _ Lam₁ y c aa aa' hc h1 h2
  ext x
  rw [FractionalIdeal.mem_singleton_mul, FractionalIdeal.mem_coeIdeal]
  rw [← h1 x]
  constructor
  · rintro ⟨y', hy', rfl⟩
    rw [FractionalIdeal.mem_coeIdeal, ← h2 y'] at hy'
    rwa [smul_smul, mul_comm] at hy'
  · intro hx
    refine ⟨c⁻¹ * x, ?_, ?_⟩
    · rw [FractionalIdeal.mem_coeIdeal, ← h2, smul_smul, mul_assoc, mul_comm x c, ← mul_assoc,
        inv_mul_cancel₀ hc, one_mul]
      exact hx
    · rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
end Formalism.HermitianLatticeCounting.P
