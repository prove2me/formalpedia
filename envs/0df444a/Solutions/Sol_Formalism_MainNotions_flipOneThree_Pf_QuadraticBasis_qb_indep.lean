-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.qb_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:53:01.139129+00:00
-- url     : https://prove2.me/submissions/ad7cd4d1-e546-4057-b67a-d4ef3ccf1889

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_QuadBasis
import Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_qb_pow
import Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_qb_zero_of_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
variable {W O : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
theorem _root_.solution {p : ℕ} (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W)) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (hθ : ∀ a : W, ¬ w ∣ θ - j a) {a b c d : W}
    (h : j a + j b * θ + j c * w + j d * θ * w = 0) : a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 :=
  ⟨qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).1,
   qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).2.1,
   qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).2.2.1,
   qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).2.2.2⟩
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
