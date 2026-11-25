-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prodUnitaryOrderRatioBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:58:11.578808+00:00
-- url     : https://prove2.me/submissions/8deb015b-8b07-41e1-89aa-3075a9495fbc

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_unitaryOrderRatioBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ThetaProd := by
  intro ι P j e ep η q h
  have hb : ∀ p ∈ P, 0 < Formalism.HermitianLatticeCounting.LatticeSumBounds.theta j (ep p) (η p) (q p) ∧
      Formalism.HermitianLatticeCounting.LatticeSumBounds.theta j (ep p) (η p) (q p) ≤ 2 ^ e := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := h p hp
    obtain ⟨b1, -, b3⟩ := unitaryOrderRatioBound j (ep p) (η p) (q p) h2 h3 h4
    exact ⟨b1, b3.trans (pow_le_pow_right₀ (by norm_num) h1)⟩
  refine ⟨Finset.prod_pos (fun p hp => (hb p hp).1), ?_⟩
  calc ∏ p ∈ P, Formalism.HermitianLatticeCounting.LatticeSumBounds.theta j (ep p) (η p) (q p) ≤ ∏ _p ∈ P, (2:ℝ) ^ e :=
        Finset.prod_le_prod (fun p hp => (hb p hp).1.le) (fun p hp => (hb p hp).2)
    _ = 2 ^ (e * P.card) := by rw [Finset.prod_const, ← pow_mul]
end Formalism.HermitianLatticeCounting.P
