-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Minors.card_lead_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:27.032806+00:00
-- url     : https://prove2.me/submissions/46929695-baa3-4045-b07d-a3ded9123112

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Minors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Minors
open Matrix
variable {K : Type} [Field K]
variable [Fintype K]
namespace Formalism.FourierDecayAlt.P.Minors
theorem _root_.solution (r : ℕ) :
    Nat.card {C : Matrix (Fin (r + 1)) (Fin (r + 1)) K // Lead (r + 1) C} =
      Nat.card {A : Matrix (Fin r) (Fin r) K // Lead r A} *
        (Fintype.card K ^ r * (Fintype.card K ^ r * (Fintype.card K - 1))) := by
  classical
  rw [Nat.card_congr (leadSuccEquiv r), Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_fun, Nat.card_congr (unitsEquivNeZero (G₀ := K)).symm, Nat.card_eq_fintype_card (α := Kˣ),
    Fintype.card_units, Nat.card_eq_fintype_card (α := K), Nat.card_eq_fintype_card (α := Fin r),
    Fintype.card_fin]
end Formalism.FourierDecayAlt.P.Minors
