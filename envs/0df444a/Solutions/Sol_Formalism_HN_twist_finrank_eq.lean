-- Prove2me | solution 1 for Formalism.HN.twist_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:02.222813+00:00
-- url     : https://prove2.me/submissions/9521c12a-b901-402f-aba4-131d0d35233a

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TwistFinrankEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] :
    (Module.finrank ℚ K : ℝ) = 2 * (nPl K : ℝ) := by
  have key : Module.finrank ℚ K = 2 * nPl K := by
    have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    haveI : IsEmpty {w : InfinitePlace K // w.IsReal} := by
      refine ⟨fun w => ?_⟩
      have hc : w.1.IsComplex := IsTotallyComplex.isComplex w.1
      first
        | exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hc) w.2
        | exact (NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2) hc
    have h3 : Nat.card {w : InfinitePlace K // w.IsComplex} = Nat.card (InfinitePlace K) :=
      Nat.card_congr (Equiv.subtypeUnivEquiv (fun w => IsTotallyComplex.isComplex w))
    simp only [Fintype.card_eq_nat_card, Nat.card_of_isEmpty, h3] at h1
    simp only [nPl, Fintype.card_eq_nat_card]
    omega
  exact_mod_cast key
end Formalism.HN
