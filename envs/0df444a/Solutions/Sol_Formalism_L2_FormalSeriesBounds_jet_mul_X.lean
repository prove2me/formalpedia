-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.jet_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:56:45.96215+00:00
-- url     : https://prove2.me/submissions/d3464911-a94b-406c-88ae-0f49f8170503

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMJet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_mfact_add_single
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.BaseCaseIdentities (OrdGE)
variable {C : Type} [Field C] {σ τ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (p : MvPolynomial σ C) (x : σ) (G : MvPowerSeries σ C) :
    jetAt0 (p * MvPolynomial.X x) G = jetAt0 p (dVar x G) := by
  unfold jetAt0
  rw [MvPolynomial.support_mul_X, Finset.sum_map]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hd : MvPowerSeries.coeff n (dVar x G) =
      ((n x + 1 : ℕ) : C) * MvPowerSeries.coeff (n + Finsupp.single x 1) G := rfl
  simp only [addRightEmbedding_apply]
  rw [MvPolynomial.coeff_mul_X, mfact_add_single, hd]
  push_cast
  ring
end Formalism.L2.FormalSeriesBounds
