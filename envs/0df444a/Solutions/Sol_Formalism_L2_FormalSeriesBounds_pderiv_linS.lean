-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.pderiv_linS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:56:57.766437+00:00
-- url     : https://prove2.me/submissions/97eb9fdb-6a05-4e56-bcd1-6a654bcdefc8

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin

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
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type*} [Field C] {σ τ : Type*} [Fintype τ]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (M : τ → σ → C) (b : τ) (w : σ) :
    pderiv C b (linS M w) = MvPowerSeries.C (M b w) := by
  unfold linS
  rw [map_sum, Finset.sum_eq_single b]
  · rw [Derivation.map_smul, pderiv_X_self, smul_eq_C_mul, mul_one]
  · intro c _ hc
    rw [Derivation.map_smul, pderiv_X_of_ne hc, smul_zero]
  · intro h; exact absurd (Finset.mem_univ b) h
end Formalism.L2.FormalSeriesBounds
