-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_subst_linS_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:02:57.652931+00:00
-- url     : https://prove2.me/submissions/4485e9cb-8793-4e65-a81a-19d4c0ed26bf

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_congr
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_linS

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
theorem _root_.solution [Finite σ] (M : τ → σ → C) {F G : MvPowerSeries σ C} {N : ℕ}
    (h : ∀ d : σ →₀ ℕ, d.degree ≤ N → coeff d F = coeff d G) (e : τ →₀ ℕ) (he : e.degree ≤ N) :
    coeff e (subst (linS M) F) = coeff e (subst (linS M) G) :=
  coeff_subst_congr (ordGE_linS M) h e he
end Formalism.L2.FormalSeriesBounds
