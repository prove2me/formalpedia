-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_subst_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:56:43.5591+00:00
-- url     : https://prove2.me/submissions/dfd4623e-4474-4e8d-9b27-8ee6e776cb2b

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_finsupp_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_hasSubst_of_ordGE

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
variable {C : Type*} [Field C] {σ τ : Type*}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s))
    {F G : MvPowerSeries σ C} {N : ℕ} (h : ∀ d : σ →₀ ℕ, d.degree ≤ N → coeff d F = coeff d G)
    (e : τ →₀ ℕ) (he : e.degree ≤ N) : coeff e (subst a F) = coeff e (subst a G) := by
  rw [coeff_subst (hasSubst_of_ordGE ha), coeff_subst (hasSubst_of_ordGE ha)]
  refine finsum_congr fun d => ?_
  by_cases hd : d.degree ≤ N
  · rw [h d hd]
  · rw [ordGE_finsupp_prod a ha d e (by omega), smul_zero, smul_zero]
end Formalism.L2.FormalSeriesBounds
