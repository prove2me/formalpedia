-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Sys.isT_partial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:14:39.099773+00:00
-- url     : https://prove2.me/submissions/bc6c5a98-d073-4086-ad9b-32a7e43980c8

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_ordGE_alt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_pow_eq_zero_of_lt
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
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {Xc : Cart V d I J} (S : Sys Xc)
namespace Formalism.L2.FormalSeriesBounds
namespace Sys
theorem _root_.solution {t : I → MvPowerSeries I C} (ht : S.IsT t) (x : I) (N : ℕ) (μ : I →₀ ℕ)
    (hμ : μ.degree ≤ N) :
    coeff μ (∑ s ∈ Finset.range (N + 1), ∑ c : I, S.al c s x • t c ^ (V.l ^ s)) =
      coeff μ (X x : MvPowerSeries I C) := by
  rw [coeff_X, ← ht.2 x μ, map_sum]
  symm
  refine Finset.sum_subset_zero_on_sdiff (Finset.range_subset_range.2 (by omega)) ?_ ?_
  · intro s hs
    have hs' : μ.degree < s := by
      have := (Finset.mem_sdiff.1 hs).2
      simp only [Finset.mem_range, not_lt] at this
      omega
    rw [map_sum]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [map_smul, coeff_pow_eq_zero_of_lt (S.ordGE_alt ht c) V.l_prime.one_lt hs', smul_zero]
  · intro s _
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, smul_eq_mul]
end Sys
end Formalism.L2.FormalSeriesBounds
