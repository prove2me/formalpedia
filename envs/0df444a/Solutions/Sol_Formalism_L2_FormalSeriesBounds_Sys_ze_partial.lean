-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Sys.ze_partial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:14:42.452418+00:00
-- url     : https://prove2.me/submissions/7fa58105-9a31-4f87-af75-aad64ec5b42c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_ordGE_alt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_pow_eq_zero_of_lt

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
theorem _root_.solution {t : I → MvPowerSeries I C} (ht : S.IsT t) (κ : J) (N : ℕ) (μ : I →₀ ℕ)
    (hμ : μ.degree ≤ N) :
    coeff μ (S.ze t κ) =
      coeff μ (-∑ s ∈ Finset.Icc 1 N, ∑ c : I, S.be c s κ • t c ^ (V.l ^ s)) := by
  have h1 : coeff μ (S.ze t κ) = -(∑ s ∈ Finset.Icc 1 μ.degree, ∑ c : I,
      S.be c s κ * coeff μ (t c ^ (V.l ^ s))) := rfl
  rw [h1, map_neg, map_sum]
  congr 1
  refine Finset.sum_subset_zero_on_sdiff (Finset.Icc_subset_Icc_right hμ) ?_ ?_
  · intro s hs
    have hs' : μ.degree < s := by
      have h2 := Finset.mem_sdiff.1 hs
      have h3 := Finset.mem_Icc.1 h2.1
      by_contra hcon
      exact h2.2 (Finset.mem_Icc.2 ⟨h3.1, not_lt.1 hcon⟩)
    rw [map_sum]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [map_smul, coeff_pow_eq_zero_of_lt (S.ordGE_alt ht c) V.l_prime.one_lt hs', smul_zero]
  · intro s _
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, smul_eq_mul]
end Sys
end Formalism.L2.FormalSeriesBounds
