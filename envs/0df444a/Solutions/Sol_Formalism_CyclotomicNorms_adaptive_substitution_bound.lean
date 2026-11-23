-- Prove2me | solution 1 for Formalism.CyclotomicNorms.adaptive_substitution_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:44.538093+00:00
-- url     : https://prove2.me/submissions/e7b491f5-c383-4e9e-ab97-acd6cff0b612

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_AdaptiveSubstitutionBound
import Theorems.Thm_Formalism_CyclotomicNorms_AdaptiveSubstitution_exists_exps_adaptive
import Theorems.Thm_Formalism_CyclotomicNorms_SubstitutionExponents_coeff_subst_weight
import Theorems.Thm_Formalism_CyclotomicNorms_SubstitutionExponents_revLex_wf
import Theorems.Thm_Formalism_CyclotomicNorms_SubstitutionExponents_unique_of_min


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.CyclotomicNorms
open SubstitutionExponents AdaptiveSubstitution
namespace Formalism.CyclotomicNorms
theorem _root_.solution : SubstitutionAdaptive := by
  intro k _ ℓ r s F B hℓ hF
  classical
  have hne : ∀ t, {d | MvPowerSeries.coeff d (F t) ≠ 0}.Nonempty := fun t =>
    (MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero _).1 (hF t)
  let α : Fin s → (Fin r →₀ ℕ) := fun t => (revLex_wf (r := r)).min _ (hne t)
  obtain ⟨e, he1, he2, he3⟩ := exists_exps_adaptive ℓ hℓ α B
  refine ⟨e, he1, he2, fun t h0 => ?_⟩
  have hn : ∀ j, ℓ ^ e j ≠ 0 := fun j => pow_ne_zero _ (by omega)
  have hc := congrArg (PowerSeries.coeff (weight (fun j => ℓ ^ e j) (α t))) h0
  rw [coeff_subst_weight (fun j => ℓ ^ e j) hn, map_zero,
    finsum_eq_single _ (α t)] at hc
  · rw [if_pos rfl] at hc
    exact (revLex_wf (r := r)).min_mem _ (hne t) hc
  · intro d hd
    by_cases hw : weight (fun j => ℓ ^ e j) d = weight (fun j => ℓ ^ e j) (α t)
    · rw [if_pos hw]
      by_contra hcd
      exact hd (unique_of_min _ (α t) (he3 t) d
        ((revLex_wf (r := r)).not_lt_min _ (show d ∈ {d | MvPowerSeries.coeff d (F t) ≠ 0} from hcd)) hw)
    · rw [if_neg hw]
end Formalism.CyclotomicNorms
