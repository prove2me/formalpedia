-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.degree_increment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:15.154836+00:00
-- url     : https://prove2.me/submissions/66fa4ed4-a7c5-431f-8210-bd92182a0b4e

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CircleIntegralInvSubEqZeroOfOutside
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_prod_shifted_ratio_bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.DegStepBound := by
  intro n μ s hμ hint
  refine ⟨fun hinj => prod_shifted_ratio_bounds n μ s hμ hint hinj, fun hinj => ?_⟩
  have hμ' : Function.Injective (-μ) := fun a b h => hμ (neg_injective h)
  have hint' : ∀ a b, ∃ m : ℤ, (-μ) a - (-μ) b = (m : ℝ) := fun a b => by
    obtain ⟨m, hm⟩ := hint a b
    exact ⟨-m, by simp only [Pi.neg_apply]; push_cast; linarith⟩
  have hinj' : Function.Injective (-μ + Pi.single s 1) := by
    intro a b h
    apply hinj
    simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply] at h ⊢
    linarith
  have hb := prod_shifted_ratio_bounds n (-μ) s hμ' hint' hinj'
  have heq : ∏ s' ∈ univ.erase s, ((-μ) s + 1 - (-μ) s') / ((-μ) s - (-μ) s') =
      ∏ s' ∈ univ.erase s, (μ s - 1 - μ s') / (μ s - μ s') := by
    refine Finset.prod_congr rfl (fun s' _ => ?_)
    simp only [Pi.neg_apply]
    rw [show -μ s + 1 - -μ s' = -(μ s - 1 - μ s') by ring, show -μ s - -μ s' = -(μ s - μ s') by ring,
      neg_div_neg_eq]
  rw [heq] at hb
  exact hb
end Formalism.HermitianLatticeCounting.P
