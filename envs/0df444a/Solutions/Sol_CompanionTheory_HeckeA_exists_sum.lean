-- Prove2me | solution 1 for CompanionTheory.HeckeA.exists_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:12.123172+00:00
-- url     : https://prove2.me/submissions/9fafca76-3de8-4914-b89f-ffad32e07c3b

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalFg
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeA
import Theorems.Thm_Formalism_UG_P_finite_supp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Formalism.UG.P
noncomputable section
open CompanionTheory CompanionTheory.HeckeA
variable {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (ι : H →* G) (K : Subgroup H)
variable {K}
namespace CompanionTheory.HeckeA
theorem _root_.solution (hK : IsCommensurated K) {φ : H → ℂ} (hφ : φ ∈ Hecke ℂ K) :
    ∃ S : Finset (H ⧸ K), ∀ (f : G → W) (g : G), op ι K φ f g = ∑ c ∈ S, φ c.out • f (g * ι c.out) :=
  ⟨(finite_supp K hK φ hφ).toFinset, fun f g => finsum_eq_sum_of_support_subset _ fun c hc => by
    rw [Set.Finite.coe_toFinset]
    exact fun h => hc (by simp only [h, zero_smul])⟩
end CompanionTheory.HeckeA
