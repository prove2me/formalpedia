-- Prove2me | solution 1 for Formalism.L2.G.RelativeIndexFlags.Core.prodSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:38:12.941951+00:00
-- url     : https://prove2.me/submissions/ddf08725-f58b-4d1d-8568-5e2ab8e7df56

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Lemmata_GeneralBFactLeftSide_Imports
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_IntegralWeylLatticeSpan_WeylEqSpanInt
import Theorems.Thm_P2M_Bl_general_b_fact_left______goal1_a57afc021d90


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.RelativeIndexFlags Formalism.L2.G.RelativeIndexFlags.Core
namespace Formalism.L2.G.RelativeIndexFlags.Core
theorem _root_.solution {O A I : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype I] [DecidableEq I]
    {B : I → Type} [∀ i, AddCommGroup (B i)] [∀ i, Module O (B i)] (ε : ∀ i, B i →ₗ[O] A) (T : ∀ i, Set (B i)) :
    Submodule.span O {X | ∃ F : ∀ i, B i, (∀ i, F i ∈ Submodule.span O (T i)) ∧ X = ∏ i, ε i (F i)} =
      Submodule.span O {X | ∃ F : ∀ i, B i, (∀ i, F i ∈ T i) ∧ X = ∏ i, ε i (F i)} := by
  first | exact Bl.general_b_fact_left'''''.goal1 .. | (apply Bl.general_b_fact_left'''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left'''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_left'''''.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left'''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_left'''''.goal1 <;> first | assumption | infer_instance)
end Formalism.L2.G.RelativeIndexFlags.Core
