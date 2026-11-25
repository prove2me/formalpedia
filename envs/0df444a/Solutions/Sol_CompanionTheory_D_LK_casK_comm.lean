-- Prove2me | solution 1 for CompanionTheory.D.LK.casK_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:35:09.18656+00:00
-- url     : https://prove2.me/submissions/b8204a5a-9363-47d5-9296-e250b8e60de9

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialCommutesWeightOperator
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KTypeCount
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_DoubleSumReduceSecond
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_FilterAll
import Theorems.Thm_UpperTheory_Reformulated_B_P6_r26a_PositivityTheory_D_LK_casK_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car
open Formalism.REAL (GlRel KHighest IsWeight CasK)
open PI.UpqRep (rhoC nsq lowK)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
variable {n : ℕ} {ε : Fin n → Bool}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace CompanionTheory.D.LK
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ V} (hE : KRel ε E) {c d : Fin n} (h : ε c = ε d) :
    Commute (E c d) (CasK ε E) :=
  _root_.UpperTheory.Reformulated.B.P6.r26a.PositivityTheory.D.LK.casK_comm hE h
end CompanionTheory.D.LK
