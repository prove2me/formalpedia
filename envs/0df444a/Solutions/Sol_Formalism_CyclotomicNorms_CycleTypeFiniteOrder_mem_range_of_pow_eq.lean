-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.mem_range_of_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:35.415877+00:00
-- url     : https://prove2.me/submissions/eeaacd6f-5fe4-4d39-bfcc-2ecad41252f9

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Theorems.Thm_Bl_general_b_fact_second_bis_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]
namespace Formalism.CyclotomicNorms.CycleTypeFiniteOrder
theorem _root_.solution (c : Fbar g) (hc : c ^ g = c) :
    c ∈ Set.range (algebraMap (ZMod g) (Fbar g)) := by
  first | exact Bl.general_b_fact_second_bis.goal1 .. | (apply Bl.general_b_fact_second_bis.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_second_bis.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_second_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_second_bis.goal1 <;> first | assumption | infer_instance)
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
