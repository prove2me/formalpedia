-- Prove2me | solution 1 for Formalism.L2.G.Triv.exists_place
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:24.073622+00:00
-- url     : https://prove2.me/submissions/42fc6d4a-439e-4184-975d-f11cbf86fc59

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ClosureUpperUni
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddPowOfMulSelfEqZero
import Definitions.Def_Lemmata_GeneralBFactLeftTail_Imports
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_OneAddPowOfSq
import Theorems.Thm_Bl_general_b_fact_left_tail_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
variable {F : Type} [Field F] [NumberField F] {k : ℕ}
namespace Formalism.L2.G.Triv
theorem _root_.solution (g : ℕ) (hg : g.Prime) : ∃ v : HeightOneSpectrum (𝓞 F), (g : 𝓞 F) ∈ v.asIdeal := by
  first | exact Bl.general_b_fact_left_tail.goal1 .. | (apply Bl.general_b_fact_left_tail.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_tail.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_tail.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_tail.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_tail.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_left_tail.goal1 F ‹_› ‹_› g hg | exact @Bl.general_b_fact_left_tail.goal1 F ‹_› ‹_› g | exact @Bl.general_b_fact_left_tail.goal1 F ‹_› ‹_› | exact @Bl.general_b_fact_left_tail.goal1 F ‹_› | exact @Bl.general_b_fact_left_tail.goal1 F
end Formalism.L2.G.Triv
