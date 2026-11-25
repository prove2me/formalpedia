-- Prove2me | solution 1 for Formalism.L2.Pj.GenericSectionMinimum.kill_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:41:31.017447+00:00
-- url     : https://prove2.me/submissions/ed83a2af-af57-405a-8665-3c349a885d59

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DerAeval
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_TotalDegreePderivLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenericSectionMinimum
open IsLocalRing Cardinal
variable {F : Type} [Field F]
namespace Formalism.L2.Pj.GenericSectionMinimum
theorem _root_.solution (K : Type) [Field K] [Algebra K F] {δ : F → F} (h : IsDer δ)
    (hK : ∀ c, δ (algebraMap K F c) = 0) (s : Set F) (hs : ∀ x ∈ s, δ x = 0) :
    ∀ x ∈ IntermediateField.adjoin K s, δ x = 0 := by
  intro x hx
  have hle : IntermediateField.adjoin K s ≤ constField K h hK :=
    IntermediateField.adjoin_le_iff.mpr (fun y hy => hs y hy)
  exact hle hx
end Formalism.L2.Pj.GenericSectionMinimum
