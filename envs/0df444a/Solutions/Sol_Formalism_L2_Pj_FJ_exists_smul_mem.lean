-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:29.961637+00:00
-- url     : https://prove2.me/submissions/47fb86c0-a58e-4824-bf65-52bfe6b8b3f3

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LocalSituation
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
import Theorems.Thm_UpperTheory_Reformulated_B_LocalSituation_exists_smul_mem


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
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace Formalism.L2.Pj.FJ
theorem _root_.solution (X : Data E r) (w : Fin r → E) : ∃ c : 𝓞 E, c ≠ 0 ∧ c • w ∈ X.Λ := by
  first | exact UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem .. | (apply UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem <;> assumption) | (intros; apply UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem E ‹_› ‹_› ‹_› r X w | exact @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem E ‹_› ‹_› ‹_› r X | exact @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem E ‹_› ‹_› ‹_› r | exact @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem E ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem E ‹_› ‹_› | exact @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem E ‹_› | exact @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem E
end Formalism.L2.Pj.FJ
