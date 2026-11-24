-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.exists_lsmul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:57.620802+00:00
-- url     : https://prove2.me/submissions/ff35e5b0-d76f-4a50-bfb9-ba87b1dd1ff5

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Theorems.Thm_Bl_ScalarIdentities_goal1
import Theorems.Thm_Bl_general_b_fact_second_version_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN
namespace Formalism.IrreducibleCountingLemmas.Z.BN
theorem _root_.solution {K A : Type} [Field K] [IsAlgClosed K] [Ring A] [Algebra K A]
    (S0 : Type) [AddCommGroup S0] [Module K S0] [Module A S0] [IsScalarTower K A S0]
    [FiniteDimensional K S0] [IsSimpleModule A S0] (φ : S0 →ₗ[K] S0) :
    ∃ u : A, ∀ v : S0, u • v = φ v := by
  first | exact Bl.ScalarIdentities.goal1 .. | (apply Bl.ScalarIdentities.goal1 <;> assumption) | (intros; apply Bl.ScalarIdentities.goal1 <;> assumption)
end Formalism.IrreducibleCountingLemmas.Z.BN
