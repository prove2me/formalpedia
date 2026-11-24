-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.finite_quotient_of_pow_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:13:28.815862+00:00
-- url     : https://prove2.me/submissions/5e62b433-61b9-4baa-8eca-632b03969131

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution (O : Type) [CommRing O] [IsNoetherianRing O] (V : Type) [AddCommGroup V]
    [Module O V] [Module.Finite O V] (l : O) (J : ℕ) (U : Submodule O V)
    (hfin : Finite (O ⧸ Ideal.span {l})) (hU : ∀ x : V, l ^ J • x ∈ U) : Finite (V ⧸ U) := by
  haveI : Finite (O ⧸ (Ideal.span {l}) ^ J) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian (Ideal.span {l})) J
  haveI : Finite (V ⧸ ((Ideal.span {l}) ^ J • ⊤ : Submodule O V)) :=
    Module.finite_of_finite (O ⧸ (Ideal.span {l}) ^ J)
  have hle : ((Ideal.span {l}) ^ J • ⊤ : Submodule O V) ≤ U := by
    rw [Submodule.smul_le]
    intro r hr n _
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hr
    obtain ⟨c, rfl⟩ := hr
    rw [mul_comm, mul_smul]
    exact U.smul_mem _ (hU n)
  exact Finite.of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
end Formalism.CohomologicalDescent.DepthNonnegative
