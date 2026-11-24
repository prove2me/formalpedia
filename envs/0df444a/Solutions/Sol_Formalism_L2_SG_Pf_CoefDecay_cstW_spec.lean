-- Prove2me | solution 1 for Formalism.L2.SG.Pf.CoefDecay.cstW_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:59:26.709802+00:00
-- url     : https://prove2.me/submissions/48b65f13-9257-488e-8b55-bf532c785c7b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_SmoothClassInFiniteOrder
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_CoefDecayA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.CoefDecay
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt PI.ComplexConjugateDerivative
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.L2.SG.Pf.CoefDecay
theorem _root_.solution {A : ℝ} {F : B.Mat k r → E} (hF : CCw k r A F) (u v : List (B.Mat k r))
    (hu : ∀ X ∈ u, B.unitLie k r X) (hv : ∀ X ∈ v, B.unitLie k r X) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    B.gN g ^ A * ‖B.dLR u v F g‖ ≤ cstW hF u v := by
  unfold cstW
  rw [dif_pos ⟨hu, hv⟩]
  exact Classical.choose_spec (hF.2 u v hu hv) g hg
end Formalism.L2.SG.Pf.CoefDecay
