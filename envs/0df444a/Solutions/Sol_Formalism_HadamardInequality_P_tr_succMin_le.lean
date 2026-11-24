-- Prove2me | solution 1 for Formalism.HadamardInequality.P.tr_succMin_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:15:22.63652+00:00
-- url     : https://prove2.me/submissions/d1726374-4b45-474e-ba8d-2c14a2dd1c49

import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_NormUnitaryBounds_NormUnitary
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShortIndependentVectorsOfDualMinimum
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HadamardInequality Formalism.HadamardInequality.P
namespace Formalism.HadamardInequality.P
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) {i : ℕ} {r : ℝ} (v : Fin i → E) (hv : ∀ j, v j ∈ L)
    (hli : LinearIndependent ℝ v) (hr : 0 ≤ r) (hn : ∀ j, ‖v j‖ ≤ r) :
    Formalism.HadamardInequality.succMin L i ≤ r :=
  csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨hr, v, hv, hli, hn⟩
end Formalism.HadamardInequality.P
