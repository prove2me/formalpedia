-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.adK_RZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:07:11.470191+00:00
-- url     : https://prove2.me/submissions/40833889-f424-4771-b934-d7f8f5994e0c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBCtMulVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBLie
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_adK_add
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_adK_smul
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_adK_rd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx2
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution (hD : IsOpen D) {Z : Mx k r} (h1 : inLieLev k r (Fin.last r) (hpart1 (Hpk k r) Z))
    (h2 : inLieLev k r (Fin.last r) (hpart2 (Hpk k r) Z)) {F : Mx k r → (Wq →L[ℂ] Wp)}
    (hF : F ∈ AdK k r z π D) : RZ (Hpk k r) Z F ∈ AdK k r z π D :=
  adK_add (adK_rd hD h1 hF) (adK_smul (adK_rd hD h2 hF) Complex.I)
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
