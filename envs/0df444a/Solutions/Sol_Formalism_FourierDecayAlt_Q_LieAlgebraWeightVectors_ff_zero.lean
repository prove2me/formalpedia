-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:52:00.363604+00:00
-- url     : https://prove2.me/submissions/24189ecc-57ce-4f7a-add6-3ccd198f9ba1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_TopLevelPointwiseIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution : (fun _ => (0 : Wq →L[ℂ] Wp)) ∈ FFl k r z z' π π' (Fin.last r) D := by
  simp only [FFl, SmoothLev, LeftEq, RightEq, Set.mem_ofPred_eq]
  refine ⟨fun g₀ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const,
    fun _ _ _ => rfl⟩, fun _ _ _ _ => (smul_zero _).symm, fun _ _ _ _ => (smul_zero _).symm,
    fun _ _ _ _ _ _ => ?_⟩
  simp
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
