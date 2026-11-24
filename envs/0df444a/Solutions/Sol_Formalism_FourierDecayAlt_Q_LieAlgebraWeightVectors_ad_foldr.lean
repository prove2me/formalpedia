-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_foldr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:52:00.16474+00:00
-- url     : https://prove2.me/submissions/dc437945-86c4-4137-a37f-5f3d40c7957f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBCtMulVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBLie

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
theorem _root_.solution {ι X Y : Type*} (K : Set X) (P : X → Y) (l : List ι) (T : ι → X → X) (T' : ι → Y → Y)
    (hK : ∀ j, ∀ x ∈ K, T j x ∈ K) (hP : ∀ j, ∀ x ∈ K, P (T j x) = T' j (P x)) (x : X) (hx : x ∈ K) :
    (l.map T).foldr (fun S h => S h) x ∈ K ∧
      P ((l.map T).foldr (fun S h => S h) x) = (l.map T').foldr (fun S h => S h) (P x) := by
  induction l with
  | nil => exact ⟨hx, rfl⟩
  | cons j l ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨hK j _ h1, ?_⟩
    simp only [List.map_cons, List.foldr_cons]
    rw [hP j _ h1, h2]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
