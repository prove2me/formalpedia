-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ad_unitB_ct_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:52:07.204752+00:00
-- url     : https://prove2.me/submissions/6693d489-a561-4a96-9b62-d505718d0955

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_AdUnitBCtMulVec

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a b : Fin m)
    (v : Fin (2 * r + k + 1) → ℂ) :
    (unitB (Hpk k r) Bs a b)ᴴ *ᵥ (Hpk k r *ᵥ v) =
      herm (Hpk k r) v (Bs a) • fun p => star (herm (Hpk k r) (bvec p) (Bs b)) := by
  unfold unitB
  funext p
  show ∑ q, star (Bs a q * herm (Hpk k r) (bvec p) (Bs b)) * (Hpk k r *ᵥ v) q =
    herm (Hpk k r) v (Bs a) * star (herm (Hpk k r) (bvec p) (Bs b))
  rw [show herm (Hpk k r) v (Bs a) = ∑ q, star (Bs a q) * (Hpk k r *ᵥ v) q from rfl, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [star_mul']
  ring
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
