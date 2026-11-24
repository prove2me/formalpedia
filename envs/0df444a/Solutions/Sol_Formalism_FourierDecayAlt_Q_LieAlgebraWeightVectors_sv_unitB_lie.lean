-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_unitB_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:23:27.077341+00:00
-- url     : https://prove2.me/submissions/936fd59f-ab00-4ddf-bf83-1ad50f313610

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_herm_out
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_herm_swap
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_unitB_kill
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpart1_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpart2_lie


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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hBs : IsFrameOf k r [z] Bs) (a b : Fin m) :
    inLieW k r z (hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b)) ∧
      inLieW k r z (hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b)) := by
  have hzB : ∀ x, herm (Hpk k r) z (Bs x) = 0 := fun x => by
    rw [sv_herm_swap, hBs.2.2 x z (List.mem_singleton_self z), star_zero]
  have heB : ∀ (c : Fin r) x, herm (Hpk k r) (bvec (eI k r c)) (Bs x) = 0 := fun c x =>
    sv_herm_out (hBs.1 x) (Or.inl (by simp [eI]))
  have hesB : ∀ (c : Fin r) x, herm (Hpk k r) (bvec (esI k r c)) (Bs x) = 0 := fun c x =>
    sv_herm_out (hBs.1 x) (Or.inr (by have := c.isLt; simp only [esI]; omega))
  have kz := sv_unitB_kill Bs a b (hzB a) (hzB b)
  have ke := fun c => sv_unitB_kill Bs a b (heB c a) (heB c b)
  have kes := fun c => sv_unitB_kill Bs a b (hesB c a) (hesB c b)
  exact ⟨⟨Qx2.hpart1_lie _, kz.1, fun c => ⟨(ke c).1, (kes c).1⟩⟩,
    ⟨Qx2.hpart2_lie _, kz.2, fun c => ⟨(ke c).2, (kes c).2⟩⟩⟩
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
