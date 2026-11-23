-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.orbZ_rep_eq_base_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:17.138736+00:00
-- url     : https://prove2.me/submissions/d7e858bd-e903-4df0-a3f9-4b1b4cfa5338

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
noncomputable section
variable {K : Type} [CommRing K] (R : Subring K) (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (w : Point K) (y) (q : Cos R w) (hq : kap R k w q = y) :
    ∃ p, IsPP R k p ∧ orbZ w (rep R q) = base R k w y * p := by
  subst hq
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (PPsub R k w.1.sum) q.2.out
  refine ⟨(((h⁻¹ : PPsub R k w.1.sum) : upUniG K w.1.sum) : GL (Fin w.1.sum) K),
    (h⁻¹ : PPsub R k w.1.sum).2, ?_⟩
  unfold base kap
  simp only [orbZ, rep]
  rw [hh]
  simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, Subgroup.coe_inv]
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.A5x9
