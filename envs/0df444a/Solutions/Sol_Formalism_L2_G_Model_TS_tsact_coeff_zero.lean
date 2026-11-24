-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.tsact_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:00:50.166157+00:00
-- url     : https://prove2.me/submissions/0b9973b9-52ac-4f32-9a9b-c2bb0dc69c4d

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingRowAction
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (G : Matrix (Fin r) (Fin r) R) (h : MvPolynomial (Fin r × Fin n) R) :
    coeff 0 (rowAct R G h) = coeff 0 h := by
  show MvPolynomial.constantCoeff (rowAct R G h) = MvPolynomial.constantCoeff h
  induction h using MvPolynomial.induction_on
  next a => simp [rowAct]
  next p q hp hq => simp only [map_add, hp, hq]
  next p v hp => simp [hp, rowAct]
end Formalism.L2.G.Model.TS
