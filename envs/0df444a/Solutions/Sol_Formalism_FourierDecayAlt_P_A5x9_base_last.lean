-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.base_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:04.749492+00:00
-- url     : https://prove2.me/submissions/73ba28ca-dd04-4bc0-b913-2ee06165178c

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_inverse_last_column_formula
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
theorem _root_.solution (h : Point K) (s : ℕ) (t : Kˣ) (hs : 1 ≤ s) (hk : h.1.sum ≤ k) (y)
    (a b : Fin (addBlock h s t).1.sum) (ha : k < a.val) (hb : b.val + 1 = (addBlock h s t).1.sum) :
    (base R k (addBlock h s t) y)⁻¹ a b = 0 := by
  have hsum : (addBlock h s t).1.sum = h.1.sum + s := by simp [addBlock]
  let c : Fin (addBlock h s t).1.sum := ⟨h.1.sum, by omega⟩
  exact (inverse_last_column_formula K h s t hs _ _ (y.1.out).2.1 (y.2.out).2 a b c hb rfl).2.1
    (by rw [Fin.lt_def]; show h.1.sum < a.val; omega)
end Formalism.FourierDecayAlt.P.A5x9
