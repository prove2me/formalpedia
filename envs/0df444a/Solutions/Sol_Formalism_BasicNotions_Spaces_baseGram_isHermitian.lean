-- Prove2me | solution 1 for Formalism.BasicNotions.Spaces.baseGram_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:10:23.829155+00:00
-- url     : https://prove2.me/submissions/88298c1d-7d2a-49c7-97d0-92aef44e41a6

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_DataKernels
import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions
open NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct
open Formalism.BasicNotions.Spaces
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (sp : Spaces R F E)
namespace Formalism.BasicNotions.Spaces
theorem _root_.solution : IsHerm (sp.cm.sig : E →+* E) sp.gram0 := by
  unfold IsHerm cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, gram0, Matrix.reindex_apply,
    Matrix.submatrix_apply, HSpace.gram]
  exact (sp.X 0).herm.eq _ _
end Formalism.BasicNotions.Spaces
