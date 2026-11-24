-- Prove2me | solution 1 for Formalism.L2.Th1.B.KNorm.b_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:34:51.257811+00:00
-- url     : https://prove2.me/submissions/ec8043d1-bf24-4edb-8773-6bb48a27dafc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_TwoTorsionKernelUniqueHolds
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_nadd_le
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_nsub_le
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_nmul1
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_npow1
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_n2le
import Theorems.Thm_Formalism_L2_Th1_B_KNorm_n4le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.KNorm
open Formalism.ELL (InFormalGroupPoints)
open Formalism.L2.Th1.E (px py IntCurve)
open WeierstrassCurve.Affine (Point)
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.L2.Th1.B.KNorm
theorem _root_.solution (W : WeierstrassCurve K) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1)
    (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) :
    ‖W.b₂‖ ≤ 1 ∧ ‖W.b₄‖ ≤ 1 ∧ ‖W.b₆‖ ≤ 1 ∧ ‖W.b₈‖ ≤ 1 := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  refine ⟨nadd_le (npow1 h1 2) (nmul1 n4le h2), nadd_le (nmul1 n2le h4) (nmul1 h1 h3),
    nadd_le (npow1 h3 2) (nmul1 n4le h6), ?_⟩
  exact nsub_le (nadd_le (nsub_le (nadd_le (nmul1 (npow1 h1 2) h6) (nmul1 (nmul1 n4le h2) h6))
    (nmul1 (nmul1 h1 h3) h4)) (nmul1 h2 (npow1 h3 2))) (npow1 h4 2)
end Formalism.L2.Th1.B.KNorm
