-- Prove2me | solution 1 for Formalism.ELL.padicMult_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:44.136824+00:00
-- url     : https://prove2.me/submissions/90aaa448-e728-496f-9d63-5e55bda0c2fc

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_PadicMult
import Theorems.Thm_Formalism_ELL_PadicMultiplication_e_natMul
import Theorems.Thm_Formalism_ELL_PadicMultiplication_integral_natMul
import Theorems.Thm_Formalism_ELL_PadicMultiplication_coeff_subst_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.ELL
open Formalism.G Formalism.ELL.PadicMultiplication
namespace Formalism.ELL
theorem _root_.solution (h : IntValuedZp.{u}) : PadicMult.{u} := by
  intro p _ K _ _ _ F l e hl he0 hel hle b n
  rw [coeff_subst_smul l e hl.1]
  refine h p K (coeffPoly l e n) (fun m => ?_) b
  rw [← coeff_subst_smul l e hl.1, e_natMul F l e hl hel m]
  exact integral_natMul F m n
end Formalism.ELL
