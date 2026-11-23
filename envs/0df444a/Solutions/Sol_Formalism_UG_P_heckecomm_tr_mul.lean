-- Prove2me | solution 1 for Formalism.UG.P.heckecomm_tr_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:53.613794+00:00
-- url     : https://prove2.me/submissions/57e386e6-6ca9-4391-9009-034e75eecef0

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckecomm
import Theorems.Thm_Formalism_UG_P_heckecomm_tr_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {R : Type} [CommRing R] {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (x y : GL (Fin n) R) :
    heckecomm_tr (x * y) = heckecomm_tr y * heckecomm_tr x := by
  apply Units.ext
  simp only [heckecomm_tr_val, Units.val_mul, Matrix.transpose_mul]
end Formalism.UG.P
