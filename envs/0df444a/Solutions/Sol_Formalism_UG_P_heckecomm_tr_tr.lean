-- Prove2me | solution 1 for Formalism.UG.P.heckecomm_tr_tr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:20.738855+00:00
-- url     : https://prove2.me/submissions/9cd56a78-64f2-477b-b37d-9c11caef06a6

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
theorem _root_.solution (x : GL (Fin n) R) : heckecomm_tr (heckecomm_tr x) = x := by
  apply Units.ext
  simp only [heckecomm_tr_val, Matrix.transpose_transpose]
end Formalism.UG.P
