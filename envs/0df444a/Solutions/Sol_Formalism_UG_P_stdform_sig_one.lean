-- Prove2me | solution 1 for Formalism.UG.P.stdform_sig_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:08.363806+00:00
-- url     : https://prove2.me/submissions/0279bb4a-6934-4634-9b29-37549b956568

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution : HasSignature (1 : Matrix n n ℂ) (Fintype.card n) 0 := by
  refine ⟨(Fintype.equivFin n).trans (Equiv.sumEmpty _ _).symm, 1, ?_⟩
  simp [Jpq, cT]
  ext (i | i) (j | j)
  all_goals first | exact Fin.elim0 i | exact Fin.elim0 j | simp [Matrix.one_apply]
end Formalism.UG.P
