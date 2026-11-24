-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gj_fvec_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:53.258195+00:00
-- url     : https://prove2.me/submissions/06227053-95ce-4f96-8c4b-09634f9515f1

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Matrix Finset
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (r + 1)) (hc : c.val < r)
    (i : Fin (2 * r + k + 1)) : fvec k r z c i = if i.val = c.val then 1 else 0 := by
  simp only [fvec, dif_pos hc, bvec, eI, Pi.single_apply, Fin.ext_iff, Fin.val_mk]
end Formalism.HermitianLatticeCounting.P
