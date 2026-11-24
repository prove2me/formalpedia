-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gf_det_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:14.430858+00:00
-- url     : https://prove2.me/submissions/6eda9432-444c-454b-b51e-afe973fd74bb

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
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {K : Type*} [Field K] (O : Subring K) {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (h : ∀ i j, A i j ∈ O) : A.det ∈ O := by
  let B : Matrix n n O := fun i j => ⟨A i j, h i j⟩
  have hB : A = B.map O.subtype := by ext i j; rfl
  have e := RingHom.map_det O.subtype B
  rw [RingHom.mapMatrix_apply] at e
  rw [hB, ← e]
  exact (B.det).2
end Formalism.HermitianLatticeCounting.P
