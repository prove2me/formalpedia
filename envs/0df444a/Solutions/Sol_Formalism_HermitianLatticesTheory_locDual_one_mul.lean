-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locDual_one_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:29.175053+00:00
-- url     : https://prove2.me/submissions/f80c0e56-673b-4e01-ab69-1289db4592ab

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {a b : K} (ha : a ∈ (1 : Submodule R K)) (hb : b ∈ (1 : Submodule R K)) :
    a * b ∈ (1 : Submodule R K) := by
  simpa using Submodule.mul_mem_mul ha hb
end Formalism.HermitianLatticesTheory
