-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locDual_mem_locR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:36:31.301+00:00
-- url     : https://prove2.me/submissions/a568f54f-50c4-47b7-abb8-9509d9bb8077

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
theorem _root_.solution (p : Ideal R) (k : K) :
    k ∈ locR (K := K) p ↔
      ∃ s ∈ hcompl (K := K) p, algebraMap R K s * k ∈ (1 : Submodule R K) := by
  show (∃ s ∈ hcompl (K := K) p, s • k ∈ (1 : Submodule R K)) ↔ _
  simp only [Algebra.smul_def]
end Formalism.HermitianLatticesTheory
