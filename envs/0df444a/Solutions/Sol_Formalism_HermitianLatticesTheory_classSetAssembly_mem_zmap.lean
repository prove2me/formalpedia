-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_mem_zmap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:56.137311+00:00
-- url     : https://prove2.me/submissions/e8d9d4ea-22ed-4423-b88b-ff182d4a36a6

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {n : ℕ} (ι : V →+ EuclideanSpace ℝ (Fin n))
    (M : Submodule (NumberField.RingOfIntegers K) V) (v : EuclideanSpace ℝ (Fin n)) :
    v ∈ zmap ι M ↔ ∃ x ∈ M, ι x = v := by
  exact Iff.rfl
end Formalism.HermitianLatticesTheory
