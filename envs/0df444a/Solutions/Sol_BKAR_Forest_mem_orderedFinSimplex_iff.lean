-- Prove2me | solution 1 for BKAR.Forest.mem_orderedFinSimplex_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:08:13.822589+00:00
-- url     : https://prove2.me/submissions/ff9ead94-9315-4184-90fd-2f3f070646cf

import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution {n : ℕ} (ts : Fin n → ℝ) :
    ts ∈ orderedFinSimplex n ↔
      (∀ i, 0 ≤ ts i ∧ ts i ≤ 1) ∧
        OrderedSimplexParams 1 (List.ofFn ts) :=
  Iff.rfl
end BKAR.Forest
