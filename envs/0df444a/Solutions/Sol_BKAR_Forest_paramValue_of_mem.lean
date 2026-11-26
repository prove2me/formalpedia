-- Prove2me | solution 1 for BKAR.Forest.paramValue_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:15:27.33246+00:00
-- url     : https://prove2.me/submissions/8a91f934-aac1-492a-a369-70162a2b02ae

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) (u : F.EdgeParam → ℝ)
    {e : Edge V} (he : e ∈ F.edges) :
    F.paramValue u e = u ⟨e, he⟩ := by
  rw [paramValue, dif_pos he]
end BKAR.Forest
