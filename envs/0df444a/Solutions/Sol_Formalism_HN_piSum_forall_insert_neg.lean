-- Prove2me | solution 1 for Formalism.HN.piSum_forall_insert_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:26.507843+00:00
-- url     : https://prove2.me/submissions/bc5e6d90-1360-4d4c-af0e-ddb567de1244

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PiSumForallInsertOnly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
variable {R : Type*} [Ring R] {ι : Type*} [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
namespace Formalism.HN
theorem _root_.solution (s : Finset ι) (a : ι) (q p : ι → Prop) (hq : ¬ q a) :
    (∀ i ∈ insert a s, q i → p i) ↔ ∀ i ∈ s, q i → p i := by
  constructor
  · intro h i hi hqi
    exact h i (Finset.mem_insert_of_mem hi) hqi
  · intro h i hi hqi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact absurd hqi hq
    · exact h i hi hqi
end Formalism.HN
