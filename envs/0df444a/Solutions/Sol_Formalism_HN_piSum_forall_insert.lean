-- Prove2me | solution 1 for Formalism.HN.piSum_forall_insert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:22.873853+00:00
-- url     : https://prove2.me/submissions/966df94b-9aed-48d2-bc59-da7e2bfd97a2

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
theorem _root_.solution (s : Finset ι) (a : ι) (q p : ι → Prop) (hq : q a) :
    (∀ i ∈ insert a s, q i → p i) ↔ p a ∧ ∀ i ∈ s, q i → p i := by
  constructor
  · intro h
    exact ⟨h a (Finset.mem_insert_self a s) hq,
      fun i hi hqi => h i (Finset.mem_insert_of_mem hi) hqi⟩
  · rintro ⟨ha, h⟩ i hi hqi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ha
    · exact h i hi hqi
end Formalism.HN
