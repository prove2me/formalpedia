-- Prove2me | solution 1 for Formalism.HN.piSum_forall_insert_only
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:26.752163+00:00
-- url     : https://prove2.me/submissions/a353a5f8-8cc7-4d5d-9fcd-d87f4cadeded

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PiSumForallInsertOnly
import Theorems.Thm_Formalism_HN_piSum_forall_insert

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
theorem _root_.solution (s : Finset ι) (a : ι) (q p : ι → Prop) (hq : q a)
    (hs : ∀ i ∈ s, ¬ q i) : (∀ i ∈ insert a s, q i → p i) ↔ p a := by
  rw [piSum_forall_insert s a q p hq]
  exact ⟨fun h => h.1, fun h => ⟨h, fun i hi hqi => absurd hqi (hs i hi)⟩⟩
end Formalism.HN
