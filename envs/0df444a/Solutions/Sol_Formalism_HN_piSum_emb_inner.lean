-- Prove2me | solution 1 for Formalism.HN.piSum_emb_inner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:41.034802+00:00
-- url     : https://prove2.me/submissions/dac299a2-52a1-4827-8d6d-5fc472eca33c

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PiSumForallInsertOnly
import Theorems.Thm_Formalism_HN_piSum_emb_apply

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
variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
namespace Formalism.HN
theorem _root_.solution (i : ι) (u v : E i) :
    inner ℝ (piSum_emb E i u) (piSum_emb E i v) = inner ℝ u v := by
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · rw [piSum_emb_apply, piSum_emb_apply, Pi.single_eq_same, Pi.single_eq_same]
  · intro j _ hj
    rw [piSum_emb_apply, piSum_emb_apply, Pi.single_eq_of_ne hj, inner_zero_left]
  · intro h
    exact absurd (Finset.mem_univ i) h
end Formalism.HN
