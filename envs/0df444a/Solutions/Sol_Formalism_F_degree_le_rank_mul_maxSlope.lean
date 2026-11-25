-- Prove2me | solution 1 for Formalism.F.degree_le_rank_mul_maxSlope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:55:23.955911+00:00
-- url     : https://prove2.me/submissions/3ca7a75d-6c6d-4750-8d48-155c977a0002

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolPos
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopesBdd
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeLeMuMaxOf
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeInequality
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_OrthSum
import Theorems.Thm_Formalism_F_covol_basic_properties
import Theorems.Thm_Formalism_F_discreteTopology_of_le
import Theorems.Thm_Formalism_F_gram_det_le
import Theorems.Thm_Formalism_F_slopeLeMuMax_of
import Theorems.Thm_Formalism_F_slopesBdd_of


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
open Formalism Formalism.F
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.F
theorem _root_.solution (L N : Submodule ℤ E) (hL : DiscreteTopology L) (hNL : N ≤ L) :
    deg N ≤ rk N * muMax L := by
  haveI := hL
  by_cases hN : N = ⊥
  · subst hN
    have h0 : covol (⊥ : Submodule ℤ E) = 1 := (covol_basic_properties E).1
    have hr : rk (⊥ : Submodule ℤ E) = 0 := by simp [rk]
    simp [deg, h0, hr]
  · haveI : DiscreteTopology N := discreteTopology_of_le hNL
    have hs : slope N ≤ muMax L := slopeLeMuMax_of (slopesBdd_of gram_det_le) E L N hL hNL hN
    have hk : 0 < rk N := Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hN)
    have hk' : (0 : ℝ) < (rk N : ℝ) := by exact_mod_cast hk
    unfold slope at hs
    rw [div_le_iff₀ hk'] at hs
    linarith
end Formalism.F
