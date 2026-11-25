-- Prove2me | solution 1 for Formalism.F.orthogonal_sum_slope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:26:11.768088+00:00
-- url     : https://prove2.me/submissions/db9f82f4-255b-494b-bc8d-9c3e96637317

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
import Theorems.Thm_Formalism_F_discreteTopology_sup_and_covol_sup
import Theorems.Thm_Formalism_F_slope_le_max_maxSlope
import Theorems.Thm_Formalism_F_covol_pos_of_discrete
import Theorems.Thm_Formalism_F_gram_det_le
import Theorems.Thm_Formalism_F_muMaxMono_of
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
namespace Formalism.F
theorem _root_.solution : OrthSum := by
  intro E _ _ _ L₁ L₂ h1 h2 h
  haveI := h1
  haveI := h2
  obtain ⟨hd, hc⟩ := discreteTopology_sup_and_covol_sup L₁ L₂ h
  refine ⟨hd, ?_, ?_⟩
  · have p1 := covol_pos_of_discrete L₁
    have p2 := covol_pos_of_discrete L₂
    unfold deg
    rw [hc, Real.log_mul p1.ne' p2.ne']
    ring
  · intro hL1 hL2
    apply le_antisymm
    · show sSup (slopes (L₁ ⊔ L₂)) ≤ _
      refine csSup_le ⟨_, L₁, le_sup_left, hL1, rfl⟩ ?_
      rintro t ⟨N, hN, hN0, rfl⟩
      exact slope_le_max_maxSlope L₁ L₂ h1 h2 h hd N hN hN0
    · have hmono := muMaxMono_of (slopesBdd_of gram_det_le)
      exact max_le (hmono E (L₁ ⊔ L₂) L₁ hd le_sup_left hL1)
        (hmono E (L₁ ⊔ L₂) L₂ hd le_sup_right hL2)
end Formalism.F
