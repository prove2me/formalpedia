-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.discreteTopology_of_norm_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:00.0098+00:00
-- url     : https://prove2.me/submissions/0192ed8e-8bfb-4e6a-9448-c6b0e67843b2

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolPos
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqCovolume
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ExistsNeZeroNormLeRankDivOfDualMinimum

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
open Formalism Formalism.NormUnitaryCountingLemmas
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.NormUnitaryCountingLemmas
theorem _root_.solution (L : Submodule ℤ E) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x ∈ L, x ≠ 0 → ε ≤ ‖x‖) : DiscreteTopology L := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hball : ({0} : Set L) = Metric.ball (0 : L) ε := by
    ext x
    simp only [Set.mem_singleton_iff, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro rfl
      simpa using hε
    · intro hx
      by_contra hne
      have hx0 : (x : E) ≠ 0 := fun h0 => hne (Subtype.ext h0)
      have := h x x.2 hx0
      rw [Submodule.coe_norm] at hx
      linarith
  rw [hball]
  exact Metric.isOpen_ball
end Formalism.NormUnitaryCountingLemmas
