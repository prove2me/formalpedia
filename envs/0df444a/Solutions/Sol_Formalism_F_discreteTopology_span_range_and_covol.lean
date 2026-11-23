-- Prove2me | solution 1 for Formalism.F.discreteTopology_span_range_and_covol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:51.489239+00:00
-- url     : https://prove2.me/submissions/1bfe4f84-7f94-43c8-bfe9-e2948f4beb79

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
import Theorems.Thm_Formalism_F_covol_eq_gram
import Theorems.Thm_Formalism_F_discreteTopology_span_range_of_linearIndependent


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
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → E)
    (hu : LinearIndependent ℝ u) :
    DiscreteTopology (span ℤ (Set.range u)) ∧
      covol (span ℤ (Set.range u)) = Real.sqrt (Matrix.gram ℝ u).det := by
  have hd := discreteTopology_span_range_of_linearIndependent u hu
  refine ⟨hd, ?_⟩
  haveI := hd
  have hZ : LinearIndependent ℤ u := hu.restrict_scalars' ℤ
  rw [covol_eq_gram E (span ℤ (Set.range u)) ι (Basis.span hZ)]
  simp only [Basis.span_apply]
end Formalism.F
