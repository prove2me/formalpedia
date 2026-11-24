-- Prove2me | solution 1 for Formalism.HN.PlaceLattice.vecAt_smul_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:23.169319+00:00
-- url     : https://prove2.me/submissions/b2f42379-e6ed-40e7-8f83-4070d4dab891

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PlaceLattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.PlaceLattice
theorem _root_.solution (b : Basis ι K V) (v : InfinitePlace K) (a : K) (i : ι) :
    Formalism.HermitianLatticesTheory.vecAt b v (a • b i) = Pi.single i (v.embedding a) := by
  funext i'
  simp only [Formalism.HermitianLatticesTheory.vecAt, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.single_apply, Pi.single_apply]
  by_cases h : i = i'
  · subst h; simp
  · simp [h, Ne.symm h]
end Formalism.HN.PlaceLattice
