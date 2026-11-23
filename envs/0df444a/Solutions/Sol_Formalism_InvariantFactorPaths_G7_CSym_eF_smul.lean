-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CSym.eF_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:17.860648+00:00
-- url     : https://prove2.me/submissions/ef9fc7e4-ea37-48a7-afac-077afdd3f9f7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_GaussElementarySymmetric
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_eF_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.InvariantFactorPaths.G7.CSym
variable {K σ : Type} [CommRing K] [Fintype σ]
namespace Formalism.InvariantFactorPaths.G7.CSym
theorem _root_.solution (c : K) (x : σ → K) (l : ℕ) : eF (fun i => c * x i) l = c ^ l * eF x l := by
  simp only [eF_eq_sum, Finset.prod_mul_distrib, Finset.prod_const, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [(Finset.mem_powersetCard.1 hs).2]
end Formalism.InvariantFactorPaths.G7.CSym
