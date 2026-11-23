-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CSym.coeff_genE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:10.334649+00:00
-- url     : https://prove2.me/submissions/dd89c82e-d5db-4b59-b3fc-35622d0dbf01

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
theorem _root_.solution (x : σ → K) (l : ℕ) : PowerSeries.coeff l (genE x) = eF x l := by
  classical
  rw [eF_eq_sum, Finset.powersetCard_eq_filter, Finset.sum_filter]
  unfold genE
  have hc : ∀ i, (1 + PowerSeries.C (x i) * PowerSeries.X : PowerSeries K) =
      PowerSeries.C (x i) * PowerSeries.X + 1 := fun i => add_comm _ _
  simp_rw [hc]
  rw [Finset.prod_add, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const, ← map_prod,
    PowerSeries.coeff_C_mul_X_pow]
  split_ifs with h1 h2 h2 <;> first | rfl | omega
end Formalism.InvariantFactorPaths.G7.CSym
