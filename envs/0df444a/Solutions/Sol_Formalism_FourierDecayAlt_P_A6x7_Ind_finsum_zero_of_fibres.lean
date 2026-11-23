-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Ind.finsum_zero_of_fibres
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:45.962128+00:00
-- url     : https://prove2.me/submissions/1f248a55-740a-433c-bd68-3be61056b80c

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.Ind
open Classical
namespace Formalism.FourierDecayAlt.P.A6x7.Ind
theorem _root_.solution {X Y : Type} (κ : X → Y) (g : X → ℂ)
    (hfin : (Function.support g).Finite)
    (h : ∀ c, ∑ᶠ x, (if κ x = c then g x else 0) = 0) : ∑ᶠ x, g x = 0 := by
  rw [finsum_eq_sum_of_support_subset g (s := hfin.toFinset) (by simp)]
  rw [← Finset.sum_fiberwise_of_maps_to (t := hfin.toFinset.image κ) (g := κ)
    (fun x hx => Finset.mem_image_of_mem κ hx)]
  apply Finset.sum_eq_zero
  intro c _
  rw [← h c, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset), Finset.sum_filter]
  intro x hx
  simp only [Set.Finite.coe_toFinset, Function.mem_support]
  intro hg
  apply hx
  simp [hg]
end Formalism.FourierDecayAlt.P.A6x7.Ind
