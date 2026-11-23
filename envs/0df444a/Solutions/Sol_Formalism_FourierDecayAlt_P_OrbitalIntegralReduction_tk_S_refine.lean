-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.tk_S_refine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:20.361431+00:00
-- url     : https://prove2.me/submissions/b398bdf4-5d4e-485f-abf7-9730bb94fe27

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_out_sub_mem
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_gi_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_relIndex_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_finsum_fst
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {V : Type} [AddCommGroup V]
variable [TopologicalSpace V] [IsTopologicalAddGroup V]
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution {V₀ M M' : AddSubgroup V} (h0 : Lat V₀) (hM : Lat M) (hM' : Lat M')
    (hle : M' ≤ M) (f : V → ℂ) (hf : ∀ v, ∀ l ∈ M, f (v + l) = f v) :
    tk_S V₀ M' f = tk_S V₀ M f := by
  have hne : M'.relIndex M ≠ 0 := relIndex_ne_zero hM'.op hM.cp
  have : Finite (M ⧸ M'.addSubgroupOf M) := Nat.finite_of_card_ne_zero hne
  have key : ∑ᶠ y : V ⧸ M', f (Quotient.out y) =
      (M'.relIndex M : ℂ) * ∑ᶠ y : V ⧸ M, f (Quotient.out y) := by
    rw [← show Nat.card (M ⧸ M'.addSubgroupOf M) = M'.relIndex M from rfl,
      ← Formalism.FourierDecayAlt.P.A6x3.finsum_fst (AddSubgroup.quotientEquivProdOfLE hle)
        (fun y : V ⧸ M => f (Quotient.out y))]
    refine finsum_congr fun y => ?_
    have := hf (Quotient.out y) _ (tk_out_sub_mem hle y)
    rw [← this]
    congr 1
    abel
  have hg : gi M V₀ = (M'.relIndex M : ℝ) * gi M' V₀ := by
    rw [← gi_trans hM hM' h0]
    congr 1
    rw [gi, AddSubgroup.relIndex_eq_one.2 hle]
    simp
  unfold tk_S
  rw [key, hg]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
