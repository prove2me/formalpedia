-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.integral_field_refinement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:30.466028+00:00
-- url     : https://prove2.me/submissions/4a0d4254-fba2-444d-aa70-7e0427e68033

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_finsum_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_out_sub_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_lat_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_volL_refine
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_relIndex_ne_zero
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
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x3
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.IntKRefine := by
  intro K _ _ _ R ψ hd Λ Λ' L d f hΛ hΛ' _ hle _ hf
  have hR := lat_R hd.isOpen hd.isCompact
  have hne : Λ'.relIndex Λ ≠ 0 := relIndex_ne_zero hΛ'.1 hΛ.2
  have : Finite (Λ ⧸ Λ'.addSubgroupOf Λ) := Nat.finite_of_card_ne_zero hne
  let e : (Fin d → K ⧸ Λ') ≃ (Fin d → K ⧸ Λ) × (Fin d → Λ ⧸ Λ'.addSubgroupOf Λ) :=
    (Equiv.piCongrRight fun _ => AddSubgroup.quotientEquivProdOfLE hle).trans
      (Equiv.arrowProdEquivProdArrow _ _ _)
  have key : ∑ᶠ y : Fin d → K ⧸ Λ', f (fun i => Quotient.out (y i)) =
      ((Λ'.relIndex Λ : ℂ)) ^ d * ∑ᶠ y : Fin d → K ⧸ Λ, f (fun i => Quotient.out (y i)) := by
    have hc : (Nat.card (Fin d → Λ ⧸ Λ'.addSubgroupOf Λ) : ℂ) = ((Λ'.relIndex Λ : ℂ)) ^ d := by
      rw [Nat.card_fun]
      simp [AddSubgroup.relIndex, AddSubgroup.index]
    rw [← hc, ← finsum_fst e (fun y : Fin d → K ⧸ Λ => f (fun i => Quotient.out (y i)))]
    refine finsum_congr fun y => ?_
    have := hf (fun i => Quotient.out (y i))
      (fun i => (Quotient.out (AddSubgroup.quotientEquivProdOfLE hle (y i)).1 : K) -
        (Quotient.out (y i) : K)) (fun i => out_sub_mem hle (y i))
    rw [← this]
    congr 1
    funext i
    simp [e]
  unfold intK
  rw [key, volL_refine hR (lat_iff.1 hΛ') (lat_iff.1 hΛ) hle]
  push_cast
  ring
end Formalism.FourierDecayAlt.P
