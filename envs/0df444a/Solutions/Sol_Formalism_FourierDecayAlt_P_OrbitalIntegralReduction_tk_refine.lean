-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.tk_refine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:37.833847+00:00
-- url     : https://prove2.me/submissions/459ee07a-46a9-4839-ae9d-b325b173e944

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_relIndex_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_finsum_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_lat_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_out_sub_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_volL_refine
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
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (hD : LocalDatum K R ψ) {ι : Type} [Fintype ι] {Λ Λ' : AddSubgroup K}
    (hΛ : IsLat Λ) (hΛ' : IsLat Λ') (hle : Λ' ≤ Λ) (f : (ι → K) → ℂ) (hf : BInv Λ f) :
    bx R Λ' ι f = bx R Λ ι f := by
  have hR := lat_R hD.isOpen hD.isCompact
  have hne : Λ'.relIndex Λ ≠ 0 := relIndex_ne_zero hΛ'.1 hΛ.2
  have : Finite (Λ ⧸ Λ'.addSubgroupOf Λ) := Nat.finite_of_card_ne_zero hne
  let e : (ι → K ⧸ Λ') ≃ (ι → K ⧸ Λ) × (ι → Λ ⧸ Λ'.addSubgroupOf Λ) :=
    (Equiv.piCongrRight fun _ => AddSubgroup.quotientEquivProdOfLE hle).trans
      (Equiv.arrowProdEquivProdArrow _ _ _)
  have key : ∑ᶠ y : ι → K ⧸ Λ', f (fun i => Quotient.out (y i)) =
      ((Λ'.relIndex Λ : ℂ)) ^ Fintype.card ι * ∑ᶠ y : ι → K ⧸ Λ, f (fun i => Quotient.out (y i)) := by
    have hc : (Nat.card (ι → Λ ⧸ Λ'.addSubgroupOf Λ) : ℂ) =
        ((Λ'.relIndex Λ : ℂ)) ^ Fintype.card ι := by
      rw [Nat.card_fun]
      simp [AddSubgroup.relIndex, AddSubgroup.index]
    rw [← hc, ← Formalism.FourierDecayAlt.P.A6x3.finsum_fst e (fun y : ι → K ⧸ Λ => f (fun i => Quotient.out (y i)))]
    refine finsum_congr fun y => ?_
    have := hf (fun i => Quotient.out (y i))
      (fun i => (Quotient.out (AddSubgroup.quotientEquivProdOfLE hle (y i)).1 : K) -
        (Quotient.out (y i) : K)) (fun i => Formalism.FourierDecayAlt.P.A6x3.out_sub_mem hle (y i))
    rw [← this]
    congr 1
    funext i
    simp [e]
  unfold bx
  rw [key, Formalism.FourierDecayAlt.P.A6x3.volL_refine hR (Formalism.FourierDecayAlt.P.A6x3.lat_iff.1 hΛ')
    (Formalism.FourierDecayAlt.P.A6x3.lat_iff.1 hΛ) hle]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
