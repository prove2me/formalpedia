-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.tk_fin_box
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:01.168358+00:00
-- url     : https://prove2.me/submissions/696e579e-dc9d-41b2-a77b-c64fb8699315

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_out_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_mk_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_fin_cpt
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution {ι : Type} [Finite ι] (Λ : AddSubgroup K) (hΛ : IsOpen (Λ : Set K))
    (C : ι → Set K) (hC : ∀ i, IsCompact (C i)) :
    {y : ι → K ⧸ Λ | ∀ i, (Quotient.out (y i) : K) ∈ C i}.Finite := by
  have h1 : ∀ i, {z : K ⧸ Λ | (Quotient.out z : K) ∈ C i}.Finite := fun i =>
    tk_fin_cpt Λ hΛ (fun z : K ⧸ Λ => (Quotient.out z : K))
      (fun q q' h => by
        have := (tk_mk_eq Λ _ _).2 h
        rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at this)
      (fun y => ⟨(y : K ⧸ Λ), by
        have := Λ.neg_mem (tk_out_sub Λ y)
        simpa using this⟩) (hC i)
  refine (Set.Finite.pi' h1).subset ?_
  intro y hy i
  exact hy i
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
