-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.tk_bx_eq_S
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:18.502892+00:00
-- url     : https://prove2.me/submissions/686a967c-04f4-41e7-bfb2-19d2c0c804db

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_reindex
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_mk_eqG
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_gi_pi
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
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution {ι : Type} [Fintype ι] (R : Subring K) (Λ : AddSubgroup K) (f : (ι → K) → ℂ)
    (hf : BInv Λ f) :
    bx R Λ ι f = tk_S (LL R ι) (AddSubgroup.pi Set.univ (fun _ : ι => Λ)) f := by
  unfold bx tk_S
  rw [tk_gi_pi]
  push_cast
  congr 1
  refine tk_reindex (X := ι → K) (fun x i => ((x i : K) : K ⧸ Λ))
    (fun x => (x : (ι → K) ⧸ AddSubgroup.pi Set.univ (fun _ : ι => Λ)))
    (fun q i => (Quotient.out (q i) : K)) (fun q => Quotient.out q)
    (fun q => funext fun i => QuotientAddGroup.out_eq' _) (fun q => QuotientAddGroup.out_eq' _)
    (fun x x' => ?_) f (fun x x' e => ?_)
  · rw [tk_mk_eqG]
    simp only [AddSubgroup.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro e i
      exact (tk_mk_eqG Λ _ _).1 (congrFun e i)
    · intro e
      funext i
      exact (tk_mk_eqG Λ _ _).2 (e i)
  · have := hf x' (x - x') (fun i => (tk_mk_eqG Λ _ _).1 (congrFun e i))
    simpa using this
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
