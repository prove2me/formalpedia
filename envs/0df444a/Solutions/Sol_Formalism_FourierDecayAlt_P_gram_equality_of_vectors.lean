-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gram_equality_of_vectors
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:27.79723+00:00
-- url     : https://prove2.me/submissions/ea6b8059-96a3-4efd-934e-89077280f59b

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_nat_tri
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
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open A6x9
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.UGramEq := by
  intro hP hC hM K _ _ _ R ψ hD m h h' t t' cr hs hcr
  have hsz : (addBlock h m t).1.sum = (addBlock h' m t').1.sum := by
    simp [addBlock, hs]
  obtain ⟨_, h2⟩ := hP K R ψ hD (addBlock h m t) (addBlock h' m t') hsz cr hcr
  have e1 : ∀ x, Ns R ψ 1 (addBlock h m t) (addBlock h' m t') (cr x) (cr x) =
      Kp R ψ (pt2 h m t (cr x)) (pt2 h' m t' (cr x)) := by
    intro x; simp [Ns, pt2]
  simp only [e1] at h2
  unfold uGram
  simp only [Set.mem_univ, if_true]
  rw [h2, hC K R ψ hD h m t, hC K R ψ hD h' m t']
  unfold Ns N0
  obtain ⟨ha, hab⟩ := hM K R ψ hD t t'
  obtain ⟨hb, _⟩ := hM K R ψ hD t' t
  rw [nat_tri m, hab]
  have ha' : (modK R (t : K)) ≠ 0 := ne_of_gt ha
  have hb' : (modK R (t' : K)) ≠ 0 := ne_of_gt hb
  push_cast
  have ha'' : ((modK R (t : K) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha'
  have hb'' : ((modK R (t' : K) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb'
  field_simp
  ring
end Formalism.FourierDecayAlt.P
