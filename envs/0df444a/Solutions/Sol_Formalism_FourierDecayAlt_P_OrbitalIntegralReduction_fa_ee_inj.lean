-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.fa_ee_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:53.643026+00:00
-- url     : https://prove2.me/submissions/c179e13c-6862-4045-9d58-e156131b557a

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
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
theorem _root_.solution {m : ℕ} : Function.Injective (ee : Fin m ⊕ Pr (m + 1) → Pr (m + 1) ⊕ Fin m) := by
  rintro (i | p) (j | q) h
  · simp only [ee, sd, Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq] at h
    rw [Fin.succ_inj.1 h.2]
  · exfalso
    simp only [ee] at h
    split_ifs at h with h0
    simp only [sd, Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq] at h
    have h1 := congrArg Fin.val h.1
    have h2 := congrArg Fin.val h.2
    have h3 := q.2
    rw [Fin.lt_def] at h3
    simp only [Fin.val_castSucc, Fin.val_pred, Fin.val_succ] at h1 h2
    have h4 : q.1.1.val ≠ 0 := fun h5 => h0 (Fin.ext h5)
    omega
  · exfalso
    simp only [ee] at h
    split_ifs at h with h0
    simp only [sd, Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq] at h
    have h1 := congrArg Fin.val h.1
    have h2 := congrArg Fin.val h.2
    have h3 := p.2
    rw [Fin.lt_def] at h3
    simp only [Fin.val_castSucc, Fin.val_pred, Fin.val_succ] at h1 h2
    have h4 : p.1.1.val ≠ 0 := fun h5 => h0 (Fin.ext h5)
    omega
  · simp only [ee] at h
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · split_ifs at h with h0 h1 h1
      · rw [h0, h1]
      · simp only [Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq] at h
        have := Fin.castSucc_inj.1 h.1
        exact Fin.pred_inj.1 this
    · split_ifs at h with h0 h1 h1
      · simp only [Sum.inr.injEq] at h
        exact Fin.pred_inj.1 h
      · simp only [Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq] at h
        exact h.2
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
