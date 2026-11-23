-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.admitted.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:25.715179+00:00
-- url     : https://prove2.me/submissions/187a9af4-bab7-407e-9280-5ceb28899ab3

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_psi_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_tube
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_perp_bdd
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Osc_compact_box
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_admitted_hess_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_admitted_quad
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_admitted_roots_bdd
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.admitted
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x7.admitted
theorem _root_.solution : GaussAdmSmall := by
  intro K _ _ _ R ψ hD h0 m L Q hL hQ _
  obtain ⟨C₁, hC₁, hperp⟩ := perp_bdd hD h0 L hL
  obtain ⟨C₂, hC₂, hroot⟩ := roots_bdd hD h0 (m + 1) (by omega) Q hQ
  obtain ⟨u, hu⟩ := h0 (m + 1) (by omega)
  have hc : ((m + 1 : ℕ) : K) * ((u⁻¹ : Kˣ) : K) = 1 := by rw [← hu]; simp
  let F : K × (K × (Fin m → K)) → K := fun p =>
    Ring.inverse 2 * (p.2.1 * p.1 * (∑ k, p.2.2 k * p.2.2 k -
      ((u⁻¹ : Kˣ) : K) * ((∑ k, p.2.2 k) * ∑ k, p.2.2 k)))
  have hF : Continuous F := by
    dsimp only [F]; fun_prop
  obtain ⟨V, hV, hVF⟩ := tube F hF 0 (C₂ ×ˢ {y : Fin m → K | ∀ k, y k ∈ C₁})
    (hC₂.prod (Osc.compact_box _ hC₁)) (R : Set K) hD.isOpen (by
      intro y _
      have : F (0, y) = 0 := by simp [F]
      rw [this]; exact R.zero_mem)
  refine ⟨V, hV, fun t z ht hz y hy => ?_⟩
  rw [Matrix.inv_eq_right_inv (hess_inv m (z * t) _ hc), quad, Units.val_mul]
  exact psi_R hD (hVF _ ht (_, y) ⟨hroot _ hz, fun k => hperp _ (hy k)⟩)
end Formalism.FourierDecayAlt.P.A6x7.admitted
