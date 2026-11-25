-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.jf_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:30:49.971324+00:00
-- url     : https://prove2.me/submissions/99ce02c6-dd06-4948-816b-82307cdbce29

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalMeasurabilityWeakThreshold
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsiNormalization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnipotentEquivHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralIdentities
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralIdentities_psi_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralIdentities_xiTau_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_haarW
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_conjugation_invariance_every_setting
import Theorems.Thm_Formalism_FourierDecayAlt_P_unipotent_radical_closed
import Theorems.Thm_Formalism_FourierDecayAlt_P_weyl_subgroup_closed
import Theorems.Thm_Formalism_QuantumDeterminants_BesselUnitaryEquiv_rep_inv
import Theorems.Thm_Formalism_QuantumDeterminants_bessel_unipotent_equiv_holds
import Theorems.Thm_Formalism_QuantumDeterminants_bessel_unitary_equiv_holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable [FiniteDimensional ℂ Wp]
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) (hp : D.inSS p)
    (g : Mat k r) : rho D p (JF D F) g = (xiTau D (1, 1) p)⁻¹ • JF D F g := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have := FiniteDimensional.complete ℂ Wp
  have := FiniteDimensional.complete ℂ Wq
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have hN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have hW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r D.z
  have hW' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r D.z'
  have hU := Formalism.QuantumDeterminants.bessel_unitary_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F
    D.z_mem D.z'_mem D.haarN.conc D.haarW.conc D.haarW'.conc D.haarW.left D.haarW'.left
    (Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting k r Wp Wq D) D.π_rep D.π'_rep
  have hNe := Formalism.QuantumDeterminants.bessel_unipotent_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F
    D.z_mem D.z'_mem D.haarN.conc D.haarN.left
  have key : JF D F (sgs p g) =
      (psi k r D.z cStd (Matrix.of p.1.2)⁻¹ * psi k r D.z' cStd (Matrix.of p.2.2)) •
        (D.π (Matrix.of p.1.1)⁻¹).comp ((JF D F g).comp (D.π' (Matrix.of p.2.1))) := by
    unfold Formalism.FourierDecayAlt.B.JF Formalism.FourierDecayAlt.B.sgs
    rw [show (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 * Matrix.of p.2.1 =
        (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) * Matrix.of p.2.1 by
      simp only [Matrix.mul_assoc]]
    rw [hU _ _ (hW.inv_mem _ h1) _ h3, hNe _ _ (hN.inv_mem _ h2) _ h4,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  ext x
  simp only [rho, key, ContinuousLinearMap.comp_apply, _root_.smul_apply, map_smul]
  rw [Formalism.QuantumDeterminants.BesselUnitaryEquiv.rep_inv D.π'_rep h3 (hW'.inv_mem _ h3) (Matrix.mul_nonsing_inv _ (hW'.unit _ h3)) x,
    Formalism.QuantumDeterminants.BesselUnitaryEquiv.rep_inv D.π_rep h1 (hW.inv_mem _ h1) (Matrix.mul_nonsing_inv _ (hW.unit _ h1))]
  congr 1
  rw [xiTau_eq, psi_inv D.z_mem h2, mul_inv, inv_inv]
end Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities
