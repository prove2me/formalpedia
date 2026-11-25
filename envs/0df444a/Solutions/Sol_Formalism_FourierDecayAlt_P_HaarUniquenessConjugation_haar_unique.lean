-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.haar_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:16:38.548751+00:00
-- url     : https://prove2.me/submissions/fc2d0723-40aa-4678-9d55-f12bf2bf0305

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftErrorLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarUniquenessConjugation
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_lmul_phi
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_phi_closedEmbedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_phi_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_phi_range_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_phi_range
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_lmul_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
variable {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r}
namespace Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
theorem _root_.solution (hE : UJEmb) (hC : UHConj) (hP : IsUnit P.det) (hH : Pᴴ * Jm ε * P = Hpk k r)
    (ν : Measure (Mt k r)) (hν : IsHaarOn (GV k r) ν) : ∃ c : ℝ≥0, ν = c • (muG ε).map (phi ε P) := by
  have hm := phi_measurable (ε := ε) hE hP
  have hce := phi_closedEmbedding (ε := ε) hE hP
  have hme : MeasurableEmbedding (phi ε P) := hce.measurableEmbedding
  have hr := phi_range hE hC hP hH
  have hfin : IsFiniteMeasureOnCompacts (ν.comap (phi ε P)) := ⟨fun K hK => by
    rw [hme.comap_apply]
    exact hν.finite_compact _ (hK.image hce.continuous)⟩
  have hinv : (ν.comap (phi ε P)).IsMulLeftInvariant := ⟨fun u => by
    ext s hs
    rw [Measure.map_apply (measurable_const_mul u) hs, hme.comap_apply, hme.comap_apply]
    have hu : Matrix.of (phi ε P u) ∈ GV k r := (phi_range_iff hE hC hP hH _).1 ⟨u, rfl⟩
    have h1 := hν.left _ hu
    have hs' : MeasurableSet (phi ε P '' s) := hme.measurableSet_image.2 hs
    conv_rhs => rw [← h1, Measure.map_apply (lmul_cont _).measurable hs']
    congr 1
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨u * w, hw, (lmul_phi hP u w).symm⟩
    · rintro ⟨v, hv, hx⟩
      refine ⟨u⁻¹ * v, by simpa using hv, ?_⟩
      have h2 : lmulM (phi ε P u⁻¹) (lmulM (phi ε P u) x) = x := by
        have h3 : (Matrix.of (phi ε P u⁻¹) : Mat k r) * Matrix.of (phi ε P u) = 1 := by
          have := lmul_phi hP u⁻¹ u
          rw [inv_mul_cancel] at this
          refine Eq.trans this ?_
          show P⁻¹ * (1 : Mat k r) * P = 1
          rw [Matrix.mul_one, Matrix.nonsing_inv_mul P hP]
        show (Matrix.of (phi ε P u⁻¹) : Mat k r) * (Matrix.of (phi ε P u) * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
      rw [← lmul_phi hP, hx]; exact h2⟩
  refine ⟨Measure.haarScalarFactor (ν.comap (phi ε P)) (muG ε), ?_⟩
  have h1 := Measure.isMulLeftInvariant_eq_smul (ν.comap (phi ε P)) (muG ε)
  have h2 : (ν.comap (phi ε P)).map (phi ε P) = ν := by
    rw [hme.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]
    have := hν.conc
    rw [← hr] at this
    exact this
  rw [← Measure.map_smul, ← h1, h2]
end Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
