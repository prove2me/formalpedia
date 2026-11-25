-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HeisenbergLevelMinors.nnMinor_of_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:54:34.43017+00:00
-- url     : https://prove2.me/submissions/b9f1f3f7-2e68-44b3-9532-d3b5a9daff44

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JDomBoundOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastLevelSliceOfScalar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormBallVolumes
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLevelMinors
import Theorems.Thm_Formalism_FourierDecayAlt_P_HeisenbergLevelMinors_gN_inv_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_HeisenbergLevelMinors_dmin_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_inv_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mono
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
theorem _root_.solution : NNMinorL → NNMinor := by
  intro hL k r z z' K hK hKD
  obtain ⟨C1, h1⟩ := hL k r z z' K hK hKD
  have hKG : K ⊆ GV k r := fun g hg => (hKD g hg).1
  have hK' : IsCompact ((fun g : Mat k r => g⁻¹) '' K) :=
    hK.image_of_continuousOn ((B6.inv_continuousOn k r).mono hKG)
  obtain ⟨C2, h2⟩ := hL k r z' z _ hK' (by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨WeylGroupFacts.uh_inv (hKG hg), fun l hl => ?_⟩
    rw [dmin_inv (hKG hg)]; exact star_ne_zero.2 ((hKD g hg).2 l hl))
  refine ⟨max C1 (max C2 0 * gN (Hpk k r) ^ (2 * (3 * r))), fun g hg n hn n' hn' => ⟨?_, ?_⟩⟩
  · exact le_trans (h1 g hg n hn n' hn')
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (B6.gN_nonneg _) _))
  · have hgG := hKG hg
    have hx := WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hn.1) hgG) hn'.1
    have hinv : (n⁻¹ * g * n')⁻¹ = n'⁻¹ * g⁻¹ * n := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hn.1),
        Matrix.mul_assoc]
    have e2 := h2 g⁻¹ ⟨g, hg, rfl⟩ n' hn' n hn
    rw [← hinv] at e2
    have hb : gN (n⁻¹ * g * n')⁻¹ ≤ gN (Hpk k r) ^ 2 * gN (n⁻¹ * g * n') := gN_inv_le hx
    calc gN n' ≤ C2 * gN (n⁻¹ * g * n')⁻¹ ^ (3 * r) := e2
      _ ≤ max C2 0 * gN (n⁻¹ * g * n')⁻¹ ^ (3 * r) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (B6.gN_nonneg _) _)
      _ ≤ max C2 0 * (gN (Hpk k r) ^ 2 * gN (n⁻¹ * g * n')) ^ (3 * r) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (B6.gN_nonneg _) hb _) (le_max_right _ _)
      _ = (max C2 0 * gN (Hpk k r) ^ (2 * (3 * r))) * gN (n⁻¹ * g * n') ^ (3 * r) := by
          rw [mul_pow, ← pow_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (B6.gN_nonneg _) _)
end Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
