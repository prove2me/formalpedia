-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.DB.bilin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:08.148478+00:00
-- url     : https://prove2.me/submissions/6571a4a8-e918-49b4-8111-fdf330924984

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_bilin_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
open Filter Topology
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
namespace DB
theorem _root_.solution (B : F →L[ℝ] G →L[ℝ] H) (hB : ‖B‖ ≤ 1) {q : ℕ} {f : E → F} {g : E → G} {u : E} {S₁ S₂ P : ℝ}
    (hf : DB q f u S₁ P) (hg : DB q g u S₂ P) (hP : 0 ≤ P) :
    DB q (fun v => B (f v) (g v)) u (2 ^ q * S₁ * S₂) P := by
  refine ⟨(B.contDiff.contDiffAt.comp u hf.1).clm_apply hg.1, fun n hn => ?_⟩
  have hS₁ := hf.nonneg
  have hS₂ := hg.nonneg
  refine (bilin_le B hB hf.1 hg.1 hn).trans ?_
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f u‖ * ‖iteratedFDeriv ℝ (n - i) g u‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (S₁ * P ^ i) * (S₂ * P ^ (n - i)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := Finset.mem_range_succ_iff.mp hi
        have h1 := hf.2 i (hi'.trans hn)
        have h2 := hg.2 (n - i) ((Nat.sub_le _ _).trans hn)
        gcongr
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (S₁ * S₂ * P ^ n) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : i ≤ n := Finset.mem_range_succ_iff.mp hi
        rw [show P ^ n = P ^ i * P ^ (n - i) by rw [← pow_add, Nat.add_sub_cancel' hi']]
        ring
    _ = 2 ^ n * (S₁ * S₂ * P ^ n) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n
    _ ≤ 2 ^ q * (S₁ * S₂ * P ^ n) := by
        have : (2 : ℝ) ^ n ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hn
        gcongr
    _ = 2 ^ q * S₁ * S₂ * P ^ n := by ring
end DB
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
