-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.DB.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:36.190793+00:00
-- url     : https://prove2.me/submissions/1a9da8fb-4f81-48d8-afd9-ba83010d0143

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_comp_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_nonneg

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
theorem _root_.solution {q : ℕ} {g : F → G} {f : E → F} {u : E} {So Po S P : ℝ} (hg : DB q g (f u) So Po)
    (hf : DB q f u S P) (hS : 1 ≤ S) (hPo : 1 ≤ Po) (hP : 0 ≤ P) :
    DB q (fun v => g (f v)) u (q.factorial * So) (Po * S * P) := by
  refine ⟨hg.1.comp u hf.1, fun n hn => ?_⟩
  have hSo := hg.nonneg
  have h := comp_le (n := n) (C := So * Po ^ n) (D := S * P) hg.1 hf.1 hn
    (fun i hi => (hg.2 i (hi.trans hn)).trans (by
      have : Po ^ i ≤ Po ^ n := pow_le_pow_right₀ hPo hi
      gcongr))
    (fun i h1 hi => (hf.2 i (hi.trans hn)).trans (by
      rw [mul_pow]
      have : S ≤ S ^ i := le_self_pow₀ hS (by omega)
      gcongr))
  refine h.trans ?_
  have hfac : (n.factorial : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_le hn
  calc (n.factorial : ℝ) * (So * Po ^ n) * (S * P) ^ n ≤ (q.factorial : ℝ) * (So * Po ^ n) * (S * P) ^ n := by
        gcongr
    _ = q.factorial * So * (Po * S * P) ^ n := by
        rw [mul_assoc Po S P, mul_pow Po (S * P) n]
        ring
end DB
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
