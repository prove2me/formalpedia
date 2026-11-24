-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.DB.prodQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:27.751709+00:00
-- url     : https://prove2.me/submissions/e860f254-d9cb-4591-801d-9ecd6410ef90

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_mulQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
open Formalism.FourierDecayAlt.G Matrix Filter Topology
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
namespace DB
theorem _root_.solution {ι : Type*} [DecidableEq ι] {q : ℕ} {f : ι → E → ℂ} {u : E} {Q P : ℝ} (s : Finset ι)
    (h : ∀ i ∈ s, DB q (f i) u (Q ^ 1) P) (hP : 0 ≤ P) (h2 : (2 : ℝ) ^ q ≤ Q) :
    DB q (fun v => ∏ i ∈ s, f i v) u (Q ^ (2 * s.card)) P := by
  induction s using Finset.induction_on with
  | empty => simpa using DB.const q (1 : ℂ) u (S := 1) (by simp) hP
  | insert a s ha ih =>
    have h1 := (h a (Finset.mem_insert_self a s)).mulQ (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) hP h2
    have e : 1 + 2 * s.card + 1 = 2 * (insert a s).card := by
      rw [Finset.card_insert_of_notMem ha]; ring
    rw [e] at h1
    simpa [Finset.prod_insert ha] using h1
end DB
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
