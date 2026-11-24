-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.pow_DB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:08.971579+00:00
-- url     : https://prove2.me/submissions/bf0afc9c-4d29-4c6a-95f7-0019b718d737

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_mulQ
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_sumQ
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Xm_DB
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Bm_DB

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
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {m q : ℕ} {tt : E → ℂ}
  {xx : E → Fin (m + 1) → ℂ} {yy : E → UT (m + 2) → ℂ} {u : E} {Q : ℝ}
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
theorem _root_.solution (h2 : (2 : ℝ) ^ q ≤ Q) (hm : ((m : ℝ) + 1) ≤ Q) (hx : ∀ k, DB q (fun v => xx v k) u Q 1)
    (hy : ∀ e, DB q (fun v => yy v e) u Q 1) (j : ℕ) :
    ∀ i, DB q (fun v => ((-Xm m (xx v, yy v)) ^ j *ᵥ Bm m (xx v, yy v)) i) u (Q ^ (3 * j + 1)) 1 := by
  have hQ0 : 0 ≤ Q := le_trans (by positivity) h2
  induction j with
  | zero => intro i; simpa using Bm_DB hQ0 hx hy i
  | succ j ih =>
    intro i
    have e : (fun v => ((-Xm m (xx v, yy v)) ^ (j + 1) *ᵥ Bm m (xx v, yy v)) i) = fun v =>
        ∑ l ∈ (Finset.univ : Finset (Fin (m + 1))),
          (-Xm m (xx v, yy v) i l) * ((-Xm m (xx v, yy v)) ^ j *ᵥ Bm m (xx v, yy v)) l := by
      funext v
      rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct]
      rfl
    rw [e]
    have h1 := DB.sumQ (Finset.univ : Finset (Fin (m + 1)))
      (fun l _ => ((Xm_DB hQ0 hx hy i l).neg).mulQ (ih l) zero_le_one h2) zero_le_one hQ0
      (by simpa using hm)
    have e2 : 1 + (3 * j + 1) + 1 + 1 = 3 * (j + 1) + 1 := by ring
    rwa [e2] at h1
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
