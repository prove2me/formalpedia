-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far.exists_derivBound_nonstationaryCutoff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:09.092065+00:00
-- url     : https://prove2.me/submissions/8050240d-1bcc-42ea-93f0-73795e11af0b

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_clm_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_critical_cutoff_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far
theorem _root_.solution (m q : ℕ) (δ : ℝ) (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : ℂ) (x : Fin (m + 1) → ℂ),
    DB q (fun x : Fin (m + 1) → ℂ => ((farCut m δ D x : ℝ) : ℂ)) x C 1 := by
  obtain ⟨C, hC⟩ := (critical_cutoff_spec m δ hδ).2.1 q
  have hDB : ∀ (z : ℂ) (x : Fin (m + 1) → ℂ), DB q (critCut (n := m + 1) δ z) x C 1 := by
    intro z x
    refine ⟨(hC z).1.contDiffAt, fun j hj => ?_⟩
    simpa using (hC z).2 j hj x
  have hC0 : 0 ≤ C := (hDB 0 0).nonneg
  refine ⟨1 + ((m : ℝ) + 2) * C, by positivity, fun D x => ?_⟩
  have hsum := DB.sum (q := q) (u := x) (f := fun z => critCut (n := m + 1) δ z) (S := fun _ => C) (P := 1)
    (rootSet (m + 2) ((-1) ^ (m + 3) * D)) zero_le_one (fun z _ => hDB z x)
  have hcard : ((rootSet (m + 2) ((-1) ^ (m + 3) * D)).card : ℝ) ≤ (m : ℝ) + 2 := by
    have h1 : (rootSet (m + 2) ((-1) ^ (m + 3) * D)).card ≤ m + 2 :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
    exact_mod_cast h1
  have hone : DB q (fun _ : Fin (m + 1) → ℂ => (1 : ℝ)) x 1 1 := DB.const q 1 x (by simp) zero_le_one
  have hsub := (hone.sub hsum).mono (S' := 1 + ((m : ℝ) + 2) * C) (P' := 1) (by
    simp only [Finset.sum_const, nsmul_eq_mul]
    have := mul_le_mul_of_nonneg_right hcard hC0
    linarith) zero_le_one le_rfl
  have := DB.clm_one Complex.ofRealCLM (by simp) hsub
  exact this
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far
