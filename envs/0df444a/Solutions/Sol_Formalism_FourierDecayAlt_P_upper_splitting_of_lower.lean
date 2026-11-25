-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.upper_splitting_of_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:02:26.659003+00:00
-- url     : https://prove2.me/submissions/68646c20-9545-4a6b-9b09-775fe34705bd

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_conjT
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_lt_conjT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.UpSplitOfLowSplit := by
  intro hLow m P hP u hu
  obtain ⟨p, ⟨hp1, hp2, hpe⟩, huniq⟩ := hLow m P hP uᴴ (ut_conjT hu)
  refine ⟨(p.2ᴴ, p.1ᴴ), ⟨lt_conjT hp2.1, lt_conjT hp1.1, ?_, ?_, ?_⟩, ?_⟩
  · simpa using hp2
  · simpa using hp1
  · simp only
    rw [← Matrix.conjTranspose_mul, ← hpe, Matrix.conjTranspose_conjTranspose]
  · rintro q ⟨_, _, hq1, hq2, hqe⟩
    have := huniq (q.2ᴴ, q.1ᴴ) ⟨hq2, hq1, by
      simp only
      rw [← Matrix.conjTranspose_mul, ← hqe]⟩
    rw [Prod.ext_iff] at this
    simp only at this
    obtain ⟨e1, e2⟩ := this
    apply Prod.ext
    · simp only; rw [← e2, Matrix.conjTranspose_conjTranspose]
    · simp only; rw [← e1, Matrix.conjTranspose_conjTranspose]
end Formalism.FourierDecayAlt.P
