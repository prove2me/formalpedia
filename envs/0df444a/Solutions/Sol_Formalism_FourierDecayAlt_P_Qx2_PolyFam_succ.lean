-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.PolyFam.succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:34:57.70652+00:00
-- url     : https://prove2.me/submissions/7a02336c-feb9-4a5b-bd6d-9fdeddd0d1de

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_smooth_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx2
namespace PolyFam
theorem _root_.solution {N : ℕ} {h : ℂ → Mx k r → E} (H : PolyFam k r i D N h) : PolyFam k r i D (N + 1) h := by
  obtain ⟨c, hc, he⟩ := H
  refine ⟨fun j x => if j < N then c j x else 0, fun j => ?_, fun Y x hx => ?_⟩
  · by_cases hj : j < N
    · simp only [if_pos hj]
      exact hc j
    · simp only [if_neg hj]
      exact smooth_zero
  · rw [he Y x hx, Finset.sum_range_succ]
    simp only [lt_self_iff_false, ↓reduceIte, smul_zero, add_zero]
    exact Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.mp hj)]
end PolyFam
end Formalism.FourierDecayAlt.P.Qx2
