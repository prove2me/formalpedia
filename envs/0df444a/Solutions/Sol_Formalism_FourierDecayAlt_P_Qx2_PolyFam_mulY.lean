-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.PolyFam.mulY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:22:48.597862+00:00
-- url     : https://prove2.me/submissions/13963f48-567f-442e-8573-433c2efc6373

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
theorem _root_.solution {N : ℕ} {h : ℂ → Mx k r → E} (H : PolyFam k r i D N h) :
    PolyFam k r i D (N + 1) (fun Y x => Y • h Y x) := by
  obtain ⟨c, hc, he⟩ := H
  refine ⟨fun j x => if j = 0 then 0 else c (j - 1) x, fun j => ?_, fun Y x hx => ?_⟩
  · by_cases hj : j = 0
    · simp only [if_pos hj]
      exact smooth_zero
    · simp only [if_neg hj]
      exact hc (j - 1)
  · try dsimp only
    rw [he Y x hx, Finset.sum_range_succ', Finset.smul_sum]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, eq_self_iff_true, if_true, smul_zero, add_zero, pow_succ',
      mul_smul]
end PolyFam
end Formalism.FourierDecayAlt.P.Qx2
