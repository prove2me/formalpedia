-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftDerivativeCurves.ld_hasDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:00:42.287037+00:00
-- url     : https://prove2.me/submissions/ee890ac9-5f16-402f-845d-9ee6e7355fbf

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_l_hasDeriv_ext

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
open Formalism.FourierDecayAlt.P.LeftDerivativeCurves
open Qx2 (Good)
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.LeftDerivativeCurves
theorem _root_.solution {f : Mx k r → E} (hf : SmoothLev k r i D f) {g X : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (hX : inLieLev k r i X) :
    HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) (LdV X f g) 0 := by
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g hg
  have hFd : DifferentiableAt ℝ F g := (hF.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)
  have h := l_hasDeriv_ext hU hgU hg.1 hX hFd he
  unfold LdV
  rw [h.deriv]
  exact h
end Formalism.FourierDecayAlt.P.LeftDerivativeCurves
