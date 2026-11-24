-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.rd_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:43:58.94473+00:00
-- url     : https://prove2.me/submissions/f2a61ca9-0deb-49f1-8947-355cd2885874

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_curve_lev
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_zero
import Theorems.Thm_Formalism_REAL_hasDerivAt_mul_exp_smul_zero


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
theorem _root_.solution (hD : IsOpen D) {f f₂ : Mx k r → E} (h : ∀ x ∈ Glev k r i ∩ D, f x = f₂ x) {g X : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) (hX : inLieLev k r i X) : RdV X f g = RdV X f₂ g := by
  have hγ := hasDerivAt_mul_exp_smul_zero g X
  have hγ0 := B5.curve_zero g X
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ D :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hD.mem_nhds hg.2)
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hmem] with t ht
  exact h _ ⟨curve_lev hg.1 hX t, ht⟩
end Formalism.FourierDecayAlt.P.Qx2
