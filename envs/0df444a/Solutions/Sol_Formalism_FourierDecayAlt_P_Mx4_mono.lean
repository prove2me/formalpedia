-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:48.109864+00:00
-- url     : https://prove2.me/submissions/51da964d-c4f1-4fa0-a1c3-a1edd6bd6fae

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution (k : ℕ) (u u' ρ : ℕ → ℝ) (h : I.Interlaces k u u' ρ) :
    ∀ d i, 1 ≤ i → i + d ≤ k → u (i + d) ≤ u i ∧ u' (i + d) ≤ u' i := by
  intro d
  induction d with
  | zero => intro i _ _; simp
  | succ d ih =>
    intro i h1 h2
    have a := ih i h1 (by omega)
    have b := h (i + d) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    have e : i + (d + 1) = i + d + 1 := by ring
    rw [e]
    constructor <;> linarith [b.1, b.2.1, b.2.2.1, b.2.2.2]
end Formalism.FourierDecayAlt.P.Mx4
