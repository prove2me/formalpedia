-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedLocSec.tmat_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:51:14.373006+00:00
-- url     : https://prove2.me/submissions/53145f83-385c-4299-a977-9114f650a3b3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_trans_expl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFRadRedLocSec
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)
variable {H}
namespace Formalism.FourierDecayAlt.P.NFRadRedLocSec
theorem _root_.solution (hH : Hᴴ = H) (a b : Fin m → ℂ) (q : ℝ) (hq : 0 < q)
    (ha : herm H a a = q) (hb : herm H b b = q) (hs : herm H a b ≠ 0) :
    tmat H a b q ∈ UH H ∧ tmat H a b q *ᵥ a = b ∧
    ∀ x, herm H x a = 0 → herm H x b = 0 → tmat H a b q *ᵥ x = x := by
  have hs' : ‖herm H a b‖ ≠ 0 := norm_ne_zero_iff.2 hs
  have hsc : ((‖herm H a b‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs'
  have hsn : star ((‖herm H a b‖ : ℝ) : ℂ) = ‖herm H a b‖ := Complex.conj_ofReal _
  have hm : herm H a b * star (herm H a b) = ((‖herm H a b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.sq_norm]; exact Complex.mul_conj _
  have hθ : tth H a b * star (tth H a b) = 1 := by
    unfold tth
    rw [star_neg, star_div₀, hsn, neg_mul_neg, div_mul_div_comm, hm, div_eq_one_iff_eq (mul_ne_zero hsc hsc)]
    push_cast
    ring
  have ht : star (tth H a b) * herm H a b = ((-‖herm H a b‖ : ℝ) : ℂ) := by
    unfold tth
    rw [star_neg, star_div₀, hsn, neg_mul, div_mul_eq_mul_div, mul_comm (star (herm H a b)), hm]
    push_cast
    field_simp
  have hqt : q * (-‖herm H a b‖) ≤ 0 := by nlinarith [norm_nonneg (herm H a b)]
  unfold tmat
  exact trans_expl hH a b q hq.ne' ha hb _ _ hθ ht hqt
end Formalism.FourierDecayAlt.P.NFRadRedLocSec
