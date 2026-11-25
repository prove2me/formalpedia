-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedLocSec.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:48:37.301057+00:00
-- url     : https://prove2.me/submissions/e1ad8b56-f289-41b0-b6fa-41da6f92ca01

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_symm
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm


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
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.NFRadRedLocSec
theorem _root_.solution {z v : Fin (2 * r + k + 1) → ℂ} {ζ : ℂ} {T T' : ℝ} (hT : T ≠ 0) (hz : herm (Hpk k r) z z = -(T : ℂ))
    (hvz : herm (Hpk k r) v z = ζ) (hvv : herm (Hpk k r) v v = -(T' : ℂ)) :
    herm (Hpk k r) (v + (ζ / (T : ℂ)) • z) (v + (ζ / (T : ℂ)) • z) = (((Complex.normSq ζ - T * T') / T : ℝ) : ℂ) ∧
      herm (Hpk k r) z (v + (ζ / (T : ℂ)) • z) = 0 := by
  have hzv : herm (Hpk k r) z v = star ζ := by
    rw [TwoByOneBlock.herm_symm (Hpk k r) (GBasic.Hpk_herm k r), hvz]
  have hT' : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hT
  have hsT : star (T : ℂ) = T := Complex.conj_ofReal T
  have hn : ((Complex.normSq ζ : ℝ) : ℂ) = ζ * star ζ := (Complex.mul_conj ζ).symm
  constructor
  · rw [TwoByOneBlock.herm_add_left, TwoByOneBlock.herm_add_right, TwoByOneBlock.herm_add_right, TwoByOneBlock.herm_smul_left,
      TwoByOneBlock.herm_smul_left, TwoByOneBlock.herm_smul_right, TwoByOneBlock.herm_smul_right, hz, hvz, hvv, hzv, star_div₀, hsT]
    push_cast
    rw [hn]
    field_simp
    ring
  · rw [TwoByOneBlock.herm_add_right, TwoByOneBlock.herm_smul_right, hz, hzv, star_div₀, hsT]
    field_simp
    ring
end Formalism.FourierDecayAlt.P.NFRadRedLocSec
