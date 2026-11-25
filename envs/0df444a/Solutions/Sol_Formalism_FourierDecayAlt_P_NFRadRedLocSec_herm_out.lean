-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedLocSec.herm_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:32.191866+00:00
-- url     : https://prove2.me/submissions/de7e4a82-d8e4-47b4-af90-79d9adf510eb

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_symm
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm
import Theorems.Thm_Formalism_QuantumDeterminants_gn_herm_bvec_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.NFRadRedLocSec
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section Trans
variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)
variable {H}
end Trans
section Smooth
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X} {m : ℕ}
end Smooth
section Main
variable {k r : ℕ}
private lemma hpk_apply_of_outer_index (i j : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    Hpk k r i j = if i.val + j.val = 2 * r + k then 1 else 0 := by
  simp only [Hpk]
  split_ifs <;> first | rfl | (exfalso; omega)
private lemma hpk_mulVec_apply_of_outer_index (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (hi : i.val < r ∨ r + k < i.val) : (Hpk k r *ᵥ v) i = v ⟨2 * r + k - i.val, by omega⟩ := by
  simp only [Matrix.mulVec, dotProduct, fun j => hpk_apply_of_outer_index (k := k) (r := r) i j hi]
  rw [Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]
  · rw [if_pos (Nat.add_sub_cancel' (by omega)), one_mul]
  · intro l _ hl
    rw [if_neg, zero_mul]
    intro h
    exact hl (Fin.ext (by show l.val = 2 * r + k - i.val; omega))
  · intro h
    exact absurd (Finset.mem_univ _) h
variable {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
end Main
end Formalism.FourierDecayAlt.P.NFRadRedLocSec
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFRadRedLocSec
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.NFRadRedLocSec
theorem _root_.solution {d : Fin (2 * r + k + 1) → ℂ} (hd : inWb k r d) {i : Fin (2 * r + k + 1)}
    (hi : ¬ TwoByOneBlock.mid k r i) : herm (Hpk k r) (bvec i) d = 0 := by
  have hi0 : ¬(r ≤ i.val ∧ i.val ≤ r + k) := hi
  have hi' : i.val < r ∨ r + k < i.val := by omega
  rw [TwoByOneBlock.herm_symm (Hpk k r) (GBasic.Hpk_herm k r), gn_herm_bvec_right, hpk_mulVec_apply_of_outer_index d i hi',
    hd _ (by show 2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val; omega), star_zero]
end Formalism.FourierDecayAlt.P.NFRadRedLocSec
