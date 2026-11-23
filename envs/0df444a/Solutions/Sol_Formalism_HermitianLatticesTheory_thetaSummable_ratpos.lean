-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.thetaSummable_ratpos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:15.162433+00:00
-- url     : https://prove2.me/submissions/1cead6b2-d136-43e5-b831-2768cc30d7f0

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (G : Matrix ι ι ℚ)
    (hZ : ∀ c : ι → ℤ, c ≠ 0 → 0 < (fun i => (c i : ℚ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℚ))) :
    ∀ w : ι → ℚ, w ≠ 0 → 0 < w ⬝ᵥ (G *ᵥ w) := by
  intro w hw
  have hdpos' : 0 < ∏ i, (w i).den := Finset.prod_pos (fun i _ => (w i).den_pos)
  have hdpos : (0 : ℚ) < ((∏ i, (w i).den : ℕ) : ℚ) := by exact_mod_cast hdpos'
  have hint : ∀ i, ∃ z : ℤ, (z : ℚ) = ((∏ i, (w i).den : ℕ) : ℚ) * w i := by
    intro i
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun i => (w i).den) (Finset.mem_univ i)
    refine ⟨(w i).num * k, ?_⟩
    rw [hk]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  choose c hc using hint
  have hc0 : c ≠ 0 := by
    intro h0
    apply hw
    funext i
    have hci := hc i
    rw [h0, Pi.zero_apply, Int.cast_zero] at hci
    have := (mul_eq_zero.mp hci.symm).resolve_left hdpos.ne'
    simpa using this
  have hcw : (fun i => (c i : ℚ)) = ((∏ i, (w i).den : ℕ) : ℚ) • w := by
    funext i
    rw [hc i, Pi.smul_apply, smul_eq_mul]
  have hpos := hZ c hc0
  rw [hcw, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at hpos
  by_contra hneg
  push_neg at hneg
  nlinarith [mul_pos hdpos hdpos]
end Formalism.HermitianLatticesTheory
