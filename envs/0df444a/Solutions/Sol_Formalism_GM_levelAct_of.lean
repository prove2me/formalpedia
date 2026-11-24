-- Prove2me | solution 1 for Formalism.GM.levelAct_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:41.519453+00:00
-- url     : https://prove2.me/submissions/50b01a1e-f4e8-442d-8b8d-0843585c06c5

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Theorems.Thm_Formalism_GM_euler_w_of_biHom
import Theorems.Thm_Formalism_GM_euler_e_of_biHom
import Theorems.Thm_Formalism_GM_F_pow_E_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.GM
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ)
variable {w e}
private theorem linearMap_pow_apply_pow_apply (f : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (m n : ℕ)
    (x : MvPolynomial σ k) : (f ^ m) ((f ^ n) x) = (f ^ (m + n)) x := by
  rw [pow_add]; first | done | rfl
end
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM
open MvPolynomial Finset
namespace Formalism.GM
theorem _root_.solution (hS : LevelSum) : LevelAct := by
  intro k σ _ _ r w e hw he hwe hr o n z l u hlo hln hF hB
  have hW := euler_w_of_biHom w e hB
  have hE := euler_e_of_biHom w e hB
  obtain ⟨N0, hN⟩ : ∃ N0, o - l + (n - l) + r = N0 + 1 := ⟨o - l + (n - l) + r - 1, by omega⟩
  have key : ∀ j, ((tieE w e ^ j).comp (tieF w e ^ j)) ((tieE w e ^ l) u) =
      ((l.descFactorial j * (N0 + l).descFactorial j : ℕ) : k) • (tieE w e ^ l) u := by
    intro j
    rw [LinearMap.comp_apply, F_pow_E_pow hw he hwe u (o - l) (n - l) N0 hW hE hF hN j l, map_smul]
    by_cases hjl : j ≤ l
    · congr 1
      rw [linearMap_pow_apply_pow_apply, show j + (l - j) = l by omega]
    · simp [Nat.descFactorial_eq_zero_iff_lt.mpr (show l < j by omega)]
  have hA : z + l ≤ o + n + r + z - 1 := by omega
  have hS' := hS (o + n + r + z - 1) z l hA
  rw [show o + n + r + z - 1 - z - l = N0 + l by omega] at hS'
  have hcast := congrArg (Rat.cast : ℚ → k) hS'
  simp only [qch, Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_one,
    Rat.cast_natCast] at hcast
  simp only [tiePhi, LinearMap.sum_apply, LinearMap.smul_apply, key, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  rw [← Finset.sum_subset (Finset.range_mono (show l + 1 ≤ o + 1 by omega)) ?_]
  · refine Eq.trans ?_ hcast
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjl : j ≤ l := by
      rw [Finset.mem_range] at hj
      omega
    have hf : ((j.factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have hc : (((o + n + r + z - 1).choose j : ℕ) : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    field_simp
  · intro j _ hj
    rw [Finset.mem_range, not_lt] at hj
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr (show l < j by omega)]
end Formalism.GM
