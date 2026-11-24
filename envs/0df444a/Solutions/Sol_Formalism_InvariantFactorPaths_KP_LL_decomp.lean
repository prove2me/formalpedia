-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:48:24.140809+00:00
-- url     : https://prove2.me/submissions/59c8cf03-9ef1-4c77-8fae-afce53d77e98

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ScalSum
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_TieFPowMulFree
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_harmonicProjection_expand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ)
private lemma cast_choose_add_eq_factorial_div_of_charZero [CharZero k] (a b : ℕ) :
    (((a + b).choose b : ℕ) : k) = ((a + b).factorial : k) / ((a.factorial : k) * (b.factorial : k)) := by
  rw [eq_div_iff (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b)))]
  have h := Nat.add_choose_mul_factorial_mul_factorial a b
  rw [mul_assoc] at h
  exact_mod_cast h
private lemma factorial_choose_signed_sum_eq_zero [CharZero k] (N j : ℕ) (hj : 1 ≤ j) (hN : 2 * j + 1 ≤ N) :
    ∑ l ∈ range (j + 1), (-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((N - 2 * l - 1).choose (j - l) : k)) *
      ((l.factorial : k) ^ 2 * ((N - l).choose l : k))⁻¹ = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → k, ∀ l, c l = (-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 *
      ((N - 2 * l - 1).choose (j - l) : k)) * ((l.factorial : k) ^ 2 * ((N - l).choose l : k))⁻¹ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ → k, ∀ l, W l = if l ≤ j then c l * (((l : ℕ) : k) * ((N - l - j : ℕ) : k)) /
      ((j : k) * ((N - 2 * l : ℕ) : k)) else 0 := ⟨_, fun _ => rfl⟩
  have key : ∀ l ∈ range (j + 1), c l = W l - W (l + 1) := by
    intro l hl
    have hl' : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    rcases Nat.eq_or_lt_of_le hl' with hlj | hlj
    · have hne : (((l : ℕ) : k) * ((N - 2 * l : ℕ) : k)) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))
      rw [hW, hW, ← hlj, if_pos le_rfl, if_neg (by omega), sub_zero, show N - l - l = N - 2 * l by omega,
        mul_div_assoc, div_self hne, mul_one]
    · obtain ⟨u, hu⟩ : ∃ u, j = l + 1 + u := ⟨j - l - 1, by omega⟩
      obtain ⟨v, hv⟩ : ∃ v, N = 2 * j + 1 + v := ⟨N - 2 * j - 1, by omega⟩
      rw [hW, hW, if_pos hl', if_pos (by omega), hc, hc]
      rw [show N - l - j = u + 2 + v by omega, show N - 2 * l - 1 = u + 1 + v + (u + 1) by omega,
        show N - 2 * l = 2 * u + 3 + v by omega, show N - l = 2 * u + 3 + v + l by omega,
        show j - l = u + 1 by omega,
        show N - (l + 1) - j = u + 1 + v by omega, show N - 2 * (l + 1) - 1 = u + v + u by omega,
        show N - 2 * (l + 1) = 2 * u + 1 + v by omega, show N - (l + 1) = 2 * u + 1 + v + (l + 1) by omega,
        show j - (l + 1) = u by omega]
      rw [cast_choose_add_eq_factorial_div_of_charZero (u + 1 + v) (u + 1), cast_choose_add_eq_factorial_div_of_charZero (2 * u + 3 + v) l,
        cast_choose_add_eq_factorial_div_of_charZero (u + v) u, cast_choose_add_eq_factorial_div_of_charZero (2 * u + 1 + v) (l + 1), hu]
      have F1 : ((u + 1).factorial : k) = ((u + 1 : ℕ) : k) * (u.factorial : k) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have F2 : ((u + 1 + v).factorial : k) = ((u + 1 + v : ℕ) : k) * ((u + v).factorial : k) := by
        rw [show u + 1 + v = u + v + 1 by ring, Nat.factorial_succ]
        push_cast
        ring
      have F3 : ((u + 1 + v + (u + 1)).factorial : k) =
          ((u + v + u + 2 : ℕ) : k) * ((u + v + u + 1 : ℕ) : k) * ((u + v + u).factorial : k) := by
        rw [show u + 1 + v + (u + 1) = u + v + u + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        ring
      have F4 : ((2 * u + 3 + v + l).factorial : k) =
          ((2 * u + 3 + v + l : ℕ) : k) * ((2 * u + 1 + v + (l + 1)).factorial : k) := by
        rw [show 2 * u + 3 + v + l = 2 * u + 1 + v + (l + 1) + 1 by ring, Nat.factorial_succ]
        push_cast
        ring
      have F5 : ((2 * u + 3 + v).factorial : k) = ((u + v + u + 3 : ℕ) : k) * ((u + v + u + 2 : ℕ) : k) *
          ((u + v + u + 1 : ℕ) : k) * ((u + v + u).factorial : k) := by
        rw [show 2 * u + 3 + v = u + v + u + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
          Nat.factorial_succ]
        push_cast
        ring
      have F6 : ((l + 1).factorial : k) = ((l + 1 : ℕ) : k) * (l.factorial : k) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have F7 : ((2 * u + 1 + v).factorial : k) = ((u + v + u + 1 : ℕ) : k) * ((u + v + u).factorial : k) := by
        rw [show 2 * u + 1 + v = u + v + u + 1 by ring, Nat.factorial_succ]
        push_cast
        ring
      rw [F3, F4, F5, F7, F2, F1, F6]
      clear hW hc W c hl hl' hlj hu hv hj hN F1 F2 F3 F4 F5 F6 F7
      have nB1 : ((u.factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB1 : ((u.factorial : ℕ) : k) = B1 at nB1 ⊢
      have nB2 : (((u + v).factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB2 : (((u + v).factorial : ℕ) : k) = B2 at nB2 ⊢
      have nB3 : (((u + v + u).factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB3 : (((u + v + u).factorial : ℕ) : k) = B3 at nB3 ⊢
      have nB4 : ((l.factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB4 : ((l.factorial : ℕ) : k) = B4 at nB4 ⊢
      have nB5 : (((2 * u + 1 + v + (l + 1)).factorial : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      generalize hB5 : (((2 * u + 1 + v + (l + 1)).factorial : ℕ) : k) = B5 at nB5 ⊢
      have nL1 : ((u + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL1 : ((u + 1 : ℕ) : k) = L1 at nL1 ⊢
      have nL2 : ((u + 1 + v : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL2 : ((u + 1 + v : ℕ) : k) = L2 at nL2 ⊢
      have nL3 : ((u + v + u + 2 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL3 : ((u + v + u + 2 : ℕ) : k) = L3 at nL3 ⊢
      have nL4 : ((u + v + u + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL4 : ((u + v + u + 1 : ℕ) : k) = L4 at nL4 ⊢
      have nL5 : ((2 * u + 3 + v + l : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL5 : ((2 * u + 3 + v + l : ℕ) : k) = L5 at nL5 ⊢
      have nL6 : ((u + v + u + 3 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL6 : ((u + v + u + 3 : ℕ) : k) = L6 at nL6 ⊢
      have nL7 : ((l + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL7 : ((l + 1 : ℕ) : k) = L7 at nL7 ⊢
      have nL8 : ((l + 1 + u : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL8 : ((l + 1 + u : ℕ) : k) = L8 at nL8 ⊢
      have nL9 : ((2 * u + 3 + v : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL9 : ((2 * u + 3 + v : ℕ) : k) = liftZP_newton at nL9 ⊢
      have nL10 : ((2 * u + 1 + v : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      generalize hL10 : ((2 * u + 1 + v : ℕ) : k) = ParameterUpperBound at nL10 ⊢
      field_simp [nB1, nB2, nB3, nB4, nB5, nL1, nL2, nL3, nL4, nL5, nL6, nL7, nL8, nL9, nL10]
      subst hB1 hB2 hB3 hB4 hB5 hL1 hL2 hL3 hL4 hL5 hL6 hL7 hL8 hL9 hL10
      push_cast
      ring
  simp only [← hc]
  rw [Finset.sum_congr rfl key, Finset.sum_range_sub', hW, hW, if_pos (Nat.zero_le _), if_neg (by omega)]
  simp
end
end Formalism.InvariantFactorPaths.KP.LL
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ)
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution [CharZero k] (hr : 1 ≤ r) (hz : ∀ c, w c ≠ zv ∧ e c ≠ zv) (o n z : ℕ) (x : MvPolynomial σ k)
    (hv : ∀ m, min o n < m → (tieF w e ^ m) x = 0) :
    X zv ^ z * x = ∑ l ∈ range (min o n + 1), ehP w e zv sv ^ l *
      M.tieP w e zv sv (o - l) (n - l) z
        (((((l.factorial : k)) ^ 2 * ((o + n + r + z - l).choose l : k)))⁻¹ • (tieF w e ^ l) x) := by
  classical
  have hT : ∀ l m : ℕ, (tieF w e ^ m) ((tieF w e ^ l) x) = (tieF w e ^ (l + m)) x := by
    intro l m
    rw [add_comm, pow_add]
    rfl
  have hterm : ∀ l ∈ range (min o n + 1), ehP w e zv sv ^ l *
      M.tieP w e zv sv (o - l) (n - l) z
        (((((l.factorial : k)) ^ 2 * ((o + n + r + z - l).choose l : k)))⁻¹ • (tieF w e ^ l) x) =
      ∑ m ∈ range (min o n - l + 1), ((-1 : k) ^ m / (((m).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (m) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (l + m) * (X zv ^ z * (tieF w e ^ (l + m)) x)) := by
    intro l hl
    have hlL : l ≤ min o n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hsub : range (min o n - l + 1) ⊆ range (o - l + 1) := by
      intro m hm
      simp only [Finset.mem_range] at hm ⊢
      omega
    rw [harmonicProjection_expand w e zv sv hz, Finset.mul_sum, ← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [LinearMap.map_smul, hT]
      simp only [MvPolynomial.smul_eq_C_mul, map_mul]
      ring
    · intro m _ hm
      simp only [Finset.mem_range, not_lt] at hm
      have h0 : (tieF w e ^ (l + m)) x = 0 := hv (l + m) (by omega)
      simp [LinearMap.map_smul, hT, h0]
  have hre : ∀ l ∈ range (min o n + 1),
      ∑ m ∈ range (min o n - l + 1), ((-1 : k) ^ m / (((m).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (m) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (l + m) * (X zv ^ z * (tieF w e ^ (l + m)) x)) =
      ∑ j ∈ Ico l (min o n + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (j) * (X zv ^ z * (tieF w e ^ (j)) x)) := by
    intro l hl
    have hlL : l ≤ min o n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    rw [Finset.sum_Ico_eq_sum_range, show min o n + 1 - l = min o n - l + 1 by omega]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Nat.add_sub_cancel_left]
  have hcomm : ∑ l ∈ range (min o n + 1), ∑ j ∈ Ico l (min o n + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (j) * (X zv ^ z * (tieF w e ^ (j)) x)) =
      ∑ j ∈ range (min o n + 1), ∑ l ∈ range (j + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (j) * (X zv ^ z * (tieF w e ^ (j)) x)) :=
    Finset.sum_comm' (fun l j => by simp only [Finset.mem_range, Finset.mem_Ico]; omega)
  have hid : ∀ j ∈ range (min o n + 1),
      ∑ l ∈ range (j + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) • (ehP w e zv sv ^ (j) * (X zv ^ z * (tieF w e ^ (j)) x)) = if j = 0 then X zv ^ z * x else 0 := by
    intro j hj
    have hjL : j ≤ min o n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [← Finset.sum_smul]
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      simp
    · rw [if_neg (by omega)]
      have hc2 : ∑ l ∈ range (j + 1), ((-1 : k) ^ (j - l) / (((j - l).factorial : k) ^ 2 * ((o - l + (n - l) + r + z - 1).choose (j - l) : k)) *
          (((l).factorial : k) ^ 2 * ((o + n + r + z - l).choose l : k))⁻¹) = 0 := by
        refine Eq.trans ?_ (factorial_choose_signed_sum_eq_zero (o + n + r + z) j hpos (by omega))
        refine Finset.sum_congr rfl fun l hl => ?_
        have hlj : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
        rw [show o - l + (n - l) + r + z - 1 = o + n + r + z - 2 * l - 1 by omega]
      rw [hc2, zero_smul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_congr rfl hre, hcomm, Finset.sum_congr rfl hid]
  simp
end Formalism.InvariantFactorPaths.KP.LL
