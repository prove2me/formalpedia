-- Prove2me | solution 1 for Formalism.HermitianLattices.ExplicitEstimates.column_parametrization_off_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:04:23.435003+00:00
-- url     : https://prove2.me/submissions/c5219046-6578-4864-b2f6-1ce3d6438c8f

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_IntegralMultipleNormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ColumnParametrizationOffDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.ExplicitEstimates
open Finset
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (hookF)
private theorem g4w9_dec (K m s : ℕ) (U v b e : ℕ → ℤ) (S eta : ℤ) (L : Layout K m s U v b e S eta) :
    ∀ d i, i + d < 2 * K → U (i + d) + (d : ℤ) ≤ U i := by
  intro d
  induction d with
  | zero => intro i _; simp
  | succ d ih =>
    intro i hi
    have h1 := ih i (by omega)
    have h2 := L.chain (i + d) (by omega)
    have e : i + (d + 1) = i + d + 1 := by omega
    rw [e]
    push_cast
    linarith [h2.1, h2.2]
private theorem g4w9_dec' (K m s : ℕ) (U v b e : ℕ → ℤ) (S eta : ℤ) (L : Layout K m s U v b e S eta)
    (i j : ℕ) (hij : i ≤ j) (hj : j < 2 * K) : U j + (j : ℤ) ≤ U i + (i : ℤ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  have h := g4w9_dec K m s U v b e S eta L d i (by omega)
  push_cast
  linarith
private theorem g4w9_anti (K m s κ : ℕ) (U v b e : ℕ → ℤ) (S eta : ℤ) (L : Layout K m s U v b e S eta)
    (hκ : κ + 1 = 2 * K) : Antitone (colW K U (k := κ + 1)) := by
  intro i j hij
  have hj : (j : ℕ) < 2 * K := by have := j.isLt; omega
  have h := g4w9_dec' K m s U v b e S eta L i j (Fin.le_iff_val_le_val.mp hij) hj
  simp only [colW]
  linarith
end Formalism.HermitianLattices.ExplicitEstimates
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ExplicitEstimates
open Finset
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (hookF)
namespace Formalism.HermitianLattices.ExplicitEstimates
theorem _root_.solution : Col_param_off := by
  intro K m s κ U v b e S eta L hO hκ
  obtain ⟨hO1, hO2, hO3, hO4⟩ := hO
  have hK := L.one_le_K
  have hKz : (1:ℤ) ≤ K := by exact_mod_cast hK
  have hκz : (κ:ℤ) + 1 = 2 * K := by exact_mod_cast hκ
  have hκ1 : 1 ≤ κ := by omega
  have hanti := g4w9_anti K m s κ U v b e S eta L hκ
  have hv0 := L.cloud_v 0 (by omega)
  have hvl := L.cloud_v (2 * K - 2) (by omega)
  have eK : 2 * K - 1 = κ := by omega
  rw [eK] at hO3
  have hU : ∀ j : ℕ, 1 ≤ j → j ≤ κ → U j + 1 ≤ S := by
    intro j hj1 hjk
    rcases Nat.lt_or_ge j κ with h | h
    · exact (L.cloud_u j hj1 (by omega)).2
    · have hjκ : j = κ := by omega
      rw [hjκ]
      linarith [hvl.2]
  have hU0 : U 0 + 1 ≤ 3 * S := by linarith [hv0.2]
  have hcw : ∀ i : Fin (κ + 1), colW K U i = U i - K + ((i : ℕ) : ℤ) + 1 := fun i => rfl
  have hlast : colW K U (Fin.last κ) = v (2 * K - 2) + K - 1 := by
    rw [hcw, Fin.val_last, hO3]
    linarith
  have hzero : colW K U (0 : Fin (κ + 1)) = U 0 - K + 1 := by
    rw [hcw]
    simp
  have hlo : ∀ i : Fin (κ + 1), colW K U (Fin.last κ) ≤ colW K U i :=
    fun i => hanti (Fin.le_last i)
  have hhi : ∀ i : Fin (κ + 1), colW K U i ≤ colW K U 0 :=
    fun i => hanti (by simp [Fin.le_iff_val_le_val])
  have hb : ∀ i : Fin (κ + 1), 0 ≤ colW K U i ∧ colW K U i ≤ 3 * S := by
    intro i
    have h1 := hlo i
    have h2 := hhi i
    rw [hlast] at h1
    rw [hzero] at h2
    constructor <;> linarith [hvl.1]
  have hc : ∀ i : Fin (κ + 1), i ≠ 0 → colW K U i - colW K U (Fin.last κ) ≤ S := by
    intro i hi
    have h0 : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext (by simpa using h))
    have hik : (i : ℕ) ≤ κ := by have := i.isLt; omega
    have hikz : ((i : ℕ) : ℤ) ≤ κ := by exact_mod_cast hik
    have h2 := hU i (by omega) hik
    rw [hcw i, hlast]
    linarith [hvl.1]
  have hpair : ∀ i : Fin (κ + 1), colW K U i + colW K U (Fin.rev i) ≤ 4 * S := by
    intro i
    have hi := i.isLt
    have hjk : (i : ℕ) ≤ κ := by omega
    rw [hcw, hcw, Fin.val_rev]
    have e1 : κ + 1 - ((i : ℕ) + 1) = κ - (i : ℕ) := by omega
    rw [e1]
    have e2 : (((κ - (i : ℕ) : ℕ)) : ℤ) = (κ : ℤ) - ((i : ℕ) : ℤ) := by omega
    have hUk := hU κ hκ1 le_rfl
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
    · have a1 : U (i : ℕ) = U 0 := by rw [h0]
      have a2 : U (κ - (i : ℕ)) = U κ := by rw [h0, Nat.sub_zero]
      have a3 : ((i : ℕ) : ℤ) = 0 := by omega
      linarith
    · rcases Nat.lt_or_ge (i : ℕ) κ with h1 | h1
      · have u1 := hU i h0 hjk
        have u2 := hU (κ - (i : ℕ)) (by omega) (by omega)
        linarith
      · have hik : (i : ℕ) = κ := by omega
        have a1 : U (i : ℕ) = U κ := by rw [hik]
        have a2 : U (κ - (i : ℕ)) = U 0 := by rw [hik, Nat.sub_self]
        have a3 : ((i : ℕ) : ℤ) = κ := by omega
        linarith
  refine ⟨hanti, hb, hc, ?_, ?_, ?_⟩
  · simp only [wt, plus]
    rw [Fin.sum_univ_succ]
    have h1 : ∑ j : Fin κ, (colW K U j.succ - colW K U (Fin.last κ)) ≤ ∑ j : Fin κ, S :=
      Finset.sum_le_sum (fun j _ => hc j.succ (Fin.succ_ne_zero j))
    have h2 : ∑ j : Fin κ, S = (κ : ℤ) * S := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h3 : colW K U (0 : Fin (κ + 1)) - colW K U (Fin.last κ) ≤ 3 * S := by
      rw [hzero, hlast]
      linarith [hvl.1]
    linarith
  · simp only [wt]
    exact Finset.sum_nonneg (fun i _ => (hb i).1)
  · have hrev : ∑ i : Fin (κ + 1), colW K U (Fin.rev i) = ∑ i : Fin (κ + 1), colW K U i :=
      Equiv.sum_comp Fin.revPerm (colW K U)
    have hs : ∑ i : Fin (κ + 1), (colW K U i + colW K U (Fin.rev i)) ≤ ∑ i : Fin (κ + 1), 4 * S :=
      Finset.sum_le_sum (fun i _ => hpair i)
    rw [Finset.sum_add_distrib, hrev] at hs
    have h4 : ∑ i : Fin (κ + 1), (4 * S) = ((κ : ℤ) + 1) * (4 * S) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    simp only [wt]
    linarith
end Formalism.HermitianLattices.ExplicitEstimates
