-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:30:49.050175+00:00
-- url     : https://prove2.me/submissions/84d8cd15-39a5-4e7e-bdb1-73de6c8e7ba2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_eval_pair_coordinates
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_aeval_eval_pair
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_eval_pair_one
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_eval_pair_sub
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_aeval_mem_pow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_aeval_sub_mem_pow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_eq_zero_of_isHomogeneous
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_sub_homogeneousComponent_mem
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_aeval_double
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_eval_pair_homogeneous
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_xs_hom
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_lin_hom
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_xs_mem
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_lin_mem
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_eval_pair_additive_first
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_symm_of
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_lin_add_lin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
open MvPolynomial
variable {S : Type} [CommRing S] {d : ℕ}
variable [Algebra ℚ S]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
theorem _root_.solution {P : MvPolynomial (Fin 2 × Fin d) S} {m j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m)
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (A Ab : Fin d → Fin d → S) (hAA : ∀ i l, A i l + Ab i l = if i = l then 1 else 0)
    (aW0 aB1 : Fin d → MvPolynomial (Fin 2 × Fin d) S)
    (hW0 : ∀ i, aW0 i - lin A 0 i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hB1 : ∀ i, aB1 i - lin Ab 1 i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hbal : ev2 P aW0 (xs S d 1) - ev2 P (xs S d 0) aB1 ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (aW : Fin d → MvPolynomial (Fin 1 × Fin d) S) (hW : ∀ i, aW i - lin A 0 i ∈ Io S (Fin 1 × Fin d) ^ 2)
    (hdiag : ev2 P (xs S d 0) aW - 1 ∈ Io S (Fin 1 × Fin d) ^ (m + 1))
    (hP : P - 1 ∈ Io S (Fin 2 × Fin d) ^ j) : P - 1 ∈ Io S (Fin 2 × Fin d) ^ (j + 1) := by
  set W := P - 1 with hWdef
  set h := homogeneousComponent j W with hhdef
  have hR : W - h ∈ Io S _ ^ (j + 1) := sub_homogeneousComponent_mem hP
  have hh : h.IsHomogeneous j := homogeneousComponent_isHomogeneous j W
  have hhI : h ∈ Io S _ ^ j := by
    have := sub_mem hP (Ideal.pow_le_pow_right (Nat.le_succ j) hR)
    simpa using this
  have hmj : ∀ {σ : Type} {p : MvPolynomial σ S}, p ∈ Io S σ ^ (m + 1) → p ∈ Io S σ ^ (j + 1) :=
    fun hp => Ideal.pow_le_pow_right (by omega) hp
  have hsq : ∀ {τ : Type} {p : MvPolynomial τ S}, p ∈ Io S τ ^ 2 → p ∈ Io S τ :=
    fun hp => Ideal.pow_le_self two_ne_zero hp
  have hPW : ∀ {τ : Type} (u v : Fin d → MvPolynomial τ S), ev2 P u v = 1 + ev2 W u v := by
    intro τ u v; rw [hWdef, eval_pair_sub, eval_pair_one]; ring
  have hTr : ∀ {τ : Type} (u v : Fin d → MvPolynomial τ S), (∀ i, u i ∈ Io S τ) → (∀ i, v i ∈ Io S τ) →
      ev2 W u v - ev2 h u v ∈ Io S τ ^ (j + 1) := by
    intro τ u v hu hv
    rw [← eval_pair_sub]
    exact aeval_mem_pow _ (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv]) _ hR
  have hEvW : ∀ {τ : Type} (u v : Fin d → MvPolynomial τ S), (∀ i, u i ∈ Io S τ) → (∀ i, v i ∈ Io S τ) →
      ev2 W u v ∈ Io S τ ^ j := fun u v hu hv =>
    aeval_mem_pow _ (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv]) _ hP
  have hRep : ∀ {τ : Type} (u v u' v' : Fin d → MvPolynomial τ S), (∀ i, u i ∈ Io S τ) → (∀ i, v i ∈ Io S τ) →
      (∀ i, u' i ∈ Io S τ) → (∀ i, v' i ∈ Io S τ) → (∀ i, u i - u' i ∈ Io S τ ^ 2) →
      (∀ i, v i - v' i ∈ Io S τ ^ 2) → ev2 h u v - ev2 h u' v' ∈ Io S τ ^ (j + 1) := by
    intro τ u v u' v' hu hv hu' hv' huu hvv
    exact aeval_sub_mem_pow _ _ (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv])
      (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu', hv'])
      (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [huu, hvv]) j h hhI
  have hx : ∀ {n : ℕ} (k : Fin n) (i : Fin d), xs S d k i ∈ Io S (Fin n × Fin d) := fun k i => xs_mem k i
  have hl : ∀ {n : ℕ} (B : Fin d → Fin d → S) (k : Fin n) (i : Fin d), lin B k i ∈ Io S (Fin n × Fin d) :=
    fun B k i => lin_mem B k i

  have hA1 : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
      ev2 h (xs S d 0) (xs S d 2) + ev2 h (xs S d 1) (xs S d 2) := by
    have hfF : ∀ i, fF i ∈ Io S _ := fun i => by
      have := add_mem (hsq (hF i)) (add_mem (hx 0 i) (hx 1 i)); simpa using this
    have k1 : ev2 W fF (xs S d 2) - ev2 W (xs S d 0) (xs S d 2) - ev2 W (xs S d 1) (xs S d 2) ∈
        Io S _ ^ (j + 1) := by
      have e : ev2 W fF (xs S d 2) - ev2 W (xs S d 0) (xs S d 2) - ev2 W (xs S d 1) (xs S d 2) =
          (ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2)) +
            ev2 W (xs S d 0) (xs S d 2) * ev2 W (xs S d 1) (xs S d 2) := by
        rw [hPW, hPW, hPW]; ring
      rw [e]
      refine add_mem (hmj hph1) (Ideal.pow_le_pow_right (by omega : j + 1 ≤ j + j) ?_)
      rw [pow_add]
      exact Ideal.mul_mem_mul (hEvW _ _ (hx 0) (hx 2)) (hEvW _ _ (hx 1) (hx 2))
    have k3 := hRep fF (xs S d 2) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) hfF (hx 2)
      (fun i => add_mem (hx 0 i) (hx 1 i)) (hx 2) hF (fun i => by simp)
    have hE : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) - ev2 h (xs S d 0) (xs S d 2) -
        ev2 h (xs S d 1) (xs S d 2) ∈ Io S _ ^ (j + 1) := by
      have e : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) - ev2 h (xs S d 0) (xs S d 2) -
          ev2 h (xs S d 1) (xs S d 2) =
          (ev2 W fF (xs S d 2) - ev2 W (xs S d 0) (xs S d 2) - ev2 W (xs S d 1) (xs S d 2)) -
            (ev2 W fF (xs S d 2) - ev2 h fF (xs S d 2)) + (ev2 W (xs S d 0) (xs S d 2) - ev2 h (xs S d 0) (xs S d 2)) +
            (ev2 W (xs S d 1) (xs S d 2) - ev2 h (xs S d 1) (xs S d 2)) -
            (ev2 h fF (xs S d 2) - ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2)) := by ring
      rw [e]
      exact sub_mem (add_mem (add_mem (sub_mem k1 (hTr _ _ hfF (hx 2))) (hTr _ _ (hx 0) (hx 2)))
        (hTr _ _ (hx 1) (hx 2))) k3
    have hom : (ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) - ev2 h (xs S d 0) (xs S d 2) -
        ev2 h (xs S d 1) (xs S d 2)).IsHomogeneous j :=
      ((eval_pair_homogeneous hh _ _ (fun i => (xs_hom 0 i).add (xs_hom 1 i)) (xs_hom 2)).sub
        (eval_pair_homogeneous hh _ _ (xs_hom 0) (xs_hom 2))).sub (eval_pair_homogeneous hh _ _ (xs_hom 1) (xs_hom 2))
    have := eq_zero_of_isHomogeneous hom hE
    rw [sub_sub, sub_eq_zero] at this
    exact this

  have hs : ev2 h (xs S d 1) (xs S d 0) = h := by
    have k : ev2 h (xs S d 1) (xs S d 0) - h ∈ Io S _ ^ (j + 1) := by
      have e : ev2 h (xs S d 1) (xs S d 0) - h = (ev2 P (xs S d 1) (xs S d 0) - P) -
          (ev2 W (xs S d 1) (xs S d 0) - ev2 h (xs S d 1) (xs S d 0)) + (W - h) := by
        rw [hPW, hWdef]; ring
      rw [e]
      exact add_mem (sub_mem (hmj hsym) (hTr _ _ (hx 1) (hx 0))) hR
    have := eq_zero_of_isHomogeneous ((eval_pair_homogeneous hh _ _ (xs_hom 1) (xs_hom 0)).sub hh) k
    exact sub_eq_zero.1 this
  have add1 : ∀ {τ : Type} (u u' v : Fin d → MvPolynomial τ S),
      ev2 h (fun i => u i + u' i) v = ev2 h u v + ev2 h u' v := fun u u' v => eval_pair_additive_first hA1 u u' v
  have symm : ∀ {τ : Type} (u v : Fin d → MvPolynomial τ S), ev2 h u v = ev2 h v u :=
    fun u v => symm_of hs u v
  have add2 : ∀ {τ : Type} (u v v' : Fin d → MvPolynomial τ S),
      ev2 h u (fun i => v i + v' i) = ev2 h u v + ev2 h u v' := by
    intro τ u v v'
    rw [symm, add1, symm v u, symm v' u]
  suffices h0 : h = 0 by
    have := add_mem hR (show h ∈ Io S _ ^ (j + 1) by rw [h0]; exact zero_mem _)
    simpa using this
  by_cases hj2 : j = 2
  · have haW : ∀ i, aW i ∈ Io S _ := fun i => by
      have := add_mem (hsq (hW i)) (hl A 0 i); simpa using this
    have haW0 : ∀ i, aW0 i ∈ Io S _ := fun i => by
      have := add_mem (hsq (hW0 i)) (hl A 0 i); simpa using this
    have haB1 : ∀ i, aB1 i ∈ Io S _ := fun i => by
      have := add_mem (hsq (hB1 i)) (hl Ab 1 i); simpa using this
    have hd1 : ev2 h (xs S d (0 : Fin 1)) (lin A 0) = 0 := by
      have k : ev2 h (xs S d (0 : Fin 1)) (lin A 0) ∈ Io S _ ^ (j + 1) := by
        have e : ev2 h (xs S d (0 : Fin 1)) (lin A 0) = (ev2 P (xs S d 0) aW - 1) -
            (ev2 W (xs S d 0) aW - ev2 h (xs S d 0) aW) - (ev2 h (xs S d 0) aW - ev2 h (xs S d 0) (lin A 0)) := by
          rw [hPW]; ring
        rw [e]
        exact sub_mem (sub_mem (hmj hdiag) (hTr _ _ (hx 0) haW))
          (hRep _ _ _ _ (hx 0) haW (hx 0) (hl A 0) (fun i => by simp) hW)
      exact eq_zero_of_isHomogeneous (eval_pair_homogeneous hh _ _ (xs_hom 0) (lin_hom A 0)) k
    have hb1 : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) = ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) := by
      have k : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) ∈ Io S _ ^ (j + 1) := by
        have e : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) =
            (ev2 P aW0 (xs S d 1) - ev2 P (xs S d 0) aB1) -
            (ev2 W aW0 (xs S d 1) - ev2 h aW0 (xs S d 1)) + (ev2 W (xs S d 0) aB1 - ev2 h (xs S d 0) aB1) -
            (ev2 h aW0 (xs S d 1) - ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2))) +
            (ev2 h (xs S d 0) aB1 - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2))) := by
          rw [hPW, hPW]; ring
        rw [e]
        exact add_mem (sub_mem (add_mem (sub_mem (hmj hbal) (hTr _ _ haW0 (hx 1))) (hTr _ _ (hx 0) haB1))
          (hRep _ _ _ _ haW0 (hx 1) (hl A 0) (hx 1) hW0 (fun i => by simp)))
          (hRep _ _ _ _ (hx 0) haB1 (hx 0) (hl Ab 1) (fun i => by simp) hB1)
      exact sub_eq_zero.1 (eq_zero_of_isHomogeneous
        ((eval_pair_homogeneous hh _ _ (lin_hom A 0) (xs_hom 1)).sub (eval_pair_homogeneous hh _ _ (xs_hom 0) (lin_hom Ab 1))) k)
    have hsub : ∀ (g : Fin 1 × Fin d → MvPolynomial (Fin 2 × Fin d) S),
        ev2 h (fun i => aeval g (xs S d (0 : Fin 1) i)) (fun i => aeval g (lin A (0 : Fin 1) i)) = 0 := by
      intro g; rw [← aeval_eval_pair, hd1, map_zero]
    have hd0 : ev2 h (xs S d (0 : Fin 2)) (lin A 0) = 0 := by
      have := hsub (fun p => xs S d (0 : Fin 2) p.2); simp [xs, lin] at this; exact this
    have hd1' : ev2 h (xs S d (1 : Fin 2)) (lin A 1) = 0 := by
      have := hsub (fun p => xs S d (1 : Fin 2) p.2); simp [xs, lin] at this; exact this
    have hd01 : ev2 h (fun i => xs S d (0 : Fin 2) i + xs S d 1 i) (fun i => lin A 0 i + lin A 1 i) = 0 := by
      have := hsub (fun p => xs S d (0 : Fin 2) p.2 + xs S d 1 p.2)
      simpa [xs, lin, mul_add, Finset.sum_add_distrib] using this
    have e1 : ev2 h (xs S d (0 : Fin 2)) (lin A (1 : Fin 2)) + ev2 h (xs S d (1 : Fin 2)) (lin A (0 : Fin 2)) = 0 := by
      have := hd01
      rw [add1, add2, add2] at this
      linear_combination this - hd0 - hd1'
    rw [symm (xs S d (1 : Fin 2)) (lin A (0 : Fin 2)), hb1] at e1
    have e2 : ev2 h (xs S d (0 : Fin 2)) (fun i => lin A (1 : Fin 2) i + lin Ab (1 : Fin 2) i) = 0 := by
      rw [add2]; linear_combination e1
    rw [lin_add_lin A Ab hAA 1, eval_pair_coordinates] at e2
    exact e2
  · have h2x : ev2 h (fun i => xs S d (0 : Fin 2) i + xs S d 0 i) (xs S d 1) = h + h := by
      rw [add1, eval_pair_coordinates]
    have h4 : ev2 h (fun i => xs S d (0 : Fin 2) i + xs S d 0 i) (fun i => xs S d 1 i + xs S d 1 i) =
        h + h + (h + h) := by
      rw [add2, h2x]
    have hf : (fun p : Fin 2 × Fin d =>
        ![fun i => xs S d (0 : Fin 2) i + xs S d 0 i, fun i => xs S d 1 i + xs S d 1 i] p.1 p.2) =
        fun p => X p + X p := by
      funext p; rcases p with ⟨k, i⟩; fin_cases k <;> simp [xs]
    have hsc : ev2 h (fun i => xs S d (0 : Fin 2) i + xs S d 0 i) (fun i => xs S d 1 i + xs S d 1 i) =
        C ((2 : S) ^ j) * h := by
      rw [← aeval_double hh]
      show aeval _ h = _
      rw [hf]
    have h4' : C ((2 : S) ^ j - 4) * h = 0 := by
      have e4 : (C (4 : S) : MvPolynomial (Fin 2 × Fin d) S) = 4 := map_ofNat C 4
      rw [map_sub, sub_mul, ← hsc, h4, e4]; ring
    have hne : (2 : ℚ) ^ j - 4 ≠ 0 := by
      intro h0
      have h1 : ((2 ^ j : ℕ) : ℚ) = ((2 ^ 2 : ℕ) : ℚ) := by push_cast; linarith
      exact hj2 (Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h1))
    have hu : IsUnit (C ((2 : S) ^ j - 4) : MvPolynomial (Fin 2 × Fin d) S) := by
      have e : ((2 : S) ^ j - 4) = algebraMap ℚ S ((2 : ℚ) ^ j - 4) := by
        rw [map_sub, map_pow, map_ofNat, map_ofNat]
      rw [e]; exact ((IsUnit.mk0 _ hne).map (algebraMap ℚ S)).map C
    exact hu.mul_right_eq_zero.1 h4'
end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
