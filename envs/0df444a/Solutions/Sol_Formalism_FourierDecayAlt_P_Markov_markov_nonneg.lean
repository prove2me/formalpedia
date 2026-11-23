-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Markov.markov_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:26.788112+00:00
-- url     : https://prove2.me/submissions/c163b35a-db6f-4140-a900-edd0ef7f9ef4

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_th_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_th_lt_pi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_schur
import Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_bernstein

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Markov
open Polynomial Real Finset
namespace Formalism.FourierDecayAlt.P.Markov
theorem _root_.solution (p : ℝ[X]) (n : ℕ) (hn : n ≠ 0) (hp : p.natDegree ≤ n) (M : ℝ)
    (hM : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |p.derivative.eval x| ≤ (n : ℝ) ^ 2 * M := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  by_cases hy : ∀ k < n, cos (th n k) < x
  · have hd : p.derivative.degree < n := by
      refine lt_of_le_of_lt (degree_le_of_natDegree_le
        ((natDegree_derivative_le p).trans (Nat.sub_le_sub_right hp 1))) ?_
      exact_mod_cast Nat.sub_lt hn0 one_pos
    have := schur n hn p.derivative hd (n * M) (fun k _ => bernstein p n hn hp M hM _) x hy hx1
    calc _ ≤ n * (n * M) := this
      _ = _ := by ring
  · push Not at hy
    obtain ⟨k, hk, hxk⟩ := hy
    have hcos : cos (arccos x) = x := cos_arccos (by linarith) hx1
    have hφ1 : th n k ≤ arccos x := by
      have := arccos_le_arccos hxk
      rwa [arccos_cos (th_pos n k hn).le (th_lt_pi hk).le] at this
    have hφ2 : arccos x ≤ π / 2 := arccos_le_pi_div_two.mpr hx0
    have hth : π / (2 * n) ≤ th n k := by
      unfold th
      gcongr
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith [pi_pos]
    have hsin : 1 / (n : ℝ) ≤ sin (arccos x) := by
      have h1 := mul_le_sin (arccos_nonneg x) hφ2
      have h2 : 2 / π * (π / (2 * n)) ≤ 2 / π * arccos x :=
        mul_le_mul_of_nonneg_left (hth.trans hφ1) (by positivity)
      have h3 : 2 / π * (π / (2 * n)) = 1 / (n : ℝ) := by
        have := pi_pos.ne'
        field_simp
      linarith
    have hb := bernstein p n hn hp M hM (arccos x)
    rw [hcos, abs_mul, abs_of_nonneg ((by positivity : (0 : ℝ) ≤ 1 / n).trans hsin)] at hb
    have h4 : 1 / (n : ℝ) * |p.derivative.eval x| ≤ n * M :=
      (mul_le_mul_of_nonneg_right hsin (abs_nonneg _)).trans hb
    calc |p.derivative.eval x| = n * (1 / (n : ℝ) * |p.derivative.eval x|) := by field_simp
      _ ≤ n * (n * M) := mul_le_mul_of_nonneg_left h4 hn'.le
      _ = _ := by ring
end Formalism.FourierDecayAlt.P.Markov
