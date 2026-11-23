-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx3.interlaceSignTwo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:06.912411+00:00
-- url     : https://prove2.me/submissions/939b9a86-13ed-45e9-8386-5f8c296eb5d9

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx3
namespace Formalism.FourierDecayAlt.P.Mx3
theorem _root_.solution : InterlaceSignTwo := by
  intro k u u' ρ l Y h1 h2 hI hC e he
  have he2 : -2 ≤ e ∧ e ≤ 2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> norm_num
  have hm := mono k u u' ρ hI

  have hlow : ∀ i ∈ Icc 1 (l - 1), 0 < Y + e + ρ i := by
    intro i hi
    have hi' := Finset.mem_Icc.1 hi
    have b := hI i (Finset.mem_Icc.2 ⟨hi'.1, by omega⟩)
    have c := hm (l - (i + 1)) (i + 1) (by omega) (by omega)
    have e1 : i + 1 + (l - (i + 1)) = l := by omega
    rw [e1] at c
    rcases hC with hC | hC <;> linarith [b.2.2.1, b.2.2.2, c.1, c.2, hC.1, hC.2]
  have hhigh : ∀ i ∈ Icc l (k - 1), 0 < -(Y + e + ρ i) := by
    intro i hi
    have hi' := Finset.mem_Icc.1 hi
    have b := hI i (Finset.mem_Icc.2 ⟨by omega, hi'.2⟩)
    have c := hm (i - l) l h1 (by omega)
    have e1 : l + (i - l) = i := by omega
    rw [e1] at c
    rcases hC with hC | hC <;> linarith [b.1, b.2.1, c.1, c.2, hC.1, hC.2]
  have hsplit : Icc 1 (k - 1) = Icc 1 (l - 1) ∪ Icc l (k - 1) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Icc 1 (l - 1)) (Icc l (k - 1)) := by
    rw [Finset.disjoint_left]; intro i a b
    have := Finset.mem_Icc.1 a; have := Finset.mem_Icc.1 b; omega
  have hcard : (Icc l (k - 1)).card = k - l := by simp; omega
  unfold I.xpoly
  rw [hsplit, Finset.prod_union hdisj]
  have hneg : ∏ i ∈ Icc l (k - 1), (Y + e + ρ i) = (-1) ^ (k - l) * ∏ i ∈ Icc l (k - 1), (-(Y + e + ρ i)) := by
    rw [← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro i _; ring
  rw [hneg]
  have p1 := Finset.prod_pos hlow
  have p2 := Finset.prod_pos hhigh
  have sq : ((-1 : ℝ) ^ (k - l)) * (-1) ^ (k - l) = 1 := by rw [← mul_pow]; simp
  calc (0:ℝ) < (∏ i ∈ Icc 1 (l - 1), (Y + e + ρ i)) * ∏ i ∈ Icc l (k - 1), (-(Y + e + ρ i)) := mul_pos p1 p2
    _ = ((-1 : ℝ) ^ (k - l) * (-1) ^ (k - l)) * ((∏ i ∈ Icc 1 (l - 1), (Y + e + ρ i)) * ∏ i ∈ Icc l (k - 1), (-(Y + e + ρ i))) := by rw [sq, one_mul]
    _ = _ := by ring
end Formalism.FourierDecayAlt.P.Mx3
