-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordLiftInduction.top_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:30.588529+00:00
-- url     : https://prove2.me/submissions/82b18026-9d3f-4265-bbfd-87f188d0c520

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordLiftInduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordLiftInduction
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.WordLiftInduction
theorem _root_.solution {W : ℝ → ℂ} {d : ℕ} {c : ℂ} (h : IsTopCoeff W d c) (y : Fin (d + 1) → ℝ)
    (hy : Function.Injective y) : ∑ j, ((lagCo y j : ℝ) : ℂ) * W (y j) = c := by
  obtain ⟨P, hd, hc, hP⟩ := h
  have hinj : Function.Injective (fun j => ((y j : ℝ) : ℂ)) :=
    fun a b hab => hy (Complex.ofReal_injective hab)
  have hlt : P.degree < (univ : Finset (Fin (d + 1))).card := by
    rw [card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hd)
  have h := Lagrange.coeff_eq_sum (s := univ) (v := fun j => ((y j : ℝ) : ℂ)) hinj.injOn hlt
  simp only [card_univ, Fintype.card_fin, Nat.add_sub_cancel] at h
  rw [← hc, h]
  refine sum_congr rfl fun i _ => ?_
  rw [hP]
  unfold lagCo
  push_cast
  rw [prod_inv_distrib, div_eq_mul_inv, mul_comm]
end Formalism.FourierDecayAlt.P.WordLiftInduction
