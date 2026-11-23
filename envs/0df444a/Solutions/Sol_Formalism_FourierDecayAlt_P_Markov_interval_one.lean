-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Markov.interval_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:41.074043+00:00
-- url     : https://prove2.me/submissions/1fea5271-c5c1-48fe-b7a7-b999e457c557

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Markov
open Polynomial
namespace Formalism.FourierDecayAlt.P.Markov
theorem _root_.solution (hA : Formalism.FourierDecayAlt.E.AMarkov) (P : ℝ[X]) (d : ℕ) (t₀ L M : ℝ) (hL : 0 < L)
    (hd : P.natDegree ≤ d) (hP : ∀ t ∈ Set.Icc t₀ (t₀ + L), |P.eval t| ≤ M) :
    ∀ t ∈ Set.Icc t₀ (t₀ + L), |P.derivative.eval t| ≤ (2 * (d : ℝ) ^ 2 / L) * M := by
  intro t ht
  set l : ℝ[X] := C (t₀ + L / 2) + C (L / 2) * X with hl
  have hldeg : l.natDegree ≤ 1 := by
    rw [hl]; compute_degree
  have hdeg : (P.comp l).natDegree ≤ d := by
    calc (P.comp l).natDegree ≤ P.natDegree * l.natDegree := natDegree_comp_le
      _ ≤ d * 1 := Nat.mul_le_mul hd hldeg
      _ = d := mul_one d
  have hleval : ∀ x : ℝ, l.eval x = t₀ + L / 2 + L / 2 * x := by
    intro x; simp [hl]
  have hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(P.comp l).eval x| ≤ M := by
    intro x hx
    rw [eval_comp, hleval]
    apply hP
    constructor <;> nlinarith [hx.1, hx.2]
  set x : ℝ := 2 * (t - t₀) / L - 1 with hx
  have hxm : x ∈ Set.Icc (-1 : ℝ) 1 := by
    have h1 : 0 ≤ 2 * (t - t₀) / L := by
      apply div_nonneg _ hL.le
      linarith [ht.1]
    have h2 : 2 * (t - t₀) / L ≤ 2 := by
      rw [div_le_iff₀ hL]
      linarith [ht.2]
    constructor <;> rw [hx] <;> linarith
  have hlx : l.eval x = t := by
    rw [hleval, hx]; field_simp; ring
  have hder : (P.comp l).derivative.eval x = L / 2 * P.derivative.eval t := by
    rw [derivative_comp, eval_mul, eval_comp, hlx]
    simp [hl]
  have key := hA (P.comp l) d M hdeg hb x hxm
  rw [hder, abs_mul, abs_of_pos (by positivity : 0 < L / 2)] at key
  have : |P.derivative.eval t| ≤ ((d : ℝ) ^ 2 * M) / (L / 2) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  calc |P.derivative.eval t| ≤ ((d : ℝ) ^ 2 * M) / (L / 2) := this
    _ = (2 * (d : ℝ) ^ 2 / L) * M := by field_simp
end Formalism.FourierDecayAlt.P.Markov
