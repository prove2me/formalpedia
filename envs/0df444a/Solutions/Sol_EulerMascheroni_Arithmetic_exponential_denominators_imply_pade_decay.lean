-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.exponential_denominators_imply_pade_decay
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T15:05:22.682744+00:00
-- url     : https://prove2.me/submissions/9756f349-d5c7-444a-bf12-5f2cbfd474cb

import Definitions.Def_eulerMascheroni_padeDecay
import Theorems.Thm_EulerMascheroni_Arithmetic_normalized_pade_tendsto_zero
open Filter EulerMascheroni.Arithmetic
open scoped Topology
namespace EulerDecay
lemma exponential_implies_decay (a : ℝ) (h : ExponentialDenominators a) :
    PadeDecayDenominators a := by
  obtain ⟨C,hC,h⟩ := h
  choose d hdpos hdle hdi using h
  refine ⟨fun n => d (2*n),fun n => hdpos (2*n),?_,fun n => hdi (2*n)⟩
  have hU : ∀ n : ℕ, |(4:ℤ)^n*(n.factorial:ℤ)| ≤ (4:ℤ)^n*(n.factorial:ℤ) := by
    intro n
    rw [abs_of_nonneg (by positivity)]
  have hh := normalized_pade_tendsto_zero (fun n => (4:ℤ)^n*(n.factorial:ℤ)) C hC
    (fun n => d (2*n)) (fun n => hdle (2*n)) hU
  convert hh using 1
  funext n
  push_cast
  field_simp
end EulerDecay


theorem solution (a : ℝ) (h : ExponentialDenominators a) :
    PadeDecayDenominators a := by
  exact EulerDecay.exponential_implies_decay a h

#print axioms solution
