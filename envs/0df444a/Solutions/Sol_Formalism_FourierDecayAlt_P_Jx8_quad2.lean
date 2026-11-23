-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.quad2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:58.590468+00:00
-- url     : https://prove2.me/submissions/f7f8a8d6-def9-40c6-b536-3019b3eb4d27

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
variable {α : Type}
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution [DecidableEq α] (F : Finset α) (k : α → α → ℂ) (x y : α) (hx : x ∈ F) (hy : y ∈ F)
    (hxy : x ≠ y) (c : ℂ) :
    ∑ u ∈ F, ∑ v ∈ F, (if u = x then (1 : ℂ) else if u = y then c else 0) *
        conj (if v = x then (1 : ℂ) else if v = y then c else 0) * k u v =
      k x x + conj c * k x y + c * k y x + c * conj c * k y y := by
  have hsub : ({x, y} : Finset α) ⊆ F := by
    intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have h0 : ∀ u, u ∉ ({x, y} : Finset α) → (if u = x then (1 : ℂ) else if u = y then c else 0) = 0 := by
    intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
    simp [hu.1, hu.2]
  rw [← Finset.sum_subset hsub (fun u _ hu => by simp [h0 u hu])]
  have inner : ∀ u, ∑ v ∈ F, (if u = x then (1 : ℂ) else if u = y then c else 0) *
        conj (if v = x then (1 : ℂ) else if v = y then c else 0) * k u v =
      ∑ v ∈ ({x, y} : Finset α), (if u = x then (1 : ℂ) else if u = y then c else 0) *
        conj (if v = x then (1 : ℂ) else if v = y then c else 0) * k u v := fun u =>
    (Finset.sum_subset hsub (fun v _ hv => by simp [h0 v hv])).symm
  simp only [inner]
  rw [Finset.sum_pair hxy, Finset.sum_pair hxy, Finset.sum_pair hxy]
  simp [hxy.symm]
  ring
end Formalism.FourierDecayAlt.P.Jx8
