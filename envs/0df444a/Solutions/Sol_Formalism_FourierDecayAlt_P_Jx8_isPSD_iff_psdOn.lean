-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.isPSD_iff_psdOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:21.680401+00:00
-- url     : https://prove2.me/submissions/64f08c4e-60a4-4fe7-a2f2-3308b5664fa4

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_conj_quad
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_quad1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_quad2

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
theorem _root_.solution (F : Finset α) (k : α → α → ℂ) : A5.IsPSD F k ↔ TA.PSDOn F k := by
  classical
  unfold A5.IsPSD TA.PSDOn
  constructor
  · intro h
    have hd : ∀ x ∈ F, (k x x).im = 0 := by
      intro x hx
      have := (h (fun u => if u = x then (1 : ℂ) else 0)).1
      rwa [quad1 F k x hx] at this
    refine ⟨?_, ?_⟩
    · intro x hx y hy
      by_cases hxy : x = y
      · subst hxy
        exact ((Complex.conj_eq_iff_im).2 (hd x hx)).symm
      · have h1 := (h (fun u => if u = x then (1 : ℂ) else if u = y then 1 else 0)).1
        rw [quad2 F k x y hx hy hxy 1] at h1
        have h2 := (h (fun u => if u = x then (1 : ℂ) else if u = y then Complex.I else 0)).1
        rw [quad2 F k x y hx hy hxy Complex.I] at h2
        simp [hd x hx, hd y hy] at h1 h2
        apply Complex.ext
        · simp; linarith
        · simp; linarith
    · intro a
      have := (h (fun u => conj (a u))).2
      have e : ∑ x ∈ F, ∑ y ∈ F, conj (a x) * conj (conj (a y)) * k x y =
          ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by
        apply Finset.sum_congr rfl; intro x _
        apply Finset.sum_congr rfl; intro y _
        rw [Complex.conj_conj]; ring
      rwa [e] at this
  · rintro ⟨hh, hp⟩ a
    have e : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y =
        ∑ x ∈ F, ∑ y ∈ F, conj (conj (a x)) * k x y * conj (a y) := by
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro y _
      rw [Complex.conj_conj]; ring
    rw [e]
    refine ⟨?_, hp (fun u => conj (a u))⟩
    have := conj_quad F k hh (fun u => conj (a u))
    rwa [Complex.conj_eq_iff_im] at this
end Formalism.FourierDecayAlt.P.Jx8
