-- Prove2me | solution 1 for Formalism.ThetaLiftIndependence.FiniteFieldPlancherel.charSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:22.055387+00:00
-- url     : https://prove2.me/submissions/d98c0b9d-3150-4ed7-904d-8cc50ffe1e52

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_FFPlancherel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ThetaLiftIndependence
open Formalism.ThetaLiftIndependence.FiniteFieldPlancherel
open Classical
namespace Formalism.ThetaLiftIndependence.FiniteFieldPlancherel
theorem _root_.solution {𝔽 U : Type} [Field 𝔽] [AddCommGroup U] [Module 𝔽 U] [Fintype U]
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (g : Module.Dual 𝔽 U) :
    ∑ e : U, ψ (g e) = if g = 0 then (Fintype.card U : ℂ) else 0 := by
  by_cases hg : g = 0
  · subst hg; simp
  · rw [if_neg hg]
    obtain ⟨a, ha⟩ : ∃ a, ψ a ≠ 1 := by
      by_contra h
      push Not at h
      apply hψ
      ext a
      simp [h a]
    obtain ⟨x, hx⟩ : ∃ x, g x ≠ 0 := by
      by_contra h
      push Not at h
      exact hg (LinearMap.ext fun x => by simp [h x])
    set e0 : U := (a / g x) • x with he0
    have hge0 : g e0 = a := by
      rw [he0, map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]
    have hshift : ∑ e : U, ψ (g e) = (∑ e : U, ψ (g e)) * ψ a := by
      calc ∑ e : U, ψ (g e) = ∑ e : U, ψ (g (e + e0)) :=
            (Fintype.sum_equiv (Equiv.addRight e0) _ _ (fun _ => rfl)).symm
        _ = (∑ e : U, ψ (g e)) * ψ a := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [map_add, AddChar.map_add_eq_mul, hge0]
    have h1 : (∑ e : U, ψ (g e)) * (ψ a - 1) = 0 := by
      rw [mul_sub, mul_one, ← hshift, sub_self]
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) ha
end Formalism.ThetaLiftIndependence.FiniteFieldPlancherel
