-- Prove2me | solution 1 for Formalism.UG.P.sf_sign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:39:48.968958+00:00
-- url     : https://prove2.me/submissions/859d01c2-fbe8-4cdb-a385-ac8ba979af0e

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField ComplexConjugate
open Formalism Formalism.UG Formalism.UG.P
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (J : Matrix n n E)
    (τ : E →+* ℂ) (hτ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hdef : ∀ ι : F →+* ℝ, IsDefiniteAt σ J ι) :
    ∃ s : ℝ, 0 < s * s ∧ ∀ x : n → E, ∃ t : ℝ, τ (hform (σ : E →+* E) J x x) = t ∧
      (x ≠ 0 → 0 < s * t) ∧ 0 ≤ s * t := by
  classical
  have hreal : ∀ a : F, conj (τ (algebraMap F E a)) = τ (algebraMap F E a) := by
    intro a
    have h1 : τ ((σ : E →+* E) (algebraMap F E a)) = conj (τ (algebraMap F E a)) :=
      RingHom.congr_fun hτ _
    have h2 : (σ : E →+* E) (algebraMap F E a) = algebraMap F E a := σ.commutes a
    rw [h2] at h1
    exact h1.symm
  have him : ∀ a : F, (τ (algebraMap F E a)).im = 0 := fun a => Complex.conj_eq_iff_im.1 (hreal a)
  let ι : F →+* ℝ :=
    { toFun := fun a => (τ (algebraMap F E a)).re
      map_one' := by simp
      map_mul' := fun a b => by simp [map_mul, Complex.mul_re, him a, him b]
      map_zero' := by simp
      map_add' := fun a b => by simp [map_add] }
  have hval : ∀ a : F, τ (algebraMap F E a) = ((ι a : ℝ) : ℂ) := fun a =>
    (Complex.conj_eq_iff_re.1 (hreal a)).symm
  have h00 : τ (hform (σ : E →+* E) J 0 0) = ((0 : ℝ) : ℂ) := by
    unfold hform
    simp
  rcases hdef ι with hpos | hneg
  · refine ⟨1, by norm_num, fun x => ?_⟩
    by_cases hx : x = 0
    · refine ⟨0, ?_, fun h => absurd hx h, by norm_num⟩
      subst hx
      exact h00
    · obtain ⟨a, ha, hpa⟩ := hpos x hx
      refine ⟨ι a, ?_, fun _ => by linarith, by linarith⟩
      rw [← ha]
      exact hval a
  · refine ⟨-1, by norm_num, fun x => ?_⟩
    by_cases hx : x = 0
    · refine ⟨0, ?_, fun h => absurd hx h, by norm_num⟩
      subst hx
      exact h00
    · obtain ⟨a, ha, hpa⟩ := hneg x hx
      refine ⟨ι a, ?_, fun _ => by linarith, by linarith⟩
      rw [← ha]
      exact hval a
end Formalism.UG.P
