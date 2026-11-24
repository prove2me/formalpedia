-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.local_congruence_condition
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:35.44358+00:00
-- url     : https://prove2.me/submissions/278be46c-3e8d-454a-be95-b03e3fe2044b

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ComplexMultiplicationRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocalCongr := by
  intro E _ _ P T T' a b c d hP hT hT' h
  have hT0 : (T : E) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hT'0 : (T' : E) ≠ 0 := Nat.cast_ne_zero.mpr hT'.ne'
  have h1P : (1 : 𝓞 E) ∉ P := (Ideal.ne_top_iff_one P).mp hP.ne_top
  have one : ∀ x : E, x = 1 → LocIn P x 1 := by
    intro x hx; unfold LocIn
    exact ⟨1, 1, h1P, by simp [hx]⟩
  have zer : ∀ x : E, x = 0 → LocIn P x 1 := by
    intro x hx; unfold LocIn
    exact ⟨1, 0, h1P, by simp [hx]⟩
  have back : ∀ (x : E) (N : ℕ), (N : E) ≠ 0 → LocIn P (x * (1 / (N : E))) 1 → LocIn P x N := by
    intro x N hN hx
    unfold LocIn at hx ⊢
    obtain ⟨y, z, hy, hyz⟩ := hx
    refine ⟨y, z, hy, ?_⟩
    have e : (y : E) * x = (N : E) * ((y : E) * (x * (1 / (N : E)))) := by
      first
      | field_simp
      | rw [mul_one_div, mul_div_assoc', mul_div_assoc', mul_div_cancel_left₀ _ hN]
    rw [e, hyz]; simp
  obtain ⟨ha, hc⟩ := h (1 / (T : E)) 0 (one _ (by field_simp)) (zer _ (by simp))
  obtain ⟨hb, hd⟩ := h 0 (1 / (T' : E)) (zer _ (by simp)) (one _ (by field_simp))
  simp only [mul_zero, add_zero, zero_add] at ha hc hb hd
  exact ⟨back _ _ hT0 ha, back _ _ hT0 hc, back _ _ hT'0 hb, back _ _ hT'0 hd⟩
end Formalism.HermitianLatticeCounting.P
