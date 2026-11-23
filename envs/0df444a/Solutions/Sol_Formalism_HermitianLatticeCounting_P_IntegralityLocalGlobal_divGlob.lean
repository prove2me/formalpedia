-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal.divGlob
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:57.33075+00:00
-- url     : https://prove2.me/submissions/a37b8492-6a09-4f5b-b7ae-de948b1ca450

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ComplexMultiplicationRoot
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_isInt_coe
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_locGlob

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
open Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
variable {E : Type} [Field E] [NumberField E]
namespace Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
theorem _root_.solution (e : E) (N : ℕ) (hN : 0 < N) (he : IsInt e)
    (h : ∀ P : Ideal (𝓞 E), P.IsPrime → (N : 𝓞 E) ∈ P → LocIn P e N) :
    ∃ β : 𝓞 E, e = (N : E) * (β : E) := by
  have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hx : IsInt (e / (N : E)) := by
    apply locGlob
    intro P hP
    by_cases hNP : (N : 𝓞 E) ∈ P
    · obtain ⟨y, z, hy, hyz⟩ := h P hP hNP
      refine ⟨y, hy, ?_⟩
      convert isInt_coe z using 1
      rw [mul_div_assoc', hyz]
      field_simp
    · refine ⟨(N : 𝓞 E), hNP, ?_⟩
      convert he using 1
      push_cast
      field_simp
  obtain ⟨β, hβ⟩ := hx
  refine ⟨β, ?_⟩
  rw [hβ]
  field_simp
end Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
