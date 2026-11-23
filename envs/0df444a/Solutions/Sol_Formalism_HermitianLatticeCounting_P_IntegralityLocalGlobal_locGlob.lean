-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal.locGlob
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:41.493409+00:00
-- url     : https://prove2.me/submissions/d9afc06a-0ea3-4aa9-861e-2940bb47b2ce

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ComplexMultiplicationRoot
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_isInt_mul
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_isInt_add
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_isInt_coe

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
theorem _root_.solution (x : E) (h : ∀ P : Ideal (𝓞 E), P.IsPrime → ∃ y : 𝓞 E, y ∉ P ∧ IsInt ((y : E) * x)) :
    IsInt x := by
  let I : Ideal (𝓞 E) :=
    { carrier := {y | IsInt ((y : E) * x)}
      add_mem' := fun {a b} ha hb => by
        show IsInt (((a + b : 𝓞 E) : E) * x)
        convert isInt_add ha hb using 1
        push_cast; ring
      zero_mem' := by
        show IsInt (((0 : 𝓞 E) : E) * x)
        convert isInt_coe (0 : 𝓞 E) using 1
        push_cast; ring
      smul_mem' := fun c y hy => by
        show IsInt (((c • y : 𝓞 E) : E) * x)
        convert isInt_mul (isInt_coe c) hy using 1
        rw [smul_eq_mul]; push_cast; ring }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨y, hy, hyx⟩ := h M hM.isPrime
    exact hy (hIM (show y ∈ I from hyx))
  have h1 : (1 : 𝓞 E) ∈ I := by rw [hI]; exact Submodule.mem_top
  have h1' : IsInt (((1 : 𝓞 E) : E) * x) := h1
  convert h1' using 1
  push_cast; ring
end Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
