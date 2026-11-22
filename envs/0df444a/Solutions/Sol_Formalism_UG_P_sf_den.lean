-- Prove2me | solution 1 for Formalism.UG.P.sf_den
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:56:33.587862+00:00
-- url     : https://prove2.me/submissions/8bbddd3c-6f04-4ed5-b87a-2e3a55a0c24d

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
variable {E : Type} [Field E] [NumberField E]
namespace Formalism.UG.P
theorem _root_.solution {ι : Type} [Finite ι] (f : ι → E) :
    ∃ d : E, d ≠ 0 ∧ IsIntegral ℤ d ∧ ∀ i, IsIntegral ℤ (d * f i) := by
  classical
  have hZ : ∀ x : ℤ, IsIntegral ℤ (x : E) := fun x => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := x))
  have hQ : ∀ i, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * f i) := by
    intro i
    obtain ⟨⟨m, hm⟩, hint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (nonZeroDivisors ℤ) (f i) (Algebra.IsIntegral.isIntegral (R := ℚ) (f i))
    refine ⟨m, nonZeroDivisors.ne_zero hm, ?_⟩
    simpa [Submonoid.smul_def, zsmul_eq_mul] using hint
  choose m hm0 hmi using hQ
  have _ := Fintype.ofFinite ι
  refine ⟨((∏ i, m i : ℤ) : E), ?_, hZ _, ?_⟩
  · exact_mod_cast Finset.prod_ne_zero_iff.2 (fun i _ => hm0 i)
  · intro i
    rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ i)]
    push_cast
    rw [mul_comm ((m i : ℤ) : E), mul_assoc]
    refine IsIntegral.mul ?_ (hmi i)
    exact_mod_cast hZ (∏ j ∈ Finset.univ.erase i, m j)
end Formalism.UG.P
