-- Prove2me | solution 1 for Formalism.UG.P.adelstabL_den
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:01:03.206137+00:00
-- url     : https://prove2.me/submissions/08634db4-e26f-4422-a90b-4a5127760d7c

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
omit [NumberField F] [Algebra F E]
namespace Formalism.UG.P
theorem _root_.solution {κ : Type} [Fintype κ] (f : κ → E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ i, IsIntegral ℤ ((m : E) * f i) := by
  classical
  have h1 : ∀ i, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * f i) := by
    intro i
    obtain ⟨⟨m, hm⟩, hint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (nonZeroDivisors ℤ) (Rₘ := ℚ) (f i) (Algebra.IsIntegral.isIntegral (R := ℚ) (f i))
    refine ⟨m, nonZeroDivisors.ne_zero hm, ?_⟩
    simpa [Submonoid.smul_def, zsmul_eq_mul] using hint
  choose m hm0 hmi using h1
  refine ⟨∏ i, m i, Finset.prod_ne_zero_iff.mpr fun i _ => hm0 i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ i), Int.cast_mul,
    mul_comm ((m i : ℤ) : E), mul_assoc]
  refine IsIntegral.mul ?_ (hmi i)
  simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := ∏ j ∈ Finset.univ.erase i, m j)
end Formalism.UG.P
