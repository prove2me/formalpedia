-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.denominator_norm_fraction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:07.705484+00:00
-- url     : https://prove2.me/submissions/432770ca-cd28-42c1-bfb2-a5e7906645ff

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductPlacesInequalitySq
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LocalIntegralStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure nonZeroDivisors
set_option linter.all false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : DenomNormFrac := by
  intro E _ _ α J hα hJ hint
  have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ α * J ≤ 1 := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    rw [FractionalIdeal.mem_spanSingleton] at hi
    obtain ⟨z, rfl⟩ := hi
    obtain ⟨w, hw⟩ := hint j hj
    rw [FractionalIdeal.mem_one_iff]
    refine ⟨z * w, ?_⟩
    rw [map_mul, Algebra.smul_def, mul_assoc]
    congr 1
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hne : FractionalIdeal.spanSingleton (𝓞 E)⁰ α * J ≠ 0 :=
    mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hα) hJ
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    apply hne
    rw [← hI]
    simp
  have hn : FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 E)⁰ α) =
      |Algebra.norm ℚ α| := by
    first
      | exact FractionalIdeal.absNorm_span_singleton (𝓞 E) α
      | exact FractionalIdeal.absNorm_span_singleton α
      | simp [FractionalIdeal.absNorm_span_singleton]
  have hc : FractionalIdeal.absNorm ((I : FractionalIdeal (𝓞 E)⁰ E)) = (Ideal.absNorm I : ℚ) := by
    first
      | exact FractionalIdeal.coeIdeal_absNorm I
      | simp [FractionalIdeal.coeIdeal_absNorm]
      | simp
  have key : |Algebra.norm ℚ α| * FractionalIdeal.absNorm J = (Ideal.absNorm I : ℚ) := by
    rw [← hn, ← map_mul, ← hI, hc]
  rw [key]
  have h0 : Ideal.absNorm I ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  exact_mod_cast Nat.one_le_iff_ne_zero.2 h0
end Formalism.HermitianLatticeCounting.P
