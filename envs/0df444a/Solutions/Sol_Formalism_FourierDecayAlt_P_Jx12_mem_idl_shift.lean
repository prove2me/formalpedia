-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx12.mem_idl_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:02.657815+00:00
-- url     : https://prove2.me/submissions/8e6f32b1-26f9-47a4-9c4a-7c9a88eaef52

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx12
namespace Formalism.FourierDecayAlt.P.Jx12
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (hg : 0 < g) (k ν : ℤ)
    (y : E) : y ∈ S6.zsub E (S6.idl E g k ν) ↔ (g : E) ^ 2 * y ∈ S6.zsub E (S6.idl E g (k + 2) ν) := by
  have hg0 : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  have key : S6.idl E g (k + 2) ν =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) ((g : E) ^ 2) * S6.idl E g k ν := by
    unfold S6.idl
    rw [zpow_add₀ hg0, ← FractionalIdeal.spanSingleton_mul_spanSingleton, zpow_two, sq]
    ring
  simp only [S6.zsub, Submodule.restrictScalars_mem, FractionalIdeal.mem_coe, key,
    FractionalIdeal.mem_singleton_mul]
  constructor
  · intro hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    rwa [mul_left_cancel₀ (pow_ne_zero 2 hg0) hzy]
end Formalism.FourierDecayAlt.P.Jx12
