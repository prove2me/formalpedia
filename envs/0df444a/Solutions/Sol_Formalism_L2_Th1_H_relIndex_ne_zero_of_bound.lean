-- Prove2me | solution 1 for Formalism.L2.Th1.H.relIndex_ne_zero_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:33:56.269987+00:00
-- url     : https://prove2.me/submissions/28dff405-f9d8-43c5-b36f-ade6020d27ab

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CommensurableK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RatFourSquares
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexNeZeroOfNsmulMem
import Theorems.Thm_Formalism_L2_Th1_H_relIndex_ne_zero_of_nsmul_mem
import Theorems.Thm_Formalism_L2_Th1_H_nsmulHom_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type*} [AddCommGroup V]
namespace Formalism.L2.Th1.H
theorem _root_.solution [Module ℂ V] (H K F : AddSubgroup V) [Module.Finite ℤ F] (N M : ℕ)
    (hN : 0 < N) (hM : 0 < M) (hK : ∀ x ∈ K, N • x ∈ F) (hH : ∀ x ∈ F, M • x ∈ H) : H.relIndex K ≠ 0 := by
  let g : K →+ F :=
    { toFun := fun x => ⟨N • (x : V), hK x x.2⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp [smul_add]) }
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply nsmulHom_injective (V := V) N hN
    exact congrArg Subtype.val hxy
  haveI : Module.Finite ℤ K := Module.Finite.of_injective g.toIntLinearMap hg
  refine relIndex_ne_zero_of_nsmul_mem H K (M * N) (Nat.mul_pos hM hN) ?_
  intro x hx
  rw [mul_smul]
  exact hH _ (hK x hx)
end Formalism.L2.Th1.H
