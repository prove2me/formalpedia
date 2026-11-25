-- Prove2me | solution 1 for Formalism.L2.Th1.H.relIndex_ne_zero_of_nsmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:04:50.065013+00:00
-- url     : https://prove2.me/submissions/cacc0d6a-42f8-4281-8846-977c0d6fe419

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CommensurableK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RatFourSquares
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexNeZeroOfNsmulMem

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
theorem _root_.solution (H F : AddSubgroup V) [Module.Finite ℤ F] (N : ℕ) (hN : 0 < N)
    (h : ∀ x ∈ F, N • x ∈ H) : H.relIndex F ≠ 0 := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨k, φ, hφ⟩ := Module.Finite.exists_fin' ℤ F
  let ψ : (Fin k → ℤ) →+ (Fin k → ZMod N) := AddMonoidHom.compLeft (Int.castAddHom (ZMod N)) (Fin k)
  have hle : ψ.ker ≤ (H.addSubgroupOf F).comap φ.toAddMonoidHom := by
    intro x hx
    have hx' := (AddMonoidHom.mem_ker).1 hx
    have hdiv : ∀ i, (N : ℤ) ∣ x i := by
      intro i
      have hi := congrFun hx' i
      simpa [ψ, AddMonoidHom.compLeft, ZMod.intCast_zmod_eq_zero_iff_dvd] using hi
    choose y hy using hdiv
    have hxy : x = (N : ℤ) • y := by
      funext i
      simp [hy i]
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, hxy]
    have hφy : φ.toAddMonoidHom ((N : ℤ) • y) = N • φ y := by
      rw [LinearMap.toAddMonoidHom_coe, map_zsmul, natCast_zsmul]
    rw [hφy, AddSubgroup.coe_nsmul]
    exact h _ (φ y).2
  have h1 : ψ.ker.index ≠ 0 := by
    haveI : Finite ((Fin k → ℤ) ⧸ ψ.ker) :=
      Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange ψ).symm.toEquiv
    exact AddSubgroup.index_ne_zero_of_finite
  have h2 : ((H.addSubgroupOf F).comap φ.toAddMonoidHom).index ≠ 0 :=
    ne_zero_of_dvd_ne_zero h1 (AddSubgroup.index_dvd_of_le hle)
  rw [AddSubgroup.index_comap_of_surjective _ hφ] at h2
  exact h2
end Formalism.L2.Th1.H
