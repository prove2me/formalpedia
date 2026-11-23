-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.hj_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:12.031794+00:00
-- url     : https://prove2.me/submissions/ec8b91f0-dbb9-4afa-93e0-9bbda3dafb36

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]
omit [StarRing E]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (h2 : Module.finrank F E = 2) (ω : E) (hω : ∀ c : F, algebraMap F E c ≠ ω) :
    ∃ β : Module.Basis (Fin 2) F E, β 0 = 1 ∧ β 1 = ω := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [h2]; norm_num)
  have hli : LinearIndependent F ![(1 : E), ω] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hω (-s / t)
      have h1 : algebraMap F E t * ω = - algebraMap F E s := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        linear_combination hst
      have h3 : algebraMap F E t * algebraMap F E t⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ ht, map_one]
      rw [div_eq_mul_inv, map_mul, map_neg]
      linear_combination (-(algebraMap F E t⁻¹)) * h1 + ω * h3
    refine ⟨?_, ht⟩
    rw [ht, zero_smul, add_zero, Algebra.smul_def, mul_one] at hst
    exact (map_eq_zero_iff _ (algebraMap F E).injective).1 hst
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [h2]; rfl), ?_, ?_⟩ <;> simp
end Formalism.HermitianLatticeCounting.P.S4aux
