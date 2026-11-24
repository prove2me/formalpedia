-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.form_repr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:30.882578+00:00
-- url     : https://prove2.me/submissions/f1b1151b-0f04-4362-a230-ac9431f91191

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeZeroOfNotMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EquivFunEquivOfMatrixSymm
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) (x y : V) :
    h x y = star (b.equivFun x) ⬝ᵥ (gramK h b *ᵥ b.equivFun y) := by
  calc h x y = h (∑ i, b.equivFun x i • b i) (∑ j, b.equivFun y j • b j) := by
        rw [b.sum_equivFun x, b.sum_equivFun y]
    _ = ∑ i, ∑ j, star (b.equivFun x i) * (b.equivFun y j * h (b i) (b j)) := by
        simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply,
          smul_eq_mul, starRingEnd_apply, RingHom.id_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = _ := by
        simp only [dotProduct, mulVec, Pi.star_apply, gramK, Matrix.of_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end Formalism.HermitianLattices.Ext.L3.HU
