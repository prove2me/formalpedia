-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.form_cmb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:26.383009+00:00
-- url     : https://prove2.me/submissions/28837154-7d30-4c5e-89df-1620b394f631

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeCmbSingle
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLiftBasis
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_coe_cmb
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
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) (c c' : κ → 𝓞 K) :
    h (cmb b c : V) (cmb b c' : V) = jK (star c ⬝ᵥ (H *ᵥ c')) := by
  have hst : ∀ r : 𝓞 K, jK (star r) = star (jK r) := fun r => rfl
  have hl : ∀ (r : 𝓞 K) (v w : V), h (r • v) w = star (jK r) * h v w := fun r v w => by
    rw [← algebraMap_smul K r v, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply]
  have hr : ∀ (r : 𝓞 K) (v w : V), h v (r • w) = jK r * h v w := fun r v w => by
    rw [← algebraMap_smul K r w, map_smul, smul_eq_mul]
  have expand : h (∑ i, c i • b i) (∑ j, c' j • b j) =
      ∑ i, ∑ j, star (jK (c i)) * (jK (c' j) * h (b i) (b j)) := by
    have h1 : ∀ w : V, h (∑ i, c i • b i) w = ∑ i, star (jK (c i)) * h (b i) w := by
      intro w
      rw [map_sum, LinearMap.sum_apply]
      exact Finset.sum_congr rfl fun i _ => hl _ _ _
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hr]
  have rhs : jK (star c ⬝ᵥ (H *ᵥ c')) = ∑ i, ∑ j, star (jK (c i)) * (jK (H i j) * jK (c' j)) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, map_sum, map_mul, hst, Finset.mul_sum]
  rw [coe_cmb, coe_cmb, expand, rhs]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hH]
  ring
end Formalism.HermitianLattices.Ext.L3.HU
