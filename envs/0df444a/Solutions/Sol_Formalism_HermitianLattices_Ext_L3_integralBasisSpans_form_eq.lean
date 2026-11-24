-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.integralBasisSpans.form_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:00.32425+00:00
-- url     : https://prove2.me/submissions/7ed13708-bcb0-437f-8ba4-447df0183fb4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_coe_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.integralBasisSpans
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.integralBasisSpans
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, algebraMap (𝓞 K) K (H i j) = h (b i) (b j)) (y y' : spanO b) :
    h (y : V) (y' : V) = algebraMap (𝓞 K) K (star (crd b y) ⬝ᵥ (H *ᵥ crd b y')) := by
  rw [coe_eq_sum b y, map_sum, LinearMap.sum_apply, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_eq_sum b y', map_smulₛₗ, LinearMap.smul_apply, map_sum, map_mul, mulVec, dotProduct, map_sum,
    smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, map_mul, hH, mul_comm]
end Formalism.HermitianLattices.Ext.L3.integralBasisSpans
