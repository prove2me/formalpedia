-- Prove2me | solution 1 for Formalism.L2.SG.Pf.fibreCountingData.h_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:35:00.620855+00:00
-- url     : https://prove2.me/submissions/281005db-1f00-468d-90f8-85aef40e27ed

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CondZIff
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_FibreCountingDataBis
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_G2_jK___ne_zero_6beb2ceebc99


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.fibreCountingData
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}
variable (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0)
  (hdiag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) (ha : ∀ i, a i ≠ 0)
include horth hdiag ha
namespace Formalism.L2.SG.Pf.fibreCountingData
theorem _root_.solution (x : V) (k : Fin m) : h (b k) x = jK (ι (a k)) * crd h b a x k := by
  unfold crd
  rw [mul_div_assoc', eq_div_iff (jK_ι_ne_zero (K := K) (ha k)), mul_comm]
end Formalism.L2.SG.Pf.fibreCountingData
