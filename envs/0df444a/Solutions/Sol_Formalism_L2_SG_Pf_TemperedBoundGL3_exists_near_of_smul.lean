-- Prove2me | solution 1 for Formalism.L2.SG.Pf.TemperedBoundGL3.exists_near_of_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:15:20.184917+00:00
-- url     : https://prove2.me/submissions/19118b17-745f-4c12-a6be-ddc8e6e9aa64

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SplitAtOf
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DivMemLocRingOfVFEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNearRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsNearOfSmul
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_near_representation
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_IsE_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_int
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_notMem_pow_vF
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_Cell_inI___dc4ac2cc5e49
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.TemperedBoundGL3
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA Formalism.HermitianLattices.Ext.L3.WCA Formalism.HermitianLattices.Ext.L3.Cell
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}
namespace Formalism.L2.SG.Pf.TemperedBoundGL3
theorem _root_.solution (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {n : 𝓞 F} (hn : n ≠ 0) {b : V}
    (hb : h b b = κ (ι n)) {s : 𝓞 F} (hs0 : s ≠ 0) (hsb : ι s • b ∈ A) :
    ∃ v : ℕ, ∀ k : ℕ, 1 ≤ k → ∀ x, InL 𝔭 A 0 x → InI 𝔭 (v + k) (h x x - κ (ι n)) →
      ∃ y, InL 𝔭 A 0 y ∧ h y y = κ (ι n) ∧ InL 𝔭 A k (y - x) := by
  have hp := h𝔭.isPrime
  have hN : 4 * (s * s * n) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero hs0 hs0) hn)
  refine ⟨vF 𝔭 (4 * (s * s * n)), fun k hk x hx hε => ?_⟩
  set v := vF 𝔭 (4 * (s * s * n)) with hv
  by_cases h1 : InI 𝔭 (v + 1) (κ (ι (s * s)) * h (x - b) (x - b))
  · by_cases h2 : InI 𝔭 (v + 1) (κ (ι (s * s)) * h (x - -b) (x - -b))
    · exfalso
      apply localValuationFiltration.notMem_pow_vF h𝔭 hN
      rw [← hv, ← inI_ι (K := K) h𝔭]
      have h3 : InI 𝔭 (v + 1) (κ (ι (2 * (s * s))) * (h x x - κ (ι n))) := by
        have := InI.mul hp (InI.int hp (ι (2 * (s * s)))) (hε.mono (by omega : v + 1 ≤ v + k))
        rwa [zero_add] at this
      have e : κ (ι (4 * (s * s * n))) = κ (ι (s * s)) * h (x - b) (x - b) +
          κ (ι (s * s)) * h (x - -b) (x - -b) - κ (ι (2 * (s * s))) * (h x x - κ (ι n)) := by
        simp only [map_sub, map_neg, LinearMap.sub_apply, LinearMap.neg_apply, hb, map_mul, map_ofNat]
        ring
      rw [e]
      exact (h1.add hp h2).sub hp h3
    · exact exists_near_representation h𝔭 hF hs hA (b := -b) (by simpa using hb)
        (by rw [smul_neg]; exact A.neg_mem hsb) hx hε h2
  · exact exists_near_representation h𝔭 hF hs hA hb hsb hx hε h1
end Formalism.L2.SG.Pf.TemperedBoundGL3
