-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G2.coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:07:09.348217+00:00
-- url     : https://prove2.me/submissions/12cf17fc-97ee-499f-975b-1bf77073246e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CardQuotSmulTopCongr
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LocFLeSpanK
import Theorems.Thm_Formalism_L2_SG_Pf_G2_h_sum
import Theorems.Thm_Formalism_L2_SG_Pf_G2_locF_le_spanK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_le_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalizedFibreSets_le_locF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Module
noncomputable section
namespace Formalism.L2.SG.Pf.G2
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
private theorem coe_iota_eq_algebraMap_coe (a : 𝓞 F) : jK (ι a) = algebraMap F K (a : F) := by
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]
private theorem jK_iota_ne_zero {a : 𝓞 F} (ha : a ≠ 0) : jK (ι a) ≠ 0 := by
  rw [coe_iota_eq_algebraMap_coe]
  refine (map_ne_zero (algebraMap F K)).mpr ?_
  exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr ha
section
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
  {n : ℕ} {b : Fin n → V} {a : Fin n → 𝓞 F}
variable (hbX : ∀ i, b i ∈ X) (hloc : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L)
  (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0)
  (hdiag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) (ha : ∀ i, a i ≠ 0)
include hbX hloc horth hdiag ha
end
end Formalism.L2.SG.Pf.G2
end
end

set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G2
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
  {n : ℕ} {b : Fin n → V} {a : Fin n → 𝓞 F}
variable (hbX : ∀ i, b i ∈ X) (hloc : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L)
  (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0)
  (hdiag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) (ha : ∀ i, a i ≠ 0)
include hbX hloc horth hdiag ha
namespace Formalism.L2.SG.Pf.G2
theorem _root_.solution (h𝔭 : 𝔭.IsPrime) (hL : IsLatIn X L) {x : V} (hx : x ∈ X) :
    x = ∑ i, (h (b i) x / jK (ι (a i))) • b i := by
  have hxs : x ∈ Submodule.span K (Set.range b) := by
    rw [← hL.2] at hx
    refine (Submodule.span_le.mpr ?_) hx
    intro y hy
    haveI := h𝔭
    have h1 : y ∈ locF 𝔭 L := Formalism.HermitianLattices.Ext.L3.localizedQuotients.le_locF 𝔭 L hy
    rw [← hloc] at h1
    exact locF_le_spanK h𝔭 h1
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hxs
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h_sum horth (fun j => by rw [hdiag j]; exact (coe_iota_eq_algebraMap_coe (a j)).symm) c i,
    mul_div_cancel_right₀ _ (jK_iota_ne_zero (ha i))]
end Formalism.L2.SG.Pf.G2
