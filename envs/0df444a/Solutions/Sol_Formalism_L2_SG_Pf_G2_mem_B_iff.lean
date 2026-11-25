-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G2.mem_B_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:24:30.655569+00:00
-- url     : https://prove2.me/submissions/54d1d39d-dbae-4384-b81c-7a4829de096b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CardQuotSmulTopCongr
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LocFLeSpanK
import Theorems.Thm_Formalism_L2_SG_Pf_G2_smul_eq_jK
import Theorems.Thm_Formalism_L2_SG_Pf_G2_h_sum
import Theorems.Thm_Formalism_L2_SG_Pf_G2_locF_le_spanK
import Theorems.Thm_Formalism_L2_SG_Pf_G2_coords
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mem_SP_iff_locF

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
theorem _root_.solution (h𝔭 : 𝔭.IsPrime) (hL : IsLatIn X L) (x : V) :
    x ∈ locF 𝔭 L ↔ x ∈ X ∧ ∀ i, h (b i) x / jK (ι (a i)) ∈ HU.SP K 𝔭 := by
  haveI := h𝔭
  have hdiag' : ∀ i, h (b i) (b i) = jK (ι (a i)) := fun i => by
    rw [hdiag i]; exact (coe_iota_eq_algebraMap_coe (a i)).symm
  have key : ∀ w ∈ Submodule.span (𝓞 K) (Set.range b), ∀ i,
      h (b i) w / jK (ι (a i)) ∈ (1 : Submodule (𝓞 K) K) := by
    intro w hw i
    obtain ⟨z, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hw
    have e : (∑ j, z j • b j) = ∑ j, jK (z j) • b j :=
      Finset.sum_congr rfl fun j _ => smul_eq_jK _ _
    rw [e, h_sum horth hdiag' _ i, mul_div_cancel_right₀ _ (jK_iota_ne_zero (ha i))]
    exact Submodule.mem_one.mpr ⟨z i, rfl⟩
  rw [← hloc]
  constructor
  · intro hx
    have hxs := locF_le_spanK h𝔭 hx
    obtain ⟨s, hs, hsx⟩ := hx
    refine ⟨Submodule.span_le.mpr ?_ hxs, fun i => ?_⟩
    · rintro _ ⟨j, rfl⟩
      exact hbX j
    · rw [HU.mem_SP_iff_locF]
      refine Exists.intro s ⟨hs, ?_⟩
      have e : s • (h (b i) x / jK (ι (a i))) = h (b i) (s • x) / jK (ι (a i)) := by
        rw [smul_eq_jK s x, map_smul, smul_eq_mul, Algebra.smul_def, mul_div_assoc]
      rw [e]
      exact key _ hsx i
  · rintro ⟨hxX, hc⟩
    rw [coords hbX hloc horth hdiag ha h𝔭 hL hxX]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨s, hs, hsc⟩ := (HU.mem_SP_iff_locF).mp (hc i)
    obtain ⟨y, hy⟩ := Submodule.mem_one.mp hsc
    refine Exists.intro s ⟨hs, ?_⟩
    rw [← smul_assoc, ← hy, ← smul_eq_jK]
    exact Submodule.smul_mem _ y (Submodule.subset_span ⟨i, rfl⟩)
end Formalism.L2.SG.Pf.G2
