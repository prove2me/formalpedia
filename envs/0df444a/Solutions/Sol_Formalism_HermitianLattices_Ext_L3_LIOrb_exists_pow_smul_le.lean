-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.exists_pow_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:41:23.583389+00:00
-- url     : https://prove2.me/submissions/d4956c72-f013-4c03-8d6b-731094aa6bd3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmulOfMemAutSub
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_mul_dvd
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_algebraMap_intCast_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_exists_zsmul_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_mem_locF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsLattice K M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ r : ℕ, ((extP K 𝔭) ^ r • locF 𝔭 M₁ : Submodule (𝓞 K) V) ≤ locF 𝔭 M₂ := by
  have := h𝔭.isPrime
  obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hM₁ hM₂
  have hc : ((n : ℤ) : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  obtain ⟨r, u, hu, hdvd⟩ := D2.exists_mul_dvd h𝔭 hc
  refine ⟨r, ?_⟩
  have key : extP K 𝔭 ^ r ≤ (locF 𝔭 M₂).colon (locF 𝔭 M₁ : Set V) := by
    unfold extP
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Submodule.mem_colon]
    intro x hx
    obtain ⟨s, hs, hsx⟩ := (LocalSpans.mem_locF 𝔭 M₁ x).1 hx
    obtain ⟨d, hd⟩ := hdvd a ha
    refine (LocalSpans.mem_locF 𝔭 M₂ _).2
      ⟨u * s, fun h => (h𝔭.isPrime.mem_or_mem h).elim hu hs, ?_⟩
    have e : algebraMap (𝓞 F) (𝓞 K) (u * s) • algebraMap (𝓞 F) (𝓞 K) a • x =
        algebraMap (𝓞 F) (𝓞 K) d • (n • (algebraMap (𝓞 F) (𝓞 K) s • x)) := by
      rw [← LocF.algebraMap_intCast_smul (F := F) (K := K) n]
      simp only [smul_smul, ← map_mul]
      congr 2
      linear_combination s * hd
    rw [e]
    exact M₂.smul_mem _ (hnx _ hsx)
  rw [Submodule.smul_le]
  intro a ha x hx
  exact Submodule.mem_colon.1 (key ha) x hx
end Formalism.HermitianLattices.Ext.L3.LIOrb
