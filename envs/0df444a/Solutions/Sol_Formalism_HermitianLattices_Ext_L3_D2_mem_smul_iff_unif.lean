-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.mem_smul_iff_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:10:30.829807+00:00
-- url     : https://prove2.me/submissions/43938739-e6b5-47f8-9452-db2ee081ec3f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_D2_algebraMap_mem_pK__28aaf4c3f0e6
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_notMem_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK_iff_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_inv_smul_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_algebraMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭)
    (hπ' : π ∉ 𝔭 ^ 2) (A₀ : Submodule (𝓞 K) V) {k : ℕ} {x : V} :
    x ∈ extP K 𝔭 ^ k • locF 𝔭 A₀ ↔ ∃ y ∈ locF 𝔭 A₀, x = algebraMap F K (π : F) ^ k • y := by
  constructor
  · intro hx
    induction hx using Submodule.smul_induction_on' with
    | smul z hz y hy =>
      obtain ⟨b, hb, e⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 (algebraMap_mem_pK' (K := K) 𝔭 hz)
      obtain ⟨t, ht, w, -, e'⟩ := (mem_pK h𝔭).1 hb
      refine ⟨(algebraMap F K (t : F))⁻¹ • (w • y), inv_smul_mem h𝔭 A₀ ht ((locF 𝔭 A₀).smul_mem w hy), ?_⟩
      rw [← algebraMap_smul K z, ← algebraMap_smul K w, e, e', smul_smul, smul_smul]
      congr 1
      have := notMem_ne_zero (K := K) ht
      field_simp
    | add x _ y _ hx hy =>
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨x' + y', (locF 𝔭 A₀).add_mem hx' hy', (smul_add _ _ _).symm⟩
  · rintro ⟨y, hy, rfl⟩
    have := Submodule.smul_mem_smul (localizedQuotients.ι_mem_pow (K := K) (Ideal.pow_mem_pow hπ k)) hy
    rwa [← algebraMap_smul K (ι (π ^ k)), MeanB.algebraMap_comp,
      show ((π ^ k : 𝓞 F) : F) = (π : F) ^ k from rfl, map_pow] at this
end Formalism.HermitianLattices.Ext.L3.D2
