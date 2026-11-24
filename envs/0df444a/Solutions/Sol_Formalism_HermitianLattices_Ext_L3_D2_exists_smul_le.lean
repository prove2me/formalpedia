-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.exists_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:14:46.130478+00:00
-- url     : https://prove2.me/submissions/227e4364-1854-4653-962e-f6f19a42c56a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsEquivOfMemEndL
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_D2___pow_smul_cc25b347fe94
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_mul_dvd
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_smul_iff_unif
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
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {A₀ B₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ r : ℕ, extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀ := by
  have := h𝔭.isPrime
  obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hA₀ hB₀
  have hc : ((n : ℤ) : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  obtain ⟨r, u, hu, hdvd⟩ := exists_mul_dvd h𝔭 hc
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  obtain ⟨v, hv⟩ := hdvd (π ^ r) (Ideal.pow_mem_pow hπ r)
  refine ⟨r, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hx
  obtain ⟨t, ht, hty⟩ := (LocalSpans.mem_locF 𝔭 A₀ y).1 hy
  refine (LocalSpans.mem_locF 𝔭 _ _).2 ⟨u * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hu ht, ?_⟩
  have : ι (u * t) • (algebraMap F K (π : F) ^ r • y) = ι v • (n • (ι t • y)) := by
    rw [← LocF.algebraMap_intCast_smul (K := K) (F := F) n, ← ι_pow_smul, smul_smul, smul_smul, smul_smul,
      ← map_mul, ← map_mul, ← map_mul]
    congr 2
    linear_combination t * hv
  rw [this]
  exact B₀.smul_mem _ (hnx _ hty)
end Formalism.HermitianLattices.Ext.L3.D2
