-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.exists_pow_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:56:18.245906+00:00
-- url     : https://prove2.me/submissions/3d014595-f6b9-439d-9f2d-87b9f648f7a9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsEquivOfMemEndL
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_D2___pow_smul_cc25b347fe94
import Theorems.Thm_Formalism_HermitianLatticesTheory_traceReal_mult
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_mul_dvd
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_algebraMap_intCast_smul
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
theorem _root_.solution {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭) (w : V) :
    ∃ n : ℕ, algebraMap F K (π : F) ^ n • w ∈ locF 𝔭 A₀ := by
  have := h𝔭.isPrime
  obtain ⟨n, hn, hnw⟩ := Formalism.HermitianLatticesTheory.traceReal_mult A₀ hA₀ w
  have hc : ((n : ℤ) : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  obtain ⟨r, u, hu, hdvd⟩ := exists_mul_dvd h𝔭 hc
  obtain ⟨v, hv⟩ := hdvd (π ^ r) (Ideal.pow_mem_pow hπ r)
  refine ⟨r, (LocalSpans.mem_locF 𝔭 _ _).2 ⟨u, hu, ?_⟩⟩
  have : ι u • (algebraMap F K (π : F) ^ r • w) = ι v • (n • w) := by
    rw [← LocF.algebraMap_intCast_smul (K := K) (F := F) n w, smul_smul, ← map_mul, mul_comm v, ← hv, map_mul,
      mul_smul, ι_pow_smul]
  rw [this]
  exact A₀.smul_mem _ hnw
end Formalism.HermitianLattices.Ext.L3.D2
