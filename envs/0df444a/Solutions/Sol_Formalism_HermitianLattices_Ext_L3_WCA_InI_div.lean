-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WCA.InI.div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:54:18.095201+00:00
-- url     : https://prove2.me/submissions/08f745ed-4ecd-424f-a1a0-f4492d0cbd23

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AkCountEqRedCountMul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_WCA____ne_zero_cf941fa073ca
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_exists_div

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WCA
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}
namespace Formalism.HermitianLattices.Ext.L3.WCA
namespace InI
theorem _root_.solution (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {v : ℕ} (hv : n ∉ 𝔭 ^ (v + 1)) {k : ℕ}
    {a : K} (ha : InI 𝔭 (v + k) a) : InI 𝔭 k ((κ (ι n))⁻¹ * a) := by
  obtain ⟨s, hs, H⟩ := exists_div (K := K) h𝔭 hn hv
  obtain ⟨t, ht, z, hz, e⟩ := ha
  obtain ⟨z', hz', f⟩ := H k z hz
  refine ⟨s * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hs ht, z', hz', ?_⟩
  have hn0 := κι_ne_zero (K := K) hn
  have f' : κ (ι s) * κ z = κ (ι n) * κ z' := by rw [← map_mul, f, map_mul]
  rw [e] at f'
  rw [map_mul, map_mul]
  field_simp
  linear_combination -f'
end InI
end Formalism.HermitianLattices.Ext.L3.WCA
