-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WCA.InL.div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:00:51.836118+00:00
-- url     : https://prove2.me/submissions/bb29a5e1-2d1b-4f0d-83a9-c4bed573f0ac

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AkCountEqRedCountMul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_WCA____ne_zero_cf941fa073ca
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_exists_div
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_exists_div_smul

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
namespace InL
theorem _root_.solution (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {v : ℕ} (hv : n ∉ 𝔭 ^ (v + 1)) {k : ℕ}
    {w : V} (hw : InL 𝔭 A (v + k) w) : InL 𝔭 A k ((κ (ι n))⁻¹ • w) := by
  obtain ⟨s, hs, H⟩ := exists_div (K := K) h𝔭 hn hv
  obtain ⟨t, ht, e⟩ := hw
  obtain ⟨p', hp', f⟩ := exists_div_smul (H k) e
  refine ⟨s * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hs ht, ?_⟩
  have hn0 := κι_ne_zero (K := K) hn
  have : ι (s * t) • (κ (ι n))⁻¹ • w = p' := by
    have h1 : ι (s * t) • (κ (ι n))⁻¹ • w = (κ (ι n))⁻¹ • (ι s • ι t • w) := by
      rw [map_mul, mul_smul, smul_comm (ι t), smul_comm (ι s)]
    rw [h1, f, ← algebraMap_smul K (ι n), smul_smul, inv_mul_cancel₀ hn0, one_smul]
  rw [this]
  exact hp'
end InL
end Formalism.HermitianLattices.Ext.L3.WCA
