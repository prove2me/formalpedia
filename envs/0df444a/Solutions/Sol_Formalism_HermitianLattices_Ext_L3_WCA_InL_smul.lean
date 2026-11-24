-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WCA.InL.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:27:41.373807+00:00
-- url     : https://prove2.me/submissions/79a3b599-9ee0-4817-9b58-e0012a224145

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AkCountEqRedCountMul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff

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
theorem _root_.solution (hp : 𝔭.IsPrime) {i k : ℕ} {a : K} {v : V} (ha : InI 𝔭 i a) (hv : InL 𝔭 A k v) :
    InL 𝔭 A (i + k) (a • v) := by
  obtain ⟨t, ht, z, hz, e⟩ := ha
  obtain ⟨u, hu, f⟩ := hv
  refine ⟨t * u, fun h => (hp.mem_or_mem h).elim ht hu, ?_⟩
  have : ι (t * u) • a • v = z • (ι u • v) := by
    rw [← algebraMap_smul K (ι (t * u)), ← algebraMap_smul K z, ← algebraMap_smul K (ι u), smul_smul,
      smul_smul, e, map_mul, map_mul]
    congr 1
    ring
  rw [this, pow_add, Submodule.mul_smul]
  exact Submodule.smul_mem_smul hz f
end InL
end Formalism.HermitianLattices.Ext.L3.WCA
