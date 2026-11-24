-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WCA.InL.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:28:15.740796+00:00
-- url     : https://prove2.me/submissions/6349d73a-1c31-4ebd-a164-3dd08b874c8d

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
theorem _root_.solution (hp : 𝔭.IsPrime) {k : ℕ} {a b : V} (ha : InL 𝔭 A k a) (hb : InL 𝔭 A k b) :
    InL 𝔭 A k (a + b) := by
  obtain ⟨t, ht, e⟩ := ha
  obtain ⟨u, hu, f⟩ := hb
  refine ⟨t * u, fun h => (hp.mem_or_mem h).elim ht hu, ?_⟩
  rw [smul_add, map_mul]
  refine add_mem ?_ ?_
  · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ e
  · rw [mul_smul]; exact Submodule.smul_mem _ _ f
end InL
end Formalism.HermitianLattices.Ext.L3.WCA
