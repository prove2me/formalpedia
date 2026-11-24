-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WCA.InI.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:27:13.527744+00:00
-- url     : https://prove2.me/submissions/d177d32d-24c4-4de5-9aaa-3b1942540941

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AkCountEqRedCountMul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



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
theorem _root_.solution (hp : 𝔭.IsPrime) {k : ℕ} {a b : K} (ha : InI 𝔭 k a) (hb : InI 𝔭 k b) :
    InI 𝔭 k (a + b) := by
  obtain ⟨t, ht, z, hz, e⟩ := ha
  obtain ⟨u, hu, y, hy, f⟩ := hb
  refine ⟨t * u, fun h => (hp.mem_or_mem h).elim ht hu, ι u * z + ι t * y,
    add_mem (Ideal.mul_mem_left _ _ hz) (Ideal.mul_mem_left _ _ hy), ?_⟩
  simp only [map_add, map_mul, e, f]
  ring
end InI
end Formalism.HermitianLattices.Ext.L3.WCA
