-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WCA.InL.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:41:23.820857+00:00
-- url     : https://prove2.me/submissions/176bc1ae-bcf5-403e-bda9-75a7d072591a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AkCountEqRedCountMul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_neg
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_neg
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_neg


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
    InL 𝔭 A k (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add hp hb.neg
end InL
end Formalism.HermitianLattices.Ext.L3.WCA
