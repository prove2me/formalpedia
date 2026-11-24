-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.pK_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:29:44.394741+00:00
-- url     : https://prove2.me/submissions/1a8eece8-6815-4846-b68d-7362036c0e0d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_locF_mono


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
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) {i j : ℕ} (hij : i ≤ j) : pK K 𝔭 j ≤ pK K 𝔭 i :=
  LocF.locF_mono 𝔭 (Submodule.map_mono (Ideal.pow_le_pow_right hij))
end Formalism.HermitianLattices.Ext.L3.D2
