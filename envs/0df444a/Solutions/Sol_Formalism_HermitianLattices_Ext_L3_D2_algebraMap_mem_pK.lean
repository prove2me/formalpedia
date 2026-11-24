-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.algebraMap_mem_pK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:44:54.690903+00:00
-- url     : https://prove2.me/submissions/cbea8de1-6661-4c52-a1a1-815e2716da05

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_D2_algebraMap_mem_pK__28aaf4c3f0e6

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
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) (z : 𝓞 K) : algebraMap (𝓞 K) K z ∈ pK K 𝔭 0 :=
  algebraMap_mem_pK' 𝔭 (by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)
end Formalism.HermitianLattices.Ext.L3.D2
