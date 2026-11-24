-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.mem_pK_zero_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:50:23.057954+00:00
-- url     : https://prove2.me/submissions/b2c7691a-7348-4623-9637-152b3eb4d178

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK


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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ∉ 𝔭) {x : K}
    {z : 𝓞 K} (e : algebraMap (𝓞 K) K z = algebraMap (𝓞 K) K (ι t) * x) : x ∈ pK K 𝔭 0 :=
  (mem_pK h𝔭).2 ⟨t, ht, z, by rw [pow_zero, Ideal.one_eq_top]; trivial, e⟩
end Formalism.HermitianLattices.Ext.L3.D2
