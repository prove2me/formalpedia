-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.star_mem_pK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:31:37.861404+00:00
-- url     : https://prove2.me/submissions/f8f53142-18f9-4888-b615-49719f533908

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_star_algebraMap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_conjO_mem_pow


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
theorem _root_.solution (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {a : K}
    (ha : a ∈ pK K 𝔭 k) : star a ∈ pK K 𝔭 k := by
  obtain ⟨t, ht, z, hz, e⟩ := (mem_pK h𝔭).1 ha
  refine (mem_pK h𝔭).2 ⟨t, ht, conjO K z, idealPowerSpanBounds.conjO_mem_pow hF 𝔭 k z hz, ?_⟩
  have : algebraMap (𝓞 K) K (conjO K z) = star (algebraMap (𝓞 K) K z) := rfl
  rw [this, e, star_mul', MeanB.star_algebraMap hF]
end Formalism.HermitianLattices.Ext.L3.D2
