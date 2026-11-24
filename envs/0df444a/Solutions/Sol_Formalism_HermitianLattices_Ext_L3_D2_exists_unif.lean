-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.exists_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:29:29.488384+00:00
-- url     : https://prove2.me/submissions/7f951c75-5486-475a-8d13-86faccc136a5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif

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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : ∃ π : 𝓞 F, π ∈ 𝔭 ∧ π ∉ 𝔭 ^ 2 := by
  have hbot : 𝔭 ≠ ⊥ := by
    rintro rfl
    exact RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.mpr h𝔭)
  have hlt : 𝔭 ^ 2 < 𝔭 := Ideal.pow_lt_self 𝔭 hbot h𝔭.ne_top 2 le_rfl
  obtain ⟨π, hπ, hπ'⟩ := SetLike.exists_of_lt hlt
  exact ⟨π, hπ, hπ'⟩
end Formalism.HermitianLattices.Ext.L3.D2
