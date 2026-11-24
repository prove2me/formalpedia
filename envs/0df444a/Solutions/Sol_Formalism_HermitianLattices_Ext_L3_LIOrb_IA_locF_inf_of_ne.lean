-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.IA.locF_inf_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:54:53.525961+00:00
-- url     : https://prove2.me/submissions/54b39adb-3139-4045-a31d-a5561529d272

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormDiscrIdealOfLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardEqRelIndex
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_locF_idem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_locF_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_mem_locF_iff


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb Formalism.HermitianLattices.Ext.L3.LIOrb.IA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.LIOrb.IA
theorem _root_.solution {𝔭 𝔮 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (h𝔮 : 𝔮.IsMaximal) (hne : 𝔮 ≠ 𝔭)
    {M N : Submodule (𝓞 K) V} {r : ℕ} (hr : ∀ a ∈ 𝔭 ^ r, ∀ y ∈ M, ι a • y ∈ locF 𝔭 N) :
    locF 𝔮 (M ⊓ locF 𝔭 N) = locF 𝔮 M := by
  apply le_antisymm (LocF.locF_mono 𝔮 inf_le_left)
  have hnle : ¬ 𝔭 ^ r ≤ 𝔮 := fun hle =>
    hne (h𝔭.eq_of_le h𝔮.ne_top (h𝔮.isPrime.le_of_pow_le hle)).symm
  obtain ⟨a, ha, ha𝔮⟩ := SetLike.not_le_iff_exists.mp hnle
  have hM : M ≤ locF 𝔮 (M ⊓ locF 𝔭 N) := by
    intro y hy
    exact (LocF.mem_locF_iff h𝔮.isPrime _ y).2
      ⟨a, ha𝔮, Submodule.mem_inf.2 ⟨M.smul_mem _ hy, hr a ha y hy⟩⟩
  calc locF 𝔮 M ≤ locF 𝔮 (locF 𝔮 (M ⊓ locF 𝔭 N)) := LocF.locF_mono 𝔮 hM
    _ = _ := LocF.locF_idem 𝔮 _
end Formalism.HermitianLattices.Ext.L3.LIOrb.IA
