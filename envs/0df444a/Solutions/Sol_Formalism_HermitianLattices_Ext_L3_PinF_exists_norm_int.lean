-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinF.exists_norm_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:13:43.516637+00:00
-- url     : https://prove2.me/submissions/d8fe53ff-988e-4913-b0d1-7870921ac655

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeVdLeOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySeventh
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsExactLift
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_algebraMap_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_form_self_star
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_algebraMap_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_eq_iff_mem_range


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinF
open idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
omit [FiniteDimensional K V]
namespace Formalism.HermitianLattices.Ext.L3.PinF
theorem _root_.solution (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {y : V} (hy : y ∈ L) :
    ∃ a : 𝓞 F, h y y = algebraMap (𝓞 K) K (ι a) := by
  obtain ⟨z, hz⟩ := (Submodule.mem_one).1 (hLi y hy y hy)
  have hzc : conjO K z = z := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [WA.algebraMap_conjO, hz, Cell.form_self_star hs y]
  obtain ⟨a, ha⟩ := (conjO_eq_iff_mem_range hF z).1 hzc
  exact ⟨a, by rw [ha, hz]⟩
end Formalism.HermitianLattices.Ext.L3.PinF
