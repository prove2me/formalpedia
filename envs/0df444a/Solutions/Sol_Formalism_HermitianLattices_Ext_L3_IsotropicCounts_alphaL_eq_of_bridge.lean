-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.IsotropicCounts.alphaL_eq_of_bridge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:37:53.174752+00:00
-- url     : https://prove2.me/submissions/853b0b62-c1c8-4de0-a3f8-fd45cebf9797

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsoCountOneInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SupEqTopOfMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlphaLEqOfBridge
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IsotropicCounts_isoCount_diag


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IsotropicCounts
open Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.IsotropicCounts
theorem _root_.solution [hFF : Fact (IsFixF K F)] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (u : Fin (finrank K V) → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤)
    (hbr : ∀ k, akCount h L 𝔭 k = isoCount 𝔭 k (diagonal u)) :
    alphaL h L 𝔭 = alphaStd K 𝔭 (finrank K V) := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    have : Ideal.absNorm 𝔭 ≠ 0 := fun h =>
      (Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F))
        (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast this
  unfold alphaL
  apply Filter.Tendsto.limUnder_eq
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [hbr, isoCount_diag hK h𝔭 u hu hunit j, eq_div_iff (pow_ne_zero _ hN)]
  ring
end Formalism.HermitianLattices.Ext.L3.IsotropicCounts
