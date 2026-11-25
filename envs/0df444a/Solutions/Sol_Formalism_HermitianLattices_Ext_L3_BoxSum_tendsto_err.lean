-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxSum.tendsto_err
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:58:21.70918+00:00
-- url     : https://prove2.me/submissions/cccee88a-7642-414b-a29b-6dab882f324e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeBotOfIsMaximal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumOfMean
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
open NumberField Module Filter Topology
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
theorem _root_.solution (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (A B : ℝ)
    (c : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → ℕ) :
    Tendsto (fun k : ℕ => A * ∑ 𝔭 ∈ S, B / (Ideal.absNorm 𝔭.1 : ℝ) ^ (k + 1 - c 𝔭)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun k : ℕ => ∑ 𝔭 ∈ S, B / (Ideal.absNorm 𝔭.1 : ℝ) ^ (k + 1 - c 𝔭)) atTop
      (𝓝 (∑ 𝔭 ∈ S, (0 : ℝ))) := by
    refine tendsto_finset_sum _ fun 𝔭 _ => ?_
    have hne : 𝔭.1 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField 𝔭.2 (NumberField.RingOfIntegers.not_isField F)
    have h1 : Ideal.absNorm 𝔭.1 ≠ 1 := fun h => 𝔭.2.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have h2 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h => hne (Ideal.absNorm_eq_zero_iff.1 h)
    have hgt : (1 : ℝ) < Ideal.absNorm 𝔭.1 := by
      have : 1 < Ideal.absNorm 𝔭.1 := by omega
      exact_mod_cast this
    refine tendsto_const_nhds.div_atTop ?_
    exact (tendsto_pow_atTop_atTop_of_one_lt hgt).comp
      ((tendsto_sub_atTop_nat (c 𝔭)).comp (tendsto_add_atTop_nat 1))
  simpa using h0.const_mul A
end Formalism.HermitianLattices.Ext.L3.BoxSum
