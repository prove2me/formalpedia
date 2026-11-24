-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.abs_x_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:00:51.817403+00:00
-- url     : https://prove2.me/submissions/d5b12c54-0fe3-4581-95a3-e85df2f960b9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldFurther
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlphaNOfVdZeroUnit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_abs_x_eq

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {m : ℕ} (hm : 2 ≤ m) :
    |etaF K F 𝔭 ^ m * ((Ideal.absNorm 𝔭 : ℝ) ^ (m - 1))⁻¹| ≤ 1 / 2 := by
  rw [abs_x_eq]
  have h1 : Ideal.absNorm 𝔭 ≠ 1 := fun h => h𝔭.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have h0 : Ideal.absNorm 𝔭 ≠ 0 := fun h =>
    (Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F))
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hN : (2 : ℝ) ≤ Ideal.absNorm 𝔭 := by
    have : 2 ≤ Ideal.absNorm 𝔭 := by omega
    exact_mod_cast this
  have hp : (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ) ^ (m - 1) :=
    le_trans hN (le_self_pow₀ (by linarith) (by omega))
  calc ((Ideal.absNorm 𝔭 : ℝ) ^ (m - 1))⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp
    _ = 1 / 2 := by norm_num
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
