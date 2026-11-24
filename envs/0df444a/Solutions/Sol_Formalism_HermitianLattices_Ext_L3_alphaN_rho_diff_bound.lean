-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.alphaN_rho_diff_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:29:30.922975+00:00
-- url     : https://prove2.me/submissions/4c77a52a-b5ee-49f5-b337-940e825195d5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldFurther
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlphaNOfVdZeroUnit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_abs_x_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_alphaN_closed
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_beta_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_one_lt_q


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
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) {n n' : 𝓞 F} (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hvv : vF 𝔭 n = vF 𝔭 n' + 1) :
    |alphaN h L 𝔭 n / (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) - alphaN h L 𝔭 n' / (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ)))| ≤
      8 * ((vF 𝔭 n : ℝ) + 1) ^ 2 *
        (Ideal.absNorm 𝔭 : ℝ) ^ (-(((finrank K V - 1) * ((vF 𝔭 n + 1) / 2) : ℕ) : ℤ)) := by
  have hq : (1 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := unitaryAbsoluteValueBounds.one_lt_q h𝔭
  rw [unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd hL hLi h𝔭 hv (by omega) _ n hn rfl,
    unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd hL hLi h𝔭 hv (by omega) _ n' hn' rfl,
    mul_div_cancel_left₀ _ (unitaryAbsoluteValueBounds.beta_pos h𝔭 (by omega)).ne',
    mul_div_cancel_left₀ _ (unitaryAbsoluteValueBounds.beta_pos h𝔭 (by omega)).ne', hvv,
    Finset.sum_range_succ _ (vF 𝔭 n' + 1), add_sub_cancel_left, abs_pow, unitaryAbsoluteValueBounds.abs_x_eq, zpow_neg,
    zpow_natCast, inv_pow, ← pow_mul]
  have h1 : ((Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * (vF 𝔭 n' + 1)))⁻¹ ≤
      ((Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * ((vF 𝔭 n' + 1 + 1) / 2)))⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hq.le (Nat.mul_le_mul_left _ (by omega)))
  have h2 : (0 : ℝ) ≤ ((Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * ((vF 𝔭 n' + 1 + 1) / 2)))⁻¹ := by
    positivity
  have h3 : (1 : ℝ) ≤ 8 * (((vF 𝔭 n' + 1 : ℕ) : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ ((vF 𝔭 n' + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  calc _ ≤ _ := h1
    _ = 1 * _ := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right h3 h2
end Formalism.HermitianLattices.Ext.L3
