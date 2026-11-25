-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.roL_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:17:30.014012+00:00
-- url     : https://prove2.me/submissions/600b7e0d-9085-4665-b386-a0a290c4d50c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormLeOfMemBoxSet
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ALocEqRoL
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_exists_vF_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_alphaN_rho_diff_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
  {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
  (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
  {S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}}
  (hS : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, vd h L 𝔭.1 ≠ 0 → 𝔭 ∈ S)
include hK hF hs hd hL hLi hS
include hm
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (j : ℕ) :
    |roL h L S 𝔭 (j + 1) - roL h L S 𝔭 j| ≤
      8 * ((j : ℝ) + 2) ^ 2 / (Ideal.absNorm 𝔭.1 : ℝ) := by
  by_cases h𝔭 : 𝔭 ∈ S
  · have h1 : ∀ i, roL h L S 𝔭 i = 1 := fun i => by rw [roL, if_pos h𝔭]
    rw [h1, h1, sub_self, abs_zero]
    positivity
  · have hv : vd h L 𝔭.1 = 0 := by
      by_contra hne
      exact h𝔭 (hS 𝔭 hne)
    have hro : ∀ i, roL h L S 𝔭 i = aLoc h L 𝔭 (exists_vF_eq 𝔭.2 i).choose := fun i => by
      rw [roL, if_neg h𝔭]
    obtain ⟨hn1, hv1⟩ := (exists_vF_eq 𝔭.2 (j + 1)).choose_spec
    obtain ⟨hn0, hv0⟩ := (exists_vF_eq 𝔭.2 j).choose_spec
    rw [hro, hro]
    unfold aLoc eFac
    have hb := alphaN_rho_diff_bound hK hF hs hd hL hLi hm 𝔭.2 hv hn1 hn0 (by rw [hv1, hv0])
    refine hb.trans ?_
    rw [hv1]

    have key : ∀ e : ℕ, 1 ≤ e → 8 * (((j + 1 : ℕ) : ℝ) + 1) ^ 2 *
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(e : ℤ)) ≤ 8 * ((j : ℝ) + 2) ^ 2 / (Ideal.absNorm 𝔭.1 : ℝ) := by
      intro e he
      have hj : (((j + 1 : ℕ) : ℝ) + 1) = (j : ℝ) + 2 := by push_cast; ring
      rw [hj, div_eq_mul_inv]
      rcases Nat.eq_zero_or_pos (Ideal.absNorm 𝔭.1) with h0 | hpos
      · rw [h0, Nat.cast_zero, zero_zpow _ (by omega), inv_zero]
      · have hx : (1 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by exact_mod_cast hpos
        have hz : (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(e : ℤ)) ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-1 : ℤ) :=
          zpow_le_zpow_right₀ hx (by omega)
        rw [zpow_neg_one] at hz
        exact mul_le_mul_of_nonneg_left hz (by positivity)
    exact key _ (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
end Formalism.HermitianLattices.Ext.L3.A5
