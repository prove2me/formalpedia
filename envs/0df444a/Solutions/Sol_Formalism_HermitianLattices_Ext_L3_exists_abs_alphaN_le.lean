-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.exists_abs_alphaN_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:00:18.447836+00:00
-- url     : https://prove2.me/submissions/bc3d8b21-ef27-4f04-a01e-2478f5147d3c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_BoxInterEqEmpty
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumOfMean
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumBoxIdeal
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_one_lt_absNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanC_one_lt_absNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_nkCount_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_nkCount_succ
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
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : ∃ C : ℝ, ∀ n : 𝓞 F, |alphaN h L 𝔭 n| ≤ C := by
  obtain ⟨C, hC⟩ := nkCount_le hK hF hs hd hL hLi hm h𝔭
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := zero_lt_one.trans (BoxSum.one_lt_absNorm h𝔭)
  refine ⟨max C |alphaN h L 𝔭 0|, fun n => ?_⟩
  by_cases hn : n = 0
  · rw [hn]; exact le_max_right _ _
  refine le_trans ?_ (le_max_left _ _)
  set u : ℕ → ℝ := fun k => (nkCount h L 𝔭 k n : ℝ) /
    (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) with hu
  set k₀ := 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 with hk₀
  have hstep : ∀ k, k₀ ≤ k → u k = u k₀ := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      rw [← ih]
      simp only [hu]
      rw [nkCount_succ hK hF hs hd hL hLi h𝔭 hn hk, add_mul, one_mul, pow_add]
      push_cast
      field_simp
  have hlim : Tendsto u atTop (𝓝 (u k₀)) :=
    tendsto_atTop_of_eventually_const (i₀ := k₀) fun k hk => hstep k hk
  have hα : alphaN h L 𝔭 n = u k₀ := hlim.limUnder_eq
  rw [hα, abs_of_nonneg (by simp only [hu]; positivity)]
  simp only [hu]
  rw [div_le_iff₀ (by positivity)]
  exact hC _ _
end Formalism.HermitianLattices.Ext.L3
