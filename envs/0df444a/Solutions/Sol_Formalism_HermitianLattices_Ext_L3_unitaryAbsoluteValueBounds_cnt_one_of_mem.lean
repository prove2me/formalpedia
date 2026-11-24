-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.cnt_one_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:10:57.085253+00:00
-- url     : https://prove2.me/submissions/167d3ab9-f02d-4da1-a203-5fd037aaab03

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldTer
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldMore
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_cnt_congr
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_one_lt_absNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanC_card_quot_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanC_finite_quot_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanC_one_lt_absNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_pow_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_sum_nkCount
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_cnt_unit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_nkCount_eq_cnt


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn : n ∈ 𝔭) :
    (cnt hF 𝔭 1 (finrank K V) (ι n) : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ (2 * finrank K V) -
      ((Ideal.absNorm 𝔭 : ℝ) - 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (2 * finrank K V - 1) *
        (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ)))) := by
  classical
  have h0 := sum_nkCount hK hF hs hd hL hLi h𝔭 1
  have := MeanC.finite_quot_pow h𝔭 1
  have := Fintype.ofFinite (𝓞 F ⧸ 𝔭 ^ 1)
  rw [finsum_eq_sum_of_fintype,
    Finset.sum_congr rfl fun n' _ => nkCount_eq_cnt hK hF hs hd hL hLi h𝔭 hv le_rfl _,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : 𝓞 F ⧸ 𝔭 ^ 1))] at h0
  have h1 : (cnt hF 𝔭 1 (finrank K V) (ι (Quotient.out (0 : 𝓞 F ⧸ 𝔭 ^ 1))) : ℝ) +
      ∑ n' ∈ Finset.univ.erase (0 : 𝓞 F ⧸ 𝔭 ^ 1),
        (cnt hF 𝔭 1 (finrank K V) (ι (Quotient.out n')) : ℝ) =
      (Ideal.absNorm 𝔭 : ℝ) ^ (2 * finrank K V * 1) := by exact_mod_cast h0
  have h2 : cnt hF 𝔭 1 (finrank K V) (ι (Quotient.out (0 : 𝓞 F ⧸ 𝔭 ^ 1))) =
      cnt hF 𝔭 1 (finrank K V) (ι n) := by
    apply cnt_congr
    rw [← map_sub, idealPowerSpanBounds.mem_pow_iff]
    refine sub_mem ?_ (by rwa [pow_one])
    rw [← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_out]
  have h3 : ∀ n' ∈ Finset.univ.erase (0 : 𝓞 F ⧸ 𝔭 ^ 1),
      (cnt hF 𝔭 1 (finrank K V) (ι (Quotient.out n')) : ℝ) =
      (Ideal.absNorm 𝔭 : ℝ) ^ (2 * finrank K V - 1) *
        (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) := by
    intro n' hn'
    have hne : Quotient.out n' ∉ 𝔭 := by
      intro hmem
      apply Finset.ne_of_mem_erase hn'
      rw [← Ideal.Quotient.mk_out n', Ideal.Quotient.eq_zero_iff_mem]
      exact (pow_one 𝔭).ge hmem
    rw [cnt_unit hK hF h𝔭 hm le_rfl hne, mul_one]
  have hcard : ((Finset.univ.erase (0 : 𝓞 F ⧸ 𝔭 ^ 1)).card : ℝ) = (Ideal.absNorm 𝔭 : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ← Nat.card_eq_fintype_card,
      MeanC.card_quot_pow, pow_one, Nat.cast_sub (MeanC.one_lt_absNorm h𝔭).le, Nat.cast_one]
  rw [h2, Finset.sum_congr rfl h3, Finset.sum_const, nsmul_eq_mul, hcard, mul_one] at h1
  linarith
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
