-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.tendsto_mean_alphaN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:58:53.789821+00:00
-- url     : https://prove2.me/submissions/d9eb90a7-ce7d-467f-a6d4-0f2c80af3f81

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanC_finite_quot_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanC_one_lt_absNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanC_vF_lt_of_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanC_card_out_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_sum_nkCount
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_alphaN_eq_of_le
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_nkCount_le
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
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    Tendsto (fun k : ℕ => (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) *
      ∑ᶠ n' : 𝓞 F ⧸ 𝔭 ^ k, alphaN h L 𝔭 (Quotient.out n')) atTop (𝓝 1) := by
  classical
  obtain ⟨C0, hC0⟩ := nkCount_le hK hF hs hd hL hLi hm h𝔭
  have hN1 := MeanC.one_lt_absNorm h𝔭
  have hNpos : (0:ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by exact_mod_cast (by omega : 0 < Ideal.absNorm 𝔭)
  have hCnn : (0:ℝ) ≤ max C0 0 := le_max_right _ _
  have hratio : ∀ (k : ℕ) (n : 𝓞 F), (nkCount h L 𝔭 k n : ℝ) /
      (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) ≤ max C0 0 := fun k n => by
    rw [div_le_iff₀ (pow_pos hNpos _)]
    exact (hC0 k n).trans (by gcongr; exact le_max_left _ _)
  have hratio0 : ∀ (k : ℕ) (n : 𝓞 F), 0 ≤ (nkCount h L 𝔭 k n : ℝ) /
      (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) := fun k n => by positivity
  have hα : ∀ n : 𝓞 F, n ≠ 0 → |alphaN h L 𝔭 n| ≤ max C0 0 := by
    intro n hn
    rw [alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn (k := 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2) le_rfl,
      abs_of_nonneg (hratio0 _ _)]
    exact hratio _ _
  let j : ℕ → ℕ := fun k => (k - 2 * vd h L 𝔭) / 2
  have hjk : ∀ k, j k ≤ k := fun k => by
    show (k - 2 * vd h L 𝔭) / 2 ≤ k
    omega
  have hgood : ∀ (k : ℕ) (n : 𝓞 F), n ∉ 𝔭 ^ j k →
      n ≠ 0 ∧ 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 ≤ k := by
    intro k n hn
    refine ⟨?_, ?_⟩
    · rintro rfl
      exact hn (Ideal.zero_mem _)
    · have : vF 𝔭 n < (k - 2 * vd h L 𝔭) / 2 := MeanC.vF_lt_of_notMem hn
      omega
  have key : ∀ k : ℕ, |(Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) *
      ∑ᶠ n' : 𝓞 F ⧸ 𝔭 ^ k, alphaN h L 𝔭 (Quotient.out n') - 1| ≤
        (2 * max C0 0 + |alphaN h L 𝔭 0|) * ((Ideal.absNorm 𝔭 : ℝ)⁻¹) ^ (j k) := by
    intro k
    haveI := MeanC.finite_quot_pow h𝔭 k
    letI := Fintype.ofFinite (𝓞 F ⧸ 𝔭 ^ k)
    have hsumr : ∑ n' : 𝓞 F ⧸ 𝔭 ^ k, (nkCount h L 𝔭 k (Quotient.out n') : ℝ) /
        (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) = (Ideal.absNorm 𝔭 : ℝ) ^ k := by
      have hS := sum_nkCount hK hF hs hd hL hLi h𝔭 k
      rw [finsum_eq_sum_of_fintype] at hS
      rw [← Finset.sum_div, ← Nat.cast_sum, hS]
      push_cast
      rw [div_eq_iff (pow_ne_zero _ hNpos.ne'), ← pow_add]
      congr 1
      have h2f : 2 * finrank K V - 1 + 1 = 2 * finrank K V := by omega
      nth_rewrite 1 [← h2f]
      ring
    rw [finsum_eq_sum_of_fintype]
    have hdiff : (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) *
        ∑ n' : 𝓞 F ⧸ 𝔭 ^ k, alphaN h L 𝔭 (Quotient.out n') - 1 =
        (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) * ∑ n' : 𝓞 F ⧸ 𝔭 ^ k,
          (alphaN h L 𝔭 (Quotient.out n') - (nkCount h L 𝔭 k (Quotient.out n') : ℝ) /
            (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1))) := by
      rw [Finset.sum_sub_distrib, hsumr, mul_sub, zpow_neg, zpow_natCast,
        inv_mul_cancel₀ (pow_ne_zero _ hNpos.ne')]
    rw [hdiff]
    have hterm : ∀ n' : 𝓞 F ⧸ 𝔭 ^ k, |alphaN h L 𝔭 (Quotient.out n') -
        (nkCount h L 𝔭 k (Quotient.out n') : ℝ) /
          (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1))| ≤
        if Quotient.out n' ∈ 𝔭 ^ j k then 2 * max C0 0 + |alphaN h L 𝔭 0| else 0 := by
      intro n'
      split_ifs with hin
      · have h1 : |alphaN h L 𝔭 (Quotient.out n')| ≤ max C0 0 + |alphaN h L 𝔭 0| := by
          by_cases h0 : Quotient.out n' = 0
          · rw [h0]
            linarith
          · linarith [hα _ h0, abs_nonneg (alphaN h L 𝔭 0)]
        have h2 := hratio k (Quotient.out n')
        have h3 := hratio0 k (Quotient.out n')
        calc _ ≤ |alphaN h L 𝔭 (Quotient.out n')| + |(nkCount h L 𝔭 k (Quotient.out n') : ℝ) /
              (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1))| := abs_sub _ _
          _ ≤ _ := by
            rw [abs_of_nonneg h3]
            linarith
      · obtain ⟨hn0, hk⟩ := hgood k _ hin
        rw [alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn0 hk, sub_self, abs_zero]
    have hcount : ((Finset.univ.filter fun n' : 𝓞 F ⧸ 𝔭 ^ k =>
        Quotient.out n' ∈ 𝔭 ^ j k).card : ℝ) * (Ideal.absNorm 𝔭 : ℝ) ^ (j k) =
          (Ideal.absNorm 𝔭 : ℝ) ^ k := by
      have h1 := MeanC.card_out_mem 𝔭 (hjk k)
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
      exact_mod_cast h1
    rw [abs_mul, abs_of_pos (zpow_pos hNpos _)]
    calc _ ≤ (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) * ∑ n' : 𝓞 F ⧸ 𝔭 ^ k,
          (if Quotient.out n' ∈ 𝔭 ^ j k then 2 * max C0 0 + |alphaN h L 𝔭 0| else 0) := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n' _ => hterm n')
      _ = (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) * (((Finset.univ.filter fun n' : 𝓞 F ⧸ 𝔭 ^ k =>
          Quotient.out n' ∈ 𝔭 ^ j k).card : ℝ) * (2 * max C0 0 + |alphaN h L 𝔭 0|)) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      _ = _ := by
          rw [zpow_neg, zpow_natCast, ← hcount, inv_pow]
          have hc0 : ((Finset.univ.filter fun n' : 𝓞 F ⧸ 𝔭 ^ k =>
              Quotient.out n' ∈ 𝔭 ^ j k).card : ℝ) ≠ 0 := by
            intro h0
            rw [h0, zero_mul] at hcount
            exact (pow_pos hNpos k).ne' hcount.symm
          field_simp
  have hj : Tendsto j atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨2 * b + 2 * vd h L 𝔭, fun k hk => ?_⟩
    show b ≤ (k - 2 * vd h L 𝔭) / 2
    omega
  have hlim : Tendsto (fun k => (2 * max C0 0 + |alphaN h L 𝔭 0|) *
      ((Ideal.absNorm 𝔭 : ℝ)⁻¹) ^ (j k)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((Ideal.absNorm 𝔭 : ℝ)⁻¹) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        (inv_lt_one_of_one_lt₀ (by exact_mod_cast hN1))
    simpa using (h1.comp hj).const_mul (2 * max C0 0 + |alphaN h L 𝔭 0|)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun k => norm_nonneg _) (fun k => by rw [Real.norm_eq_abs]; exact key k) hlim
end Formalism.HermitianLattices.Ext.L3
