-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxSum.tendsto_sum_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:42:50.339857+00:00
-- url     : https://prove2.me/submissions/02dad5b5-f4d7-4bbd-a7fe-fff693044fc4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumCoset
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumPeriodic
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_exists_crt
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_sum_split
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_tendsto_sum_coset
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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {m : ℕ} (hm : 1 ≤ m)
    (k : ℕ) (φ : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (𝓞 F ⧸ 𝔭.1 ^ k) → ℝ)
    (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    ∀ (b : Ideal (𝓞 F)), b ≠ ⊥ → (∀ 𝔭 ∈ S, b ⊔ 𝔭.1 = ⊤) → ∀ x₀ : 𝓞 F,
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n - x₀ ∈ b},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
            ∏ 𝔭 ∈ S, φ 𝔭 (Ideal.Quotient.mk (𝔭.1 ^ k) n))
      atTop (𝓝 ((m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm b : ℝ) *
          ∏ 𝔭 ∈ S, ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-(k : ℤ)) * ∑ᶠ c, φ 𝔭 c))) := by
  induction S using Finset.induction_on with
  | empty =>
    intro b hb _ x₀
    have := tendsto_sum_coset hK hF hm hb x₀
    simp only [Finset.prod_empty, mul_one]
    exact this
  | insert 𝔮 S' h𝔮S ih =>
    intro b hb hcop x₀
    have h𝔮0 : 𝔮.1 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField 𝔮.2 (RingOfIntegers.not_isField F)
    have h𝔞0 : 𝔮.1 ^ k ≠ ⊥ := by
      have h0 : 𝔮.1 ≠ 0 := by simpa only [Ideal.zero_eq_bot] using h𝔮0
      simpa only [Ideal.zero_eq_bot] using pow_ne_zero k h0
    haveI : Fintype (𝓞 F ⧸ 𝔮.1 ^ k) := @Fintype.ofFinite _ (finite_quot h𝔞0)
    have hco : b ⊔ 𝔮.1 ^ k = ⊤ := by
      have h1 : IsCoprime b 𝔮.1 := Ideal.isCoprime_iff_sup_eq.mpr (hcop 𝔮 (Finset.mem_insert_self _ _))
      exact Ideal.isCoprime_iff_sup_eq.mp h1.pow_right
    choose x hx using fun c => exists_crt hco x₀ c
    have hb' : b * 𝔮.1 ^ k ≠ ⊥ := by
      have h0 : b ≠ 0 := by simpa only [Ideal.zero_eq_bot] using hb
      have h1 : 𝔮.1 ^ k ≠ 0 := by simpa only [Ideal.zero_eq_bot] using h𝔞0
      simpa only [Ideal.zero_eq_bot] using mul_ne_zero h0 h1
    have hcop' : ∀ 𝔭 ∈ S', b * 𝔮.1 ^ k ⊔ 𝔭.1 = ⊤ := by
      intro 𝔭 h𝔭
      have h1 : IsCoprime b 𝔭.1 := Ideal.isCoprime_iff_sup_eq.mpr (hcop 𝔭 (Finset.mem_insert_of_mem h𝔭))
      have hne : 𝔮.1 ≠ 𝔭.1 := fun e => h𝔮S ((Subtype.ext e : 𝔮 = 𝔭) ▸ h𝔭)
      have h2 : IsCoprime 𝔮.1 𝔭.1 := Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne 𝔮.2 𝔭.2 hne)
      have h3 : IsCoprime (𝔮.1 ^ k) 𝔭.1 := h2.pow_left
      exact Ideal.isCoprime_iff_sup_eq.mp (h1.mul_left h3)
    have hlim := fun c => ih (b * 𝔮.1 ^ k) hb' hcop' (x c)

    have hsplit : ∀ j : ℕ, ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n - x₀ ∈ b},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ insert 𝔮 S', φ 𝔭 (Ideal.Quotient.mk (𝔭.1 ^ k) n) =
        ∑ c, φ 𝔮 c * ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n - x c ∈ b * 𝔮.1 ^ k},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * ∏ 𝔭 ∈ S', φ 𝔭 (Ideal.Quotient.mk (𝔭.1 ^ k) n) := by
      intro j
      rw [← sum_split hK hF _ hco x₀ (fun n => (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) *
        ∏ 𝔭 ∈ S', φ 𝔭 (Ideal.Quotient.mk (𝔭.1 ^ k) n)) (φ 𝔮) x hx]
      refine finsum_mem_congr rfl fun n _ => ?_
      rw [Finset.prod_insert h𝔮S]
      ring
    have hT := tendsto_finset_sum (Finset.univ : Finset (𝓞 F ⧸ 𝔮.1 ^ k)) fun c _ => (hlim c).const_mul (φ 𝔮 c)
    convert hT using 1
    · funext j
      rw [hsplit j, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    · congr 1
      rw [Finset.prod_insert h𝔮S, finsum_eq_sum_of_fintype]
      simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow, zpow_neg, zpow_natCast, Finset.mul_sum,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
end Formalism.HermitianLattices.Ext.L3.BoxSum
