-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.alphaN_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:02:41.927397+00:00
-- url     : https://prove2.me/submissions/d5dd9c37-b23a-46fe-b188-4ad955db96a2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldMore
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldFurther
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_eta_pow_sq
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_pow_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mul_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_pow_le_span_sup
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_cntI_add_two
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_cntI_eq_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_cntI_one_of_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_cntP_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_cnt_eq_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_cnt_one_of_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_cnt_unit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_mem_pow_iff_le_vF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_nkCount_eq_cnt
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_one_lt_q
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_real_step
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
private theorem exists_uniformizer_sq_mul_congr_of_two_le_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0)
    (h2 : 2 ≤ vF 𝔭 n) {N : ℕ} (hN : vF 𝔭 n + 1 ≤ N) :
    ∃ ϖ ∈ 𝔭, ϖ ∉ 𝔭 ^ 2 ∧ ∃ n' : 𝓞 F, n' ≠ 0 ∧ vF 𝔭 n' + 2 = vF 𝔭 n ∧ n - ϖ ^ 2 * n' ∈ 𝔭 ^ N := by
  have h0 : 𝔭 ≠ ⊥ := idealPowerSpanBounds.ne_bot h𝔭
  obtain ⟨ϖ, hϖ1, hϖ2⟩ : ∃ ϖ ∈ 𝔭, ϖ ∉ 𝔭 ^ 2 := by
    by_contra hcon
    push Not at hcon
    have heq : 𝔭 ^ 2 = 𝔭 := le_antisymm (Ideal.pow_le_self two_ne_zero) (fun x hx => hcon x hx)
    have hmul : 𝔭 * 𝔭 = 𝔭 * 1 := by rw [mul_one, ← pow_two, heq]
    have h1 : 𝔭 = 1 := mul_left_cancel₀ h0 hmul
    exact h𝔭.ne_top (by rw [h1, Ideal.one_eq_top])
  have hg : ϖ ^ 2 ∉ 𝔭 ^ (2 + 1) := by
    have := idealPowerSpanBounds.mul_notMem h𝔭.isPrime h0 (i := 1) (j := 1) hϖ2 hϖ2
    rwa [← pow_two] at this
  have hmem : ∀ e, n ∈ 𝔭 ^ e ↔ e ≤ vF 𝔭 n := mem_pow_iff_le_vF h𝔭 hn
  have hsup := idealPowerSpanBounds.pow_le_span_sup h𝔭.isPrime h0 hg N ((hmem 2).mpr h2)
  obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.mp hsup
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  have hdiff : n - ϖ ^ 2 * r = e := by rw [← hae]; ring
  have heN : ∀ t, t ≤ N → e ∈ 𝔭 ^ t := fun t ht => Ideal.pow_le_pow_right ht he
  refine ⟨ϖ, hϖ1, hϖ2, r, ?_, ?_, by rw [hdiff]; exact he⟩
  · rintro rfl
    have : n ∈ 𝔭 ^ N := by rw [← hae]; simpa using he
    have := (hmem N).mp this
    omega
  · have hr0 : r ≠ 0 := by
      rintro rfl
      have : n ∈ 𝔭 ^ N := by rw [← hae]; simpa using he
      have := (hmem N).mp this
      omega
    have hmemr : ∀ t, r ∈ 𝔭 ^ t ↔ t ≤ vF 𝔭 r := mem_pow_iff_le_vF h𝔭 hr0
    have hup : ¬ (vF 𝔭 n - 1 ≤ vF 𝔭 r) := by
      intro hle
      have hr := (hmemr (vF 𝔭 n - 1)).mpr hle
      have h3 : ϖ ^ 2 * r ∈ 𝔭 ^ (vF 𝔭 n + 1) := by
        have := Ideal.mul_mem_mul (Ideal.pow_mem_pow hϖ1 2) hr
        rwa [← pow_add, show 2 + (vF 𝔭 n - 1) = vF 𝔭 n + 1 by omega] at this
      have h4 : n ∈ 𝔭 ^ (vF 𝔭 n + 1) := by
        have h3' : r * ϖ ^ 2 ∈ 𝔭 ^ (vF 𝔭 n + 1) := by rw [mul_comm]; exact h3
        have := Ideal.add_mem _ h3' (heN _ hN)
        rwa [hae] at this
      have := (hmem _).mp h4
      omega
    have hlow : vF 𝔭 n - 2 ≤ vF 𝔭 r := by
      rcases Nat.eq_zero_or_pos (vF 𝔭 n - 2) with h | h
      · omega
      · by_contra hlt
        have hr : r ∉ 𝔭 ^ ((vF 𝔭 n - 3) + 1) := by
          rw [hmemr]; omega
        have h5 := idealPowerSpanBounds.mul_notMem h𝔭.isPrime h0 hg hr
        have h6 : ϖ ^ 2 * r ∈ 𝔭 ^ vF 𝔭 n := by
          rw [show ϖ ^ 2 * r = n - e by rw [← hdiff]; ring]
          exact Ideal.sub_mem _ ((hmem _).mpr le_rfl) (heN _ (by omega))
        rw [show 2 + (vF 𝔭 n - 3) + 1 = vF 𝔭 n by omega] at h5
        exact h5 h6
    omega
private theorem pow_mul_div_pow_eq_inv_sq_mul (q c' : ℝ) (j m : ℕ) (hq : 0 < q) :
    (q ^ (2 * (m + 1)) * c') / q ^ ((j + 2) * (2 * (m + 1) - 1)) =
      ((q ^ m)⁻¹) ^ 2 * (c' / q ^ (j * (2 * (m + 1) - 1))) := by
  have hq0 : q ≠ 0 := hq.ne'
  rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega,
    show (j + 2) * (2 * m + 1) = j * (2 * m + 1) + (2 * m + 2) + 2 * m by ring,
    show 2 * (m + 1) = 2 * m + 2 by ring, pow_add, pow_add]
  field_simp
  ring
private theorem sub_single_one_add_single_one_of_ne_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {m : ℕ} {n : 𝓞 F} (hn : n ∈ 𝔭)
    (hc1 : (cnt hF 𝔭 1 (m + 1) (ι n) : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ (2 * (m + 1)) -
      ((Ideal.absNorm 𝔭 : ℝ) - 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (2 * (m + 1) - 1) * (1 - etaF K F 𝔭 ^ (m + 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (m + 1))⁻¹))) (j : ℕ) :
    (cnt hF 𝔭 (j + 2) (m + 1) (ι n) : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ ((j + 2) * (2 * (m + 1) - 1)) =
      (1 - etaF K F 𝔭 ^ (m + 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (m + 1))⁻¹) * (1 + etaF K F 𝔭 ^ (m + 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ m)⁻¹) +
      (cntI hF 𝔭 (j + 2) (m + 1) (ι n) : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ ((j + 2) * (2 * (m + 1) - 1)) := by
  have hιn : ι n ∈ extP K 𝔭 := by
    have := (idealPowerSpanBounds.mem_pow_iff (K := K) 𝔭 1 n).mpr (by rwa [pow_one])
    rwa [pow_one] at this
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by have := one_lt_q h𝔭; linarith
  have hadd := cnt_eq_add hF h𝔭 (j + 2) (m + 1) (ι n)
  have hP := cntP_eq hK hF h𝔭 (j + 1) (Nat.le_add_left 1 m) (idealPowerSpanBounds.conjO_map hF n)
  have hadd1 := cnt_eq_add hF h𝔭 1 (m + 1) (ι n)
  have hI1 := cntI_one_of_mem hF 𝔭 (m + 1) hιn
  have hP1 : (cntP hF 𝔭 1 (m + 1) (ι n) : ℝ) = (cnt hF 𝔭 1 (m + 1) (ι n) : ℝ) - 1 := by
    rw [hadd1, hI1]; push_cast; ring
  rw [hadd, hP]
  push_cast
  rw [hP1]
  exact real_step _ _ _ _ _ _ j m hq rfl (eta_pow_sq (K := K) 𝔭 (m + 1)) rfl hc1
private theorem stab_lemma (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {m : ℕ}
    (hc1 : ∀ n : 𝓞 F, n ∈ 𝔭 → (cnt hF 𝔭 1 (m + 1) (ι n) : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ (2 * (m + 1)) -
      ((Ideal.absNorm 𝔭 : ℝ) - 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (2 * (m + 1) - 1) * (1 - etaF K F 𝔭 ^ (m + 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (m + 1))⁻¹))) :
    ∀ v : ℕ, ∀ n : 𝓞 F, n ≠ 0 → vF 𝔭 n = v → ∀ k : ℕ, 2 * v + 1 ≤ k →
      (cnt hF 𝔭 k (m + 1) (ι n) : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * (m + 1) - 1)) =
        (1 - etaF K F 𝔭 ^ (m + 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (m + 1))⁻¹) * ∑ l ∈ Finset.range (v + 1), (etaF K F 𝔭 ^ (m + 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ m)⁻¹) ^ l := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by have := one_lt_q h𝔭; linarith
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro n hn0 hnv k hk
    have hmem : ∀ e, n ∈ 𝔭 ^ e ↔ e ≤ vF 𝔭 n := mem_pow_iff_le_vF h𝔭 hn0
    rcases v with _ | _ | w
    · have hn𝔭 : n ∉ 𝔭 := by
        intro h
        have := (hmem 1).mp (by rwa [pow_one])
        omega
      rw [cnt_unit hK hF h𝔭 (Nat.le_add_left 1 m) (by omega) hn𝔭,
        show k * (2 * (m + 1) - 1) = (2 * (m + 1) - 1) * k from mul_comm _ _,
        mul_div_cancel_left₀ _ (pow_ne_zero _ hq.ne'), zpow_neg, zpow_natCast]
      simp
    · have hn𝔭 : n ∈ 𝔭 := by rw [← pow_one 𝔭]; exact (hmem 1).mpr (by omega)
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      rw [sub_single_one_add_single_one_of_ne_zero hK hF h𝔭 hn𝔭 (hc1 n hn𝔭) j]
      have hn2 : ι n ∉ extP K 𝔭 ^ 2 := by
        rw [idealPowerSpanBounds.mem_pow_iff, hmem]; omega
      rw [cntI_eq_zero hF 𝔭 j (m + 1) hn2]
      simp [Finset.sum_range_succ]
    · have hn𝔭 : n ∈ 𝔭 := by rw [← pow_one 𝔭]; exact (hmem 1).mpr (by omega)
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      rw [sub_single_one_add_single_one_of_ne_zero hK hF h𝔭 hn𝔭 (hc1 n hn𝔭) j]
      obtain ⟨ϖ, h1, h2, n', hn'0, hn'v, hdiv⟩ := exists_uniformizer_sq_mul_congr_of_two_le_vF h𝔭 hn0 (by omega) (N := j + 2) (by omega)
      have hdivK : ι n - ι ϖ ^ 2 * ι n' ∈ extP K 𝔭 ^ (j + 2) := by
        rw [← map_pow, ← map_mul, ← map_sub, idealPowerSpanBounds.mem_pow_iff]
        exact hdiv
      rw [cntI_add_two hK hF h𝔭 h1 h2 j (m + 1) hdivK]
      have hih := ih w (by omega) n' hn'0 (by omega) j (by omega)
      push_cast
      rw [pow_mul_div_pow_eq_inv_sq_mul _ _ j m hq, hih]
      set x := (etaF K F 𝔭 ^ (m + 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ m)⁻¹) with hx
      have hx2 : x ^ 2 = ((Ideal.absNorm 𝔭 : ℝ) ^ m)⁻¹ ^ 2 := by
        rw [hx, mul_pow, eta_pow_sq (K := K) 𝔭 (m + 1), one_mul]
      have hgeo : ∑ l ∈ Finset.range (w + 1 + 1 + 1), x ^ l =
          1 + x + x ^ 2 * ∑ l ∈ Finset.range (w + 1), x ^ l := by
        rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum,
          Finset.sum_congr rfl (fun i _ => (show x ^ (i + 1 + 1) = x ^ 2 * x ^ i by ring))]
        simp only [pow_zero, zero_add, pow_one]
        ring
      rw [hgeo, ← hx2]
      ring
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
end
end

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
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn : n ≠ 0) (hn𝔭 : n ∈ 𝔭) :
    alphaN h L 𝔭 n =
      (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) *
        (1 + etaF K F 𝔭 ^ finrank K V * ((Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V - 1))⁻¹) +
      (cntI hF 𝔭 (2 * vF 𝔭 n + 2) (finrank K V) (ι n) : ℝ) /
        (Ideal.absNorm 𝔭 : ℝ) ^ ((2 * vF 𝔭 n + 2) * (2 * finrank K V - 1)) := by
  obtain ⟨m, hm'⟩ : ∃ m, finrank K V = m + 1 := ⟨finrank K V - 1, by omega⟩
  have hc1 : ∀ n : 𝓞 F, n ∈ 𝔭 → (cnt hF 𝔭 1 (m + 1) (ι n) : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ (2 * (m + 1)) -
      ((Ideal.absNorm 𝔭 : ℝ) - 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (2 * (m + 1) - 1) * (1 - etaF K F 𝔭 ^ (m + 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (m + 1))⁻¹)) := by
    intro n' hn'
    have h := cnt_one_of_mem hK hF hs hd hL hLi h𝔭 hv hm hn'
    rw [hm'] at h
    rw [h, zpow_neg, zpow_natCast]
  have hA : alphaN h L 𝔭 n = (1 - etaF K F 𝔭 ^ (m + 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (m + 1))⁻¹) * ∑ l ∈ Finset.range (vF 𝔭 n + 1), (etaF K F 𝔭 ^ (m + 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ m)⁻¹) ^ l := by
    rw [alphaN]
    apply Filter.Tendsto.limUnder_eq
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop (2 * vF 𝔭 n + 1)] with k hk
    rw [nkCount_eq_cnt hK hF hs hd hL hLi h𝔭 hv (by omega) n, hm',
      stab_lemma hK hF h𝔭 hc1 (vF 𝔭 n) n hn rfl k hk]
  rw [hA, ← stab_lemma hK hF h𝔭 hc1 (vF 𝔭 n) n hn rfl (2 * vF 𝔭 n + 2) (by omega), hm',
    sub_single_one_add_single_one_of_ne_zero hK hF h𝔭 hn𝔭 (hc1 n hn𝔭) (2 * vF 𝔭 n)]
  simp only [zpow_neg, zpow_natCast, Nat.add_sub_cancel]
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
