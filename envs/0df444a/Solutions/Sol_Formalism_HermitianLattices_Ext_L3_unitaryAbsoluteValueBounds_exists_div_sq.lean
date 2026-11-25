-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.exists_div_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:02:50.330483+00:00
-- url     : https://prove2.me/submissions/f3022be3-6eb2-4eae-ad22-4998b21996cd

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldMore
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldFurther
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mul_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_pow_le_span_sup
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_mem_pow_iff_le_vF
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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {w : ℕ}
    (hvn : vF 𝔭 n = w + 2) {N : ℕ} (hN : w + 3 ≤ N) :
    ∃ ϖ ∈ 𝔭, ϖ ∉ 𝔭 ^ 2 ∧ ∃ n' : 𝓞 F, n' ≠ 0 ∧ vF 𝔭 n' = w ∧ n - ϖ ^ 2 * n' ∈ 𝔭 ^ N := by
  obtain ⟨ϖ, h1, h2, n', hn', hv', hd⟩ := exists_uniformizer_sq_mul_congr_of_two_le_vF h𝔭 hn (by omega) (N := N) (by omega)
  exact ⟨ϖ, h1, h2, n', hn', by omega, hd⟩
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
