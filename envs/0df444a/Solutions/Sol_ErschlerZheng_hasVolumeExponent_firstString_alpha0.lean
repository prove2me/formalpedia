-- Prove2me | solution 1 for ErschlerZheng.hasVolumeExponent_firstString_alpha0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T11:37:50.42563+00:00
-- url     : https://prove2.me/submissions/5a6da72a-02d7-438e-8172-3e3c75fb1c3d

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Theorems.Thm_ErschlerZheng_exists_measure_mass_le_rpow_and_exp_le_growth
import Theorems.Thm_Bartholdi_card_wordBall_le_exp_mul_rpow_alpha0
import Theorems.Thm_ErschlerZheng_grigorchuk_firstString_eq_grigorchukGroup_and_gen_eq

section
/-!
# K4: `log log v(n) / log n → α_0` for `G_012` (abstract, p. 3)

A reduction: the lower bound `v(n) ⩾ exp(c_ε n^{α_0-ε})` is Theorem A (K2), the upper bound
`v(n) ⩽ exp(C n^{α_0})` is Bartholdi's (K3), transported to `G_{(012)^∞}` along A1.
-/

namespace ErschlerZheng

namespace VolumeDev

theorem wordBall_image {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (T : Set G) (n : ℕ) :
    Chou.wordBall (e '' T) n = e '' Chou.wordBall T n := by
  ext y
  constructor
  · rintro ⟨l, hl, hls, rfl⟩
    refine ⟨(l.map e.symm).prod, ⟨l.map e.symm, by simpa using hl, ?_, rfl⟩, ?_⟩
    · intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      rcases hls z hz with ⟨t, ht, rfl⟩ | ⟨t, ht, he⟩
      · left; simpa using ht
      · right
        rw [← map_inv, ← he]
        simpa using ht
    · rw [map_list_prod, List.map_map]
      simp
  · rintro ⟨g, ⟨l, hl, hls, rfl⟩, rfl⟩
    refine ⟨l.map e, by simpa using hl, ?_, by rw [map_list_prod]⟩
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rcases hls z hz with h | h
    · left; exact ⟨z, h, rfl⟩
    · right; exact ⟨z⁻¹, h, by simp⟩

theorem gens_finite (ω : ℕ → Fin 3) : (gens ω).Finite := by
  unfold gens
  exact (((Set.finite_singleton _).insert _).insert _).insert _

/-- Bartholdi's bound, transported to `G_{(012)^∞}` with `S = {a, b, c, d}`. -/
theorem growth_le : ∃ C : ℝ, ∀ n : ℕ, (growth (genSet firstString) n : ℝ) ≤
    Real.exp (C * (n : ℝ) ^ alpha0) := by
  have hA1 := grigorchuk_firstString_eq_grigorchukGroup_and_gen_eq.1
  let e : grigorchuk firstString ≃* Garrido.GrigorchukGroup := MulEquiv.subgroupCongr hA1
  have hfin : (genSet firstString).Finite :=
    (gens_finite firstString).preimage Subtype.val_injective.injOn
  set S' : Finset Garrido.GrigorchukGroup := (hfin.image e).toFinset with hS'
  have hS'coe : (S' : Set Garrido.GrigorchukGroup) = e '' genSet firstString := by
    rw [hS', Set.Finite.coe_toFinset]
  have hgen : Subgroup.closure (genSet firstString) = ⊤ := Subgroup.closure_closure_coe_preimage
  have hS'gen : Subgroup.closure (S' : Set Garrido.GrigorchukGroup) = ⊤ := by
    rw [hS'coe, ← MonoidHom.coe_coe e, ← MonoidHom.map_closure, hgen]
    exact Subgroup.map_top_of_surjective _ e.surjective
  obtain ⟨C, hC⟩ := Bartholdi.card_wordBall_le_exp_mul_rpow_alpha0 S' hS'gen
  refine ⟨C, fun n => ?_⟩
  have := hC n
  rw [hS'coe, wordBall_image, Nat.card_image_of_injective e.injective] at this
  unfold growth
  rwa [Nat.floor_natCast]

end VolumeDev

end ErschlerZheng
end

section
open ErschlerZheng
open VolumeDev in
theorem solution :
    HasVolumeExponent (genSet firstString) alpha0 := by
  have hlow := exists_measure_mass_le_rpow_and_exp_le_growth.2
  obtain ⟨C, hC⟩ := growth_le
  set C' := max C 1 with hC'
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log n) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- `log v(n) > 0` for `n ⩾ 1`
  obtain ⟨c₁, hc₁, hlow₁⟩ := hlow 1 one_pos
  have hvpos : ∀ n : ℕ, 1 ≤ n → 0 < Real.log (growth (genSet firstString) n) := by
    intro n hn
    apply Real.log_pos
    calc (1 : ℝ) < Real.exp (c₁ * (n : ℝ) ^ (alpha0 - 1)) := by
          have : (0 : ℝ) < (n : ℝ) ^ (alpha0 - 1) :=
            Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _
          rw [← Real.exp_zero]
          exact Real.exp_lt_exp.mpr (by positivity)
      _ ≤ _ := hlow₁ n hn
  unfold HasVolumeExponent
  rw [tendsto_order]
  constructor
  · -- lower bound
    intro a ha
    set ε := (alpha0 - a) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    obtain ⟨c, hc, hlowε⟩ := hlow ε hε0
    have hlim : Filter.Tendsto (fun n : ℕ => Real.log c / Real.log n) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hlog
    filter_upwards [hlim.eventually (lt_mem_nhds (show (-ε : ℝ) < 0 by linarith)),
      hlog.eventually_gt_atTop 0, Filter.eventually_ge_atTop 1] with n h1 h2 h3
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hb := hlowε n h3
    have hpow : 0 < (n : ℝ) ^ (alpha0 - ε) := Real.rpow_pos_of_pos hn0 _
    have hl1 : c * (n : ℝ) ^ (alpha0 - ε) ≤ Real.log (growth (genSet firstString) n) := by
      have := Real.log_le_log (Real.exp_pos _) hb
      rwa [Real.log_exp] at this
    have hl2 : Real.log c + (alpha0 - ε) * Real.log n ≤
        Real.log (Real.log (growth (genSet firstString) n)) := by
      have := Real.log_le_log (by positivity) hl1
      rwa [Real.log_mul hc.ne' hpow.ne', Real.log_rpow hn0] at this
    rw [lt_div_iff₀ h2]
    have : -ε < Real.log c / Real.log n := h1
    rw [lt_div_iff₀ h2] at this
    nlinarith
  · -- upper bound
    intro b hb
    have hC'pos : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hlim : Filter.Tendsto (fun n : ℕ => Real.log C' / Real.log n) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hlog
    filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < b - alpha0 by linarith)),
      hlog.eventually_gt_atTop 0, Filter.eventually_ge_atTop 1] with n h1 h2 h3
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hpow : 0 < (n : ℝ) ^ alpha0 := Real.rpow_pos_of_pos hn0 _
    have hu1 : Real.log (growth (genSet firstString) n) ≤ C' * (n : ℝ) ^ alpha0 := by
      have hv : (0 : ℝ) < growth (genSet firstString) n := by
        have := hvpos n h3
        rcases Nat.eq_zero_or_pos (growth (genSet firstString) n) with h | h
        · rw [h] at this; simp at this
        · exact_mod_cast h
      have := Real.log_le_log hv (hC n)
      rw [Real.log_exp] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow.le)
    have hu2 : Real.log (Real.log (growth (genSet firstString) n)) ≤
        Real.log C' + alpha0 * Real.log n := by
      have := Real.log_le_log (hvpos n h3) hu1
      rwa [Real.log_mul hC'pos.ne' hpow.ne', Real.log_rpow hn0] at this
    rw [div_lt_iff₀ h2]
    have : Real.log C' / Real.log n < b - alpha0 := h1
    rw [div_lt_iff₀ h2] at this
    nlinarith
end
