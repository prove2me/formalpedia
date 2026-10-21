-- Prove2me | solution 1 for DynFairDiv.Uniform.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T12:15:48.545792+00:00
-- url     : https://prove2.me/submissions/3afd62b0-e475-4799-b395-7e7abb11e865

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model
import Theorems.Thm_DynFairDiv_Uniform_theorem_1
import Theorems.Thm_DynFairDiv_Uniform_ffa_realizes
import Theorems.Thm_DynFairDiv_Uniform_ffaTotal_uniform_monotone
import Theorems.Thm_DynFairDiv_Uniform_eq_E_1

open DynFairDiv.Uniform Filter Topology

theorem solution (d : ℕ) (hd : 1 ≤ d) :
    (∃ X, AchievesRatio (uniformCV d) ⊤ (uniformRatio d) X) ∧
    (∀ σ : ℝ, uniformRatio d < σ →
      ∃ n : ℕ, 1 ≤ n ∧ ¬ ∃ X, AchievesRatio (uniformCV d) (n : ℕ∞) σ X) ∧
    (⨅ n : {n : ℕ∞ // 1 ≤ n}, fairnessRatio (uniformCV d) n.1) = uniformRatio d := by
  set s := uniformRatio d with hs
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : 0 < Real.log (((d : ℝ) + 1) / d) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hd']; linarith
  have hspos : 0 < s := by rw [hs, uniformRatio]; positivity
  have hkey : ∀ σ : ℝ, σ * ((d : ℝ) + 1) * Real.log (((d : ℝ) + 1) / d) = σ / s := by
    intro σ; rw [hs, uniformRatio]; field_simp
  -- FFA with σ* stays feasible forever
  have hbound : ∀ t : ℕ, ffaTotal (uniformCV d) s t ≤ 1 := by
    intro t
    have hlim := eq_E_1 d hd s
    rw [hkey, div_self hspos.ne'] at hlim
    refine ge_of_tendsto hlim (eventually_atTop.2 ⟨t, fun ℓ hℓ => ?_⟩)
    exact ffaTotal_uniform_monotone d hd s hspos.le (by nlinarith)
  -- Part 1
  obtain ⟨X, hX, -⟩ := ffa_realizes (uniformCV d) ⊤ s hspos.le (fun t _ _ => hbound t)
  have hXn : ∀ n : ℕ∞, AchievesRatio (uniformCV d) n s X := by
    intro n
    refine ⟨fun t ht _ => hX.1 t ht le_top, fun t ht _ => hX.2 t ht le_top⟩
  -- Part 2
  have part2 : ∀ σ : ℝ, s < σ →
      ∃ n : ℕ, 1 ≤ n ∧ ¬ ∃ X, AchievesRatio (uniformCV d) (n : ℕ∞) σ X := by
    intro σ hσ
    have hlim := eq_E_1 d hd σ
    rw [hkey] at hlim
    have hgt : 1 < σ / s := by rw [lt_div_iff₀ hspos]; linarith
    obtain ⟨ℓ, hℓ1, hℓ2⟩ := ((hlim.eventually (lt_mem_nhds hgt)).and
      (eventually_ge_atTop 1)).exists
    refine ⟨ℓ * (d + 1), by nlinarith, ?_⟩
    rintro ⟨Y, hY⟩
    have := (theorem_1 (uniformCV d) _ σ Y (by linarith) hY (ℓ * (d + 1)) (by nlinarith)
      le_rfl).2
    linarith
  refine ⟨⟨X, hXn ⊤⟩, part2, ?_⟩
  -- Part 3
  have hbdd : ∀ n : ℕ∞, 1 ≤ n → BddAbove {σ : ℝ | ∃ X, AchievesRatio (uniformCV d) n σ X} := by
    intro n hn
    refine ⟨1, ?_⟩
    rintro σ ⟨Y, hF, hR⟩
    have h1 := hR 1 le_rfl (by exact_mod_cast hn) 0 one_pos
    have h2 := (hF 1 le_rfl (by exact_mod_cast hn)).2.1
    simp at h1 h2
    linarith
  have hlow : ∀ n : {n : ℕ∞ // 1 ≤ n}, s ≤ fairnessRatio (uniformCV d) n.1 :=
    fun n => le_csSup (hbdd n.1 n.2) ⟨X, hXn n.1⟩
  have hup : ∀ σ : ℝ, s < σ → ∃ n : {n : ℕ∞ // 1 ≤ n}, fairnessRatio (uniformCV d) n.1 ≤ σ := by
    intro σ hσ
    obtain ⟨N, hN1, hN⟩ := part2 σ hσ
    refine ⟨⟨N, by exact_mod_cast hN1⟩, csSup_le ⟨s, X, hXn _⟩ ?_⟩
    rintro r ⟨Y, hF, hR⟩
    by_contra hr
    push Not at hr
    refine hN ⟨Y, hF, fun t ht htn k hk => le_trans ?_ (hR t ht htn k hk)⟩
    have : (0 : ℝ) < t := by exact_mod_cast ht
    exact div_le_div_of_nonneg_right hr.le this.le
  haveI : Nonempty {n : ℕ∞ // 1 ≤ n} := ⟨⟨1, le_rfl⟩⟩
  have hbb : BddBelow (Set.range fun n : {n : ℕ∞ // 1 ≤ n} => fairnessRatio (uniformCV d) n.1) :=
    ⟨s, by rintro _ ⟨n, rfl⟩; exact hlow n⟩
  apply le_antisymm
  · by_contra hc
    push Not at hc
    obtain ⟨n, hn⟩ := hup ((s + ⨅ n : {n : ℕ∞ // 1 ≤ n}, fairnessRatio (uniformCV d) n.1) / 2)
      (by linarith)
    have := ciInf_le hbb n
    linarith
  · exact le_ciInf hlow
