-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.NMul.key_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:43:10.461536+00:00
-- url     : https://prove2.me/submissions/a1bfdaa5-4ec4-4a97-ad2c-069f333ac576

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormMul
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_blockDeg_add
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_bweight_pos
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_bweight_add
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_comb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.NMul
namespace Formalism.NormUnitaryCountingLemmas.NMul
theorem _root_.solution {N n : ℕ} {ν : Fin N → ℕ} {F G : MvPolynomial (Fin N × Fin n) ℂ}
    (hF : ∀ a ∈ F.support, ∀ j, blockDeg a j = ν j) (c : Fin N × Fin n →₀ ℕ) :
    ‖∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
        coeff p.1 F * coeff p.2 G‖ ^ 2 * bweight c ≤
      ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
        (‖coeff p.1 F‖ ^ 2 * bweight p.1) * (‖coeff p.2 G‖ ^ 2 * bweight p.2) := by
  classical
  rcases ((F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c)).eq_empty_or_nonempty
    with hA | hA
  · simp [hA]
  have hmem : ∀ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      p.1 ∈ F.support ∧ p.2 ∈ G.support ∧ p.1 + p.2 = c := by
    intro p hp
    rw [mem_filter, mem_product] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2⟩
  have hDpos : 0 < Dc ν c := by
    obtain ⟨p0, hp0⟩ := hA
    obtain ⟨h1, _, h3⟩ := hmem p0 hp0
    refine prod_pos fun j _ => ?_
    have : ν j ≤ blockDeg c j := by
      rw [← h3, ← hF _ h1 j, blockDeg_add]
      exact Nat.le_add_right _ _
    exact_mod_cast Nat.choose_pos this
  have hPpos : ∀ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      0 < Pc c p.1 := by
    intro p hp
    obtain ⟨_, _, h3⟩ := hmem p hp
    refine prod_pos fun j _ => prod_pos fun k _ => ?_
    have : p.1 (j, k) ≤ c (j, k) := by
      rw [← h3]
      simp
    exact_mod_cast Nat.choose_pos this
  have hW : ∀ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      bweight c = bweight p.1 * bweight p.2 * Pc c p.1 / Dc ν c := by
    intro p hp
    obtain ⟨h1, _, h3⟩ := hmem p hp
    have := bweight_add p.1 p.2
    rw [h3] at this
    have e : ∏ j, ((blockDeg c j).choose (blockDeg p.1 j) : ℝ) = Dc ν c :=
      prod_congr rfl fun j _ => by rw [hF _ h1 j]
    rw [e] at this
    rw [eq_div_iff hDpos.ne']
    exact this
  have hsumP : ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c), Pc c p.1 ≤
      Dc ν c := by
    have := comb ν F.support G.support hF c
    unfold Pc Dc
    exact_mod_cast this
  have hgpos : ∀ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      0 < Pc c p.1 / Dc ν c := fun p hp => div_pos (hPpos p hp) hDpos
  have hsumg : ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      Pc c p.1 / Dc ν c ≤ 1 := by
    rw [← sum_div, div_le_one hDpos]
    exact hsumP
  have hsumgpos : 0 < ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      Pc c p.1 / Dc ν c := sum_pos hgpos hA
  have hsed := sq_sum_div_le_sum_sq_div _ (fun p => ‖coeff p.1 F * coeff p.2 G‖) hgpos
  have h1 : ‖∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
        coeff p.1 F * coeff p.2 G‖ ^ 2 ≤
      ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
        ‖coeff p.1 F * coeff p.2 G‖ ^ 2 / (Pc c p.1 / Dc ν c) := by
    calc _ ≤ (∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
          ‖coeff p.1 F * coeff p.2 G‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := le_div_self (sq_nonneg _) hsumgpos hsumg
      _ ≤ _ := hsed
  calc _ ≤ (∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
        ‖coeff p.1 F * coeff p.2 G‖ ^ 2 / (Pc c p.1 / Dc ν c)) * bweight c :=
        mul_le_mul_of_nonneg_right h1 (bweight_pos c).le
    _ = _ := by
      rw [sum_mul]
      refine sum_congr rfl fun p hp => ?_
      have hP := hPpos p hp
      rw [hW p hp, norm_mul]
      field_simp
end Formalism.NormUnitaryCountingLemmas.NMul
