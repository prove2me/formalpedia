-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:43:13.330823+00:00
-- url     : https://prove2.me/submissions/6a6d8637-f546-410c-89cb-171787052bcf

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLocL
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplBox
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exbox_round_abs_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exbox_log_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exbox_log_nonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exbox_sum_biUnion_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exbox_mem_ball
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exbox_window
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exOrd_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_local


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (T : ℝ), 3 ≤ M → 0 ≤ T →
    ∃ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ (exLF χ ρ = 0 ∧ 9 / 10 ≤ ρ.re ∧ |ρ.im| ≤ T)) ∧
      (∀ t : ℝ, ((∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), exOrd χ ρ : ℕ) : ℝ) ≤
        C * Real.log ((M : ℝ) * (|t| + 2))) ∧
      (Z.card : ℝ) ≤ C * (T + 1) * Real.log ((M : ℝ) * (T + 2)) := by
  obtain ⟨C0, hC0, hloc⟩ := ex_local
  refine ⟨180 * C0, by positivity, ?_⟩
  intro M _ χ T hM hT
  choose D hD hS _ using fun t : ℝ => hloc M χ t hM
  obtain ⟨N, hN⟩ : ∃ N : ℤ, N = ⌈T⌉ := ⟨_, rfl⟩
  have hTN : T ≤ N := by rw [hN]; exact Int.le_ceil T
  have hNT : (N : ℝ) < T + 1 := by rw [hN]; exact Int.ceil_lt_add_one T
  have hN0 : 0 ≤ N := by rw [hN]; exact Int.ceil_nonneg hT
  obtain ⟨Z, hZdef⟩ : ∃ Z : Finset ℂ, Z = ((Finset.Icc (-(7 * N)) (7 * N)).biUnion
      (fun k => D ((k : ℝ) / 7))).filter (fun ρ => exLF χ ρ = 0 ∧ 9 / 10 ≤ ρ.re ∧ |ρ.im| ≤ T) := ⟨_, rfl⟩
  have hZmem : ∀ ρ : ℂ, ρ ∈ Z ↔ (exLF χ ρ = 0 ∧ 9 / 10 ≤ ρ.re ∧ |ρ.im| ≤ T) := by
    intro ρ
    rw [hZdef]
    constructor
    · intro h
      exact (Finset.mem_filter.1 h).2
    · rintro ⟨h0, h1, h2⟩
      refine Finset.mem_filter.2 ⟨?_, h0, h1, h2⟩
      have hk : |round (7 * ρ.im)| ≤ 7 * N := by
        apply exbox_round_abs_le
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 7)]
        push_cast
        linarith
      refine Finset.mem_biUnion.2 ⟨round (7 * ρ.im), Finset.mem_Icc.2 (abs_le.1 hk), ?_⟩
      refine (hD _ _).2 ⟨exbox_mem_ball χ h0 h1 ?_, h0⟩
      have h3 := abs_le.1 (abs_sub_round (7 * ρ.im))
      rw [abs_le]
      constructor <;> linarith [h3.1, h3.2]
  have hZ' : ∀ ρ ∈ Z, exLF χ ρ = 0 ∧ 9 / 10 ≤ ρ.re :=
    fun ρ h => ⟨((hZmem ρ).1 h).1, ((hZmem ρ).1 h).2.1⟩
  have hW := exbox_window χ hM hC0 D hD hS Z hZ'
  refine ⟨Z, hZmem, ?_, ?_⟩
  · intro t
    have hL := exbox_log_nonneg hM (abs_nonneg t)
    refine (hW t).trans ?_
    have h1 : 0 ≤ C0 * Real.log ((M : ℝ) * (|t| + 2)) := mul_nonneg hC0.le hL
    nlinarith
  · have hL := exbox_log_nonneg hM hT
    have sub : Z ⊆ (Finset.Icc (-N) N).biUnion
        (fun j => Z.filter (fun ρ => |ρ.im - (j : ℝ)| ≤ 1)) := by
      intro ρ hρ
      obtain ⟨h0, h1, h2⟩ := (hZmem ρ).1 hρ
      have hk : |round ρ.im| ≤ N := exbox_round_abs_le _ _ (h2.trans hTN)
      refine Finset.mem_biUnion.2 ⟨round ρ.im, Finset.mem_Icc.2 (abs_le.1 hk), ?_⟩
      refine Finset.mem_filter.2 ⟨hρ, ?_⟩
      have h3 := abs_sub_round ρ.im
      linarith
    have h1 : Z.card ≤ ∑ ρ ∈ Z, exOrd χ ρ := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum (fun ρ h => exOrd_pos χ (hZ' ρ h).1)
    have h2 : Z.card ≤ ∑ j ∈ Finset.Icc (-N) N,
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im - (j : ℝ)| ≤ 1), exOrd χ ρ :=
      h1.trans ((Finset.sum_le_sum_of_subset sub).trans (exbox_sum_biUnion_le _ _ _))
    have h3 : (Z.card : ℝ) ≤ ∑ j ∈ Finset.Icc (-N) N,
        ((∑ ρ ∈ Z.filter (fun ρ => |ρ.im - (j : ℝ)| ≤ 1), exOrd χ ρ : ℕ) : ℝ) := by
      have h4 : (Z.card : ℝ) ≤ ((∑ j ∈ Finset.Icc (-N) N,
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im - (j : ℝ)| ≤ 1), exOrd χ ρ : ℕ) : ℝ) := by
        exact_mod_cast h2
      refine h4.trans (le_of_eq ?_)
      rw [Nat.cast_sum]
    have h4 : ∀ j ∈ Finset.Icc (-N) N,
        ((∑ ρ ∈ Z.filter (fun ρ => |ρ.im - (j : ℝ)| ≤ 1), exOrd χ ρ : ℕ) : ℝ) ≤
          60 * C0 * Real.log ((M : ℝ) * (T + 2)) := by
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
      have hj1' : -(N : ℝ) ≤ j := by exact_mod_cast hj1
      have hj2' : (j : ℝ) ≤ N := by exact_mod_cast hj2
      have h5 : |(j : ℝ)| ≤ T + 1 := by
        rw [abs_le]
        constructor <;> linarith
      have h6 := exbox_log_le hM hT (abs_nonneg (j : ℝ)) h5
      calc _ ≤ 30 * C0 * Real.log ((M : ℝ) * (|(j : ℝ)| + 2)) := hW j
        _ ≤ 30 * C0 * (2 * Real.log ((M : ℝ) * (T + 2))) :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
        _ = _ := by ring
    have h5 := Finset.sum_le_card_nsmul _ _ _ h4
    have hc : ((Finset.Icc (-N) N).card : ℝ) = 2 * N + 1 := by
      rw [Int.card_Icc]
      have h6 : ((N + 1 - -N).toNat : ℤ) = 2 * N + 1 := by
        rw [Int.toNat_of_nonneg (by omega)]
        ring
      exact_mod_cast h6
    rw [nsmul_eq_mul, hc] at h5
    refine h3.trans (h5.trans ?_)
    have h7 : 0 ≤ C0 * Real.log ((M : ℝ) * (T + 2)) := mul_nonneg hC0.le hL
    have h8 : (2 * (N : ℝ) + 1) ≤ 3 * (T + 1) := by linarith
    calc (2 * (N : ℝ) + 1) * (60 * C0 * Real.log ((M : ℝ) * (T + 2)))
        = (2 * (N : ℝ) + 1) * (60 * (C0 * Real.log ((M : ℝ) * (T + 2)))) := by ring
      _ ≤ (3 * (T + 1)) * (60 * (C0 * Real.log ((M : ℝ) * (T + 2)))) :=
          mul_le_mul_of_nonneg_right h8 (by positivity)
      _ = 180 * C0 * (T + 1) * Real.log ((M : ℝ) * (T + 2)) := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
