-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exbox_window
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:33:24.591323+00:00
-- url     : https://prove2.me/submissions/75c3cdb8-b908-44b4-914d-be900a9d3bc9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLocL
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplBox
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exbox_round_abs_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exbox_log_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exbox_sum_biUnion_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exbox_mem_ball

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
theorem _root_.solution {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (hM : 3 ≤ M) {C0 : ℝ} (hC0 : 0 < C0)
    (D : ℝ → Finset ℂ)
    (hD : ∀ (u : ℝ) (ρ : ℂ), ρ ∈ D u ↔
      (ρ ∈ Metric.closedBall ((101 / 100 : ℂ) + u * I) (2 / 15) ∧ exLF χ ρ = 0))
    (hS : ∀ u : ℝ, ((∑ ρ ∈ D u, exOrd χ ρ : ℕ) : ℝ) ≤ C0 * Real.log ((M : ℝ) * (|u| + 2)))
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, exLF χ ρ = 0 ∧ 9 / 10 ≤ ρ.re) (t : ℝ) :
    ((∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), exOrd χ ρ : ℕ) : ℝ) ≤
      30 * C0 * Real.log ((M : ℝ) * (|t| + 2)) := by
  have sub : Z.filter (fun ρ => |ρ.im - t| ≤ 1) ⊆
      (Finset.Icc (-7 : ℤ) 7).biUnion (fun k => D (t + (k : ℝ) / 7)) := by
    intro ρ hρ
    obtain ⟨hρZ, hρt⟩ := Finset.mem_filter.1 hρ
    obtain ⟨h0, h1⟩ := hZ ρ hρZ
    have hk : |round (7 * (ρ.im - t))| ≤ 7 := by
      apply exbox_round_abs_le
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 7)]
      push_cast
      linarith
    refine Finset.mem_biUnion.2 ⟨round (7 * (ρ.im - t)), Finset.mem_Icc.2 (abs_le.1 hk), ?_⟩
    refine (hD _ _).2 ⟨exbox_mem_ball χ h0 h1 ?_, h0⟩
    have h2 := abs_le.1 (abs_sub_round (7 * (ρ.im - t)))
    rw [abs_le]
    constructor <;> linarith [h2.1, h2.2]
  have h1 : (∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), exOrd χ ρ) ≤
      ∑ k ∈ Finset.Icc (-7 : ℤ) 7, ∑ ρ ∈ D (t + (k : ℝ) / 7), exOrd χ ρ :=
    (Finset.sum_le_sum_of_subset sub).trans (exbox_sum_biUnion_le _ _ _)
  have h2 : ((∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), exOrd χ ρ : ℕ) : ℝ) ≤
      ∑ k ∈ Finset.Icc (-7 : ℤ) 7, ((∑ ρ ∈ D (t + (k : ℝ) / 7), exOrd χ ρ : ℕ) : ℝ) := by
    have h3 : ((∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), exOrd χ ρ : ℕ) : ℝ) ≤
      ((∑ k ∈ Finset.Icc (-7 : ℤ) 7, ∑ ρ ∈ D (t + (k : ℝ) / 7), exOrd χ ρ : ℕ) : ℝ) := by
      exact_mod_cast h1
    refine h3.trans (le_of_eq ?_)
    rw [Nat.cast_sum]
  have h3 : ∀ k ∈ Finset.Icc (-7 : ℤ) 7, ((∑ ρ ∈ D (t + (k : ℝ) / 7), exOrd χ ρ : ℕ) : ℝ) ≤
      2 * C0 * Real.log ((M : ℝ) * (|t| + 2)) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
    have hk1' : (-7 : ℝ) ≤ k := by exact_mod_cast hk1
    have hk2' : (k : ℝ) ≤ 7 := by exact_mod_cast hk2
    have h4 : |t + (k : ℝ) / 7| ≤ |t| + 1 := by
      refine (abs_add_le _ _).trans ?_
      have : |(k : ℝ) / 7| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      linarith
    have h5 := exbox_log_le hM (abs_nonneg t) (abs_nonneg (t + (k : ℝ) / 7)) h4
    calc _ ≤ C0 * Real.log ((M : ℝ) * (|t + (k : ℝ) / 7| + 2)) := hS _
      _ ≤ C0 * (2 * Real.log ((M : ℝ) * (|t| + 2))) := mul_le_mul_of_nonneg_left h5 hC0.le
      _ = _ := by ring
  have h4 := Finset.sum_le_card_nsmul _ _ _ h3
  have h5 : (Finset.Icc (-7 : ℤ) 7).card = 15 := by simp
  rw [h5] at h4
  refine h2.trans (h4.trans (le_of_eq ?_))
  rw [nsmul_eq_mul]; push_cast; ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
