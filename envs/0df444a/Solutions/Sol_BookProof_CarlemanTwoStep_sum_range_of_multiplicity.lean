-- Prove2me | solution 1 for BookProof.CarlemanTwoStep.sum_range_of_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:51:33.821118+00:00
-- url     : https://prove2.me/submissions/1274c4cd-2d84-4cd2-97fc-f1ab54ce6852

-- Generated from ChapterCarlemanTwoStep.lean — solution of BookProof.CarlemanTwoStep.sum_range_of_multiplicity
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.CarlemanTwoStep




open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}
variable {lam : (Fin d →₀ ℕ) → ℝ} {w1 w2 : Fin d → ℂ} {z : ℂ}

set_option maxHeartbeats 1000000 in

theorem solution {B : ℝ} (m : ℕ)
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B)
    (G : ℕ → Finset (Fin d →₀ ℕ))
    (hm : ∀ (a : Fin d →₀ ℕ) (M : ℕ),
      (((Finset.range M).filter (fun N => a ∈ G N)).card) ≤ m)
    (M : ℕ) : ∑ N ∈ Finset.range M, ∑ a ∈ G N, ‖u a‖ ^ 2 ≤ (m : ℝ) * B := by
  classical
  set T : Finset (Fin d →₀ ℕ) := (Finset.range M).biUnion G with hT
  have hsub : ∀ N ∈ Finset.range M, G N ⊆ T := by
    intro N hN a ha
    exact Finset.mem_biUnion.mpr ⟨N, hN, ha⟩
  have hstep1 : ∀ N ∈ Finset.range M,
      ∑ a ∈ G N, ‖u a‖ ^ 2 = ∑ a ∈ T, if a ∈ G N then ‖u a‖ ^ 2 else 0 := by
    intro N hN
    rw [← Finset.sum_filter]
    refine (Finset.sum_congr ?_ fun _ _ => rfl).symm
    ext a
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub N hN h, h⟩⟩
  have hstep2 : ∀ a : Fin d →₀ ℕ,
      ∑ N ∈ Finset.range M, (if a ∈ G N then ‖u a‖ ^ 2 else 0)
        = (((Finset.range M).filter (fun N => a ∈ G N)).card : ℝ) * ‖u a‖ ^ 2 := by
    intro a
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  calc ∑ N ∈ Finset.range M, ∑ a ∈ G N, ‖u a‖ ^ 2
      = ∑ N ∈ Finset.range M, ∑ a ∈ T, (if a ∈ G N then ‖u a‖ ^ 2 else 0) :=
        Finset.sum_congr rfl hstep1
    _ = ∑ a ∈ T, ∑ N ∈ Finset.range M, (if a ∈ G N then ‖u a‖ ^ 2 else 0) := Finset.sum_comm
    _ = ∑ a ∈ T, (((Finset.range M).filter (fun N => a ∈ G N)).card : ℝ) * ‖u a‖ ^ 2 :=
        Finset.sum_congr rfl fun a _ => hstep2 a
    _ ≤ ∑ a ∈ T, (m : ℝ) * ‖u a‖ ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast hm a M
    _ = (m : ℝ) * ∑ a ∈ T, ‖u a‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (m : ℝ) * B := by
        refine mul_le_mul_of_nonneg_left (hbes T) (by positivity)
