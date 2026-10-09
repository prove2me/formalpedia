-- Prove2me | solution 1 for BookProof.FockQuadratic.fockH_essentiallySelfAdjointOn_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:26:28.167669+00:00
-- url     : https://prove2.me/submissions/5eb5458b-2571-4a5d-ab0a-a3e6598a42a8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterFockQuadraticEsa.lean — solution of BookProof.FockQuadratic.fockH_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
import Theorems.Thm_BookProof_FockQuadratic_pairOp_symmetricOn
import Theorems.Thm_BookProof_FockQuadratic_pairOp_commForm_le
import Theorems.Thm_BookProof_FockQuadratic_freeOp_symmetricOn
import Theorems.Thm_BookProof_FockQuadratic_freeOp_norm_le
import Theorems.Thm_BookProof_FockQuadratic_freeOp_commForm
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_quadForm_nonneg
import Definitions.Def_ChapterNavierStokesIkebeKato
import Theorems.Thm_BookProof_OperatorSeries_commForm_add
import Theorems.Thm_BookProof_OperatorSeries_essentiallySelfAdjointOn_finiteModes_of_bounds
import Theorems.Thm_BookProof_OperatorSeries_seriesOp_commForm_le
import Theorems.Thm_BookProof_OperatorSeries_seriesOp_norm_le
import Theorems.Thm_BookProof_OperatorSeries_seriesOp_symmetricOn
open BookProof.FockQuadratic



open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

variable {ι : Type*}

variable {ι : Type*}
variable {ω : ι → ℝ}
variable {κ : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (hω : ∀ i, 0 ≤ ω i) (P Q : κ → Idx ι) (g : κ → ℂ)
    (hPQ : ∀ k, deg (P k) + deg (Q k) ≤ 2)
    (hsum : Summable fun k => ‖g k‖ * (wsum ω (P k) + wsum ω (Q k) + 2)) :
    EssentiallySelfAdjointOn (lpFiniteModes (Idx ι))
      ((fockH hω P Q g hPQ hsum).comp
        (Submodule.inclusion (finiteModes_le_maxDom (sig ω)))) := by

  classical
  have hc0 : ∀ b : Idx ι, 0 ≤ sig ω b := fun b => sig_nonneg hω b
  set T : κ → (maxDom (sig ω) →ₗ[ℂ] L2I (Idx ι)) :=
    fun k => pairOp hω (g k) (P k) (Q k) (hPQ k) with hT
  set A : κ → ℝ := fun k => 4 * ‖g k‖ with hAdef
  have hnorm : ∀ (k : κ) (x : maxDom (sig ω)),
      ‖(T k x : L2I (Idx ι))‖ ≤ A k * ‖(diagMax (sig ω) x : L2I (Idx ι))‖ :=
    fun k x => pairOp_norm_le hω (g k) (P k) (Q k) (hPQ k) x
  have hA : Summable A := by
    refine Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => ?_) (hsum.mul_left 4)
    have h1 : (0 : ℝ) ≤ wsum ω (P k) := wsum_nonneg hω _
    have h2 : (0 : ℝ) ≤ wsum ω (Q k) := wsum_nonneg hω _
    have h3 : (0 : ℝ) ≤ ‖g k‖ := norm_nonneg _
    nlinarith
  have hfock : fockH hω P Q g hPQ hsum = freeOp hω + seriesOp T A hnorm hA := rfl
  set B : κ → ℝ := fun k => 4 * ‖g k‖ * (wsum ω (P k) + wsum ω (Q k) + 2) with hBdef
  have hB0 : ∀ k, 0 ≤ B k := by
    intro k
    have h1 : (0 : ℝ) ≤ wsum ω (P k) := wsum_nonneg hω _
    have h2 : (0 : ℝ) ≤ wsum ω (Q k) := wsum_nonneg hω _
    have h3 : (0 : ℝ) ≤ ‖g k‖ := norm_nonneg _
    simp only [hBdef]
    positivity
  have hBsum : Summable B := by
    have := hsum.mul_left 4
    refine this.congr fun k => ?_
    simp only [hBdef]
    ring
  have hcomm : ∀ (k : κ) (x : maxDom (sig ω)),
      |commForm (T k) (diagMax (sig ω)) x| ≤ B k * quadForm (diagMax (sig ω)) x := by
    intro k x
    have h := pairOp_commForm_le hω (g k) (P k) (Q k) (hPQ k) x
    simpa [hBdef, hT, mul_assoc] using h
  rw [hfock]
  refine essentiallySelfAdjointOn_finiteModes_of_bounds (sig ω) hc0 _
    (1 + ∑' k, A k) (∑' k, B k) (tsum_nonneg hB0) ?_ ?_ ?_
  · intro x y
    have h1 := freeOp_symmetricOn hω x y
    have h2 := seriesOp_symmetricOn hnorm hA
      (fun k => pairOp_symmetricOn hω (g k) (P k) (Q k) (hPQ k)) x y
    simp only [LinearMap.add_apply, inner_add_left, inner_add_right, h1, h2]
  · intro x
    have h1 := freeOp_norm_le hω x
    have h2 := seriesOp_norm_le hnorm hA x
    have hn : (0 : ℝ) ≤ ‖(diagMax (sig ω) x : L2I (Idx ι))‖ := norm_nonneg _
    have hadd : ‖((freeOp hω + seriesOp T A hnorm hA) x : L2I (Idx ι))‖
        ≤ ‖(freeOp hω x : L2I (Idx ι))‖ + ‖(seriesOp T A hnorm hA x : L2I (Idx ι))‖ := by
      simpa only [LinearMap.add_apply] using
        norm_add_le (freeOp hω x : L2I (Idx ι)) (seriesOp T A hnorm hA x : L2I (Idx ι))
    nlinarith [hadd, h1, h2]
  · intro x
    have hq : 0 ≤ quadForm (diagMax (sig ω)) x := diagMax_quadForm_nonneg (sig ω) hc0 x
    have hsplit := commForm_add (freeOp hω) (seriesOp T A hnorm hA) (diagMax (sig ω)) x
    have hfree := freeOp_commForm hω x
    have hser := seriesOp_commForm_le hnorm hA hBsum hcomm
      (fun y => diagMax_quadForm_nonneg (sig ω) hc0 y) x
    rw [hsplit, hfree, zero_add]
    exact hser
