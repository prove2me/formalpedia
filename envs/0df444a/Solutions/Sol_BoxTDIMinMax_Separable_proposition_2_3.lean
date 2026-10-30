-- Prove2me | solution 1 for BoxTDIMinMax.Separable.proposition_2_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:11:19.437333+00:00
-- url     : https://prove2.me/submissions/272750e2-eadb-43f5-bb9a-7667213996af

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting

open Matrix BoxTDIMinMax.Separable

namespace BoxTDIMinMax.Separable.Prop23Aux

theorem dualObj_sub {κ : Type*} [Fintype κ] (b d : κ → ℚ) (y : κ → ℝ) :
    dualObj (b - d) y = dualObj b y - ∑ i, y i * (d i : ℝ) := by
  unfold dualObj
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.sub_apply, Rat.cast_sub]
  ring

theorem feas_mulVec {κ S : Type*} [Fintype κ] [Fintype S] (M : Matrix κ S ℚ) (c : S → ℤ)
    (y : κ → ℝ) (hy : y ∈ DualFeas M c) (z : S → ℚ) :
    ∑ i, y i * (((M *ᵥ z) i : ℚ) : ℝ) = ∑ s, (c s : ℝ) * (z s : ℝ) := by
  obtain ⟨_, h1⟩ := hy
  have hc : ∀ s, (c s : ℝ) = ∑ i, y i * (M i s : ℝ) := by
    intro s
    have := congrFun h1 s
    simp only [vecMul, dotProduct, Matrix.map_apply] at this
    exact this.symm
  simp only [mulVec, dotProduct, Rat.cast_sum, Rat.cast_mul]
  simp_rw [hc, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

end BoxTDIMinMax.Separable.Prop23Aux

open BoxTDIMinMax.Separable.Prop23Aux in
theorem solution {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
    (Q : Matrix ι S ℤ) (p : ι → ℤ) (hbox : IsBoxTDI (ratMat Q) (ratVec p))
    (zStar : S → ℚ) :
    IsBoxTDI (ratMat Q) (ratVec p - ratMat Q *ᵥ zStar) := by
  intro f g hfg c hfe hbdd
  set A := ratMat Q
  have hrhs : boxRhs (ratVec p - A *ᵥ zStar) f g =
      boxRhs (ratVec p) (f + zStar) (g + zStar) - boxMat A *ᵥ zStar := by
    funext r
    rcases r with i | s | s
    · simp [boxRhs, boxMat, Matrix.fromRows_mulVec]
    · simp [boxRhs, boxMat, Matrix.fromRows_mulVec]
    · simp [boxRhs, boxMat, Matrix.fromRows_mulVec, Matrix.neg_mulVec]
  have hT := hbox (f + zStar) (g + zStar) (fun s => by
    simp only [Pi.add_apply]; linarith [hfg s])
  set K : ℝ := ∑ s, (c s : ℝ) * (zStar s : ℝ)
  have hobj : ∀ y ∈ DualFeas (boxMat A) c,
      dualObj (boxRhs (ratVec p - A *ᵥ zStar) f g) y =
        dualObj (boxRhs (ratVec p) (f + zStar) (g + zStar)) y - K := by
    intro y hy
    rw [hrhs, dualObj_sub, feas_mulVec _ c y hy]
  obtain ⟨B, hB⟩ := hbdd
  have hbdd1 : BddAbove (dualObj (boxRhs (ratVec p) (f + zStar) (g + zStar)) ''
      DualFeas (boxMat A) c) := by
    refine ⟨B + K, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have := hB ⟨y, hy, rfl⟩
    rw [hobj y hy] at this
    linarith
  obtain ⟨y, hyF, hyopt⟩ := hT c hfe hbdd1
  refine ⟨y, hyF, fun y' hy' => ?_⟩
  rw [hobj y' hy', hobj _ hyF]
  linarith [hyopt y' hy']
