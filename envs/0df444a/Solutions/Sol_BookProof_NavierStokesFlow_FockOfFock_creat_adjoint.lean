-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.creat_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:44:10.771518+00:00
-- url     : https://prove2.me/submissions/d9e946d9-799f-4c5b-bddf-9aadda2c4439

-- Adapted from Leonardo Pedro, timepiece commit61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockSpace.lean
import Definitions.Def_ChapterNavierStokesFockSpace
import Mathlib
set_option autoImplicit false
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LpNat

variable {M : Type*}

private theorem add_single_sub_single (m : M) (n : Conf M) :
    (n + Finsupp.single m 1 : Conf M) - Finsupp.single m 1 = n := by
  exact add_tsub_cancel_right n _

private theorem annih_coe (m : M) (f : FockDom M) (n : Conf M) :
    (((annih m f : FockDom M) : FockL2 M) : Conf M → ℂ) n
      = (Real.sqrt (n m + 1) : ℂ) * ((f : FockL2 M) : Conf M → ℂ) (n + Finsupp.single m 1) := rfl

private theorem creat_coe (m : M) (f : FockDom M) (n : Conf M) :
    (((creat m f : FockDom M) : FockL2 M) : Conf M → ℂ) n
      = (Real.sqrt (n m) : ℂ) * ((f : FockL2 M) : Conf M → ℂ) (n - Finsupp.single m 1) := rfl

theorem solution [DecidableEq M] (m : M) (v w : FockDom M) :
    (inner ℂ ((creat m v : FockDom M) : FockL2 M) ((w : FockDom M) : FockL2 M) : ℂ)
      = inner ℂ ((v : FockDom M) : FockL2 M) ((annih m w : FockDom M) : FockL2 M) := by
  classical
  set V : Conf M → ℂ := ((v : FockL2 M) : Conf M → ℂ) with hV
  set W : Conf M → ℂ := ((w : FockL2 M) : Conf M → ℂ) with hW
  set F : Conf M → ℂ :=
    fun n => (Real.sqrt (n m) : ℂ) * (starRingEnd ℂ) (V (n - Finsupp.single m 1)) * W n with hF
  have hleft : (inner ℂ ((creat m v : FockDom M) : FockL2 M) ((w : FockDom M) : FockL2 M) : ℂ)
      = ∑' n : Conf M, F n := by
    rw [lp.inner_eq_tsum]
    refine tsum_congr fun n => ?_
    simp only [RCLike.inner_apply, creat_coe, hF, hV, hW, map_mul, Complex.conj_ofReal]
    ring
  have hright : (inner ℂ ((v : FockDom M) : FockL2 M) ((annih m w : FockDom M) : FockL2 M) : ℂ)
      = ∑' n : Conf M, F (n + Finsupp.single m 1) := by
    rw [lp.inner_eq_tsum]
    refine tsum_congr fun n => ?_
    have hm : ((n + Finsupp.single m 1 : Conf M) m : ℝ) = (n m : ℝ) + 1 := by push_cast; simp
    simp only [RCLike.inner_apply, annih_coe, hF, hV, hW, add_single_sub_single, hm]
    ring
  have hsupp : Function.support F ⊆ Set.range fun n : Conf M => n + Finsupp.single m 1 := by
    intro n hn
    simp only [Function.mem_support, hF] at hn
    have hpos : 1 ≤ n m := by
      by_contra hlt
      have hz : n m = 0 := by omega
      exact hn (by simp [hz])
    exact ⟨n - Finsupp.single m 1, sub_single_add_single hpos⟩
  rw [hleft, hright, (add_left_injective (Finsupp.single m 1)).tsum_eq hsupp]


#print axioms solution
