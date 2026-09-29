-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.ccr_same
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:44:12.634068+00:00
-- url     : https://prove2.me/submissions/e00122af-a9bd-4159-8e2b-49779018a625

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

theorem solution [DecidableEq M] (m : M) :
    (annih m).comp (creat m) - (creat m).comp (annih m)
      = LinearMap.id (R := ℂ) (M := FockDom M) := by
  ext f n
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
    Submodule.coe_sub, Pi.sub_apply, annih_coe, creat_coe, lp.coeFn_sub]
  have h1 : ((n + Finsupp.single m 1 : Conf M) m : ℝ) = (n m : ℝ) + 1 := by push_cast; simp
  have h2 : (n + Finsupp.single m 1 : Conf M) - Finsupp.single m 1 = n :=
    add_single_sub_single m n
  rw [h1, h2]
  rcases Nat.eq_zero_or_pos (n m) with h | h
  · simp [h]
  · have h3 : ((n - Finsupp.single m 1 : Conf M) m : ℝ) + 1 = (n m : ℝ) := by
      have : (n - Finsupp.single m 1 : Conf M) m = n m - 1 := by simp
      rw [this]
      have : (1 : ℕ) ≤ n m := h
      push_cast [Nat.cast_sub this]
      ring
    have h4 : (n - Finsupp.single m 1 : Conf M) + Finsupp.single m 1 = n :=
      sub_single_add_single h
    rw [h3, h4]
    have hsq : (Real.sqrt ((n m : ℝ) + 1) : ℂ) * (Real.sqrt ((n m : ℝ) + 1) : ℂ)
        = ((n m : ℝ) + 1 : ℝ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    have hsq2 : (Real.sqrt (n m : ℝ) : ℂ) * (Real.sqrt (n m : ℝ) : ℂ) = ((n m : ℝ) : ℝ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    have hexp : ∀ z : ℂ, (Real.sqrt ((n m : ℝ) + 1) : ℂ) * ((Real.sqrt ((n m : ℝ) + 1) : ℂ) * z)
        - (Real.sqrt (n m : ℝ) : ℂ) * ((Real.sqrt (n m : ℝ) : ℂ) * z) = z := by
      intro z
      rw [← mul_assoc, ← mul_assoc, hsq, hsq2]
      push_cast
      ring
    exact hexp _


#print axioms solution
