-- Prove2me | solution 1 for GRH.dirichlet_nonzero_of_sieved_period_cover
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T15:37:15.298916+00:00
-- url     : https://prove2.me/submissions/944a05ed-c4fc-4280-a266-8cf1de45cb8a

import Definitions.Def_GRH_DirichletPeriod
import Theorems.Thm_GRH_dirichlet_one_disk_of_initial_nonunits
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Complex GRH.DirichletPeriod

/-- A successful period test gives nonvanishing for every character of the
original level, on the entire unbounded-to-the-right rectangle. -/
theorem solution (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (a H : ℝ) (ha : 0 < a) (hH : 0 ≤ H) (hw : Covers d a H)
    (s : ℂ) (hs : a ≤ s.re) (ht : |s.im| ≤ H) : χ.LFunction s ≠ 0 := by
  obtain ⟨Q,M,hQ,hdq,hM,hgap,hnum⟩ := hw
  let : NeZero Q := ⟨by omega⟩
  let ψ := DirichletCharacter.changeLevel hdq χ
  have hψ : ψ ≠ 1 := fun e => hχ ((DirichletCharacter.changeLevel_eq_one_iff hdq).1 e)
  have hs0 := ha.trans_le hs
  have imratio : |s.im|/s.re ≤ H/a :=
    div_le_div₀ hH ht ha hs
  have normratio : ‖s‖/s.re ≤ Real.sqrt (1+(H/a)^2) := by
    have sq : (‖s‖/s.re)^2=1+(|s.im|/s.re)^2 := by
      rw [div_pow,div_pow,sq_abs]
      field_simp
      linarith [Complex.sq_norm_sub_sq_re s]
    have x : 0 ≤ |s.im|/s.re := div_nonneg (abs_nonneg _) hs0.le
    have y : 0 ≤ H/a := div_nonneg hH ha.le
    have hsq := mul_self_le_mul_self x imratio
    have rt := Real.sq_sqrt (show 0 ≤ 1+(H/a)^2 by positivity)
    nlinarith [Real.sqrt_nonneg (1+(H/a)^2)]
  have powle := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ (M:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) M]) hs
  have strict := (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) normratio)
    (show 0 ≤ (Q.totient:ℝ)/4 by positivity)).trans_lt (hnum.trans_le powle)
  have disk := GRH.dirichlet_one_disk_of_initial_nonunits Q hQ ψ hψ M hM hgap s hs0
  rw [Real.rpow_neg (show 0 ≤ (M:ℝ)+1 by positivity),← div_eq_mul_inv] at disk
  have lt1 := disk.trans_lt ((div_lt_one (Real.rpow_pos_of_pos (by positivity) _)).2 strict)
  intro zero
  have ez := DirichletCharacter.LFunction_changeLevel hdq χ (s:=s) (.inl hχ)
  rw [zero,zero_mul] at ez
  change ‖(DirichletCharacter.changeLevel hdq χ).LFunction s - 1‖ < 1 at lt1
  simp [ez] at lt1
