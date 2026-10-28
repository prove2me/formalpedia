-- Prove2me | solution 1 for D1Bound5.QuadInt.mem_disk_iff
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T22:59:16.020782+00:00
-- url     : https://prove2.me/submissions/d6c3ff6f-5070-4e07-992d-aafdead8242a

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Theorems.Thm_D1Bound5_QuadInt_four_norm

section
namespace D1Bound5.QuadInt

variable {tau nu : ℤ}

/-- A squared integer bound implies the corresponding exact integer
square-root bound; no floating-point approximation is used. -/
theorem abs_le_int_sqrt_of_sq_le {a n : ℤ} (h : a^2 ≤ n) : |a| ≤ Int.sqrt n := by
  have hn : 0 ≤ n := (sq_nonneg a).trans h
  have hc : (a.natAbs : ℤ)^2 ≤ (n.toNat : ℤ) := by
    simpa only [Int.natCast_natAbs, sq_abs, Int.toNat_of_nonneg hn] using h
  have hnat : a.natAbs^2 ≤ n.toNat := by exact_mod_cast hc
  rw [← Int.natCast_natAbs, Int.sqrt]
  exact_mod_cast (Nat.le_sqrt'.mpr hnat)



/-- Exact completeness and soundness of disk enumeration. This is valid
for every integer cutoff, including an empty negative-cutoff disk. -/
theorem _root_.solution (hd : 0 < discriminant tau nu) (M : ℤ) (z : QuadInt tau nu) :
    z ∈ disk tau nu M ↔ z.norm ≤ M := by
  constructor
  · intro hz
    unfold disk at hz
    obtain ⟨⟨e,f⟩, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨_, hpar, hbound⟩ := Finset.mem_filter.mp hp
    dsimp only at hpar hbound
    have he : 2*((e-tau*f)/2)+tau*f = e := by omega
    have hN := four_norm (⟨(e-tau*f)/2,f⟩ : QuadInt tau nu)
    change 4*(⟨(e-tau*f)/2,f⟩ : QuadInt tau nu).norm =
      (2*((e-tau*f)/2)+tau*f)^2+discriminant tau nu*f^2 at hN
    rw [he] at hN
    change (⟨(e-tau*f)/2,f⟩ : QuadInt tau nu).norm ≤ M
    omega
  · intro hz
    let e := 2*z.re+tau*z.im
    have hsum : e^2+discriminant tau nu*z.im^2 ≤ 4*M := by
      have hN := four_norm z
      change 4*z.norm = e^2+discriminant tau nu*z.im^2 at hN
      omega
    have he : e^2 ≤ 4*M := by
      have hpos := mul_nonneg hd.le (sq_nonneg z.im)
      nlinarith only [hsum, hpos]
    have hf : z.im^2 ≤ 4*M := by
      have hmul := mul_le_mul_of_nonneg_right (show 1 ≤ discriminant tau nu by omega)
        (sq_nonneg z.im)
      nlinarith only [hsum, hmul, sq_nonneg e]
    have heb := abs_le.mp (abs_le_int_sqrt_of_sq_le he)
    have hfb := abs_le.mp (abs_le_int_sqrt_of_sq_le hf)
    unfold disk
    apply Finset.mem_image.mpr
    refine ⟨(e,z.im), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr heb, Finset.mem_Icc.mpr hfb⟩, ?_, hsum⟩
      dsimp only [e]
      omega
    · apply QuadraticAlgebra.ext
      · change (e-tau*z.im)/2 = z.re
        dsimp only [e]
        omega
      · rfl





end D1Bound5.QuadInt
end
