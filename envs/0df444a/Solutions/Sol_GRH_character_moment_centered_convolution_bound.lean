-- Prove2me | solution 1 for GRH.character_moment_centered_convolution_bound
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T17:27:15.524074+00:00
-- url     : https://prove2.me/submissions/bfa3a44b-3065-487e-b3fd-c5043249f7aa

import Definitions.Def_GRH_CharacterMoment
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open GRH.CharacterMoment

private noncomputable def value {q : ℕ} (χ : DirichletCharacter ℂ q) (U : Finset ℕ) (f : ℕ → ℕ) : ℂ :=
  ∑ a ∈ U, (f a:ℂ)*χ (a:ZMod q)

private lemma square_value {q : ℕ} (χ : DirichletCharacter ℂ q) (U : Finset ℕ)
    (iv f : ℕ → ℕ) (h : Permutes q U iv) :
    value χ U (square q U iv f) = (value χ U f)^2 := by
  have inner (a : ℕ) (ha : a ∈ U) :
      (∑ k ∈ U,(f (iv a*k%q):ℂ)*χ (k:ZMod q)) = χ (a:ZMod q)*value χ U f := by
    dsimp [value]
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_nbij' (i:=fun b : ℕ => a*b%q) (j:=fun k : ℕ => iv a*k%q)
      (fun b hb => (h a ha b hb).1) (fun k hk => (h a ha k hk).2.1)
      (fun b hb => (h a ha b hb).2.2.1) (fun k hk => (h a ha k hk).2.2.2) ?_
    intro b hb
    rw [(h a ha b hb).2.2.1,ZMod.natCast_mod,Nat.cast_mul,map_mul]
    ring
  dsimp only [value,square]
  simp only [Nat.cast_sum,Nat.cast_mul,Finset.sum_mul]
  rw [Finset.sum_comm,pow_two,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  calc _ = (f a:ℂ)*∑ k ∈ U, (f (iv a*k%q):ℂ)*χ (k:ZMod q) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
       _ = _ := by rw [inner a ha]; dsimp [value]; ring

/-- The Fourier coefficient of each convolution row is the square of the
preceding coefficient. Subtracting a constant from the last row bounds
its coefficient by the sum of the absolute integer deviations. -/
theorem solution (q : ℕ) (χ : DirichletCharacter ℂ q) (U : Finset ℕ)
    (iv f : ℕ → ℕ) (rows : List (Array ℕ)) (c : ℕ) (hp : Permutes q U iv)
    (hz : ∑ a ∈ U, χ (a:ZMod q) = 0) (hrows : Rows q U iv f rows) :
    ‖∑ a ∈ U, (f a:ℂ)*χ (a:ZMod q)‖^(2^rows.length) ≤ (deviation U (lastRow f rows) c:ℝ) := by
  have power (F : ℕ → ℕ) (rs : List (Array ℕ)) (hr : Rows q U iv F rs) :
      (value χ U F)^(2^rs.length) = value χ U (lastRow F rs) := by
    induction rs generalizing F with
    | nil => simp [lastRow]
    | cons x xs ih =>
      have equal : value χ U (read x) = (value χ U F)^2 := by
        rw [← square_value χ U iv F hp]
        exact Finset.sum_congr rfl (fun k hk => by rw [hr.1 k hk])
      rw [List.length_cons,pow_succ, Nat.mul_comm, pow_mul,← equal]
      exact ih _ hr.2
  let g := lastRow f rows
  have changeCenter : value χ U g = ∑ a ∈ U, ((g a:ℂ)-(c:ℂ))*χ (a:ZMod q) := by
    dsimp only [value]
    simp only [sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum,hz,mul_zero,sub_zero]
  change ‖value χ U f‖^(2^rows.length) ≤ _
  rw [← norm_pow,power f rows hrows]
  change ‖value χ U g‖ ≤ (deviation U g c:ℝ)
  rw [changeCenter]
  apply (norm_sum_le _ _).trans
  simp only [deviation,Nat.cast_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left (χ.norm_le_one _) (norm_nonneg _)).trans
  rw [mul_one,← Complex.ofReal_natCast,← Complex.ofReal_natCast,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs]
  by_cases h : c ≤ g k
  · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h)),
      Nat.sub_eq_zero_of_le h,add_zero,Nat.cast_sub h]
  · have h' := Nat.le_of_not_ge h
    rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h')),Nat.sub_eq_zero_of_le h',
      zero_add,Nat.cast_sub h']
    linarith
