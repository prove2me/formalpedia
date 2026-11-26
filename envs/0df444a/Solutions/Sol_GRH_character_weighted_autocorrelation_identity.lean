-- Prove2me | solution 1 for GRH.character_weighted_autocorrelation_identity
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T17:44:16.024617+00:00
-- url     : https://prove2.me/submissions/7babe2b5-52d4-4d2d-b029-4c8e9f881a21

import Definitions.Def_GRH_CharacterMoment
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic.Ring

open GRH.CharacterMoment Complex
open scoped ComplexConjugate

private noncomputable def valχ {q : ℕ} (χ : DirichletCharacter ℂ q) (U : Finset ℕ)
    (f : ℕ → ℕ) := ∑ b ∈ U,(f b:ℂ)*χ (b:ZMod q)

private lemma correlation (q : ℕ) (χ : DirichletCharacter ℂ q) (U : Finset ℕ)
    (iv f : ℕ → ℕ) (hp : Permutes q U iv) (hu : ∀ b ∈ U, IsUnit (b:ZMod q)) :
    (∑ k ∈ U, ((∑ b ∈ U, f b*f (b*k%q):ℕ):ℂ)*χ (k:ZMod q)) =
       ((‖valχ χ U f‖^2:ℝ):ℂ) := by
  have inner (b : ℕ) (hb : b∈U) :
      (∑ k ∈ U,(f (b*k%q):ℂ)*χ (k:ZMod q)) = conj (χ (b:ZMod q))*valχ χ U f := by
    have norm : ‖χ (b:ZMod q)‖=1 := χ.unit_norm_eq_one (hu b hb).unit
    have cancel : conj (χ (b:ZMod q))*χ (b:ZMod q)=1 := by rw [mul_comm,Complex.mul_conj',norm]; norm_num
    dsimp [valχ]
    rw [Finset.mul_sum]
    refine Finset.sum_nbij' (i:=fun k : ℕ => b*k%q) (j:=fun k : ℕ => iv b*k%q)
      (fun k hk => (hp b hb k hk).1) (fun k hk => (hp b hb k hk).2.1)
      (fun k hk => (hp b hb k hk).2.2.1) (fun k hk => (hp b hb k hk).2.2.2) ?_
    intro k _
    rw [ZMod.natCast_mod,Nat.cast_mul,map_mul]
    calc _ = (conj (χ (b:ZMod q))*χ (b:ZMod q))*((f (b*k%q):ℂ)*χ (k:ZMod q)) := by rw [cancel,one_mul]
         _ = _ := by ring
  simp only [Nat.cast_sum,Nat.cast_mul,Finset.sum_mul]
  rw [Finset.sum_comm]
  calc _ = (∑ b ∈ U, (f b:ℂ)*conj (χ (b:ZMod q)))*valχ χ U f := by
             rw [Finset.sum_mul]
             apply Finset.sum_congr rfl
             intro b hb
             calc _ = (f b:ℂ)*∑ k ∈ U,(f (b*k%q):ℂ)*χ (k:ZMod q) := by
                        rw [Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro k _
                        ring
                  _ = _ := by rw [inner b hb]; ring
       _ = _ := by
         have conjval : conj (valχ χ U f)=∑ b ∈ U,(f b:ℂ)*conj (χ (b:ZMod q)) := by
           simp [valχ]
         rw [← conjval,mul_comm,Complex.mul_conj',Complex.ofReal_pow]

/-- The combined quotient-product counts evaluate to a positive weighted
sum of squared Fourier coefficients at the same Dirichlet character. -/
theorem solution (q : ℕ) (χ : DirichletCharacter ℂ q) (I U : Finset ℕ)
    (iv v : ℕ → ℕ) (f : ℕ → ℕ → ℕ) (hp : Permutes q U iv)
    (hu : ∀ b ∈ U, IsUnit (b:ZMod q)) :
    (∑ k ∈ U, ((∑ i ∈ I,v i*(∑ b ∈ U,f i b*f i (b*k%q)) : ℕ):ℂ)*χ (k:ZMod q)) =
      ((∑ i ∈ I,(v i:ℝ)*‖∑ b ∈ U,(f i b:ℂ)*χ (b:ZMod q)‖^2 : ℝ):ℂ) := by
  simp only [Nat.cast_sum,Nat.cast_mul,Finset.sum_mul,Complex.ofReal_sum,Complex.ofReal_mul,
    Complex.ofReal_natCast]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc _ = (v i:ℂ)*∑ k ∈ U,((∑ b ∈ U,f i b*f i (b*k%q):ℕ):ℂ)*χ (k:ZMod q) := by
             rw [Finset.mul_sum]
             simp only [Nat.cast_sum,Nat.cast_mul]
             apply Finset.sum_congr rfl
             intro k _
             ring
       _ = _ := by rw [correlation q χ U iv (f i) hp hu]; rfl
