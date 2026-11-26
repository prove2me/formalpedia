-- Prove2me | solution 1 for GRH.dirichlet_nonzero_of_character_moment_cover
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T17:28:45.12059+00:00
-- url     : https://prove2.me/submissions/0177860a-c191-4d95-aaf6-a59c6b07491d

import Theorems.Thm_GRH_character_moment_uniform_prefix_bound
import Theorems.Thm_GRH_dirichlet_abel_bound_of_prefix_envelope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open GRH.CharacterMoment

private lemma bracket (D p t n v : ℕ) (hn : 0<n) (ht : 0<t)
    (lo : (v-1)^t*n^p ≤ D^t) (hi : D^t ≤ v^t*n^p) :
    ((v-1:ℕ):ℝ) ≤ (D:ℝ)*(n:ℝ)^(-((p:ℝ)/t)) ∧
      (D:ℝ)*(n:ℝ)^(-((p:ℝ)/t)) ≤ (v:ℝ) := by
  let z := (n:ℝ)^((p:ℝ)/t)
  have hz : 0 < z := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have power : z^t=(n:ℝ)^p := by
    dsimp [z]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _),div_mul_cancel₀ _
      (Nat.cast_ne_zero.mpr ht.ne'),Real.rpow_natCast]
  have l : (((v-1:ℕ):ℝ)*z)^t ≤ (D:ℝ)^t := by
    rw [mul_pow,power]
    exact_mod_cast lo
  have u : (D:ℝ)^t ≤ ((v:ℝ)*z)^t := by
    rw [mul_pow,power]
    exact_mod_cast hi
  rw [Real.rpow_neg (Nat.cast_nonneg _),← div_eq_mul_inv]
  exact ⟨(le_div_iff₀ hz).2 (le_of_pow_le_pow_left₀ ht.ne' (by positivity) l),
    (div_le_iff₀ hz).2 (le_of_pow_le_pow_left₀ ht.ne' (by positivity) u)⟩

/-- A finite convolution profile and integer power brackets exclude zeros
throughout the closed rectangle at every divisor of the witness modulus. -/
theorem solution (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ≠1)
    (a b H : ℝ) (hc : Covers d a b H) (s : ℂ) (ha : a ≤ s.re) (hb : s.re ≤ b)
    (hH : |s.im| ≤ H) : χ.LFunction s ≠ 0 := by
  obtain ⟨Q,M,R,D,S,p,t,v,w,B,u,hQ,hd,hD,hS,hp,ht,hw,hx,hrect,hprof,hR,htable,hstrict⟩ := hc
  let : NeZero Q := ⟨by omega⟩
  let ψ := DirichletCharacter.changeLevel hd χ
  have hn : ψ ≠ 1 := fun e => hχ ((DirichletCharacter.changeLevel_eq_one_iff hd).1 e)
  let x := (p:ℝ)/t
  let K := (v:ℝ)/w
  have hxp : 0 < x := div_pos (by exact_mod_cast hp) (by exact_mod_cast ht)
  have Spos : 0 < (S:ℝ) := by exact_mod_cast hS
  have Dpos : 0 < (D:ℝ) := by exact_mod_cast hD
  have wpos : 0 < (w:ℝ) := by exact_mod_cast hw
  have xs : x ≤ s.re := hx.trans ha
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have sb : ‖s‖ ≤ K*x := by
    have re := mul_self_le_mul_self (hxp.le.trans xs) hb
    have im := mul_self_le_mul_self (abs_nonneg _) hH
    rw [← sq,sq_abs] at im
    change b^2+H^2 ≤ (K*x)^2 at hrect
    nlinarith [Complex.sq_norm_sub_sq_re s,mul_nonneg hK hxp.le,norm_nonneg s]
  have disk (k : ℕ) : ‖(∑ j ∈ Finset.range k,ψ ((j+1:ℕ):ZMod Q))-1‖ ≤ (B (k%Q):ℝ)/S := by
    apply (le_div_iff₀ Spos).2
    rw [mul_comm]
    exact GRH.character_moment_uniform_prefix_bound Q S ψ hn B hprof k
  have est := GRH.dirichlet_abel_bound_of_prefix_envelope Q M ψ hn s x K ((R:ℝ)/S)
    (fun k => (B (k%Q):ℝ)/S) hxp xs ((div_le_iff₀ hxp).2 sb) (by positivity)
    (fun _ => by positivity) disk (fun k => by
      apply div_le_div_of_nonneg_right _ Spos.le
      exact_mod_cast hR ⟨k%Q,Nat.mod_lt _ (NeZero.pos Q)⟩)
  let E := (∑ k ∈ Finset.range M,(B ((k+1)%Q):ℝ)*
    (((k:ℝ)+1)^(-x)-((k:ℝ)+2)^(-x)))+(R:ℝ)*((M:ℝ)+1)^(-x)
  have factor : ‖ψ.LFunction s-1‖ ≤ K*(E/S) := by
    simpa only [E,add_div,Finset.sum_div,div_mul_eq_mul_div] using est
  have val (k : ℕ) (hk : k ≤ M) :
      ((u (k+1)-1:ℕ):ℝ) ≤ (D:ℝ)*((k:ℝ)+1)^(-x) ∧
      (D:ℝ)*((k:ℝ)+1)^(-x) ≤ (u (k+1):ℝ) := by
    obtain ⟨_,l,h,_⟩ := htable ⟨k,by omega⟩
    simpa only [Nat.cast_add,Nat.cast_one] using bracket D p t (k+1) (u (k+1))
      (by omega) ht l h
  have term (k : ℕ) (hk : k ∈ Finset.range M) :
      (D:ℝ)*((B ((k+1)%Q):ℝ)*(((k:ℝ)+1)^(-x)-((k:ℝ)+2)^(-x))) ≤
      ((B ((k+1)%Q)*(u (k+1)-(u (k+2)-1)):ℕ):ℝ) := by
    have hk' := Finset.mem_range.mp hk
    have mono := (htable ⟨k,by omega⟩).2.2.2
    change u (k+2) ≤ u (k+1) at mono
    have hsub : u (k+2)-1 ≤ u (k+1) := (Nat.sub_le _ _).trans mono
    rw [Nat.cast_mul,Nat.cast_sub hsub]
    have l := (val (k+1) (by omega)).1
    simp only [Nat.cast_add,Nat.cast_one] at l
    rw [show (k:ℝ)+1+1=(k:ℝ)+2 by ring] at l
    have hi := (val k (by omega)).2
    have bound := mul_le_mul_of_nonneg_left (sub_le_sub hi l) (Nat.cast_nonneg (α:=ℝ) (B ((k+1)%Q)))
    linarith only [bound]
  have all : (D:ℝ)*E ≤ (mass Q M R B u:ℝ) := by
    dsimp [E,mass]
    rw [mul_add,Finset.mul_sum,Nat.cast_add,Nat.cast_sum,Nat.cast_mul]
    apply add_le_add (Finset.sum_le_sum term)
    have bnd := mul_le_mul_of_nonneg_left (val M le_rfl).2 (Nat.cast_nonneg (α:=ℝ) R)
    linarith only [bnd]
  have strict : (v:ℝ)*(mass Q M R B u:ℝ) < (w:ℝ)*(D:ℝ)*(S:ℝ) := by exact_mod_cast hstrict
  have product := (mul_le_mul_of_nonneg_left all (Nat.cast_nonneg (α:=ℝ) v)).trans_lt strict
  have ordered : ((v:ℝ)*E)*(D:ℝ) < ((w:ℝ)*(S:ℝ))*(D:ℝ) := by linarith only [product]
  have lt := (mul_lt_mul_iff_left₀ Dpos).1 ordered
  have finalBound : K*(E/S) < 1 := by
    dsimp only [K]
    rw [div_mul_div_comm,div_lt_one (mul_pos wpos Spos)]
    exact lt
  intro hz
  have lift := DirichletCharacter.LFunction_changeLevel hd χ (s:=s) (.inl hχ)
  rw [hz,zero_mul] at lift
  have strictDisk := factor.trans_lt finalBound
  change ‖(DirichletCharacter.changeLevel hd χ).LFunction s-1‖ < 1 at strictDisk
  simp [lift] at strictDisk
