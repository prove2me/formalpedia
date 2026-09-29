-- Prove2me | solution 1 for BlockCycleRotation.tsum_gTerm_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:36:36.729442+00:00
-- url     : https://prove2.me/submissions/1334b272-6f7c-439d-bd5e-39a07cfadfc1

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Remark21
import Theorems.Thm_BlockCycleRotation_gTerm_smul
import Mathlib

open Real Finset Filter Topology

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

/-- `cTerm` is `gTerm` restricted to coprime pairs. -/
theorem cTerm_eq_gTerm (p : ℕ × ℕ) :
    cTerm p = if Nat.gcd p.1 p.2 = 1 then gTerm p else 0 := by
  unfold cTerm gTerm
  by_cases hc : Nat.gcd p.1 p.2 = 1
  · rw [if_pos hc]
    by_cases h : 1 ≤ p.2 ∧ p.2 < p.1
    · rw [if_pos ⟨h.1, h.2, hc⟩, if_pos h]
    · rw [if_neg (by tauto), if_neg h]
  · rw [if_neg hc, if_neg (by tauto)]

theorem uTerm_pos (d : ℕ) : 0 < uTerm d := by
  unfold uTerm; positivity

/-- The support of `cTerm`. -/
theorem cTerm_ne_zero {p : ℕ × ℕ} (h : cTerm p ≠ 0) :
    1 ≤ p.2 ∧ p.2 < p.1 ∧ Nat.gcd p.1 p.2 = 1 := by
  unfold cTerm at h
  split_ifs at h with hc
  · exact hc
  · exact absurd rfl h

/-- The support of `gTerm`. -/
theorem gTerm_ne_zero {p : ℕ × ℕ} (h : gTerm p ≠ 0) : 1 ≤ p.2 ∧ p.2 < p.1 := by
  unfold gTerm at h
  split_ifs at h with hc
  · exact hc
  · exact absurd rfl h

theorem cTerm_pos {a a' : ℕ} (h1 : 1 ≤ a') (h2 : a' < a) (h3 : Nat.gcd a a' = 1) :
    0 < cTerm (a, a') := by
  unfold cTerm
  rw [if_pos ⟨h1, h2, h3⟩]
  have ha : (0 : ℝ) < (a : ℝ) := by
    have : 0 < a := by omega
    exact_mod_cast this
  have ha' : (0 : ℝ) < (a' : ℝ) := by
    have : 0 < a' := by omega
    exact_mod_cast this
  positivity

end BlockCycleRotation

open BlockCycleRotation in
/-- **The `ζ(3)` unfolding.** -/
theorem solution : ∑' p : ℕ × ℕ, gTerm p = ∑' q : ℕ × (ℕ × ℕ), uTerm q.1 * cTerm q.2:= by
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun x => ((x.1.1 + 1) * x.1.2.1, (x.1.1 + 1) * x.1.2.2)) ?_ ?_ ?_
  · -- injective
    rintro ⟨⟨d, a, a'⟩, hx⟩ ⟨⟨e, b, b'⟩, hy⟩ heq
    simp only [Function.mem_support, ne_eq] at hx hy
    have hcx : cTerm (a, a') ≠ 0 := fun h => hx (by simp [h])
    have hcy : cTerm (b, b') ≠ 0 := fun h => hy (by simp [h])
    obtain ⟨hx1, hx2, hx3⟩ := cTerm_ne_zero hcx
    obtain ⟨hy1, hy2, hy3⟩ := cTerm_ne_zero hcy
    simp only [Prod.mk.injEq] at heq
    obtain ⟨he1, he2⟩ := heq
    have hg : Nat.gcd ((d + 1) * a) ((d + 1) * a') = d + 1 := by
      rw [Nat.gcd_mul_left, hx3, Nat.mul_one]
    have hg' : Nat.gcd ((e + 1) * b) ((e + 1) * b') = e + 1 := by
      rw [Nat.gcd_mul_left, hy3, Nat.mul_one]
    have hde : d + 1 = e + 1 := by rw [← hg, ← hg', he1, he2]
    have hd : d = e := by omega
    subst hd
    have hab : a = b := Nat.eq_of_mul_eq_mul_left (by omega) he1
    have hab' : a' = b' := Nat.eq_of_mul_eq_mul_left (by omega) he2
    subst hab; subst hab'
    rfl
  · -- surjective onto the support of `gTerm`
    rintro p hp
    simp only [Function.mem_support, ne_eq] at hp
    obtain ⟨h1, h2⟩ := gTerm_ne_zero hp
    set g0 := Nat.gcd p.1 p.2 with hg0
    have hg0pos : 0 < g0 := Nat.gcd_pos_of_pos_left _ (by omega)
    have hd1 : g0 ∣ p.1 := Nat.gcd_dvd_left _ _
    have hd2 : g0 ∣ p.2 := Nat.gcd_dvd_right _ _
    set a := p.1 / g0 with ha
    set a' := p.2 / g0 with ha'
    have he1 : g0 * a = p.1 := Nat.mul_div_cancel' hd1
    have he2 : g0 * a' = p.2 := Nat.mul_div_cancel' hd2
    have hco : Nat.gcd a a' = 1 := Nat.coprime_div_gcd_div_gcd hg0pos
    have hpos1 : 1 ≤ a' := by
      rcases Nat.eq_zero_or_pos a' with h | h
      · rw [h, Nat.mul_zero] at he2; omega
      · omega
    have hlt : a' < a := by
      by_contra hc
      have : g0 * a ≤ g0 * a' := Nat.mul_le_mul_left _ (by omega)
      omega
    refine ⟨⟨(g0 - 1, (a, a')), ?_⟩, ?_⟩
    · simp only [Function.mem_support, ne_eq]
      exact ne_of_gt (mul_pos (uTerm_pos _) (cTerm_pos hpos1 hlt hco))
    · simp only [Nat.sub_add_cancel hg0pos]
      rw [he1, he2]
  · -- the values match
    rintro ⟨⟨d, a, a'⟩, hx⟩
    simp only [Function.mem_support, ne_eq] at hx
    have hcx : cTerm (a, a') ≠ 0 := fun h => hx (by simp [h])
    obtain ⟨hx1, hx2, hx3⟩ := cTerm_ne_zero hcx
    have hg : gTerm ((d + 1) * a, (d + 1) * a') = gTerm (a, a') / ((d + 1 : ℕ) : ℝ) ^ 3 :=
      gTerm_smul (by omega) hx1 hx2
    have hcg : cTerm (a, a') = gTerm (a, a') := by
      rw [cTerm_eq_gTerm, if_pos hx3]
    change gTerm ((d + 1) * a, (d + 1) * a') = uTerm d * cTerm (a, a')
    rw [hg, hcg, uTerm]
    push_cast
    ring
