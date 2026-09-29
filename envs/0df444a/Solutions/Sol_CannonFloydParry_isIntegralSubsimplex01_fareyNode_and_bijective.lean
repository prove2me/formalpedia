-- Prove2me | solution 1 for CannonFloydParry.isIntegralSubsimplex01_fareyNode_and_bijective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T20:53:24.028265+00:00
-- url     : https://prove2.me/submissions/64c5ac2c-6d6d-4a79-8819-713333b7a338

import Definitions.Def_CannonFloydParry_PIP
import Theorems.Thm_CannonFloydParry_isIntegralSubsimplex01_iff

/-!
# Farey intervals and integral projective maps of `[0,1]` (CFP §7, pp. 251–253)

Basic facts: the action of `GL(2, ℤ)` on `(t, 1)`, Farey intervals, and the explicit linear
fractional map `mob I J` between two Farey intervals.
-/

namespace CannonFloydParry.S7

open FracInterval

/-! ### `glAct` on `(t, 1)` -/

lemma glAct_t0 (A : GL (Fin 2) ℤ) (t : ℝ) :
    glAct A ![t, 1] 0 = ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ) * t +
      ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ) := by
  simp [glAct, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma glAct_t1 (A : GL (Fin 2) ℤ) (t : ℝ) :
    glAct A ![t, 1] 1 = ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * t +
      ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) := by
  simp [glAct, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma det_GL (A : GL (Fin 2) ℤ) :
    (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 ∨
      (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -1 := by
  have h := Matrix.isUnits_det_units A
  rw [Matrix.det_fin_two] at h
  exact Int.isUnit_iff.mp h

lemma glAct_entries (A : GL (Fin 2) ℤ) : ∃ p q r s : ℤ, (p * s - q * r = 1 ∨ p * s - q * r = -1) ∧
    ∀ t : ℝ, glAct A ![t, 1] 0 = (p : ℝ) * t + q ∧ glAct A ![t, 1] 1 = (r : ℝ) * t + s :=
  ⟨_, _, _, _, det_GL A, fun t => ⟨glAct_t0 A t, glAct_t1 A t⟩⟩

/-- The denominator of an integral projective map is positive. -/
lemma denom_pos {A : GL (Fin 2) ℤ} {U : Set ℝ} {f : ℝ → ℝ} (h : IsIntegralProjective01Via A U f)
    {t : ℝ} (ht : t ∈ U) : 0 < glAct A ![t, 1] 1 := by
  obtain ⟨h0, h1, -⟩ := h t ht
  by_contra hle
  have hy : glAct A ![t, 1] 1 = 0 := le_antisymm (not_lt.mp hle) (h0.trans h1)
  have hx : glAct A ![t, 1] 0 = 0 := le_antisymm (hy ▸ h1) h0
  rw [glAct_t0] at hx
  rw [glAct_t1] at hy
  set M := (A : Matrix (Fin 2) (Fin 2) ℤ)
  have hd : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ℝ) = 0 := by
    push_cast
    linear_combination (M 0 0 : ℝ) * hy - (M 1 0 : ℝ) * hx
  rcases det_GL A with h | h <;> rw [h] at hd <;> norm_num at hd

/-! ### Farey intervals -/

section Farey

variable {I : FracInterval}

lemma IsFarey.det (hI : I.IsFarey) : (I.a : ℤ) * I.d - (I.b : ℤ) * I.c = -1 := hI.2.2.2.2.2

lemma IsFarey.leftPart (hI : I.IsFarey) : I.leftPart.IsFarey := by
  obtain ⟨hb, hc, hd, hab, hcd, hdet⟩ := hI
  refine ⟨hb, by simp [FracInterval.leftPart]; omega, by simp [FracInterval.leftPart]; omega,
    le_refl _ |>.trans hab, by simp [FracInterval.leftPart]; omega, ?_⟩
  simp only [FracInterval.leftPart]
  push_cast
  linear_combination hdet

lemma IsFarey.rightPart (hI : I.IsFarey) : I.rightPart.IsFarey := by
  obtain ⟨hb, hc, hd, hab, hcd, hdet⟩ := hI
  refine ⟨by simp [FracInterval.rightPart]; omega, hc, hd, by simp [FracInterval.rightPart]; omega,
    hcd, ?_⟩
  simp only [FracInterval.rightPart]
  push_cast
  linear_combination hdet

lemma IsFarey.isCoprime_ab (hI : I.IsFarey) : IsCoprime (I.a : ℤ) (I.b : ℤ) :=
  ⟨-(I.d : ℤ), I.c, by linear_combination (-1 : ℤ) * (IsFarey.det hI)⟩

lemma IsFarey.isCoprime_cd (hI : I.IsFarey) : IsCoprime (I.c : ℤ) (I.d : ℤ) :=
  ⟨I.b, -(I.a : ℤ), by linear_combination (-1 : ℤ) * (IsFarey.det hI)⟩

lemma IsFarey.coprime_ab (hI : I.IsFarey) : Nat.Coprime I.a I.b :=
  Nat.isCoprime_iff_coprime.mp (IsFarey.isCoprime_ab hI)

lemma IsFarey.coprime_cd (hI : I.IsFarey) : Nat.Coprime I.c I.d :=
  Nat.isCoprime_iff_coprime.mp (IsFarey.isCoprime_cd hI)

end Farey

/-! ### Reduced fractions -/

lemma eq_of_div_eq {a b a' b' : ℕ} (hb : 0 < b) (hb' : 0 < b') (h : Nat.Coprime a b)
    (h' : Nat.Coprime a' b') (heq : (a : ℝ) / b = (a' : ℝ) / b') : a = a' ∧ b = b' := by
  have hbR : (b : ℝ) ≠ 0 := by positivity
  have hbR' : (b' : ℝ) ≠ 0 := by positivity
  rw [div_eq_div_iff hbR hbR'] at heq
  have hN : a * b' = a' * b := by exact_mod_cast heq
  have h1 : b ∣ b' := h.symm.dvd_of_dvd_mul_left ⟨a', by linarith⟩
  have h2 : b' ∣ b := h'.symm.dvd_of_dvd_mul_left ⟨a, by linarith⟩
  have hbb : b = b' := Nat.dvd_antisymm h1 h2
  subst hbb
  exact ⟨Nat.eq_of_mul_eq_mul_right hb hN, rfl⟩

lemma FracInterval.ext_of_lo_hi {I J : FracInterval} (hI : I.IsFarey) (hJ : J.IsFarey)
    (hlo : I.lo = J.lo) (hhi : I.hi = J.hi) : I = J := by
  obtain ⟨h1, h2⟩ := eq_of_div_eq hI.1 hJ.1 (IsFarey.coprime_ab hI) (IsFarey.coprime_ab hJ) hlo
  obtain ⟨h3, h4⟩ := eq_of_div_eq hI.2.2.1 hJ.2.2.1 (IsFarey.coprime_cd hI) (IsFarey.coprime_cd hJ) hhi
  cases I; cases J; simp_all

/-! ### A continuous map with the right bounds maps `[l, h]` onto `[f l, f h]` -/

lemma image_Icc_of_bounds {f : ℝ → ℝ} {l h : ℝ} (hlh : l ≤ h) (hc : ContinuousOn f (Set.Icc l h))
    (hb : ∀ t ∈ Set.Icc l h, f l ≤ f t ∧ f t ≤ f h) : f '' Set.Icc l h = Set.Icc (f l) (f h) := by
  apply le_antisymm
  · rintro _ ⟨t, ht, rfl⟩; exact hb t ht
  · exact intermediate_value_Icc hlh hc

lemma image_Icc_of_bounds' {f : ℝ → ℝ} {l h : ℝ} (hlh : l ≤ h) (hc : ContinuousOn f (Set.Icc l h))
    (hb : ∀ t ∈ Set.Icc l h, f h ≤ f t ∧ f t ≤ f l) : f '' Set.Icc l h = Set.Icc (f h) (f l) := by
  apply le_antisymm
  · rintro _ ⟨t, ht, rfl⟩; exact hb t ht
  · exact intermediate_value_Icc' hlh hc

end CannonFloydParry.S7

/-!
# The linear fractional map between two Farey intervals (CFP §7, p. 252)

`mob I J` is the map `ρ ∘ (M_J M_I⁻¹)` in the coordinate `t`; it is integral projective on
`[I.lo, I.hi]`, maps it onto `[J.lo, J.hi]` endpoint to endpoint, and it is the only integral
projective map on `[I.lo, I.hi]` with those endpoint values.
-/

namespace CannonFloydParry.S7

variable {I J : FracInterval}

/-! ### Uniqueness -/

end CannonFloydParry.S7

/-!
# Integral subsimplices of `[0,1]` and the maps between them (CFP §7, pp. 251–253)
-/

namespace CannonFloydParry.S7

/-- The root `[0/1, 1/1]` of the Farey tree. -/
def root : FracInterval := ⟨0, 1, 1, 1⟩

lemma root_isFarey : root.IsFarey := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by norm_num [root]⟩

lemma subsimplex_of_farey {K : FracInterval} (hK : K.IsFarey) : IsIntegralSubsimplex01 K.lo K.hi :=
  ((isIntegralSubsimplex01_iff hK.1 hK.2.1 hK.2.2.1 hK.2.2.2.1 hK.2.2.2.2.1).mpr
    hK.2.2.2.2.2).2.2.2

/-- Every integral subsimplex of `[0,1]` is a Farey interval. -/
lemma exists_farey_of_subsimplex {p q : ℝ} (h : IsIntegralSubsimplex01 p q) :
    ∃ K : FracInterval, K.IsFarey ∧ K.lo = p ∧ K.hi = q := by
  obtain ⟨f, ⟨-, B, hB⟩, himg⟩ := h
  obtain ⟨P, Q, R, S, hdet, hgl⟩ := glAct_entries B
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have y0 := denom_pos hB h0
  have y1 := denom_pos hB h1
  obtain ⟨x0, xy0, -⟩ := hB 0 h0
  obtain ⟨x1, xy1, -⟩ := hB 1 h1
  rw [(hgl _).2] at y0 y1 xy0 xy1
  rw [(hgl _).1] at x0 x1 xy0 xy1
  simp only [mul_zero, zero_add, mul_one] at y0 y1 xy0 xy1 x0 x1
  have iQ : 0 ≤ Q := by exact_mod_cast x0
  have iS : 0 < S := by exact_mod_cast y0
  have iQS : Q ≤ S := by exact_mod_cast xy0
  have iX : 0 ≤ P + Q := by exact_mod_cast x1
  have iY : 0 < R + S := by exact_mod_cast y1
  have iXY : P + Q ≤ R + S := by exact_mod_cast xy1
  lift Q to ℕ using iQ with a
  lift S to ℕ using iS.le with b
  obtain ⟨c, hc⟩ : ∃ c : ℕ, P + a = c := ⟨(P + a).toNat, (Int.toNat_of_nonneg iX).symm⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, R + b = d := ⟨(R + b).toNat, (Int.toNat_of_nonneg iY.le).symm⟩
  have hP : P = c - a := by omega
  have hR : R = d - b := by omega
  subst hP hR
  have hb : 0 < b := by exact_mod_cast iS
  have hd0 : 0 < d := by omega
  have hab : a ≤ b := by exact_mod_cast iQS
  have hcd : c ≤ d := by omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  -- the formula for `f`
  have hden : ∀ t ∈ Set.Icc (0 : ℝ) 1, (0 : ℝ) < ((d : ℝ) - b) * t + b := by
    intro t ht
    have := denom_pos hB ht
    rw [(hgl _).2] at this
    push_cast at this
    exact this
  have hf : Set.EqOn f (fun t => (((c : ℝ) - a) * t + a) / (((d : ℝ) - b) * t + b))
      (Set.Icc 0 1) := by
    intro t ht
    rw [(hB t ht).2.2, (hgl _).1, (hgl _).2]
    push_cast
    rfl
  have hcont : ContinuousOn f (Set.Icc 0 1) :=
    ContinuousOn.congr (ContinuousOn.div (by fun_prop) (by fun_prop)
      fun t ht => (hden t ht).ne') hf
  have f0 : f 0 = (a : ℝ) / b := by rw [hf h0]; simp
  have f1 : f 1 = (c : ℝ) / d := by rw [hf h1]; simp
  have hdR' : ((c - a : ℤ) * b - a * (d - b) : ℤ) = (c : ℤ) * b - a * d := by ring
  rcases hdet with hdet | hdet <;> rw [hdR'] at hdet
  · -- orientation preserving: `K = [a/b, c/d]`
    have hK : (⟨a, b, c, d⟩ : FracInterval).IsFarey := by
      refine ⟨hb, ?_, hd0, hab, hcd, by simp only; linarith⟩
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; push_cast at hdet; nlinarith
      · exact h
    have hdetR : (c : ℝ) * b - a * d = 1 := by exact_mod_cast hdet
    have himg' : f '' Set.Icc 0 1 = Set.Icc (f 0) (f 1) := by
      refine image_Icc_of_bounds zero_le_one hcont fun t ht => ?_
      have hD := hden t ht
      rw [f0, f1, hf ht]
      constructor
      · rw [div_le_div_iff₀ hbR hD]; nlinarith [ht.1]
      · rw [div_le_div_iff₀ hD hdR]; nlinarith [ht.2]
    rw [himg', f0, f1] at himg
    have hle : (a : ℝ) / b ≤ c / d := by
      rw [div_le_div_iff₀ hbR hdR]; linarith
    obtain ⟨hp, hq⟩ := (Set.Icc_eq_Icc_iff hle).mp himg
    exact ⟨_, hK, hp, hq⟩
  · -- orientation reversing: `K = [c/d, a/b]`
    have hK : (⟨c, d, a, b⟩ : FracInterval).IsFarey := by
      refine ⟨hd0, ?_, hb, hcd, hab, by simp only; linarith⟩
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h; push_cast at hdet; nlinarith
      · exact h
    have hdetR : (c : ℝ) * b - a * d = -1 := by exact_mod_cast hdet
    have himg' : f '' Set.Icc 0 1 = Set.Icc (f 1) (f 0) := by
      refine image_Icc_of_bounds' zero_le_one hcont fun t ht => ?_
      have hD := hden t ht
      rw [f0, f1, hf ht]
      constructor
      · rw [div_le_div_iff₀ hdR hD]; nlinarith [ht.2]
      · rw [div_le_div_iff₀ hD hbR]; nlinarith [ht.1]
    rw [himg', f0, f1] at himg
    have hle : (c : ℝ) / d ≤ a / b := by
      rw [div_le_div_iff₀ hdR hbR]; linarith
    obtain ⟨hp, hq⟩ := (Set.Icc_eq_Icc_iff hle).mp himg
    exact ⟨_, hK, hp, hq⟩

/-! ### Target: the criterion of p. 251 -/


/-! ### Target: the two parts are integral subsimplices -/


/-! ### Target: the unique integral projective map between two Farey intervals -/


/-! ### Target: restriction and gluing -/


end CannonFloydParry.S7

/-!
# The tree `𝒯′` of integral subsimplices of `[0,1]` (CFP §7, p. 252)
-/

namespace CannonFloydParry.S7

/-- One step down the Farey tree. -/
def fstep (I : FracInterval) (x : Bool) : FracInterval := if x then I.rightPart else I.leftPart

lemma fareyNode_eq (w : List Bool) : fareyNode w = w.foldl fstep root := rfl

lemma fareyNode_append (w : List Bool) (x : Bool) :
    fareyNode (w ++ [x]) = fstep (fareyNode w) x := by
  simp [fareyNode_eq, List.foldl_append]

lemma fstep_isFarey {I : FracInterval} (hI : I.IsFarey) (x : Bool) : (fstep I x).IsFarey := by
  cases x
  · exact IsFarey.leftPart hI
  · exact IsFarey.rightPart hI

lemma fareyNode_isFarey (w : List Bool) : (fareyNode w).IsFarey := by
  induction w using List.reverseRecOn with
  | nil => exact root_isFarey
  | append_singleton w x ih => rw [fareyNode_append]; exact fstep_isFarey ih x

/-- The side of a step can be read off from the comparison of `b` and `d`. -/
lemma fstep_bd {I : FracInterval} (hI : I.IsFarey) (x : Bool) :
    (x = false → (fstep I x).b < (fstep I x).d) ∧ (x = true → (fstep I x).d < (fstep I x).b) := by
  obtain ⟨hb, -, hd, -⟩ := hI
  cases x <;> simp [fstep, FracInterval.leftPart, FracInterval.rightPart] <;> omega

lemma fstep_ne_root {I : FracInterval} (hI : I.IsFarey) (x : Bool) : fstep I x ≠ root := by
  intro h
  have := fstep_bd hI x
  rw [h] at this
  cases x <;> simp [root] at this

lemma fstep_inj {I J : FracInterval} {x y : Bool} (hI : I.IsFarey) (hJ : J.IsFarey)
    (h : fstep I x = fstep J y) : x = y ∧ I = J := by
  have hx := fstep_bd hI x
  have hy := fstep_bd hJ y
  rw [h] at hx
  have hxy : x = y := by
    cases x <;> cases y
    · rfl
    · have := hx.1 rfl; have := hy.2 rfl; omega
    · have := hx.2 rfl; have := hy.1 rfl; omega
    · rfl
  subst hxy
  refine ⟨rfl, ?_⟩
  obtain ⟨a, b, c, d⟩ := I
  obtain ⟨a', b', c', d'⟩ := J
  cases x <;> simp [fstep, FracInterval.leftPart, FracInterval.rightPart] at h ⊢ <;> omega

lemma fareyNode_injective : Function.Injective fareyNode := by
  intro w₁
  induction w₁ using List.reverseRecOn with
  | nil =>
    intro w₂ h
    induction w₂ using List.reverseRecOn with
    | nil => rfl
    | append_singleton v y _ =>
      rw [fareyNode_append] at h
      exact absurd h.symm (fstep_ne_root (fareyNode_isFarey v) y)
  | append_singleton u x ih =>
    intro w₂ h
    induction w₂ using List.reverseRecOn with
    | nil =>
      rw [fareyNode_append] at h
      exact absurd h (fstep_ne_root (fareyNode_isFarey u) x)
    | append_singleton v y _ =>
      rw [fareyNode_append, fareyNode_append] at h
      obtain ⟨rfl, h'⟩ := fstep_inj (fareyNode_isFarey u) (fareyNode_isFarey v) h
      rw [ih h']

/-- Euclid descent: every Farey interval is a vertex of `𝒯′`. -/
lemma exists_fareyNode_aux (n : ℕ) :
    ∀ K : FracInterval, K.IsFarey → K.b + K.d = n → ∃ w, fareyNode w = K := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rintro ⟨a, b, c, d⟩ ⟨hb, hc, hd, hab, hcd, hdet⟩ hn
  simp only at hb hc hd hab hcd hdet hn
  have hN : a * d + 1 = b * c := by
    have : ((a * d + 1 : ℕ) : ℤ) = ((b * c : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  rcases lt_trichotomy b d with hbd | hbd | hbd
  · -- a left part: parent `[a/b, (c-a)/(d-b)]`
    have hac : a ≤ c := by
      by_contra h
      push Not at h
      nlinarith
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hac
    obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_lt hbd
    have hN' : a * (f + 1) + 1 = b * e := by nlinarith
    have he : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · subst h; simp at hN'
      · exact h
    have hef : e ≤ f + 1 := by
      by_contra h
      push Not at h
      have hb1 : b ≤ 1 := by nlinarith
      have hb1' : b = 1 := by omega
      subst hb1'
      have ha : a ≤ 1 := hab
      interval_cases a <;> omega
    have hlt : b + (f + 1) < n := by omega
    have hZ : (a : ℤ) * (f + 1) + 1 = b * e := by exact_mod_cast hN'
    have hK' : (⟨a, b, e, f + 1⟩ : FracInterval).IsFarey :=
      ⟨hb, he, by simp, hab, hef, by push_cast; linear_combination hZ⟩
    obtain ⟨w, hw⟩ := ih (b + (f + 1)) hlt ⟨a, b, e, f + 1⟩ hK' rfl
    refine ⟨w ++ [false], ?_⟩
    rw [fareyNode_append, hw]
    simp [fstep, FracInterval.leftPart]
    omega
  · -- the root
    subst hbd
    have hca : a < c := by
      by_contra h
      push Not at h
      nlinarith
    have hb1 : b = 1 := by
      have : b * (a + 1) ≤ b * c := Nat.mul_le_mul_left b hca
      nlinarith
    subst hb1
    have hc1 : c = 1 := by omega
    subst hc1
    have ha0 : a = 0 := by omega
    subst ha0
    exact ⟨[], rfl⟩
  · -- a right part: parent `[(a-c)/(b-d), c/d]`
    have hca : c ≤ a := by
      by_contra h
      push Not at h
      nlinarith
    obtain ⟨h', rfl⟩ := Nat.exists_eq_add_of_le hca
    obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_lt hbd
    have hN' : h' * d + 1 = (g + 1) * c := by nlinarith
    have hhg : h' ≤ g + 1 := by
      by_contra h
      push Not at h
      nlinarith
    have hlt : g + 1 + d < n := by omega
    have hZ : (h' : ℤ) * d + 1 = (g + 1) * c := by exact_mod_cast hN'
    have hK' : (⟨h', g + 1, c, d⟩ : FracInterval).IsFarey :=
      ⟨by simp, hc, hd, hhg, hcd, by push_cast; linear_combination hZ⟩
    obtain ⟨w, hw⟩ := ih (g + 1 + d) hlt ⟨h', g + 1, c, d⟩ hK' rfl
    refine ⟨w ++ [true], ?_⟩
    rw [fareyNode_append, hw]
    simp [fstep, FracInterval.rightPart]
    omega

lemma exists_fareyNode {K : FracInterval} (hK : K.IsFarey) : ∃ w, fareyNode w = K :=
  exists_fareyNode_aux _ K hK rfl

theorem isIntegralSubsimplex01_fareyNode_and_bijective' :
    (∀ w, IsIntegralSubsimplex01 (fareyNode w).lo (fareyNode w).hi) ∧
      Function.Injective (fun w => ((fareyNode w).lo, (fareyNode w).hi)) ∧
      ∀ p q, IsIntegralSubsimplex01 p q → ∃ w, (fareyNode w).lo = p ∧ (fareyNode w).hi = q := by
  refine ⟨fun w => subsimplex_of_farey (fareyNode_isFarey w), ?_, ?_⟩
  · intro w₁ w₂ h
    simp only [Prod.mk.injEq] at h
    exact fareyNode_injective
      (FracInterval.ext_of_lo_hi (fareyNode_isFarey w₁) (fareyNode_isFarey w₂) h.1 h.2)
  · intro p q h
    obtain ⟨K, hK, hlo, hhi⟩ := exists_farey_of_subsimplex h
    obtain ⟨w, rfl⟩ := exists_fareyNode hK
    exact ⟨w, hlo, hhi⟩

end CannonFloydParry.S7

open CannonFloydParry in
theorem solution :
    (∀ w, IsIntegralSubsimplex01 (fareyNode w).lo (fareyNode w).hi) ∧
      Function.Injective (fun w => ((fareyNode w).lo, (fareyNode w).hi)) ∧
      ∀ p q, IsIntegralSubsimplex01 p q → ∃ w, (fareyNode w).lo = p ∧ (fareyNode w).hi = q := by
  exact S7.isIntegralSubsimplex01_fareyNode_and_bijective'
