-- Prove2me | solution 1 for CannonFloydParry.isIntegralSubsimplex01_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T20:21:11.415987+00:00
-- url     : https://prove2.me/submissions/53f63466-299a-4b35-8da2-0689cf7b9561

import Definitions.Def_CannonFloydParry_PIP

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

lemma IsFarey.detR (hI : I.IsFarey) : (I.a : ℝ) * I.d - (I.b : ℝ) * I.c = -1 := by
  exact_mod_cast (IsFarey.det hI)

lemma IsFarey.b_pos (hI : I.IsFarey) : (0 : ℝ) < I.b := by exact_mod_cast hI.1
lemma IsFarey.d_pos (hI : I.IsFarey) : (0 : ℝ) < I.d := by exact_mod_cast hI.2.2.1
lemma IsFarey.a_le_b (hI : I.IsFarey) : (I.a : ℝ) ≤ I.b := by exact_mod_cast hI.2.2.2.1
lemma IsFarey.c_le_d (hI : I.IsFarey) : (I.c : ℝ) ≤ I.d := by exact_mod_cast hI.2.2.2.2.1

lemma IsFarey.isCoprime_ab (hI : I.IsFarey) : IsCoprime (I.a : ℤ) (I.b : ℤ) :=
  ⟨-(I.d : ℤ), I.c, by linear_combination (-1 : ℤ) * (IsFarey.det hI)⟩

lemma IsFarey.isCoprime_cd (hI : I.IsFarey) : IsCoprime (I.c : ℤ) (I.d : ℤ) :=
  ⟨I.b, -(I.a : ℤ), by linear_combination (-1 : ℤ) * (IsFarey.det hI)⟩

lemma IsFarey.coprime_ab (hI : I.IsFarey) : Nat.Coprime I.a I.b :=
  Nat.isCoprime_iff_coprime.mp (IsFarey.isCoprime_ab hI)

lemma IsFarey.coprime_cd (hI : I.IsFarey) : Nat.Coprime I.c I.d :=
  Nat.isCoprime_iff_coprime.mp (IsFarey.isCoprime_cd hI)

lemma IsFarey.lo_nonneg (hI : I.IsFarey) : 0 ≤ I.lo := by
  unfold FracInterval.lo; positivity

lemma IsFarey.hi_le_one (hI : I.IsFarey) : I.hi ≤ 1 := by
  unfold FracInterval.hi
  rw [div_le_one (IsFarey.d_pos hI)]; exact (IsFarey.c_le_d hI)

lemma IsFarey.lo_lt_hi (hI : I.IsFarey) : I.lo < I.hi := by
  unfold FracInterval.lo FracInterval.hi
  rw [div_lt_div_iff₀ (IsFarey.b_pos hI) (IsFarey.d_pos hI)]
  linarith [(IsFarey.detR hI)]

lemma IsFarey.Icc_subset (hI : I.IsFarey) : Set.Icc I.lo I.hi ⊆ Set.Icc 0 1 :=
  Set.Icc_subset_Icc (IsFarey.lo_nonneg hI) (IsFarey.hi_le_one hI)

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


/-- Numerator of the map `I → J`. -/
noncomputable def mobN (I J : FracInterval) (t : ℝ) : ℝ :=
  ((J.c : ℝ) * I.b - (J.a : ℝ) * I.d) * t + ((J.a : ℝ) * I.c - (J.c : ℝ) * I.a)

/-- Denominator of the map `I → J`. -/
noncomputable def mobD (I J : FracInterval) (t : ℝ) : ℝ :=
  ((J.d : ℝ) * I.b - (J.b : ℝ) * I.d) * t + ((J.b : ℝ) * I.c - (J.d : ℝ) * I.a)

/-- The linear fractional map carrying `[I.lo, I.hi]` onto `[J.lo, J.hi]`. -/
noncomputable def mob (I J : FracInterval) (t : ℝ) : ℝ := mobN I J t / mobD I J t

lemma mobN_eq (I J : FracInterval) (t : ℝ) :
    mobN I J t = ((I.c : ℝ) - I.d * t) * J.a + ((I.b : ℝ) * t - I.a) * J.c := by
  unfold mobN; ring

lemma mobD_eq (I J : FracInterval) (t : ℝ) :
    mobD I J t = ((I.c : ℝ) - I.d * t) * J.b + ((I.b : ℝ) * t - I.a) * J.d := by
  unfold mobD; ring

variable {I J : FracInterval}

lemma alpha_nonneg (hI : I.IsFarey) {t : ℝ} (ht : t ∈ Set.Icc I.lo I.hi) :
    0 ≤ (I.c : ℝ) - I.d * t := by
  have h := ht.2
  unfold FracInterval.hi at h
  rw [le_div_iff₀ (IsFarey.d_pos hI)] at h
  linarith

lemma beta_nonneg (hI : I.IsFarey) {t : ℝ} (ht : t ∈ Set.Icc I.lo I.hi) :
    0 ≤ (I.b : ℝ) * t - I.a := by
  have h := ht.1
  unfold FracInterval.lo at h
  rw [div_le_iff₀ (IsFarey.b_pos hI)] at h
  linarith

lemma alpha_beta (hI : I.IsFarey) (t : ℝ) :
    (I.b : ℝ) * ((I.c : ℝ) - I.d * t) + (I.d : ℝ) * ((I.b : ℝ) * t - I.a) = 1 := by
  linear_combination -(IsFarey.detR hI)

lemma mobD_pos (hI : I.IsFarey) (hJ : J.IsFarey) {t : ℝ} (ht : t ∈ Set.Icc I.lo I.hi) :
    0 < mobD I J t := by
  rw [mobD_eq]
  have hα := alpha_nonneg hI ht
  have hβ := beta_nonneg hI ht
  have hab := alpha_beta hI t
  have hb := IsFarey.b_pos hJ
  have hd := IsFarey.d_pos hJ
  rcases hα.lt_or_eq with hα | hα
  · have := mul_pos hα hb
    nlinarith [mul_nonneg hβ hd.le]
  · rw [← hα] at hab ⊢
    have : 0 < (I.b : ℝ) * t - I.a := by
      by_contra h
      have : (I.b : ℝ) * t - I.a = 0 := le_antisymm (not_lt.mp h) hβ
      rw [this] at hab; simp at hab
    simp only [zero_mul, zero_add]
    exact mul_pos this hd

lemma continuousOn_mob (hI : I.IsFarey) (hJ : J.IsFarey) :
    ContinuousOn (mob I J) (Set.Icc I.lo I.hi) := by
  unfold mob mobN mobD
  exact ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => (mobD_pos hI hJ ht).ne'

/-- The integer matrix of the map. -/
def mobMat (I J : FracInterval) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(J.c : ℤ) * I.b - (J.a : ℤ) * I.d, (J.a : ℤ) * I.c - (J.c : ℤ) * I.a;
     (J.d : ℤ) * I.b - (J.b : ℤ) * I.d, (J.b : ℤ) * I.c - (J.d : ℤ) * I.a]

lemma mobMat_det (hI : I.IsFarey) (hJ : J.IsFarey) : (mobMat I J).det = 1 := by
  rw [Matrix.det_fin_two]
  simp only [mobMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  linear_combination ((I.a : ℤ) * I.d - (I.b : ℤ) * I.c) * (IsFarey.det hJ) - (IsFarey.det hI)

/-- The matrix as an element of `GL(2, ℤ)`. -/
def glOfDetOne (M : Matrix (Fin 2) (Fin 2) ℤ) (h : M.det = 1) : GL (Fin 2) ℤ :=
  ⟨M, M.adjugate, by rw [Matrix.mul_adjugate, h, one_smul],
    by rw [Matrix.adjugate_mul, h, one_smul]⟩

lemma mob_via (hI : I.IsFarey) (hJ : J.IsFarey) :
    IsIntegralProjective01Via (glOfDetOne (mobMat I J) (mobMat_det hI hJ))
      (Set.Icc I.lo I.hi) (mob I J) := by
  intro t ht
  have e0 : glAct (glOfDetOne (mobMat I J) (mobMat_det hI hJ)) ![t, 1] 0 = mobN I J t := by
    rw [glAct_t0]
    simp [glOfDetOne, mobMat, mobN]
  have e1 : glAct (glOfDetOne (mobMat I J) (mobMat_det hI hJ)) ![t, 1] 1 = mobD I J t := by
    rw [glAct_t1]
    simp [glOfDetOne, mobMat, mobD]
  rw [e0, e1]
  refine ⟨?_, ?_, rfl⟩
  · rw [mobN_eq]
    have := alpha_nonneg hI ht
    have := beta_nonneg hI ht
    positivity
  · rw [mobN_eq, mobD_eq]
    have := mul_nonneg (alpha_nonneg hI ht) (sub_nonneg.mpr (IsFarey.a_le_b hJ))
    have := mul_nonneg (beta_nonneg hI ht) (sub_nonneg.mpr (IsFarey.c_le_d hJ))
    nlinarith

lemma mob_isIP (hI : I.IsFarey) (hJ : J.IsFarey) :
    IsIntegralProjective01 (Set.Icc I.lo I.hi) (mob I J) :=
  ⟨IsFarey.Icc_subset hI, _, mob_via hI hJ⟩

lemma lo_mem (hI : I.IsFarey) : I.lo ∈ Set.Icc I.lo I.hi := ⟨le_rfl, (IsFarey.lo_lt_hi hI).le⟩
lemma hi_mem (hI : I.IsFarey) : I.hi ∈ Set.Icc I.lo I.hi := ⟨(IsFarey.lo_lt_hi hI).le, le_rfl⟩

lemma mob_lo (hI : I.IsFarey) (hJ : J.IsFarey) : mob I J I.lo = J.lo := by
  have hD := mobD_pos hI hJ (lo_mem hI)
  have hb := IsFarey.b_pos hI
  unfold mob FracInterval.lo at *
  rw [div_eq_div_iff hD.ne' (IsFarey.b_pos hJ).ne']
  unfold mobN mobD
  field_simp
  ring

lemma mob_hi (hI : I.IsFarey) (hJ : J.IsFarey) : mob I J I.hi = J.hi := by
  have hD := mobD_pos hI hJ (hi_mem hI)
  have hd := IsFarey.d_pos hI
  unfold mob FracInterval.hi at *
  rw [div_eq_div_iff hD.ne' (IsFarey.d_pos hJ).ne']
  unfold mobN mobD
  field_simp
  ring

lemma mob_bounds (hI : I.IsFarey) (hJ : J.IsFarey) {t : ℝ} (ht : t ∈ Set.Icc I.lo I.hi) :
    J.lo ≤ mob I J t ∧ mob I J t ≤ J.hi := by
  have hD := mobD_pos hI hJ ht
  have hβ := beta_nonneg hI ht
  have hα := alpha_nonneg hI ht
  have hdJ := IsFarey.detR hJ
  unfold mob FracInterval.lo FracInterval.hi
  constructor
  · rw [div_le_div_iff₀ (IsFarey.b_pos hJ) hD, mobN_eq, mobD_eq]
    nlinarith
  · rw [div_le_div_iff₀ hD (IsFarey.d_pos hJ), mobN_eq, mobD_eq]
    nlinarith

lemma mob_image (hI : I.IsFarey) (hJ : J.IsFarey) :
    mob I J '' Set.Icc I.lo I.hi = Set.Icc J.lo J.hi := by
  have h := image_Icc_of_bounds (IsFarey.lo_lt_hi hI).le (continuousOn_mob hI hJ)
    (fun t ht => by rw [mob_lo hI hJ, mob_hi hI hJ]; exact mob_bounds hI hJ ht)
  rwa [mob_lo hI hJ, mob_hi hI hJ] at h

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

lemma root_Icc : Set.Icc root.lo root.hi = Set.Icc 0 1 := by
  simp [root, FracInterval.lo, FracInterval.hi]

lemma subsimplex_of_farey {K : FracInterval} (hK : K.IsFarey) : IsIntegralSubsimplex01 K.lo K.hi :=
  ⟨mob root K, root_Icc ▸ mob_isIP root_isFarey hK, root_Icc ▸ mob_image root_isFarey hK⟩

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

theorem isIntegralSubsimplex01_iff' {a b c d : ℕ} (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a ≤ b) (hcd : c ≤ d) :
    (Nat.gcd a b = 1 ∧ Nat.gcd c d = 1 ∧ (a : ℝ) / b < (c : ℝ) / d ∧
        IsIntegralSubsimplex01 ((a : ℝ) / b) ((c : ℝ) / d)) ↔
      (a : ℤ) * d - (b : ℤ) * c = -1 := by
  constructor
  · rintro ⟨g1, g2, -, hs⟩
    obtain ⟨K, hK, hlo, hhi⟩ := exists_farey_of_subsimplex hs
    obtain ⟨e1, e2⟩ := eq_of_div_eq hK.1 hb (IsFarey.coprime_ab hK) g1 hlo
    obtain ⟨e3, e4⟩ := eq_of_div_eq hK.2.2.1 hd (IsFarey.coprime_cd hK) g2 hhi
    have := IsFarey.det hK
    rw [e1, e2, e3, e4] at this
    exact this
  · intro hdet
    have hK : (⟨a, b, c, d⟩ : FracInterval).IsFarey := ⟨hb, hc, hd, hab, hcd, hdet⟩
    exact ⟨IsFarey.coprime_ab hK, IsFarey.coprime_cd hK, IsFarey.lo_lt_hi hK,
      subsimplex_of_farey hK⟩

/-! ### Target: the two parts are integral subsimplices -/


/-! ### Target: the unique integral projective map between two Farey intervals -/


/-! ### Target: restriction and gluing -/


end CannonFloydParry.S7

open CannonFloydParry in
theorem solution {a b c d : ℕ} (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a ≤ b) (hcd : c ≤ d) :
    (Nat.gcd a b = 1 ∧ Nat.gcd c d = 1 ∧ (a : ℝ) / b < (c : ℝ) / d ∧
        IsIntegralSubsimplex01 ((a : ℝ) / b) ((c : ℝ) / d)) ↔
      (a : ℤ) * d - (b : ℤ) * c = -1 := by
  exact S7.isIntegralSubsimplex01_iff' hb hc hd hab hcd
