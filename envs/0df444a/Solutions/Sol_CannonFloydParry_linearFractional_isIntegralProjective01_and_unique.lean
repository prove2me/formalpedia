-- Prove2me | solution 1 for CannonFloydParry.linearFractional_isIntegralProjective01_and_unique
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T20:27:40.980508+00:00
-- url     : https://prove2.me/submissions/8be08842-ee77-40e4-9696-9463256d11d5

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

/-! ### A continuous map with the right bounds maps `[l, h]` onto `[f l, f h]` -/

lemma image_Icc_of_bounds {f : ℝ → ℝ} {l h : ℝ} (hlh : l ≤ h) (hc : ContinuousOn f (Set.Icc l h))
    (hb : ∀ t ∈ Set.Icc l h, f l ≤ f t ∧ f t ≤ f h) : f '' Set.Icc l h = Set.Icc (f l) (f h) := by
  apply le_antisymm
  · rintro _ ⟨t, ht, rfl⟩; exact hb t ht
  · exact intermediate_value_Icc hlh hc

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

lemma prim_mult {x y u v : ℤ} (hc : IsCoprime x y) (hy : 0 < y) (hv : 0 < v)
    (h : x * v = u * y) : ∃ l : ℤ, 0 < l ∧ u = l * x ∧ v = l * y := by
  obtain ⟨k, hk⟩ : y ∣ v := hc.symm.dvd_of_dvd_mul_left ⟨u, by rw [h]; ring⟩
  refine ⟨k, ?_, ?_, by rw [hk]; ring⟩
  · rw [hk] at hv
    exact pos_of_mul_pos_right hv hy.le
  · rw [hk] at h
    have : (u - k * x) * y = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact absurd h' hy.ne'

lemma mob_unique (hI : I.IsFarey) (hJ : J.IsFarey) {g : ℝ → ℝ}
    (hg : IsIntegralProjective01 (Set.Icc I.lo I.hi) g) (hlo : g I.lo = J.lo)
    (hhi : g I.hi = J.hi) : Set.EqOn g (mob I J) (Set.Icc I.lo I.hi) := by
  obtain ⟨-, B, hB⟩ := hg
  obtain ⟨p, q, r, s, hdet, hgl⟩ := glAct_entries B
  have hbI := IsFarey.b_pos hI
  have hdI := IsFarey.d_pos hI
  have hbJ := IsFarey.b_pos hJ
  have hdJ := IsFarey.d_pos hJ
  -- at the left endpoint
  have y0 := denom_pos hB (lo_mem hI)
  have g0 := (hB _ (lo_mem hI)).2.2
  rw [(hgl _).2] at y0
  rw [hlo, (hgl _).1, (hgl _).2] at g0
  have hv0 : (0 : ℝ) < r * I.a + s * I.b := by
    have : (r : ℝ) * I.a + s * I.b = I.b * (r * I.lo + s) := by
      unfold FracInterval.lo; field_simp
    rw [this]; positivity
  have huv0 : (J.a : ℝ) * (r * I.a + s * I.b) = (p * I.a + q * I.b) * J.b := by
    have y0' := y0
    unfold FracInterval.lo at g0 y0'
    rw [div_eq_div_iff hbJ.ne' y0'.ne'] at g0
    field_simp at g0
    linear_combination g0
  -- at the right endpoint
  have y1 := denom_pos hB (hi_mem hI)
  have g1 := (hB _ (hi_mem hI)).2.2
  rw [(hgl _).2] at y1
  rw [hhi, (hgl _).1, (hgl _).2] at g1
  have hv1 : (0 : ℝ) < r * I.c + s * I.d := by
    have : (r : ℝ) * I.c + s * I.d = I.d * (r * I.hi + s) := by
      unfold FracInterval.hi; field_simp
    rw [this]; positivity
  have huv1 : (J.c : ℝ) * (r * I.c + s * I.d) = (p * I.c + q * I.d) * J.d := by
    have y1' := y1
    unfold FracInterval.hi at g1 y1'
    rw [div_eq_div_iff hdJ.ne' y1'.ne'] at g1
    field_simp at g1
    linear_combination g1
  obtain ⟨l, hl, hl1, hl2⟩ := prim_mult (IsFarey.isCoprime_ab hJ) (by exact_mod_cast hJ.1)
    (by exact_mod_cast hv0) (by exact_mod_cast huv0)
  obtain ⟨m, hm, hm1, hm2⟩ := prim_mult (IsFarey.isCoprime_cd hJ) (by exact_mod_cast hJ.2.2.1)
    (by exact_mod_cast hv1) (by exact_mod_cast huv1)
  have hdI' := IsFarey.det hI
  have hdJ' := IsFarey.det hJ
  have hlm : l * m = p * s - q * r := by
    have key : (p * I.a + q * I.b) * (r * I.c + s * I.d) - (p * I.c + q * I.d) * (r * I.a + s * I.b)
        = (p * s - q * r) * ((I.a : ℤ) * I.d - (I.b : ℤ) * I.c) := by ring
    rw [hl1, hl2, hm1, hm2, hdI'] at key
    linear_combination -key + l * m * hdJ'
  have hl1' : l = 1 := by
    rcases hdet with h | h
    · exact Int.eq_one_of_mul_eq_one_right hl.le (hlm.trans h)
    · nlinarith [mul_pos hl hm]
  have hm1' : m = 1 := by
    rw [hl1', one_mul] at hlm
    rcases hdet with h | h
    · exact hlm.trans h
    · nlinarith
  subst hl1' hm1'
  simp only [one_mul] at hl1 hl2 hm1 hm2
  have ep : p = (J.c : ℤ) * I.b - (J.a : ℤ) * I.d := by
    linear_combination (-(I.d : ℤ)) * hl1 + (I.b : ℤ) * hm1 + p * hdI'
  have eq' : q = (J.a : ℤ) * I.c - (J.c : ℤ) * I.a := by
    linear_combination (-(I.a : ℤ)) * hm1 + (I.c : ℤ) * hl1 + q * hdI'
  have er : r = (J.d : ℤ) * I.b - (J.b : ℤ) * I.d := by
    linear_combination (-(I.d : ℤ)) * hl2 + (I.b : ℤ) * hm2 + r * hdI'
  have es : s = (J.b : ℤ) * I.c - (J.d : ℤ) * I.a := by
    linear_combination (-(I.a : ℤ)) * hm2 + (I.c : ℤ) * hl2 + s * hdI'
  intro t ht
  rw [(hB t ht).2.2, (hgl _).1, (hgl _).2, ep, eq', er, es]
  unfold mob mobN mobD
  push_cast
  rfl

end CannonFloydParry.S7

/-!
# Integral subsimplices of `[0,1]` and the maps between them (CFP §7, pp. 251–253)
-/

namespace CannonFloydParry.S7

/-! ### Target: the criterion of p. 251 -/


/-! ### Target: the two parts are integral subsimplices -/


/-! ### Target: the unique integral projective map between two Farey intervals -/

theorem linearFractional_isIntegralProjective01_and_unique' {I J : FracInterval}
    (hI : I.IsFarey) (hJ : J.IsFarey) :
    let f : ℝ → ℝ := fun t =>
      (((J.c : ℝ) * I.b - (J.a : ℝ) * I.d) * t + ((J.a : ℝ) * I.c - (J.c : ℝ) * I.a)) /
        (((J.d : ℝ) * I.b - (J.b : ℝ) * I.d) * t + ((J.b : ℝ) * I.c - (J.d : ℝ) * I.a))
    IsIntegralProjective01 (Set.Icc I.lo I.hi) f ∧ f '' Set.Icc I.lo I.hi = Set.Icc J.lo J.hi ∧
      f I.lo = J.lo ∧ f I.hi = J.hi ∧
      ∀ g : ℝ → ℝ, IsIntegralProjective01 (Set.Icc I.lo I.hi) g →
        Set.MapsTo g (Set.Icc I.lo I.hi) (Set.Icc J.lo J.hi) → g I.lo = J.lo → g I.hi = J.hi →
          Set.EqOn g f (Set.Icc I.lo I.hi) :=
  ⟨mob_isIP hI hJ, mob_image hI hJ, mob_lo hI hJ, mob_hi hI hJ,
    fun _ hg _ h1 h2 => mob_unique hI hJ hg h1 h2⟩

/-! ### Target: restriction and gluing -/


end CannonFloydParry.S7

open CannonFloydParry in
theorem solution {I J : FracInterval} (hI : I.IsFarey)
    (hJ : J.IsFarey) :
    let f : ℝ → ℝ := fun t =>
      (((J.c : ℝ) * I.b - (J.a : ℝ) * I.d) * t + ((J.a : ℝ) * I.c - (J.c : ℝ) * I.a)) /
        (((J.d : ℝ) * I.b - (J.b : ℝ) * I.d) * t + ((J.b : ℝ) * I.c - (J.d : ℝ) * I.a))
    IsIntegralProjective01 (Set.Icc I.lo I.hi) f ∧ f '' Set.Icc I.lo I.hi = Set.Icc J.lo J.hi ∧
      f I.lo = J.lo ∧ f I.hi = J.hi ∧
      ∀ g : ℝ → ℝ, IsIntegralProjective01 (Set.Icc I.lo I.hi) g →
        Set.MapsTo g (Set.Icc I.lo I.hi) (Set.Icc J.lo J.hi) → g I.lo = J.lo → g I.hi = J.hi →
          Set.EqOn g f (Set.Icc I.lo I.hi) := by
  exact S7.linearFractional_isIntegralProjective01_and_unique' hI hJ
