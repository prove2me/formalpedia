-- Prove2me | solution 1 for CannonFloydParry.isIntegralProjective01_restrict_and_glue
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T20:58:08.397195+00:00
-- url     : https://prove2.me/submissions/00c11378-7380-4a2c-9b3c-64f6b1b08dc6

import Definitions.Def_CannonFloydParry_PIP
import Theorems.Thm_CannonFloydParry_linearFractional_isIntegralProjective01_and_unique

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

lemma IsIntegralProjective01.mono {U V : Set ℝ} {f : ℝ → ℝ} (h : IsIntegralProjective01 U f)
    (hVU : V ⊆ U) : IsIntegralProjective01 V f := by
  obtain ⟨hU, A, hA⟩ := h
  exact ⟨hVU.trans hU, A, fun t ht => hA t (hVU ht)⟩

/-! ### Farey intervals -/

section Farey

variable {I : FracInterval}

lemma IsFarey.det (hI : I.IsFarey) : (I.a : ℤ) * I.d - (I.b : ℤ) * I.c = -1 := hI.2.2.2.2.2

lemma IsFarey.detR (hI : I.IsFarey) : (I.a : ℝ) * I.d - (I.b : ℝ) * I.c = -1 := by
  exact_mod_cast (IsFarey.det hI)

lemma IsFarey.b_pos (hI : I.IsFarey) : (0 : ℝ) < I.b := by exact_mod_cast hI.1
lemma IsFarey.d_pos (hI : I.IsFarey) : (0 : ℝ) < I.d := by exact_mod_cast hI.2.2.1

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

lemma IsFarey.lo_lt_hi (hI : I.IsFarey) : I.lo < I.hi := by
  unfold FracInterval.lo FracInterval.hi
  rw [div_lt_div_iff₀ (IsFarey.b_pos hI) (IsFarey.d_pos hI)]
  linarith [(IsFarey.detR hI)]

/-- The mediant. -/
lemma leftPart_lo : I.leftPart.lo = I.lo := rfl
lemma rightPart_hi : I.rightPart.hi = I.hi := rfl
lemma leftPart_hi : I.leftPart.hi = ((I.a : ℝ) + I.c) / ((I.b : ℝ) + I.d) := by
  simp [FracInterval.leftPart, FracInterval.hi]
lemma rightPart_lo : I.rightPart.lo = ((I.a : ℝ) + I.c) / ((I.b : ℝ) + I.d) := by
  simp [FracInterval.rightPart, FracInterval.lo]

lemma IsFarey.lo_le_mediant (hI : I.IsFarey) :
    I.lo ≤ ((I.a : ℝ) + I.c) / ((I.b : ℝ) + I.d) := by
  unfold FracInterval.lo
  rw [div_le_div_iff₀ (IsFarey.b_pos hI) (by linarith [(IsFarey.b_pos hI), (IsFarey.d_pos hI)])]
  nlinarith [(IsFarey.detR hI)]

lemma IsFarey.mediant_le_hi (hI : I.IsFarey) :
    ((I.a : ℝ) + I.c) / ((I.b : ℝ) + I.d) ≤ I.hi := by
  unfold FracInterval.hi
  rw [div_le_div_iff₀ (by linarith [(IsFarey.b_pos hI), (IsFarey.d_pos hI)]) (IsFarey.d_pos hI)]
  nlinarith [(IsFarey.detR hI)]

lemma IsFarey.leftPart_subset (hI : I.IsFarey) :
    Set.Icc I.leftPart.lo I.leftPart.hi ⊆ Set.Icc I.lo I.hi := by
  rw [leftPart_lo, leftPart_hi]
  exact Set.Icc_subset_Icc le_rfl (IsFarey.mediant_le_hi hI)

lemma IsFarey.rightPart_subset (hI : I.IsFarey) :
    Set.Icc I.rightPart.lo I.rightPart.hi ⊆ Set.Icc I.lo I.hi := by
  rw [rightPart_hi, rightPart_lo]
  exact Set.Icc_subset_Icc (IsFarey.lo_le_mediant hI) le_rfl

end Farey

/-! ### Reduced fractions -/

/-! ### A continuous map with the right bounds maps `[l, h]` onto `[f l, f h]` -/

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

/-- The published theorem, stated for `mob I J` (which is definitionally its `f`). -/
lemma mob_pub (hI : I.IsFarey) (hJ : J.IsFarey) :
    IsIntegralProjective01 (Set.Icc I.lo I.hi) (mob I J) ∧
      mob I J '' Set.Icc I.lo I.hi = Set.Icc J.lo J.hi ∧
      mob I J I.lo = J.lo ∧ mob I J I.hi = J.hi ∧
      ∀ g : ℝ → ℝ, IsIntegralProjective01 (Set.Icc I.lo I.hi) g →
        Set.MapsTo g (Set.Icc I.lo I.hi) (Set.Icc J.lo J.hi) → g I.lo = J.lo → g I.hi = J.hi →
          Set.EqOn g (mob I J) (Set.Icc I.lo I.hi) :=
  CannonFloydParry.linearFractional_isIntegralProjective01_and_unique hI hJ

lemma mob_isIP (hI : I.IsFarey) (hJ : J.IsFarey) :
    IsIntegralProjective01 (Set.Icc I.lo I.hi) (mob I J) :=
  (mob_pub hI hJ).1

lemma lo_mem (hI : I.IsFarey) : I.lo ∈ Set.Icc I.lo I.hi := ⟨le_rfl, (IsFarey.lo_lt_hi hI).le⟩
lemma hi_mem (hI : I.IsFarey) : I.hi ∈ Set.Icc I.lo I.hi := ⟨(IsFarey.lo_lt_hi hI).le, le_rfl⟩

lemma mediant_mem (hI : I.IsFarey) :
    ((I.a : ℝ) + I.c) / ((I.b : ℝ) + I.d) ∈ Set.Icc I.lo I.hi :=
  ⟨IsFarey.lo_le_mediant hI, IsFarey.mediant_le_hi hI⟩

lemma mob_lo (hI : I.IsFarey) (hJ : J.IsFarey) : mob I J I.lo = J.lo := (mob_pub hI hJ).2.2.1

lemma mob_hi (hI : I.IsFarey) (hJ : J.IsFarey) : mob I J I.hi = J.hi := (mob_pub hI hJ).2.2.2.1

lemma mob_mediant (hI : I.IsFarey) (hJ : J.IsFarey) :
    mob I J (((I.a : ℝ) + I.c) / ((I.b : ℝ) + I.d)) = ((J.a : ℝ) + J.c) / ((J.b : ℝ) + J.d) := by
  have hD := mobD_pos hI hJ (mediant_mem hI)
  have hbd : (0 : ℝ) < I.b + I.d := by linarith [IsFarey.b_pos hI, IsFarey.d_pos hI]
  have hbd' : (0 : ℝ) < J.b + J.d := by linarith [IsFarey.b_pos hJ, IsFarey.d_pos hJ]
  unfold mob at *
  rw [div_eq_div_iff hD.ne' hbd'.ne']
  unfold mobN mobD
  field_simp
  ring

lemma mob_image (hI : I.IsFarey) (hJ : J.IsFarey) :
    mob I J '' Set.Icc I.lo I.hi = Set.Icc J.lo J.hi := (mob_pub hI hJ).2.1

/-! ### Uniqueness -/

/-- An integral projective map on `[I.lo, I.hi]` taking the endpoints to `J.lo` and `J.hi` maps
`[I.lo, I.hi]` into `[J.lo, J.hi]`: it is linear fractional with positive denominator, hence
monotone. -/
lemma IP_mapsTo (hI : I.IsFarey) (hJ : J.IsFarey) {g : ℝ → ℝ}
    (hg : IsIntegralProjective01 (Set.Icc I.lo I.hi) g) (hlo : g I.lo = J.lo)
    (hhi : g I.hi = J.hi) : Set.MapsTo g (Set.Icc I.lo I.hi) (Set.Icc J.lo J.hi) := by
  obtain ⟨-, B, hB⟩ := hg
  obtain ⟨p, q, r, s, hdet, hgl⟩ := glAct_entries B
  have hD : ∀ u ∈ Set.Icc I.lo I.hi, 0 < (r : ℝ) * u + s := fun u hu => by
    have := denom_pos hB hu; rwa [(hgl u).2] at this
  have key : ∀ u ∈ Set.Icc I.lo I.hi, ∀ v ∈ Set.Icc I.lo I.hi,
      g v - g u = ((p * s - q * r : ℤ) : ℝ) * (v - u) / (((r : ℝ) * u + s) * ((r : ℝ) * v + s)) := by
    intro u hu v hv
    have Du := hD u hu
    have Dv := hD v hv
    rw [(hB u hu).2.2, (hB v hv).2.2, (hgl u).1, (hgl u).2, (hgl v).1, (hgl v).2,
      div_sub_div _ _ Dv.ne' Du.ne', eq_div_iff (mul_pos Du Dv).ne',
      div_mul_eq_mul_div, div_eq_iff (mul_pos Dv Du).ne']
    push_cast
    ring
  have hJlt := IsFarey.lo_lt_hi hJ
  have hIlt := IsFarey.lo_lt_hi hI
  have D0 := hD _ (lo_mem hI)
  have D1 := hD _ (hi_mem hI)
  have he : ((p * s - q * r : ℤ) : ℝ) = 1 := by
    rcases hdet with h | h
    · rw [h]; norm_num
    · exfalso
      have k := key _ (lo_mem hI) _ (hi_mem hI)
      rw [hlo, hhi, h] at k
      have : ((-1 : ℤ) : ℝ) * (I.hi - I.lo) / (((r : ℝ) * I.lo + s) * ((r : ℝ) * I.hi + s)) < 0 :=
        div_neg_of_neg_of_pos (by push_cast; linarith) (mul_pos D0 D1)
      linarith
  intro t ht
  have Dt := hD t ht
  have k0 := key _ (lo_mem hI) _ ht
  have k1 := key _ ht _ (hi_mem hI)
  rw [he, one_mul, hlo] at k0
  rw [he, one_mul, hhi] at k1
  constructor
  · have : 0 ≤ (t - I.lo) / (((r : ℝ) * I.lo + s) * ((r : ℝ) * t + s)) :=
      div_nonneg (by linarith [ht.1]) (mul_pos D0 Dt).le
    linarith
  · have : 0 ≤ (I.hi - t) / (((r : ℝ) * t + s) * ((r : ℝ) * I.hi + s)) :=
      div_nonneg (by linarith [ht.2]) (mul_pos Dt D1).le
    linarith

lemma mob_unique (hI : I.IsFarey) (hJ : J.IsFarey) {g : ℝ → ℝ}
    (hg : IsIntegralProjective01 (Set.Icc I.lo I.hi) g) (hlo : g I.lo = J.lo)
    (hhi : g I.hi = J.hi) : Set.EqOn g (mob I J) (Set.Icc I.lo I.hi) :=
  (mob_pub hI hJ).2.2.2.2 g hg (IP_mapsTo hI hJ hg hlo hhi) hlo hhi

end CannonFloydParry.S7

/-!
# Integral subsimplices of `[0,1]` and the maps between them (CFP §7, pp. 251–253)
-/

namespace CannonFloydParry.S7

/-! ### Target: the criterion of p. 251 -/


/-! ### Target: the two parts are integral subsimplices -/


/-! ### Target: the unique integral projective map between two Farey intervals -/


/-! ### Target: restriction and gluing -/

lemma IP_mediant {I J : FracInterval} (hI : I.IsFarey) (hJ : J.IsFarey) {f : ℝ → ℝ}
    (hf : IsIntegralProjective01 (Set.Icc I.lo I.hi) f) (h1 : f I.lo = J.lo) (h2 : f I.hi = J.hi) :
    f (((I.a : ℝ) + I.c) / ((I.b : ℝ) + I.d)) = ((J.a : ℝ) + J.c) / ((J.b : ℝ) + J.d) := by
  rw [mob_unique hI hJ hf h1 h2 (mediant_mem hI), mob_mediant hI hJ]

lemma IP_left {I J : FracInterval} (hI : I.IsFarey) (hJ : J.IsFarey) {f : ℝ → ℝ}
    (hf : IsIntegralProjective01 (Set.Icc I.lo I.hi) f) (h1 : f I.lo = J.lo) (h2 : f I.hi = J.hi) :
    Set.EqOn f (mob I.leftPart J.leftPart) (Set.Icc I.leftPart.lo I.leftPart.hi) :=
  mob_unique (IsFarey.leftPart hI) (IsFarey.leftPart hJ) (IsIntegralProjective01.mono hf (IsFarey.leftPart_subset hI))
    h1 (by rw [leftPart_hi, leftPart_hi, IP_mediant hI hJ hf h1 h2])

lemma IP_right {I J : FracInterval} (hI : I.IsFarey) (hJ : J.IsFarey) {f : ℝ → ℝ}
    (hf : IsIntegralProjective01 (Set.Icc I.lo I.hi) f) (h1 : f I.lo = J.lo) (h2 : f I.hi = J.hi) :
    Set.EqOn f (mob I.rightPart J.rightPart) (Set.Icc I.rightPart.lo I.rightPart.hi) :=
  mob_unique (IsFarey.rightPart hI) (IsFarey.rightPart hJ) (IsIntegralProjective01.mono hf (IsFarey.rightPart_subset hI))
    (by rw [rightPart_lo, rightPart_lo, IP_mediant hI hJ hf h1 h2]) h2

theorem isIntegralProjective01_restrict_and_glue' {I J : FracInterval} (hI : I.IsFarey)
    (hJ : J.IsFarey) :
    (∀ f : ℝ → ℝ, IsIntegralProjective01 (Set.Icc I.lo I.hi) f → f I.lo = J.lo → f I.hi = J.hi →
        f I.rightPart.lo = J.rightPart.lo ∧
          f '' Set.Icc I.leftPart.lo I.leftPart.hi = Set.Icc J.leftPart.lo J.leftPart.hi ∧
          f '' Set.Icc I.rightPart.lo I.rightPart.hi = Set.Icc J.rightPart.lo J.rightPart.hi) ∧
      ∀ g₁ g₂ : ℝ → ℝ,
        IsIntegralProjective01 (Set.Icc I.leftPart.lo I.leftPart.hi) g₁ →
        g₁ I.leftPart.lo = J.leftPart.lo → g₁ I.leftPart.hi = J.leftPart.hi →
        IsIntegralProjective01 (Set.Icc I.rightPart.lo I.rightPart.hi) g₂ →
        g₂ I.rightPart.lo = J.rightPart.lo → g₂ I.rightPart.hi = J.rightPart.hi →
        ∃ g : ℝ → ℝ, IsIntegralProjective01 (Set.Icc I.lo I.hi) g ∧
          Set.EqOn g g₁ (Set.Icc I.leftPart.lo I.leftPart.hi) ∧
          Set.EqOn g g₂ (Set.Icc I.rightPart.lo I.rightPart.hi) := by
  refine ⟨fun f hf h1 h2 => ⟨?_, ?_, ?_⟩, fun g₁ g₂ hg₁ a₁ b₁ hg₂ a₂ b₂ => ?_⟩
  · rw [rightPart_lo, rightPart_lo, IP_mediant hI hJ hf h1 h2]
  · rw [(IP_left hI hJ hf h1 h2).image_eq, mob_image (IsFarey.leftPart hI) (IsFarey.leftPart hJ)]
  · rw [(IP_right hI hJ hf h1 h2).image_eq,
      mob_image (IsFarey.rightPart hI) (IsFarey.rightPart hJ)]
  · refine ⟨mob I J, mob_isIP hI hJ, ?_, ?_⟩
    · exact (IP_left hI hJ (mob_isIP hI hJ) (mob_lo hI hJ) (mob_hi hI hJ)).trans
        (mob_unique (IsFarey.leftPart hI) (IsFarey.leftPart hJ) hg₁ a₁ b₁).symm
    · exact (IP_right hI hJ (mob_isIP hI hJ) (mob_lo hI hJ) (mob_hi hI hJ)).trans
        (mob_unique (IsFarey.rightPart hI) (IsFarey.rightPart hJ) hg₂ a₂ b₂).symm

end CannonFloydParry.S7

open CannonFloydParry in
theorem solution {I J : FracInterval} (hI : I.IsFarey)
    (hJ : J.IsFarey) :
    (∀ f : ℝ → ℝ, IsIntegralProjective01 (Set.Icc I.lo I.hi) f → f I.lo = J.lo → f I.hi = J.hi →
        f I.rightPart.lo = J.rightPart.lo ∧
          f '' Set.Icc I.leftPart.lo I.leftPart.hi = Set.Icc J.leftPart.lo J.leftPart.hi ∧
          f '' Set.Icc I.rightPart.lo I.rightPart.hi = Set.Icc J.rightPart.lo J.rightPart.hi) ∧
      ∀ g₁ g₂ : ℝ → ℝ,
        IsIntegralProjective01 (Set.Icc I.leftPart.lo I.leftPart.hi) g₁ →
        g₁ I.leftPart.lo = J.leftPart.lo → g₁ I.leftPart.hi = J.leftPart.hi →
        IsIntegralProjective01 (Set.Icc I.rightPart.lo I.rightPart.hi) g₂ →
        g₂ I.rightPart.lo = J.rightPart.lo → g₂ I.rightPart.hi = J.rightPart.hi →
        ∃ g : ℝ → ℝ, IsIntegralProjective01 (Set.Icc I.lo I.hi) g ∧
          Set.EqOn g g₁ (Set.Icc I.leftPart.lo I.leftPart.hi) ∧
          Set.EqOn g g₂ (Set.Icc I.rightPart.lo I.rightPart.hi) := by
  exact S7.isIntegralProjective01_restrict_and_glue' hI hJ
