-- Prove2me | solution 1 for FuzzyExtractors.Hamming.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T01:39:27.575396+00:00
-- url     : https://prove2.me/submissions/3d01319b-3e8f-46a6-b501-94a0b0311416

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic

open scoped BigOperators ENNReal NNReal Classical
open FuzzyExtractors.Hamming

namespace Lemma21Proof

noncomputable def guessingMass {α : Type*} (W : PMF α) : ℝ≥0∞ :=
  ⨆ w, W w

noncomputable def guessing {α : Type*} (W : PMF α) : ℝ :=
  (guessingMass W).toReal

theorem guessingMass_le_one {α : Type*} (W : PMF α) : guessingMass W ≤ 1 :=
  iSup_le fun w => W.coe_le_one w

theorem guessingMass_ne_top {α : Type*} (W : PMF α) : guessingMass W ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (guessingMass_le_one W) ENNReal.one_lt_top)

theorem guessing_pos {α : Type*} (W : PMF α) : 0 < guessing W := by
  obtain ⟨w, hw⟩ := W.support_nonempty
  have hpos : 0 < guessingMass W :=
    lt_of_lt_of_le (W.apply_pos_iff w |>.mpr hw) (le_iSup (fun w => W w) w)
  exact ENNReal.toReal_pos hpos.ne' (guessingMass_ne_top W)

theorem minEntropy_eq_neg_log_guessing {α : Type*} (W : PMF α) :
    minEntropy W = -Real.logb 2 (guessing W) := rfl

theorem mass_tsum {A : Type*} (P : PMF A) : ∑' a, (P a).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq P.apply_ne_top, P.tsum_coe, ENNReal.toReal_one]

theorem mass_sum {α : Type*} [Fintype α] (W : PMF α) : ∑ w, (W w).toReal = 1 := by
  have h := mass_tsum W
  rwa [tsum_fintype] at h

noncomputable def average {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card A

theorem average_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    average (fun _ : A => c) = c := by
  have h : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [average, h]

theorem average_mul {A : Type*} [Fintype A] (c : ℝ) (f : A → ℝ) :
    average (fun a => c * f a) = c * average f := by
  simp [average, ← Finset.mul_sum, mul_div_assoc]

theorem average_sum {A B : Type*} [Fintype A] [Fintype B] (f : A → B → ℝ) :
    average (fun a => ∑ b, f a b) = ∑ b, average (fun a => f a b) := by
  simp only [average, Finset.sum_div]
  rw [Finset.sum_comm]

theorem average_nonneg {A : Type*} [Fintype A] {f : A → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ average f := by
  exact div_nonneg (Finset.sum_nonneg fun a _ => h a) (Nat.cast_nonneg _)

set_option linter.unusedSectionVars false

section AbstractHash

variable {α X B : Type*} [Fintype α] [DecidableEq α] [Fintype X] [Nonempty X]
  [Fintype B] [DecidableEq B] [Nonempty B]

noncomputable def bucket (H : X → α → B) (a : α → ℝ) (x : X) (y : B) : ℝ :=
  ∑ w, if H x w = y then a w else 0

theorem sum_bucket (H : X → α → B) (a : α → ℝ) (x : X) :
    ∑ y, bucket H a x y = ∑ w, a w := by
  simp only [bucket]
  rw [Finset.sum_comm]
  simp

theorem sum_bucket_sq (H : X → α → B) (a : α → ℝ) (x : X) :
    ∑ y, (bucket H a x y) ^ 2 =
      ∑ w, ∑ v, (if H x w = H x v then (1 : ℝ) else 0) * (a w * a v) := by
  simp only [bucket, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases he : H x w = H x v
  · simp [← he, mul_comm]
  · simp [he, Ne.symm he, ite_mul, mul_ite]

theorem collision_all (H : X → α → B)
    (hH : ∀ a b, a ≠ b → average (fun x : X => if H x a = H x b then (1 : ℝ) else 0) =
      1 / Fintype.card B)
    (w v : α) :
    average (fun x : X => if H x w = H x v then (1 : ℝ) else 0) =
      1 / Fintype.card B + (if w = v then (1 : ℝ) - 1 / Fintype.card B else 0) := by
  by_cases h : w = v
  · subst v
    simp [average_const]
  · rw [hH w v h, if_neg h, add_zero]

theorem second_moment (H : X → α → B)
    (hH : ∀ a b, a ≠ b → average (fun x : X => if H x a = H x b then (1 : ℝ) else 0) =
      1 / Fintype.card B)
    (a : α → ℝ) :
    average (fun x : X => ∑ y, (bucket H a x y) ^ 2) =
      (∑ w, a w) ^ 2 / Fintype.card B +
        (1 - 1 / Fintype.card B) * ∑ w, (a w) ^ 2 := by
  simp_rw [sum_bucket_sq, average_sum]
  have hh (w v : α) : average (fun x : X =>
      (if H x w = H x v then (1 : ℝ) else 0) * (a w * a v)) =
      (1 / Fintype.card B + if w = v then (1 : ℝ) - 1 / Fintype.card B else 0) *
        (a w * a v) := by
    simpa only [mul_comm] using
      (average_mul (a w * a v) (fun x : X => if H x w = H x v then (1 : ℝ) else 0)).trans
        (congrArg (fun z : ℝ => (a w * a v) * z) (collision_all H hH w v))
  simp_rw [hh, add_mul, Finset.sum_add_distrib]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [← sq, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem variance (H : X → α → B)
    (hH : ∀ a b, a ≠ b → average (fun x : X => if H x a = H x b then (1 : ℝ) else 0) =
      1 / Fintype.card B)
    (a : α → ℝ) :
    average (fun x : X => ∑ y,
      (bucket H a x y - (∑ w, a w) / Fintype.card B) ^ 2) =
      (1 - 1 / Fintype.card B) * ∑ w, (a w) ^ 2 := by
  have hb : (Fintype.card B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hp (x : X) : (∑ y,
      (bucket H a x y - (∑ w, a w) / Fintype.card B) ^ 2) =
      (∑ y, (bucket H a x y) ^ 2) - (∑ w, a w) ^ 2 / Fintype.card B := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_bucket]
    field_simp
    ring
  simp_rw [hp]
  unfold average
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sub_div]
  have hs := second_moment H hH a
  unfold average at hs
  have hc : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [mul_div_cancel_left₀ _ hc, hs]
  ring

noncomputable def hashL1 (H : X → α → B) (a : α → ℝ) : ℝ :=
  average (fun x : X => ∑ y, |bucket H a x y - (∑ w, a w) / Fintype.card B|)

omit [DecidableEq α] [Nonempty X] [Nonempty B] in
theorem hashL1_nonneg (H : X → α → B) (a : α → ℝ) : 0 ≤ hashL1 H a :=
  average_nonneg fun _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem hashL1_sq (H : X → α → B)
    (hH : ∀ a b, a ≠ b → average (fun x : X => if H x a = H x b then (1 : ℝ) else 0) =
      1 / Fintype.card B)
    (a : α → ℝ) (g : ℝ) (ha : ∀ w, 0 ≤ a w) (hag : ∀ w, a w ≤ g) :
    (hashL1 H a) ^ 2 ≤ (Fintype.card B : ℝ) * ((∑ w, a w) * g) := by
  let d : X × B → ℝ := fun p => bucket H a p.1 p.2 - (∑ w, a w) / Fintype.card B
  have hs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (X × B))
    (fun _ => (1 : ℝ)) (fun p => |d p|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, sq_abs, Fintype.card_prod, Nat.cast_mul,
    Fintype.sum_prod_type] at hs
  have hc : 0 < (Fintype.card X : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hb : 0 ≤ (Fintype.card B : ℝ) := Nat.cast_nonneg _
  have hv := variance H hH a
  change (∑ x, ∑ y, (d (x, y)) ^ 2) / (Fintype.card X : ℝ) = _ at hv
  have hsum : (∑ w, (a w) ^ 2) ≤ (∑ w, a w) * g := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun w _ => by nlinarith [mul_le_mul_of_nonneg_left (hag w) (ha w)]
  have hvar : (∑ x, ∑ y, (d (x, y)) ^ 2) / (Fintype.card X : ℝ) ≤ (∑ w, a w) * g := by
    rw [hv]
    apply le_trans _ hsum
    have hn := Finset.sum_nonneg (s := Finset.univ) (fun w _ => sq_nonneg (a w))
    have hi : 0 ≤ 1 / (Fintype.card B : ℝ) := by positivity
    nlinarith
  have hv' := (div_le_iff₀ hc).mp hvar
  have hm := mul_le_mul_of_nonneg_left hv' (mul_nonneg hc.le hb)
  unfold hashL1 average
  change ((∑ x, ∑ y, |d (x, y)|) / (Fintype.card X : ℝ)) ^ 2 ≤ _
  rw [div_pow, div_le_iff₀ (sq_pos_of_pos hc)]
  nlinarith [hs]

end AbstractHash

theorem universal_collision {α X : Type} [Fintype X] {ℓ : ℕ}
    (H : X → α → (Fin ℓ → Bool)) (hH : IsUniversal H) (a b : α) (hab : a ≠ b) :
    average (fun x : X => if H x a = H x b then (1 : ℝ) else 0) =
      1 / (Fintype.card (Fin ℓ → Bool) : ℝ) := by
  unfold average
  have hsum : (∑ x : X, if H x a = H x b then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun x => H x a = H x b).card : ℝ) := by
    simp [Finset.sum_boole]
  rw [hsum, hH a b hab]
  have hcard : (Fintype.card (Fin ℓ → Bool) : ℝ) = (2 : ℝ) ^ ℓ := by
    simp [Fintype.card_fin]
  rw [hcard, zpow_neg, zpow_natCast, one_div]

theorem extract_mass_enn_no_aux {α X : Type} [Fintype α] [Fintype X] [Nonempty X] {ℓ : ℕ}
    (H : X → α → (Fin ℓ → Bool)) (W : PMF α)
    (y : Fin ℓ → Bool) (x : X) :
    extractLaw (fun w x => H x w) W (y, x) =
      (∑ w, if H x w = y then W w else 0) * (Fintype.card X : ℝ≥0∞)⁻¹ := by
  have hk (w : α) :
      ((PMF.uniformOfFintype X).map fun x' => (H x' w, x')) (y, x) =
      if y = H x w then (Fintype.card X : ℝ≥0∞)⁻¹ else 0 := by
    rw [PMF.map_apply, tsum_eq_single x]
    · simp [Prod.mk.injEq]
    · intro x' hx'
      have hh : x ≠ x' := Ne.symm hx'
      simp [Prod.mk.injEq, hh]
  rw [extractLaw, PMF.bind_apply, tsum_fintype]
  simp_rw [hk, mul_ite, mul_zero]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _
  by_cases he : y = H x w
  · simp [he]
  · simp [he, Ne.symm he]

theorem extract_mass_real_no_aux {α X : Type} [Fintype α] [Fintype X] [Nonempty X] {ℓ : ℕ}
    (H : X → α → (Fin ℓ → Bool)) (W : PMF α)
    (y : Fin ℓ → Bool) (x : X) :
    (extractLaw (fun w x => H x w) W (y, x)).toReal =
      bucket H (fun w => (W w).toReal) x y / Fintype.card X := by
  rw [extract_mass_enn_no_aux, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [ENNReal.toReal_sum (fun w _ => by split_ifs <;> simp [W.apply_ne_top])]
  simp only [bucket, apply_ite ENNReal.toReal, ENNReal.toReal_zero, div_eq_mul_inv]

theorem replacement_mass_enn_no_aux {B X : Type} [Fintype B] [Nonempty B]
    (Q : PMF (B × X)) (y : B) (x : X) :
    (Q.bind fun a => (PMF.uniformOfFintype B).map fun u => (u, a.2)) (y, x) =
      (∑ b, Q (b, x)) * (Fintype.card B : ℝ≥0∞)⁻¹ := by
  have hk (x' : X) :
      ((PMF.uniformOfFintype B).map fun u => (u, x')) (y, x) =
      if x = x' then (Fintype.card B : ℝ≥0∞)⁻¹ else 0 := by
    rw [PMF.map_apply, tsum_eq_single y]
    · simp [Prod.mk.injEq]
    · intro u hu
      simp [Prod.mk.injEq, Ne.symm hu]
  rw [PMF.bind_apply, ENNReal.tsum_prod']
  simp_rw [hk, mul_ite, mul_zero]
  simp only [tsum_ite_eq', tsum_fintype, ← Finset.sum_mul]

theorem replacement_mass_real_no_aux {α X : Type} [Fintype α] [Fintype X] [Nonempty X] {ℓ : ℕ}
    (H : X → α → (Fin ℓ → Bool)) (W : PMF α)
    (y : Fin ℓ → Bool) (x : X) :
    (((extractLaw (fun w x => H x w) W).bind
      fun a => (uniformBits ℓ).map fun u => (u, a.2)) (y, x)).toReal =
      (∑ w, (W w).toReal) / Fintype.card (Fin ℓ → Bool) / Fintype.card X := by
  rw [uniformBits, replacement_mass_enn_no_aux, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  rw [ENNReal.toReal_sum (fun _ _ => PMF.apply_ne_top _ _)]
  simp only [extract_mass_real_no_aux, ← Finset.sum_div, sum_bucket]
  ring

theorem hash_distance_eq_no_aux {α X : Type} [Fintype α] [Fintype X] [Nonempty X] {ℓ : ℕ}
    (H : X → α → (Fin ℓ → Bool)) (W : PMF α) :
    statDist (extractLaw (fun w x => H x w) W)
      ((extractLaw (fun w x => H x w) W).bind
        fun a => (uniformBits ℓ).map fun u => (u, a.2)) =
      (1 / 2 : ℝ) * hashL1 H (fun w => (W w).toReal) := by
  unfold statDist hashL1 average
  congr 1
  rw [tsum_fintype, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [extract_mass_real_no_aux, replacement_mass_real_no_aux,
    ← sub_div, abs_div,
    abs_of_nonneg (Nat.cast_nonneg (Fintype.card X) : (0 : ℝ) ≤ _),
    ← Finset.sum_div]

theorem hash_security_no_aux {α X : Type} [Fintype α] [Fintype X] [Nonempty X] {ℓ : ℕ}
    (H : X → α → (Fin ℓ → Bool)) (hH : IsUniversal H) (W : PMF α) :
    statDist (extractLaw (fun w x => H x w) W)
      ((extractLaw (fun w x => H x w) W).bind
        fun y => (uniformBits ℓ).map fun u => (u, y.2)) ≤
      (1 / 2 : ℝ) * Real.sqrt ((Fintype.card (Fin ℓ → Bool) : ℝ) * guessing W) := by
  rw [hash_distance_eq_no_aux H W]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.le_sqrt_of_sq_le
  have hsq := hashL1_sq H (universal_collision H hH) (fun w => (W w).toReal) (guessing W)
    (fun _ => ENNReal.toReal_nonneg)
    (fun w => ENNReal.toReal_mono (guessingMass_ne_top W) (le_iSup (fun w => W w) w))
  rw [mass_sum W, one_mul] at hsq
  exact hsq

theorem length_product_bound (g ε m : ℝ) (ℓ : ℕ)
    (hg : 0 < g) (hε : 0 < ε)
    (hm : m ≤ -Real.logb 2 g)
    (hℓ : (ℓ : ℝ) ≤ m - 2 * Real.logb 2 (1 / ε) + 2) :
    (2 : ℝ) ^ ℓ * g ≤ 4 * ε ^ 2 := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hp : 0 < (2 : ℝ) ^ ℓ * g := mul_pos (pow_pos htwo _) hg
  have hr : 0 < 4 * ε ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hε)
  apply (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hp hr).mp
  have hl : Real.logb 2 ((2 : ℝ) ^ ℓ * g) = (ℓ : ℝ) + Real.logb 2 g := by
    rw [Real.logb_mul (pow_ne_zero _ htwo.ne') hg.ne', Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    ring
  have hrlog : Real.logb 2 (4 * ε ^ 2) = 2 + 2 * Real.logb 2 ε := by
    rw [Real.logb_mul (by norm_num : (4 : ℝ) ≠ 0) (pow_ne_zero _ hε.ne'), Real.logb_pow]
    have : Real.logb 2 (4 : ℝ) = 2 := by
      calc
        Real.logb 2 (4 : ℝ) = Real.logb 2 ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
        _ = 2 := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; norm_num
    rw [this]
    norm_num
  have hi : Real.logb 2 (1 / ε) = -Real.logb 2 ε := by simp [one_div]
  rw [hl, hrlog]
  rw [hi] at hℓ
  linarith

theorem half_sqrt_le (x ε : ℝ) (hε : 0 < ε) (hx : x ≤ 4 * ε ^ 2) :
    (1 / 2 : ℝ) * Real.sqrt x ≤ ε := by
  have h : Real.sqrt x ≤ 2 * ε := (Real.sqrt_le_left (by positivity)).2 (by nlinarith)
  linarith

end Lemma21Proof

theorem solution {α X : Type} [Fintype α] [Fintype X] [Nonempty X] {ℓ : ℕ}
    (H : X → α → (Fin ℓ → Bool)) (hH : IsUniversal H) :
    (∀ W : PMF α,
      statDist (extractLaw (fun w x => H x w) W)
          ((extractLaw (fun w x => H x w) W).bind fun y => (uniformBits ℓ).map fun u => (u, y.2))
        ≤ (1 / 2 : ℝ) * Real.sqrt ((2 : ℝ) ^ (-minEntropy W) * (2 : ℝ) ^ (ℓ : ℝ))) ∧
    (∀ m ε : ℝ, 0 < ε → (ℓ : ℝ) ≤ m - 2 * Real.logb 2 (1 / ε) + 2 →
      IsStrongExtractor m ε (fun w x => H x w)) := by
  have hcard : (Fintype.card (Fin ℓ → Bool) : ℝ) = (2 : ℝ) ^ ℓ := by
    simp [Fintype.card_fin]
  constructor
  · intro W
    have hg : (2 : ℝ) ^ (-minEntropy W) = Lemma21Proof.guessing W := by
      rw [Lemma21Proof.minEntropy_eq_neg_log_guessing, neg_neg]
      exact Real.rpow_logb (by norm_num) (by norm_num) (Lemma21Proof.guessing_pos W)
    have hpow : (2 : ℝ) ^ (ℓ : ℝ) = (Fintype.card (Fin ℓ → Bool) : ℝ) := by
      rw [hcard, Real.rpow_natCast]
    rw [hg, hpow, mul_comm (Lemma21Proof.guessing W)]
    exact Lemma21Proof.hash_security_no_aux H hH W
  · intro m ε hε hℓ W hm
    refine (Lemma21Proof.hash_security_no_aux H hH W).trans ?_
    apply Lemma21Proof.half_sqrt_le _ ε hε
    rw [hcard]
    exact Lemma21Proof.length_product_bound (Lemma21Proof.guessing W) ε m ℓ
      (Lemma21Proof.guessing_pos W) hε
      (by simpa only [Lemma21Proof.minEntropy_eq_neg_log_guessing] using hm) hℓ
