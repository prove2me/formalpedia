-- Prove2me | solution 1 for Bernstein.theorem_B_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T17:54:54.246501+00:00
-- url     : https://prove2.me/submissions/a8b21031-9c09-4820-8700-b1eaf96c265b

import Mathlib
import Definitions.Def_Curve25519Bernstein
import Theorems.Thm_Bernstein_group_law
namespace Bernstein.Montgomery
open WeierstrassCurve

variable {p : ℕ} [Fact p.Prime] {A : ℤ}

lemma natCast_ne_zero_of_lt (hp : 5 ≤ p) (n : ℕ) (hn0 : 0 < n) (hn : n < 5) :
    ((n : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
  intro h
  have := Nat.le_of_dvd hn0 h
  omega

lemma four_ne_zero' (hp : 5 ≤ p) : (4 : ZMod p) ≠ 0 := by
  exact_mod_cast natCast_ne_zero_of_lt hp 4 (by norm_num) (by norm_num)

lemma four_ne_zero_Fp2 (hp : 5 ≤ p) : (4 : Fp2 p) ≠ 0 := by
  intro h
  apply four_ne_zero' hp
  apply (emb p).injective
  rw [map_ofNat, map_zero]; exact h

lemma curve_eq (u y : Fp2 p) (h : (Ecurve p A).Nonsingular u y) :
    y ^ 2 = u ^ 3 + emb p A * u ^ 2 + u := by
  have := h.1
  rw [Affine.equation_iff] at this
  simp [Ecurve, curve, WeierstrassCurve.baseChange, WeierstrassCurve.map] at this
  rw [map_intCast]
  linear_combination this

lemma frac_eq_none {x z : ZMod p} : frac x z = (none : Option (Fp2 p)) ↔ z = 0 := by
  unfold frac; split_ifs with h <;> simp [h]

lemma frac_eq_some {x z : ZMod p} {u : Fp2 p} :
    frac x z = some u ↔ z ≠ 0 ∧ u = emb p (x / z) := by
  unfold frac; split_ifs with h <;> simp [h, eq_comm]

lemma frac_of_ne {x z : ZMod p} (hz : z ≠ 0) : frac x z = some (emb p (x / z)) := by
  simp [frac, hz]

lemma X_zero : X (0 : Pt p A) = none := rfl

lemma X_some (u y : Fp2 p) (h) : X (.some u y h : Pt p A) = some u := rfl

theorem montgomery_identity {F : Type*} [Field F] (a u u' y y' : F) (hd : u' - u ≠ 0)
    (hy : y ^ 2 = u ^ 3 + a * u ^ 2 + u) (hy' : y' ^ 2 = u' ^ 3 + a * u' ^ 2 + u') :
    (((y' - y) / (u' - u)) ^ 2 - a - u - u') * (((-y' - y) / (u' - u)) ^ 2 - a - u - u')
      * (u - u') ^ 2 = (u * u' - 1) ^ 2 := by
  have hd2 : (u' - u) ^ 2 ≠ 0 := pow_ne_zero 2 hd
  have e1 : ((y' - y) / (u' - u)) ^ 2 - a - u - u' =
      ((y' - y) ^ 2 - (a + u + u') * (u' - u) ^ 2) / (u' - u) ^ 2 := by
    rw [div_pow, sub_div, mul_div_cancel_right₀ _ hd2]; ring
  have e2 : ((-y' - y) / (u' - u)) ^ 2 - a - u - u' =
      ((y' + y) ^ 2 - (a + u + u') * (u' - u) ^ 2) / (u' - u) ^ 2 := by
    rw [div_pow, sub_div, mul_div_cancel_right₀ _ hd2]; ring
  have key : ((y' - y) ^ 2 - (a + u + u') * (u' - u) ^ 2) *
      ((y' + y) ^ 2 - (a + u + u') * (u' - u) ^ 2) = (u' - u) ^ 2 * (u * u' - 1) ^ 2 := by
    linear_combination (y' ^ 2 - y ^ 2 + (u' ^ 3 + a * u' ^ 2 + u') - (u ^ 3 + a * u ^ 2 + u)) * (hy' - hy)
      - 2 * (a + u + u') * (u' - u) ^ 2 * (hy + hy')
  rw [e1, e2, div_mul_div_comm, key, show (u - u') ^ 2 = (u' - u) ^ 2 by ring]
  field_simp

theorem diffadd (hp : 5 ≤ p) (hA : ¬ IsSquare ((A : ZMod p) ^ 2 - 4)) (x z x' z' x₁ z₁ : ZMod p)
    (hxz : (x, z) ≠ (0, 0)) (hxz' : (x', z') ≠ (0, 0)) (hx₁ : x₁ ≠ 0) (hz₁ : z₁ ≠ 0)
    (Q Q' : Pt p A) (hQ : X Q = frac x z) (hQ' : X Q' = frac x' z')
    (hD : X (Q - Q') = frac x₁ z₁) :
    (4 * (x * x' - z * z') ^ 2 * z₁, 4 * (x * z' - z * x') ^ 2 * x₁) ≠ (0, 0) ∧
      X (Q + Q') = frac (4 * (x * x' - z * z') ^ 2 * z₁) (4 * (x * z' - z * x') ^ 2 * x₁) := by
  obtain ⟨-, -, -, -, -, hnegsome, -, -, -, hdbl, hadd⟩ := group_law p hp A hA
  rw [frac_of_ne hz₁] at hD
  have h4 := four_ne_zero' hp
  cases Q with
  | zero =>
    have hz : z = 0 := frac_eq_none.mp hQ.symm
    subst hz
    have hx : x ≠ 0 := by intro hx; exact hxz (by simp [hx])
    have e0 : (Affine.Point.zero : Pt p A) = 0 := rfl
    rw [e0, zero_sub] at hD
    rw [e0, zero_add]
    cases Q' with
    | zero => exact absurd hD (by rw [e0, neg_zero]; simp [X_zero])
    | some u' y' h' =>
      obtain ⟨h₁, hn⟩ := hnegsome u' y' h'
      rw [hn, X_some] at hD
      obtain ⟨hz', hu'⟩ := frac_eq_some.mp hQ'.symm
      have hrel : x' / z' = x₁ / z₁ :=
        (emb p).injective (by rw [← hu']; exact Option.some_injective _ hD)
      rw [div_eq_div_iff hz' hz₁] at hrel
      have hz3 : 4 * (x * z' - 0 * x') ^ 2 * x₁ ≠ 0 := by simp [h4, hx, hz', hx₁]
      refine ⟨fun h0 => hz3 (congrArg Prod.snd h0), ?_⟩
      rw [X_some, frac_of_ne hz3, hu']
      congr 2
      rw [div_eq_div_iff hz' hz3]
      linear_combination (-4 * x ^ 2 * x' * z') * hrel
  | some u y h =>
    obtain ⟨hz, hu⟩ := frac_eq_some.mp hQ.symm
    have hy2 := curve_eq u y h
    cases Q' with
    | zero =>
      have hz' : z' = 0 := frac_eq_none.mp hQ'.symm
      subst hz'
      have hx' : x' ≠ 0 := by intro hx; exact hxz' (by simp [hx])
      have e0 : (Affine.Point.zero : Pt p A) = 0 := rfl
      rw [e0, sub_zero, X_some] at hD
      rw [e0, add_zero]
      have hrel : x / z = x₁ / z₁ :=
        (emb p).injective (by rw [← hu]; exact Option.some_injective _ hD)
      rw [div_eq_div_iff hz hz₁] at hrel
      have hz3 : 4 * (x * 0 - z * x') ^ 2 * x₁ ≠ 0 := by simp [h4, hx', hz, hx₁]
      refine ⟨fun h0 => hz3 (congrArg Prod.snd h0), ?_⟩
      rw [X_some, frac_of_ne hz3, hu]
      congr 2
      rw [div_eq_div_iff hz hz3]
      linear_combination (-4 * x * x' ^ 2 * z) * hrel
    | some u' y' h' =>
      obtain ⟨hz', hu'⟩ := frac_eq_some.mp hQ'.symm
      have hy2' := curve_eq u' y' h'
      have hzF : emb p z ≠ 0 := (map_ne_zero (emb p)).mpr hz
      have hzF' : emb p z' ≠ 0 := (map_ne_zero (emb p)).mpr hz'
      by_cases huu : u = u'
      · have hdet : x * z' - z * x' = 0 := by
          have : x / z = x' / z' := (emb p).injective (by rw [← hu, ← hu', huu])
          rw [div_eq_div_iff hz hz'] at this
          linear_combination this
        subst huu
        by_cases hyy : y' = y
        · subst hyy
          rw [sub_self] at hD
          exact absurd hD (by simp [X_zero])
        · have hsum0 : y' + y = 0 := by
            have : (y' - y) * (y' + y) = 0 := by linear_combination hy2' - hy2
            exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hyy)
          have hy' : y' = -y := eq_neg_of_add_eq_zero_left hsum0
          subst hy'
          have hy0 : y ≠ 0 := by rintro rfl; exact hyy (by simp)
          have hQ'neg : (Affine.Point.some u (-y) h' : Pt p A) = -Affine.Point.some u y h := by
            obtain ⟨h₁, hn⟩ := hnegsome u y h
            rw [hn]
          rw [hQ'neg, sub_neg_eq_add] at hD
          rw [hQ'neg, add_neg_cancel]
          obtain ⟨hx'', h'', hsum⟩ := hdbl u y h hy0
          rw [hsum, X_some] at hD
          have hw := Option.some_injective _ hD
          rw [hx''] at hw
          have hu1 : u ^ 2 - 1 ≠ 0 := by
            intro h0
            rw [h0] at hw
            have : emb p (x₁ / z₁) ≠ 0 :=
              (map_ne_zero (emb p)).mpr (div_ne_zero hx₁ hz₁)
            apply this
            rw [← hw]; simp
          have hx3 : 4 * (x * x' - z * z') ^ 2 * z₁ ≠ 0 := by
            have hm : x * x' - z * z' ≠ 0 := by
              intro h0
              apply hu1
              have e : u ^ 2 = emb p ((x * x') / (z * z')) := by
                rw [map_div₀, map_mul, map_mul]
                have h1 := hu; have h2 := hu'
                rw [map_div₀] at h1 h2
                rw [pow_two]; nth_rewrite 1 [h1]; rw [h2]
                field_simp
              rw [e, show x * x' / (z * z') = 1 by
                rw [div_eq_one_iff_eq (mul_ne_zero hz hz')]; linear_combination h0,
                map_one, sub_self]
            exact mul_ne_zero (mul_ne_zero h4 (pow_ne_zero 2 hm)) hz₁
          refine ⟨fun h0 => hx3 (congrArg Prod.fst h0), ?_⟩
          rw [hdet]
          simp [X_zero, frac]
      · have hd : u' - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huu)
        obtain ⟨hs_ns, hsum⟩ := hadd u y u' y' h h' (Ne.symm huu)
        obtain ⟨h₁, hn⟩ := hnegsome u' y' h'
        obtain ⟨ht_ns, hdiff⟩ := hadd u y u' (-y') h h₁ (Ne.symm huu)
        rw [sub_eq_add_neg, hn, hdiff, X_some] at hD
        have ht := Option.some_injective _ hD
        have mi := montgomery_identity (emb p A) u u' y y' hd hy2 hy2'
        rw [ht] at mi
        have hdet : x * z' - z * x' ≠ 0 := by
          intro h0
          apply huu
          rw [hu, hu']
          congr 1
          rw [div_eq_div_iff hz hz']
          linear_combination h0
        have hz3 : 4 * (x * z' - z * x') ^ 2 * x₁ ≠ 0 :=
          mul_ne_zero (mul_ne_zero h4 (pow_ne_zero 2 hdet)) hx₁
        refine ⟨fun h0 => hz3 (congrArg Prod.snd h0), ?_⟩
        rw [hsum, X_some, frac_of_ne hz3]
        congr 1
        have hwne : emb p (x₁ / z₁) * (u - u') ^ 2 ≠ 0 :=
          mul_ne_zero ((map_ne_zero (emb p)).mpr (div_ne_zero hx₁ hz₁))
            (pow_ne_zero 2 (sub_ne_zero.mpr huu))
        apply mul_right_cancel₀ hwne
        rw [← mul_assoc, mi]
        have hdetF : emb p x * emb p z' - emb p z * emb p x' ≠ 0 := by
          rw [← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero (emb p)).mpr hdet
        have hz₁F : emb p z₁ ≠ 0 := (map_ne_zero (emb p)).mpr hz₁
        have hx₁F : emb p x₁ ≠ 0 := (map_ne_zero (emb p)).mpr hx₁
        have h4F := four_ne_zero_Fp2 (p := p) hp
        rw [hu, hu']
        simp only [map_div₀, map_mul, map_sub, map_pow, map_ofNat]
        field_simp

theorem theorem_B_2_dev (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (A : ℤ)
    (hA : ¬ IsSquare ((A : ZMod p) ^ 2 - 4)) (x z x' z' x₁ z₁ : ZMod p)
    (hxz : (x, z) ≠ (0, 0)) (hxz' : (x', z') ≠ (0, 0)) (hx₁ : x₁ ≠ 0) (hz₁ : z₁ ≠ 0) :
    let x₃ := 4 * (x * x' - z * z') ^ 2 * z₁
    let z₃ := 4 * (x * z' - z * x') ^ 2 * x₁
    x₃ = ((x - z) * (x' + z') + (x + z) * (x' - z')) ^ 2 * z₁ ∧
    z₃ = ((x - z) * (x' + z') - (x + z) * (x' - z')) ^ 2 * x₁ ∧
    ∀ Q Q' : Pt p A, X Q = frac x z → X Q' = frac x' z' → X (Q - Q') = frac x₁ z₁ →
      (x₃, z₃) ≠ (0, 0) ∧ X (Q + Q') = frac x₃ z₃ := by
  intro x₃ z₃
  refine ⟨by ring, by ring, ?_⟩
  intro Q Q' hQ hQ' hD
  exact diffadd hp hA x z x' z' x₁ z₁ hxz hxz' hx₁ hz₁ Q Q' hQ hQ' hD

end Bernstein.Montgomery

theorem solution : type_of% @Bernstein.Montgomery.theorem_B_2_dev := @Bernstein.Montgomery.theorem_B_2_dev
