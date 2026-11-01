-- Prove2me | solution 1 for Gelbart.hasse_minkowski
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T18:19:21.552146+00:00
-- url     : https://prove2.me/submissions/f04b2daf-ea5e-40b6-b073-8e00d780cf6b

import Mathlib

set_option autoImplicit false

namespace HMlib

/-- `T K a b`: the ternary form `z^2 - a x^2 - b y^2` has a nontrivial zero over `K`. -/
def T (K : Type*) [Field K] (a b : K) : Prop :=
  ∃ x y z : K, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2

variable {K : Type*} [Field K]

lemma T_iff (a b : K) (ha : a ≠ 0) :
    T K a b ↔ IsSquare a ∨ ∃ u v : K, b = u ^ 2 - a * v ^ 2 := by
  constructor
  · rintro ⟨x, y, z, hne, h⟩
    by_cases hy : y = 0
    · subst hy
      have hx : x ≠ 0 := by
        rintro rfl
        rcases hne with h1 | h1 | h1
        · exact h1 rfl
        · exact h1 rfl
        · apply h1; simpa using h
      left; refine ⟨z / x, ?_⟩
      field_simp
      linear_combination -h
    · right; refine ⟨z / y, x / y, ?_⟩
      field_simp
      linear_combination -h
  · rintro (⟨s, hs⟩ | ⟨u, v, huv⟩)
    · exact ⟨1, 0, s, Or.inl one_ne_zero, by rw [hs]; ring⟩
    · exact ⟨v, 1, u, Or.inr (Or.inl one_ne_zero), by rw [huv]; ring⟩

lemma T_symm (a b : K) : T K a b ↔ T K b a := by
  constructor <;>
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨y, x, z, by tauto, by linear_combination h⟩

lemma T_mul_sq (a b c : K) (hc : c ≠ 0) : T K a (b * c ^ 2) ↔ T K a b := by
  constructor
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨x, y * c, z, ?_, by linear_combination h⟩
    rcases hne with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl (mul_ne_zero h1 hc))
    · exact Or.inr (Or.inr h1)
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨x, y / c, z, ?_, ?_⟩
    · rcases hne with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl (div_ne_zero h1 hc))
      · exact Or.inr (Or.inr h1)
    · rw [h]; field_simp

/-- Descent step (any field): if `b * b' = t^2 - a` then the two ternary forms are isotropic together. -/
lemma T_descent (a b b' t : K) (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (h : b * b' = t ^ 2 - a) : T K a b ↔ T K a b' := by
  have key : ∀ c c' : K, c ≠ 0 → c' ≠ 0 → c * c' = t ^ 2 - a →
      (∃ u v : K, c = u ^ 2 - a * v ^ 2) → ∃ u v : K, c' = u ^ 2 - a * v ^ 2 := by
    rintro c c' hc hc' hcc ⟨u, v, huv⟩
    refine ⟨(t * u + a * v) / c, (t * v + u) / c, ?_⟩
    field_simp
    have : c' * c ^ 2 = (t ^ 2 - a) * c := by rw [← hcc]; ring
    rw [huv] at this ⊢
    linear_combination this
  rw [T_iff a b ha, T_iff a b' ha]
  constructor
  · rintro (hs | hn)
    · exact Or.inl hs
    · exact Or.inr (key b b' hb hb' h hn)
  · rintro (hs | hn)
    · exact Or.inl hs
    · exact Or.inr (key b' b hb' hb (by rw [mul_comm]; exact h) hn)

/-- Isotropy maps forward along field homomorphisms. -/
lemma T_map {L : Type*} [Field L] (f : K →+* L) (a b : K) (h : T K a b) : T L (f a) (f b) := by
  obtain ⟨x, y, z, hne, h⟩ := h
  refine ⟨f x, f y, f z, ?_, by rw [← map_pow, h]; simp⟩
  rcases hne with h1 | h1 | h1
  · exact Or.inl ((map_ne_zero f).mpr h1)
  · exact Or.inr (Or.inl ((map_ne_zero f).mpr h1))
  · exact Or.inr (Or.inr ((map_ne_zero f).mpr h1))


section Local
variable {p : ℕ} [hp : Fact p.Prime]

lemma toZMod_eq_zero_iff_dvd (x : ℤ_[p]) : PadicInt.toZMod x = 0 ↔ (p : ℤ_[p]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits,
    PadicInt.norm_lt_one_iff_dvd]

lemma toZMod_eq_zero_iff_not_unit (x : ℤ_[p]) : PadicInt.toZMod x = 0 ↔ ¬ IsUnit x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

lemma local_core (a b : ℤ) (hpa : ¬ (p : ℤ) ∣ a) (hpb : (p : ℤ) ∣ b) (hpb2 : ¬ (p : ℤ) ^ 2 ∣ b)
    (X Y Z : ℤ_[p]) (hu : IsUnit X ∨ IsUnit Y ∨ IsUnit Z)
    (h : Z ^ 2 = (a : ℤ_[p]) * X ^ 2 + (b : ℤ_[p]) * Y ^ 2) : IsSquare (a : ZMod p) := by
  have hφ := congrArg PadicInt.toZMod h
  simp only [map_add, map_mul, map_pow, map_intCast] at hφ
  have hb0 : ((b : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd b p).mpr hpb
  rw [hb0, zero_mul, add_zero] at hφ
  by_cases hX : PadicInt.toZMod X = 0
  · exfalso
    rw [hX] at hφ; simp at hφ
    obtain ⟨X1, rfl⟩ := (toZMod_eq_zero_iff_dvd X).mp hX
    obtain ⟨Z1, rfl⟩ := (toZMod_eq_zero_iff_dvd Z).mp hφ
    obtain ⟨b1, rfl⟩ := hpb
    have hb1 : ¬ (p : ℤ) ∣ b1 := by
      rintro ⟨c, rfl⟩; exact hpb2 ⟨c, by ring⟩
    have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have h2 : (p : ℤ_[p]) * ((p : ℤ_[p]) * (Z1 ^ 2 - a * X1 ^ 2) - b1 * Y ^ 2) = 0 := by
      push_cast at h; linear_combination h
    have h3 : (p : ℤ_[p]) * (Z1 ^ 2 - a * X1 ^ 2) = b1 * Y ^ 2 := by
      have := (mul_eq_zero.mp h2).resolve_left hp0; linear_combination this
    have h4 := congrArg PadicInt.toZMod h3
    simp only [map_mul, map_sub, map_pow, map_natCast, map_intCast, ZMod.natCast_self, zero_mul] at h4
    have hb1' : ((b1 : ℤ) : ZMod p) ≠ 0 := fun h0 => hb1 ((ZMod.intCast_zmod_eq_zero_iff_dvd b1 p).mp h0)
    have hY : PadicInt.toZMod Y = 0 := by
      have := h4.symm; rw [mul_eq_zero] at this
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (this.resolve_left hb1')
    have nX : ¬ IsUnit ((p : ℤ_[p]) * X1) := (toZMod_eq_zero_iff_not_unit _).mp hX
    have nZ : ¬ IsUnit ((p : ℤ_[p]) * Z1) := (toZMod_eq_zero_iff_not_unit _).mp hφ
    have nY : ¬ IsUnit Y := (toZMod_eq_zero_iff_not_unit _).mp hY
    rcases hu with h1 | h1 | h1
    · exact nX h1
    · exact nY h1
    · exact nZ h1
  · refine ⟨PadicInt.toZMod Z / PadicInt.toZMod X, ?_⟩
    field_simp
    linear_combination -hφ

lemma exists_max_norm (x y z : ℚ_[p]) (h : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    ∃ w : ℚ_[p], w ≠ 0 ∧ ‖x‖ ≤ ‖w‖ ∧ ‖y‖ ≤ ‖w‖ ∧ ‖z‖ ≤ ‖w‖ ∧ (w = x ∨ w = y ∨ w = z) := by
  have key : ∀ w : ℚ_[p], (w = x ∨ w = y ∨ w = z) → ‖x‖ ≤ ‖w‖ → ‖y‖ ≤ ‖w‖ → ‖z‖ ≤ ‖w‖ →
      ∃ w : ℚ_[p], w ≠ 0 ∧ ‖x‖ ≤ ‖w‖ ∧ ‖y‖ ≤ ‖w‖ ∧ ‖z‖ ≤ ‖w‖ ∧ (w = x ∨ w = y ∨ w = z) := by
    intro w hw h1 h2 h3
    refine ⟨w, ?_, h1, h2, h3, hw⟩
    rintro rfl
    simp only [norm_zero, norm_le_zero_iff] at h1 h2 h3
    rcases h with h | h | h <;> contradiction
  rcases le_total ‖x‖ ‖y‖ with hxy | hxy <;> rcases le_total ‖y‖ ‖z‖ with hyz | hyz <;>
    rcases le_total ‖x‖ ‖z‖ with hxz | hxz
  all_goals first
    | exact key x (Or.inl rfl) le_rfl (by linarith) (by linarith)
    | exact key y (Or.inr (Or.inl rfl)) (by linarith) le_rfl (by linarith)
    | exact key z (Or.inr (Or.inr rfl)) (by linarith) (by linarith) le_rfl

/-- Local step of Legendre's descent: if `p ∣ b` exactly, `p ∤ a` and `z^2 = a x^2 + b y^2` has a
nontrivial `p`-adic zero, then `a` is a square mod `p`. -/
theorem sq_mod_of_T_padic (a b : ℤ) (hpa : ¬ (p : ℤ) ∣ a) (hpb : (p : ℤ) ∣ b)
    (hpb2 : ¬ (p : ℤ) ^ 2 ∣ b) (hT : T ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p])) : IsSquare (a : ZMod p) := by
  obtain ⟨x, y, z, hne, h⟩ := hT
  obtain ⟨w, hw0, hxw, hyw, hzw, hw⟩ := exists_max_norm x y z hne
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hle : ∀ u : ℚ_[p], ‖u‖ ≤ ‖w‖ → ‖u / w‖ ≤ 1 := by
    intro u hu; rw [norm_div]; exact (div_le_one hwn).mpr hu
  let X : ℤ_[p] := ⟨x / w, hle x hxw⟩
  let Y : ℤ_[p] := ⟨y / w, hle y hyw⟩
  let Z : ℤ_[p] := ⟨z / w, hle z hzw⟩
  apply local_core a b hpa hpb hpb2 X Y Z
  · have hU : ∀ U : ℤ_[p], (U : ℚ_[p]) = 1 → IsUnit U := by
      intro U hU1; rw [PadicInt.isUnit_iff, PadicInt.norm_def, hU1, norm_one]
    have hx1 : (X : ℚ_[p]) = x / w := rfl
    have hy1 : (Y : ℚ_[p]) = y / w := rfl
    have hz1 : (Z : ℚ_[p]) = z / w := rfl
    rcases hw with rfl | rfl | rfl
    · exact Or.inl (hU X (by rw [hx1, div_self hw0]))
    · exact Or.inr (Or.inl (hU Y (by rw [hy1, div_self hw0])))
    · exact Or.inr (Or.inr (hU Z (by rw [hz1, div_self hw0])))
  · have hx1 : (X : ℚ_[p]) = x / w := rfl
    have hy1 : (Y : ℚ_[p]) = y / w := rfl
    have hz1 : (Z : ℚ_[p]) = z / w := rfl
    have e : ((Z ^ 2 : ℤ_[p]) : ℚ_[p]) = (((a : ℤ_[p]) * X ^ 2 + (b : ℤ_[p]) * Y ^ 2 : ℤ_[p]) : ℚ_[p]) := by
      push_cast
      rw [hx1, hy1, hz1]
      field_simp
      linear_combination h
    exact PadicInt.ext e

/-- Integer form: `a` is a square modulo `p`. -/
theorem exists_sq_mod_of_T_padic (a b : ℤ) (hpa : ¬ (p : ℤ) ∣ a) (hpb : (p : ℤ) ∣ b)
    (hpb2 : ¬ (p : ℤ) ^ 2 ∣ b) (hT : T ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p])) :
    ∃ t : ℤ, (p : ℤ) ∣ t ^ 2 - a := by
  obtain ⟨s, hs⟩ := sq_mod_of_T_padic a b hpa hpb hpb2 hT
  refine ⟨(s.val : ℤ), (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val, hs]; ring

end Local

/-! ## Legendre's theorem by descent -/

lemma T_one_left (K : Type*) [Field K] (b : K) : T K 1 b :=
  ⟨1, 0, 1, Or.inl one_ne_zero, by ring⟩

lemma T_cast_descent {K : Type*} [Field K] [CharZero K] (a b b' t : ℤ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hb' : b' ≠ 0) (h : b * b' = t ^ 2 - a) : T K (a : K) (b : K) ↔ T K (a : K) (b' : K) :=
  T_descent _ _ _ (t : K) (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hb')
    (by exact_mod_cast h)

lemma T_cast_sq {K : Type*} [Field K] [CharZero K] (a0 b0 s r : ℤ) (hs : s ≠ 0) (hr : r ≠ 0) :
    T K ((a0 * s ^ 2 : ℤ) : K) ((b0 * r ^ 2 : ℤ) : K) ↔ T K (a0 : K) (b0 : K) := by
  push_cast
  rw [T_mul_sq _ _ _ (by exact_mod_cast hr), T_symm, T_mul_sq _ _ _ (by exact_mod_cast hs), T_symm]

lemma int_sq_mul_squarefree (a : ℤ) (ha : a ≠ 0) :
    ∃ a0 s : ℤ, a = a0 * s ^ 2 ∧ s ≠ 0 ∧ a0 ≠ 0 ∧ Squarefree a0.natAbs ∧ a0.natAbs ≤ a.natAbs := by
  obtain ⟨r, s, hsr, hr⟩ := Nat.sq_mul_squarefree a.natAbs
  have hna : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha
  have hs : s ≠ 0 := by rintro rfl; simp at hsr; omega
  have hr0 : r ≠ 0 := by rintro rfl; simp at hsr; omega
  refine ⟨a.sign * r, s, ?_, by exact_mod_cast hs, ?_, ?_, ?_⟩
  · conv_lhs => rw [← Int.sign_mul_natAbs a]
    rw [← hsr]; push_cast; ring
  · exact mul_ne_zero (by rw [Ne, Int.sign_eq_zero_iff_zero]; exact ha) (by exact_mod_cast hr0)
  · rwa [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero ha, one_mul, Int.natAbs_natCast]
  · rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero ha, one_mul, Int.natAbs_natCast, ← hsr]
    exact Nat.le_mul_of_pos_left r (by positivity)

lemma sq_mod_crt (a : ℤ) (B : ℕ) (hB : Squarefree B)
    (hloc : ∀ p : ℕ, p.Prime → p ∣ B → ∃ t : ℤ, (p : ℤ) ∣ t ^ 2 - a) :
    ∃ t : ℤ, (B : ℤ) ∣ t ^ 2 - a := by
  have key : ∀ d : ℕ, d ∣ B → ∃ t : ℤ, (d : ℤ) ∣ t ^ 2 - a := by
    intro d
    induction d using Nat.recOnPrimeCoprime with
    | zero =>
      intro h
      rw [zero_dvd_iff] at h
      subst h
      exact absurd hB not_squarefree_zero
    | prime_pow p n hp =>
      intro hd
      rcases n with _ | _ | n
      · exact ⟨0, by simp⟩
      · simpa using hloc p hp (by simpa using hd)
      · exfalso
        have h1 : p * p ∣ B := dvd_trans ⟨p ^ n, by ring⟩ hd
        exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hB p h1))
    | coprime m n _ _ hmn ihm ihn =>
      intro hd
      obtain ⟨t1, h1⟩ := ihm (dvd_trans (dvd_mul_right m n) hd)
      obtain ⟨t2, h2⟩ := ihn (dvd_trans (dvd_mul_left n m) hd)
      have hc : IsCoprime (m : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.mpr hmn
      obtain ⟨u, v, huv⟩ := hc
      refine ⟨t1 * v * n + t2 * u * m, ?_⟩
      push_cast
      apply IsCoprime.mul_dvd ⟨u, v, huv⟩
      · have hX : t1 * v * n + t2 * u * m = t1 + m * (t2 * u - t1 * u) := by
          linear_combination t1 * huv
        rw [hX]
        have e : (t1 + m * (t2 * u - t1 * u)) ^ 2 - a
            = (t1 ^ 2 - a) + m * (2 * t1 * (t2 * u - t1 * u) + m * (t2 * u - t1 * u) ^ 2) := by ring
        rw [e]
        exact dvd_add h1 (Dvd.intro _ rfl)
      · have hX : t1 * v * n + t2 * u * m = t2 + n * (t1 * v - t2 * v) := by
          linear_combination t2 * huv
        rw [hX]
        have e : (t2 + n * (t1 * v - t2 * v)) ^ 2 - a
            = (t2 ^ 2 - a) + n * (2 * t2 * (t1 * v - t2 * v) + n * (t1 * v - t2 * v) ^ 2) := by ring
        rw [e]
        exact dvd_add h2 (Dvd.intro _ rfl)
  exact key B dvd_rfl

/-- One descent step for squarefree `b`, `|a| ≤ |b|`, `|b| ≥ 2`. -/
theorem legendre_step (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hbs : Squarefree b.natAbs)
    (hab : a.natAbs ≤ b.natAbs) (hb2 : 2 ≤ b.natAbs)
    (hP : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → T ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p])) :
    IsSquare a ∨ ∃ b' t : ℤ, b' ≠ 0 ∧ b'.natAbs < b.natAbs ∧ b * b' = t ^ 2 - a := by
  have hloc : ∀ p : ℕ, p.Prime → p ∣ b.natAbs → ∃ t : ℤ, (p : ℤ) ∣ t ^ 2 - a := by
    intro p hp hpb
    by_cases h2 : p = 2
    · subst h2
      refine ⟨a, ?_⟩
      have := Int.even_mul_pred_self a
      rw [even_iff_two_dvd] at this
      have e : a ^ 2 - a = a * (a - 1) := by ring
      rw [e]; exact_mod_cast this
    by_cases hpa : (p : ℤ) ∣ a
    · exact ⟨0, by simpa using hpa⟩
    have : Fact p.Prime := ⟨hp⟩
    refine exists_sq_mod_of_T_padic a b hpa (Int.natCast_dvd.mpr hpb) ?_ (hP p h2)
    intro h
    have h' : p * p ∣ b.natAbs := by
      have := Int.natCast_dvd.mp h
      simpa [Int.natAbs_pow, sq] using this
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hbs p h'))
  obtain ⟨t, ht⟩ := sq_mod_crt a b.natAbs hbs hloc
  have htb : b ∣ t ^ 2 - a := by
    rw [Int.natCast_natAbs] at ht; exact (abs_dvd b _).mp ht
  -- balanced residue
  set r := t % b with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg t hb
  have hrl : r < |b| := by
    have h := Int.emod_lt t hb; rwa [Int.natCast_natAbs] at h
  have hbt : b ∣ r - t := by
    have := Int.emod_add_mul_ediv t b
    exact ⟨-(t / b), by rw [hr]; linear_combination this⟩
  have hbabs : b ∣ |b| := (dvd_abs b b).mpr dvd_rfl
  obtain ⟨t', ht'b, ht'⟩ : ∃ t' : ℤ, b ∣ t' - t ∧ 2 * |t'| ≤ |b| := by
    by_cases h2r : 2 * r ≤ |b|
    · exact ⟨r, hbt, by rw [abs_of_nonneg hr0]; exact h2r⟩
    · refine ⟨r - |b|, ?_, ?_⟩
      · have : r - |b| - t = (r - t) - |b| := by ring
        rw [this]; exact dvd_sub hbt hbabs
      · rw [abs_of_neg (by linarith)]; linarith
  have hdiv : b ∣ t' ^ 2 - a := by
    have e : t' ^ 2 - a = (t ^ 2 - a) + (t' - t) * (t' + t) := by ring
    rw [e]; exact dvd_add htb (dvd_mul_of_dvd_left ht'b _)
  obtain ⟨b', hb'⟩ := hdiv
  by_cases hb'0 : b' = 0
  · left
    refine ⟨t', ?_⟩
    rw [hb'0, mul_zero] at hb'
    linear_combination -hb'
  right
  refine ⟨b', t', hb'0, ?_, by linear_combination -hb'⟩
  have hA : |a| ≤ |b| := by
    have := hab; zify at this; exact this
  have hB2 : 2 ≤ |b| := by
    have := hb2; zify at this; exact this
  have hmul : |b| * |b'| = |t' ^ 2 - a| := by rw [← abs_mul, hb']
  have htri : |t' ^ 2 - a| ≤ |t'| ^ 2 + |a| := by
    calc |t' ^ 2 - a| ≤ |t' ^ 2| + |a| := abs_sub _ _
      _ = |t'| ^ 2 + |a| := by rw [abs_pow]
  zify
  by_contra hcon
  push Not at hcon
  have h0 : 0 ≤ |t'| := abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hcon (abs_nonneg b)]

lemma not_T_neg_one_real : ¬ T ℝ (-1) (-1) := by
  rintro ⟨x, y, z, hne, h⟩
  have hx : x ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hz : z ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  rcases hne with h1 | h1 | h1
  · exact h1 (pow_eq_zero_iff two_ne_zero |>.mp hx)
  · exact h1 (pow_eq_zero_iff two_ne_zero |>.mp hy)
  · exact h1 (pow_eq_zero_iff two_ne_zero |>.mp hz)

lemma natAbs_eq_one {a : ℤ} (h : a.natAbs = 1) : a = 1 ∨ a = -1 := by omega

theorem legendre_aux : ∀ N : ℕ, ∀ a b : ℤ, a.natAbs + b.natAbs ≤ N → a ≠ 0 → b ≠ 0 →
    T ℝ (a : ℝ) (b : ℝ) → (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → T ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p])) →
    T ℚ (a : ℚ) (b : ℚ) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  -- squarefree version with |a| ≤ |b|
  have main : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → Squarefree b.natAbs → a.natAbs ≤ b.natAbs →
      a.natAbs + b.natAbs ≤ N → T ℝ (a : ℝ) (b : ℝ) →
      (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → T ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p])) → T ℚ (a : ℚ) (b : ℚ) := by
    intro a b ha hb hbs hab hN hR hP
    by_cases hb2 : 2 ≤ b.natAbs
    · rcases legendre_step a b ha hb hbs hab hb2 hP with ⟨s, hs⟩ | ⟨b', t, hb'0, hlt, he⟩
      · refine (T_iff _ _ (by exact_mod_cast ha)).mpr (Or.inl ⟨(s : ℚ), by rw [hs]; push_cast; ring⟩)
      · rw [T_cast_descent a b b' t ha hb hb'0 he]
        refine ih (a.natAbs + b'.natAbs) (by omega) a b' le_rfl ha hb'0 ?_ ?_
        · exact (T_cast_descent a b b' t ha hb hb'0 he).mp hR
        · intro p _ hp2
          exact (T_cast_descent a b b' t ha hb hb'0 he).mp (hP p hp2)
    · have hb1 : b.natAbs = 1 := by have := Int.natAbs_ne_zero.mpr hb; omega
      have ha1 : a.natAbs = 1 := by have := Int.natAbs_ne_zero.mpr ha; omega
      rcases natAbs_eq_one ha1 with rfl | rfl
      · simpa using T_one_left ℚ (b : ℚ)
      rcases natAbs_eq_one hb1 with rfl | rfl
      · rw [T_symm]; simpa using T_one_left ℚ ((-1 : ℤ) : ℚ)
      · exact absurd (by simpa using hR) not_T_neg_one_real
  intro a b hN ha hb hR hP
  obtain ⟨a0, s, rfl, hs, ha0, ha0sq, ha0le⟩ := int_sq_mul_squarefree a ha
  obtain ⟨b0, r, rfl, hr, hb0, hb0sq, hb0le⟩ := int_sq_mul_squarefree b hb
  rw [T_cast_sq a0 b0 s r hs hr] at hR ⊢
  have hP0 : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → T ℚ_[p] (a0 : ℚ_[p]) (b0 : ℚ_[p]) := by
    intro p _ hp2
    exact (T_cast_sq a0 b0 s r hs hr).mp (hP p hp2)
  rcases le_total a0.natAbs b0.natAbs with hle | hle
  · exact main a0 b0 ha0 hb0 hb0sq hle (by omega) hR hP0
  · rw [T_symm]
    refine main b0 a0 hb0 ha0 ha0sq hle (by omega) ((T_symm _ _).mp hR) ?_
    intro p _ hp2
    exact (T_symm _ _).mp (hP0 p hp2)

/-- **Legendre's theorem** (Hasse–Minkowski for `z^2 = a x^2 + b y^2`): local solvability at `ℝ`
and at every odd prime implies a rational solution. -/
theorem legendre_ternary (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hR : T ℝ (a : ℝ) (b : ℝ))
    (hP : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → T ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p])) :
    T ℚ (a : ℚ) (b : ℚ) :=
  legendre_aux _ a b le_rfl ha hb hR hP


section Hensel
variable {p : ℕ} [hp : Fact p.Prime]

lemma hensel_quad (A c a : ℤ_[p]) (h : ‖A * a ^ 2 + c‖ < ‖2 * A * a‖ ^ 2) :
    ∃ z : ℤ_[p], A * z ^ 2 + c = 0 ∧ ‖z - a‖ < ‖2 * A * a‖ := by
  set F : Polynomial ℤ_[p] := Polynomial.C A * Polynomial.X ^ 2 + Polynomial.C c with hF
  have he : ∀ x : ℤ_[p], Polynomial.aeval x F = A * x ^ 2 + c := by
    intro x; simp [hF]
  have hd : Polynomial.aeval a (Polynomial.derivative F) = 2 * A * a := by
    simp [hF]; ring
  obtain ⟨z, hz, hza, -, -⟩ := hensels_lemma (F := F) (a := a) (by rw [he, hd]; exact h)
  exact ⟨z, by rw [← he]; exact hz, by rw [← hd]; exact hza⟩

lemma int_norm_one {k : ℤ} (hk : ¬ (p : ℤ) ∣ k) : ‖(k : ℤ_[p])‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one _) (not_lt.mp (mt (PadicInt.norm_int_lt_one_iff_dvd k).mp hk))

lemma sq_cast_of_padicInt (u : ℤ) (z : ℤ_[p]) (hz : z ^ 2 = (u : ℤ_[p])) : IsSquare (u : ℚ_[p]) := by
  refine ⟨(z : ℚ_[p]), ?_⟩
  have := congrArg ((↑) : ℤ_[p] → ℚ_[p]) hz
  push_cast at this
  rw [← this]; ring

lemma prime_int_not_dvd_two (hp2 : p ≠ 2) : ¬ (p : ℤ) ∣ 2 := by
  intro h
  have : p ∣ 2 := by exact_mod_cast h
  rcases (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this with h2
  exact hp2 h2

/-- Odd `p`: a `p`-adic unit integer that is a square mod `p` is a square in `ℚ_[p]`. -/
theorem padic_sq_of_sq_mod (hp2 : p ≠ 2) (u t : ℤ) (hu : ¬ (p : ℤ) ∣ u) (ht : (p : ℤ) ∣ t ^ 2 - u) :
    IsSquare (u : ℚ_[p]) := by
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have htp : ¬ (p : ℤ) ∣ t := by
    intro h
    apply hu
    have : (p : ℤ) ∣ t ^ 2 := dvd_pow h two_ne_zero
    have := dvd_sub this ht
    simpa using this
  have h2t : ¬ (p : ℤ) ∣ 2 * t := by
    intro h
    rcases hpr.dvd_or_dvd h with h | h
    · exact prime_int_not_dvd_two hp2 h
    · exact htp h
  obtain ⟨z, hz, -⟩ := hensel_quad (p := p) 1 (-(u : ℤ_[p])) (t : ℤ_[p]) (by
    have e1 : (1 : ℤ_[p]) * (t : ℤ_[p]) ^ 2 + -(u : ℤ_[p]) = ((t ^ 2 - u : ℤ) : ℤ_[p]) := by
      push_cast; ring
    have e2 : (2 : ℤ_[p]) * 1 * (t : ℤ_[p]) = ((2 * t : ℤ) : ℤ_[p]) := by push_cast; ring
    rw [e1, e2, int_norm_one h2t, one_pow]
    exact (PadicInt.norm_int_lt_one_iff_dvd _).mpr ht)
  exact sq_cast_of_padicInt u z (by linear_combination hz)

/-- `u ≡ 1 mod 8` is a square in `ℚ_[2]`. -/
theorem two_adic_sq (u : ℤ) (hu : u % 8 = 1) : IsSquare (u : ℚ_[2]) := by
  have h8 : ((2 : ℕ) ^ 3 : ℤ) ∣ 1 - u := by
    have : (8 : ℤ) ∣ 1 - u := by omega
    simpa using this
  obtain ⟨z, hz, -⟩ := hensel_quad (p := 2) 1 (-(u : ℤ_[2])) 1 (by
    have e1 : (1 : ℤ_[2]) * 1 ^ 2 + -(u : ℤ_[2]) = ((1 - u : ℤ) : ℤ_[2]) := by push_cast; ring
    have e2 : (2 : ℤ_[2]) * 1 * 1 = ((2 : ℕ) : ℤ_[2]) := by push_cast; ring
    rw [e1, e2, PadicInt.norm_p]
    have := (PadicInt.norm_int_le_pow_iff_dvd (p := 2) (k := 1 - u) (n := 3)).mpr h8
    calc ‖((1 - u : ℤ) : ℤ_[2])‖ ≤ ((2 : ℕ) : ℝ) ^ (-(3 : ℕ) : ℤ) := this
      _ < (((2 : ℕ) : ℝ)⁻¹) ^ 2 := by norm_num)
  exact sq_cast_of_padicInt u z (by linear_combination hz)

/-- Odd `p`: a diagonal ternary form with unit integer coefficients has a `p`-adic zero with `z ≠ 0`. -/
theorem ternary_units_isotropic (hp2 : p ≠ 2) (a1 a2 a3 : ℤ) (h1 : ¬ (p : ℤ) ∣ a1)
    (h2 : ¬ (p : ℤ) ∣ a2) (h3 : ¬ (p : ℤ) ∣ a3) :
    ∃ x y z : ℚ_[p], z ≠ 0 ∧ (a1 : ℚ_[p]) * x ^ 2 + a2 * y ^ 2 + a3 * z ^ 2 = 0 := by
  have hz : ∀ a : ℤ, ¬ (p : ℤ) ∣ a → (a : ZMod p) ≠ 0 := fun a ha h0 =>
    ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h0)
  have hcard : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]; exact Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  obtain ⟨r, s, hrs⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.C ((a1 : ZMod p)) * Polynomial.X ^ 2)
    (g := Polynomial.C ((a2 : ZMod p)) * Polynomial.X ^ 2 + Polynomial.C ((a3 : ZMod p)))
    (Polynomial.degree_C_mul_X_pow 2 (hz a1 h1))
    (by
      have hd2 := Polynomial.degree_C_mul_X_pow 2 (hz a2 h2)
      rw [Polynomial.degree_add_C (by rw [hd2]; exact WithBot.coe_lt_coe.mpr (by norm_num)), hd2]
      rfl)
    hcard
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_add] at hrs
  set x0 : ℤ := (r.val : ℤ)
  set y0 : ℤ := (s.val : ℤ)
  have hdiv : (p : ℤ) ∣ a1 * x0 ^ 2 + a2 * y0 ^ 2 + a3 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast [x0, y0]
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    linear_combination hrs
  obtain ⟨z, hz0, hz1⟩ := hensel_quad (p := p) (a3 : ℤ_[p]) ((a1 * x0 ^ 2 + a2 * y0 ^ 2 : ℤ) : ℤ_[p]) 1 (by
    have e1 : (a3 : ℤ_[p]) * 1 ^ 2 + ((a1 * x0 ^ 2 + a2 * y0 ^ 2 : ℤ) : ℤ_[p])
        = ((a1 * x0 ^ 2 + a2 * y0 ^ 2 + a3 : ℤ) : ℤ_[p]) := by push_cast; ring
    have e2 : (2 : ℤ_[p]) * a3 * 1 = ((2 * a3 : ℤ) : ℤ_[p]) := by push_cast; ring
    have h23 : ¬ (p : ℤ) ∣ 2 * a3 := by
      intro h
      rcases (Nat.prime_iff_prime_int.mp hp.out).dvd_or_dvd h with h | h
      · exact prime_int_not_dvd_two hp2 h
      · exact h3 h
    rw [e1, e2, int_norm_one h23, one_pow]
    exact (PadicInt.norm_int_lt_one_iff_dvd _).mpr hdiv)
  refine ⟨x0, y0, (z : ℚ_[p]), ?_, ?_⟩
  · intro h0
    have hz0' : z = 0 := by simpa using h0
    rw [hz0', zero_sub, norm_neg, norm_one] at hz1
    exact absurd (PadicInt.norm_le_one _) (not_le.mpr hz1)
  · have := congrArg ((↑) : ℤ_[p] → ℚ_[p]) hz0
    push_cast at this
    linear_combination this

end Hensel


/-! ## Primitive zeros, field identity -/

theorem T_primitive {p : ℕ} [Fact p.Prime] (a b : ℤ) (hT : T ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p])) :
    ∃ X Y Z : ℤ_[p], (IsUnit X ∨ IsUnit Y ∨ IsUnit Z) ∧
      Z ^ 2 = (a : ℤ_[p]) * X ^ 2 + (b : ℤ_[p]) * Y ^ 2 := by
  obtain ⟨x, y, z, hne, h⟩ := hT
  obtain ⟨w, hw0, hxw, hyw, hzw, hw⟩ := exists_max_norm x y z hne
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hle : ∀ u : ℚ_[p], ‖u‖ ≤ ‖w‖ → ‖u / w‖ ≤ 1 := by
    intro u hu; rw [norm_div]; exact (div_le_one hwn).mpr hu
  let X : ℤ_[p] := ⟨x / w, hle x hxw⟩
  let Y : ℤ_[p] := ⟨y / w, hle y hyw⟩
  let Z : ℤ_[p] := ⟨z / w, hle z hzw⟩
  have hx1 : (X : ℚ_[p]) = x / w := rfl
  have hy1 : (Y : ℚ_[p]) = y / w := rfl
  have hz1 : (Z : ℚ_[p]) = z / w := rfl
  refine ⟨X, Y, Z, ?_, ?_⟩
  · have hU : ∀ U : ℤ_[p], (U : ℚ_[p]) = 1 → IsUnit U := by
      intro U hU1; rw [PadicInt.isUnit_iff, PadicInt.norm_def, hU1, norm_one]
    rcases hw with rfl | rfl | rfl
    · exact Or.inl (hU X (by rw [hx1, div_self hw0]))
    · exact Or.inr (Or.inl (hU Y (by rw [hy1, div_self hw0])))
    · exact Or.inr (Or.inr (hU Z (by rw [hz1, div_self hw0])))
  · have e : ((Z ^ 2 : ℤ_[p]) : ℚ_[p]) = (((a : ℤ_[p]) * X ^ 2 + (b : ℤ_[p]) * Y ^ 2 : ℤ_[p]) : ℚ_[p]) := by
      push_cast
      rw [hx1, hy1, hz1]
      field_simp
      linear_combination h
    exact PadicInt.ext e

lemma T_neg_mul {K : Type*} [Field K] (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    T K a b ↔ T K a (-(a * b)) := by
  have h1 : T K a b ↔ T K a (-a / b) :=
    T_descent a b (-a / b) 0 ha hb (div_ne_zero (neg_ne_zero.mpr ha) hb) (by field_simp; ring)
  have h2 : -(a * b) * (1 / b) ^ 2 = -a / b := by field_simp
  rw [h1, ← h2, T_mul_sq _ _ _ (one_div_ne_zero hb)]

lemma T_int_of_sq {p : ℕ} [Fact p.Prime] (a b x0 y0 : ℤ) (h : IsSquare ((a * x0 ^ 2 + b * y0 ^ 2 : ℤ) : ℚ_[p]))
    (hN : a * x0 ^ 2 + b * y0 ^ 2 ≠ 0) : T ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p]) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨x0, y0, s, Or.inr (Or.inr ?_), ?_⟩
  · rintro rfl
    apply hN
    exact_mod_cast (by simpa using hs : ((a * x0 ^ 2 + b * y0 ^ 2 : ℤ) : ℚ_[p]) = 0)
  · push_cast at hs; rw [sq, ← hs]

/-! ## The prime 2 -/

def e8 (u : ZMod (2 ^ 3)) : ZMod 2 := if u = 3 ∨ u = 7 then 1 else 0
def w8 (u : ZMod (2 ^ 3)) : ZMod 2 := if u = 3 ∨ u = 5 then 1 else 0
/-- Explicit `2`-adic symbol (additive, `0 ↔ +1`) for `2^α u, 2^β v`, `u v` odd. -/
def hf2 (α β : ℕ) (u v : ZMod (2 ^ 3)) : ZMod 2 :=
  e8 u * e8 v + (α : ZMod 2) * w8 v + (β : ZMod 2) * w8 u

lemma isUnit_iff_not_two_dvd (X : ℤ_[2]) : IsUnit X ↔ ¬ (2 : ℤ_[2]) ∣ X := by
  have h := PadicInt.norm_lt_one_iff_dvd (p := 2) X
  push_cast at h
  rw [PadicInt.isUnit_iff, ← h]
  constructor
  · intro h1; rw [h1]; exact lt_irrefl 1
  · intro h1; exact le_antisymm (PadicInt.norm_le_one X) (not_lt.mp h1)

lemma two_dvd_iff_val (X : ℤ_[2]) :
    (2 : ℤ_[2]) ∣ X ↔ (PadicInt.toZModPow 3 X).val % 2 = 0 := by
  constructor
  · rintro ⟨Y, rfl⟩
    rw [map_mul, map_ofNat]
    generalize PadicInt.toZModPow 3 Y = k
    revert k; decide
  · intro h
    set k := PadicInt.toZModPow 3 X with hk
    have hker : X - (k.val : ℤ_[2]) ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 3) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, ← hk, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
    obtain ⟨c, hc⟩ := hker
    obtain ⟨j, hj⟩ : 2 ∣ k.val := Nat.dvd_of_mod_eq_zero h
    refine ⟨(j : ℤ_[2]) + 4 * c, ?_⟩
    have hj' : (k.val : ℤ_[2]) = 2 * (j : ℤ_[2]) := by rw [hj]; push_cast; ring
    push_cast at hc
    linear_combination hc + hj'

lemma sq8_facts : ∀ k : ZMod (2 ^ 3),
    (k.val % 2 = 1 → k ^ 2 = 1) ∧ (k.val % 2 = 0 → k ^ 2 = 0 ∨ k ^ 2 = 4) := by decide

lemma sq_class (X : ℤ_[2]) :
    ((PadicInt.toZModPow 3 X) ^ 2 = 0 ∨ (PadicInt.toZModPow 3 X) ^ 2 = 1 ∨
      (PadicInt.toZModPow 3 X) ^ 2 = 4) ∧ (IsUnit X → (PadicInt.toZModPow 3 X) ^ 2 = 1) := by
  obtain ⟨h1, h0⟩ := sq8_facts (PadicInt.toZModPow 3 X)
  refine ⟨?_, ?_⟩
  · rcases Nat.mod_two_eq_zero_or_one (PadicInt.toZModPow 3 X).val with h | h
    · rcases h0 h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
    · exact Or.inr (Or.inl (h1 h))
  · intro hu
    rw [isUnit_iff_not_two_dvd, two_dvd_iff_val] at hu
    exact h1 (by omega)

lemma odd_val8 (u : ℤ) (hu : u % 2 = 1) : ((u : ZMod (2 ^ 3))).val % 2 = 1 := by
  have := ZMod.val_intCast (n := 2 ^ 3) u
  push_cast at this
  omega

lemma dec_imp : ∀ α ∈ ({0, 1} : Finset ℕ), ∀ u v : ZMod (2 ^ 3), u.val % 2 = 1 → v.val % 2 = 1 →
    ∀ SX ∈ ({0, 1, 4} : Finset (ZMod (2 ^ 3))), ∀ SY ∈ ({0, 1, 4} : Finset (ZMod (2 ^ 3))),
    ∀ SZ ∈ ({0, 1, 4} : Finset (ZMod (2 ^ 3))), (SX = 1 ∨ SY = 1 ∨ SZ = 1) →
    SZ = 2 ^ α * u * SX + v * SY → hf2 α 0 u v = 0 := by decide

lemma dec_rev : ∀ α ∈ ({0, 1} : Finset ℕ), ∀ u v : ZMod (2 ^ 3), u.val % 2 = 1 → v.val % 2 = 1 →
    hf2 α 0 u v = 0 → ∃ x ∈ ({0, 1, 2} : Finset (ZMod (2 ^ 3))), ∃ y ∈ ({0, 1, 2} : Finset (ZMod (2 ^ 3))),
    2 ^ α * u * x ^ 2 + v * y ^ 2 = 1 := by decide

lemma dec_11 : ∀ u v : ZMod (2 ^ 3), u.val % 2 = 1 → v.val % 2 = 1 →
    hf2 1 1 u v = hf2 1 0 u (-(u * v)) := by decide

lemma dec_01 : ∀ u v : ZMod (2 ^ 3), hf2 0 1 u v = hf2 1 0 v u := by decide

lemma zmod8_one (N : ℤ) (h : (N : ZMod (2 ^ 3)) = 1) : N % 8 = 1 := by
  have := (ZMod.intCast_eq_intCast_iff' N 1 (2 ^ 3)).mp (by rw [Int.cast_one]; exact h)
  push_cast at this
  omega

/-- Core at `2` for `α ≤ 1`, `β = 0`. -/
theorem core2 (α : ℕ) (hα : α ≤ 1) (u v : ℤ) (hu : u % 2 = 1) (hv : v % 2 = 1) :
    T ℚ_[2] ((2 ^ α * u : ℤ) : ℚ_[2]) (v : ℚ_[2]) ↔ hf2 α 0 (u : ZMod (2 ^ 3)) (v : ZMod (2 ^ 3)) = 0 := by
  have hαm : α ∈ ({0, 1} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  constructor
  · intro hT
    obtain ⟨X, Y, Z, hU, hE⟩ := T_primitive _ _ hT
    have hφ := congrArg (PadicInt.toZModPow (p := 2) 3) hE
    simp only [map_add, map_mul, map_pow, map_intCast] at hφ
    push_cast at hφ
    obtain ⟨cX, uX⟩ := sq_class X
    obtain ⟨cY, uY⟩ := sq_class Y
    obtain ⟨cZ, uZ⟩ := sq_class Z
    have mem : ∀ S : ZMod (2 ^ 3), (S = 0 ∨ S = 1 ∨ S = 4) → S ∈ ({0, 1, 4} : Finset (ZMod (2 ^ 3))) := by
      intro S hS; simp only [Finset.mem_insert, Finset.mem_singleton]; exact hS
    refine dec_imp α hαm _ _ (odd_val8 u hu) (odd_val8 v hv) _ (mem _ cX) _ (mem _ cY) _ (mem _ cZ) ?_ ?_
    · rcases hU with h | h | h
      · exact Or.inl (uX h)
      · exact Or.inr (Or.inl (uY h))
      · exact Or.inr (Or.inr (uZ h))
    · rw [hφ]
  · intro hh
    obtain ⟨x, -, y, -, hxy⟩ := dec_rev α hαm _ _ (odd_val8 u hu) (odd_val8 v hv) hh
    have hN : ((2 ^ α * u * (x.val : ℤ) ^ 2 + v * (y.val : ℤ) ^ 2 : ℤ) : ZMod (2 ^ 3)) = 1 := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      exact hxy
    have h8 := zmod8_one _ hN
    apply T_int_of_sq _ _ (x.val : ℤ) (y.val : ℤ)
    · have := two_adic_sq _ h8
      push_cast at this ⊢
      exact this
    · intro h0; rw [h0] at h8; norm_num at h8


/-! ## Odd primes -/

def lg (p : ℕ) [Fact p.Prime] (u : ℤ) : ZMod 2 := if legendreSym p u = 1 then 0 else 1

def hfo (p : ℕ) [Fact p.Prime] (α β : ℕ) (u v : ℤ) : ZMod 2 :=
  (α * β : ZMod 2) * lg p (-1) + (α : ZMod 2) * lg p v + (β : ZMod 2) * lg p u

def hform (p : ℕ) [Fact p.Prime] (α β : ℕ) (u v : ℤ) : ZMod 2 :=
  if p = 2 then hf2 α β (u : ZMod (2 ^ 3)) (v : ZMod (2 ^ 3)) else hfo p α β u v

section OddP
variable {p : ℕ} [hp : Fact p.Prime]

lemma unit_zmod {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) : (u : ZMod p) ≠ 0 := fun h =>
  hu ((ZMod.intCast_zmod_eq_zero_iff_dvd u p).mp h)

lemma lg_eq_zero_iff {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) : lg p u = 0 ↔ IsSquare (u : ZMod p) := by
  rw [← legendreSym.eq_one_iff p (unit_zmod hu)]
  unfold lg
  split_ifs with h
  · simp [h]
  · simp only [one_ne_zero, false_iff]; exact h

lemma lg_mul {u v : ℤ} (hu : ¬ (p : ℤ) ∣ u) (hv : ¬ (p : ℤ) ∣ v) : lg p (u * v) = lg p u + lg p v := by
  have h1 := legendreSym.eq_one_or_neg_one p (unit_zmod hu)
  have h2 := legendreSym.eq_one_or_neg_one p (unit_zmod hv)
  unfold lg
  rw [legendreSym.mul]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> decide

lemma not_dvd_mul {u v : ℤ} (hu : ¬ (p : ℤ) ∣ u) (hv : ¬ (p : ℤ) ∣ v) : ¬ (p : ℤ) ∣ u * v := by
  intro h
  rcases (Nat.prime_iff_prime_int.mp hp.out).dvd_or_dvd h with h | h
  · exact hu h
  · exact hv h

lemma not_dvd_neg_one : ¬ (p : ℤ) ∣ -1 := by
  intro h
  have : (p : ℤ) ∣ 1 := by simpa using h
  have := Int.eq_one_of_dvd_one (by positivity) this
  exact hp.out.one_lt.ne' (by exact_mod_cast this)

lemma T_sq_unit (hp2 : p ≠ 2) (c v : ℤ) (hc : c ≠ 0) (hv : ¬ (p : ℤ) ∣ v)
    (hs : IsSquare (v : ZMod p)) : T ℚ_[p] (c : ℚ_[p]) (v : ℚ_[p]) := by
  obtain ⟨s, hs⟩ := hs
  have ht : (p : ℤ) ∣ (s.val : ℤ) ^ 2 - v := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, hs]; ring
  have hsq := padic_sq_of_sq_mod hp2 v _ hv ht
  rw [T_symm, T_iff _ _ (by exact_mod_cast (fun h0 : v = 0 => hv (h0 ▸ dvd_zero _)))]
  exact Or.inl hsq

theorem coreO_10 (hp2 : p ≠ 2) (u v : ℤ) (hu : ¬ (p : ℤ) ∣ u) (hv : ¬ (p : ℤ) ∣ v) :
    T ℚ_[p] ((p * u : ℤ) : ℚ_[p]) (v : ℚ_[p]) ↔ lg p v = 0 := by
  rw [lg_eq_zero_iff hv]
  constructor
  · intro hT
    rw [T_symm] at hT
    refine sq_mod_of_T_padic v (p * u) hv (dvd_mul_right _ _) ?_ hT
    rintro ⟨c, hc⟩
    apply hu
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    exact ⟨c, by
      have : (p : ℤ) * (u - p * c) = 0 := by linear_combination hc
      have := (mul_eq_zero.mp this).resolve_left hp0
      linear_combination this⟩
  · intro hs
    have hpu : (p : ℤ) * u ≠ 0 := mul_ne_zero (by exact_mod_cast hp.out.ne_zero)
      (fun h0 => hu (h0 ▸ dvd_zero _))
    exact T_sq_unit hp2 _ v hpu hv hs

theorem coreO (hp2 : p ≠ 2) (α β : ℕ) (hα : α ≤ 1) (hβ : β ≤ 1) (u v : ℤ) (hu : ¬ (p : ℤ) ∣ u)
    (hv : ¬ (p : ℤ) ∣ v) :
    T ℚ_[p] (((p : ℤ) ^ α * u : ℤ) : ℚ_[p]) (((p : ℤ) ^ β * v : ℤ) : ℚ_[p]) ↔ hfo p α β u v = 0 := by
  have hu0 : u ≠ 0 := fun h0 => hu (h0 ▸ dvd_zero _)
  have hv0 : v ≠ 0 := fun h0 => hv (h0 ▸ dvd_zero _)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  interval_cases α <;> interval_cases β
  · simp only [pow_zero, one_mul, hfo, Nat.cast_zero, zero_mul, add_zero, iff_true]
    obtain ⟨x, y, z, hz, h⟩ := ternary_units_isotropic hp2 u v (-1) hu hv not_dvd_neg_one
    exact ⟨x, y, z, Or.inr (Or.inr hz), by push_cast at h; linear_combination -h⟩
  · simp only [pow_zero, one_mul, pow_one, hfo, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul,
      zero_add]
    rw [T_symm]; exact coreO_10 hp2 v u hv hu
  · simp only [pow_zero, one_mul, pow_one, hfo, Nat.cast_zero, Nat.cast_one, mul_zero, zero_mul,
      one_mul, add_zero, zero_add]
    exact coreO_10 hp2 u v hu hv
  · simp only [pow_one, hfo, Nat.cast_one, one_mul]
    have huv : ¬ (p : ℤ) ∣ -(u * v) := by
      rw [dvd_neg]; exact not_dvd_mul hu hv
    rw [T_neg_mul _ _ (by exact_mod_cast mul_ne_zero hp0 hu0) (by exact_mod_cast mul_ne_zero hp0 hv0)]
    have e : -(((p * u : ℤ) : ℚ_[p]) * ((p * v : ℤ) : ℚ_[p])) = ((-(u * v) : ℤ) : ℚ_[p]) * ((p : ℚ_[p])) ^ 2 := by
      push_cast; ring
    rw [e, T_mul_sq _ _ _ (by exact_mod_cast hp.out.ne_zero), coreO_10 hp2 u _ hu huv]
    have : -(u * v) = (-1) * (u * v) := by ring
    rw [this, lg_mul not_dvd_neg_one (not_dvd_mul hu hv), lg_mul hu hv]
    constructor <;> intro h <;> linear_combination h

end OddP

/-! ## The prime 2, all exponents ≤ 1 -/

lemma odd_mul_odd (u v : ℤ) (hu : u % 2 = 1) (hv : v % 2 = 1) : (-(u * v)) % 2 = 1 := by
  have h := ((Int.odd_iff.mpr hu).mul (Int.odd_iff.mpr hv)).neg
  exact Int.odd_iff.mp h

theorem core2' (α β : ℕ) (hα : α ≤ 1) (hβ : β ≤ 1) (u v : ℤ) (hu : u % 2 = 1) (hv : v % 2 = 1) :
    T ℚ_[2] ((2 ^ α * u : ℤ) : ℚ_[2]) ((2 ^ β * v : ℤ) : ℚ_[2]) ↔
      hf2 α β (u : ZMod (2 ^ 3)) (v : ZMod (2 ^ 3)) = 0 := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  interval_cases α <;> interval_cases β
  · have := core2 0 (by norm_num) u v hu hv
    simpa using this
  · rw [T_symm, dec_01]
    have := core2 1 le_rfl v u hv hu
    simpa using this
  · have := core2 1 le_rfl u v hu hv
    simpa using this
  · rw [T_neg_mul _ _ (by exact_mod_cast mul_ne_zero two_ne_zero hu0)
      (by exact_mod_cast mul_ne_zero two_ne_zero hv0)]
    have e : -(((2 ^ 1 * u : ℤ) : ℚ_[2]) * ((2 ^ 1 * v : ℤ) : ℚ_[2]))
        = ((-(u * v) : ℤ) : ℚ_[2]) * ((2 : ℚ_[2])) ^ 2 := by
      push_cast; ring
    rw [e, T_mul_sq _ _ _ two_ne_zero, dec_11 _ _ (odd_val8 u hu) (odd_val8 v hv),
      core2 1 le_rfl u (-(u * v)) hu (odd_mul_odd u v hu hv)]
    push_cast
    exact Iff.rfl


/-! ## General exponents, the symbol `hilb`, the real place -/

lemma T_pow_mod2 {K : Type*} [Field K] [CharZero K] (q : ℤ) (hq : q ≠ 0) (α β : ℕ) (u v : ℤ) :
    T K ((q ^ α * u : ℤ) : K) ((q ^ β * v : ℤ) : K) ↔
      T K ((q ^ (α % 2) * u : ℤ) : K) ((q ^ (β % 2) * v : ℤ) : K) := by
  have e : ∀ (γ : ℕ) (w : ℤ), q ^ γ * w = (q ^ (γ % 2) * w) * (q ^ (γ / 2)) ^ 2 := by
    intro γ w
    conv_lhs => rw [← Nat.mod_add_div γ 2]
    ring
  rw [e α u, e β v]
  exact T_cast_sq _ _ _ _ (pow_ne_zero _ hq) (pow_ne_zero _ hq)

lemma hform_mod2 (p : ℕ) [Fact p.Prime] (α β : ℕ) (u v : ℤ) :
    hform p α β u v = hform p (α % 2) (β % 2) u v := by
  simp only [hform, hf2, hfo, ZMod.natCast_mod]

theorem T_pow_iff (p : ℕ) [hp : Fact p.Prime] (α β : ℕ) (u v : ℤ) (hu : ¬ (p : ℤ) ∣ u)
    (hv : ¬ (p : ℤ) ∣ v) :
    T ℚ_[p] (((p : ℤ) ^ α * u : ℤ) : ℚ_[p]) (((p : ℤ) ^ β * v : ℤ) : ℚ_[p]) ↔ hform p α β u v = 0 := by
  rw [T_pow_mod2 _ (by exact_mod_cast hp.out.ne_zero), hform_mod2]
  have hα := Nat.mod_lt α two_pos
  have hβ := Nat.mod_lt β two_pos
  unfold hform
  split_ifs with h2
  · subst h2
    have hu' : ¬ (2 : ℤ) ∣ u := by exact_mod_cast hu
    have hv' : ¬ (2 : ℤ) ∣ v := by exact_mod_cast hv
    have := core2' (α % 2) (β % 2) (by omega) (by omega) u v (by omega) (by omega)
    simp only [Nat.cast_ofNat]
    exact this
  · exact coreO h2 _ _ (by omega) (by omega) u v hu hv

def vp (p : ℕ) (a : ℤ) : ℕ := a.natAbs.factorization p
def up (p : ℕ) (a : ℤ) : ℤ := a.sign * ((a.natAbs / p ^ vp p a : ℕ) : ℤ)

lemma decomp (p : ℕ) (a : ℤ) : a = (p : ℤ) ^ (vp p a) * up p a := by
  unfold up vp
  have h := Nat.ordProj_mul_ordCompl_eq_self a.natAbs p
  conv_lhs => rw [← Int.sign_mul_natAbs a, ← h]
  push_cast; ring

lemma up_natAbs (p : ℕ) {a : ℤ} (ha : a ≠ 0) : (up p a).natAbs = a.natAbs / p ^ vp p a := by
  unfold up
  rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero ha, one_mul, Int.natAbs_natCast]

lemma up_not_dvd (p : ℕ) [hp : Fact p.Prime] {a : ℤ} (ha : a ≠ 0) : ¬ (p : ℤ) ∣ up p a := by
  rw [Int.natCast_dvd, up_natAbs p ha]
  exact Nat.not_dvd_ordCompl hp.out (Int.natAbs_ne_zero.mpr ha)

lemma vp_mul (p : ℕ) {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) : vp p (a * b) = vp p a + vp p b := by
  unfold vp
  rw [Int.natAbs_mul, Nat.factorization_mul (Int.natAbs_ne_zero.mpr ha) (Int.natAbs_ne_zero.mpr hb)]
  rfl

lemma up_mul (p : ℕ) (a b : ℤ) : up p (a * b) = up p a * up p b := by
  unfold up vp
  rw [Int.sign_mul, Int.natAbs_mul, Nat.ordCompl_mul]
  push_cast; ring

/-- The (additive) Hilbert symbol at a prime `p` of two integers: `0 ↔ +1`. -/
def hilb (p : ℕ) [Fact p.Prime] (a b : ℤ) : ZMod 2 := hform p (vp p a) (vp p b) (up p a) (up p b)

theorem T_iff_hilb (p : ℕ) [Fact p.Prime] (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    T ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p]) ↔ hilb p a b = 0 := by
  have := T_pow_iff p (vp p a) (vp p b) (up p a) (up p b) (up_not_dvd p ha) (up_not_dvd p hb)
  rw [← decomp p a, ← decomp p b] at this
  exact this

def hinf (a b : ℤ) : ZMod 2 := if a < 0 ∧ b < 0 then 1 else 0

theorem T_real_iff (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : T ℝ (a : ℝ) (b : ℝ) ↔ hinf a b = 0 := by
  unfold hinf
  split_ifs with h
  · simp only [one_ne_zero, iff_false]
    rintro ⟨x, y, z, hne, he⟩
    have ha' : (a : ℝ) < 0 := by exact_mod_cast h.1
    have hb' : (b : ℝ) < 0 := by exact_mod_cast h.2
    have h1 : (a : ℝ) * x ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha'.le (sq_nonneg x)
    have h2 : (b : ℝ) * y ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb'.le (sq_nonneg y)
    have hz : z ^ 2 = 0 := by nlinarith [sq_nonneg z]
    have hx : (a : ℝ) * x ^ 2 = 0 := by nlinarith [sq_nonneg z]
    have hy : (b : ℝ) * y ^ 2 = 0 := by nlinarith [sq_nonneg z]
    have hx' := (mul_eq_zero.mp hx).resolve_left ha'.ne
    have hy' := (mul_eq_zero.mp hy).resolve_left hb'.ne
    rcases hne with h0 | h0 | h0
    · exact h0 (pow_eq_zero_iff two_ne_zero |>.mp hx')
    · exact h0 (pow_eq_zero_iff two_ne_zero |>.mp hy')
    · exact h0 (pow_eq_zero_iff two_ne_zero |>.mp hz)
  · simp only [iff_true]
    by_cases ha0 : 0 < a
    · have : (0 : ℝ) ≤ a := by exact_mod_cast ha0.le
      exact ⟨1, 0, Real.sqrt a, Or.inl one_ne_zero, by rw [Real.sq_sqrt this]; ring⟩
    · have hb0 : 0 < b := by
        rcases lt_or_gt_of_ne hb with hb1 | hb1
        · exact absurd ⟨by omega, hb1⟩ h
        · exact hb1
      have : (0 : ℝ) ≤ b := by exact_mod_cast hb0.le
      exact ⟨0, 1, Real.sqrt b, Or.inr (Or.inl one_ne_zero), by rw [Real.sq_sqrt this]; ring⟩

/-! ## S4: Hilbert reciprocity (product formula) for integers -/

def hilbN (p : ℕ) (a b : ℤ) : ZMod 2 := if h : p.Prime then @hilb p ⟨h⟩ a b else 0

lemma hilbN_eq (p : ℕ) [hp : Fact p.Prime] (a b : ℤ) : hilbN p a b = hilb p a b := by
  rw [hilbN, dif_pos hp.out]

lemma vp_of_not_dvd (p : ℕ) {a : ℤ} (h : ¬ p ∣ a.natAbs) : vp p a = 0 :=
  Nat.factorization_eq_zero_of_not_dvd h

lemma up_of_not_dvd (p : ℕ) {a : ℤ} (h : ¬ p ∣ a.natAbs) : up p a = a := by
  unfold up; rw [vp_of_not_dvd p h, pow_zero, Nat.div_one, Int.sign_mul_natAbs]

lemma vp_self (p : ℕ) [hp : Fact p.Prime] : vp p (p : ℤ) = 1 := by
  unfold vp; rw [Int.natAbs_natCast]; exact hp.out.factorization_self

lemma up_self (p : ℕ) [hp : Fact p.Prime] : up p (p : ℤ) = 1 := by
  unfold up; rw [vp_self, Int.natAbs_natCast, pow_one, Nat.div_self hp.out.pos,
    Int.sign_eq_one_of_pos (by exact_mod_cast hp.out.pos)]; rfl

lemma not_dvd_one_natAbs (p : ℕ) [hp : Fact p.Prime] : ¬ p ∣ (-1 : ℤ).natAbs := by
  simp only [Int.reduceNeg, Int.natAbs_neg, Int.natAbs_one, Nat.dvd_one]
  exact hp.out.one_lt.ne'

lemma not_dvd_prime (p q : ℕ) [hp : Fact p.Prime] (hq : q.Prime) (hpq : p ≠ q) :
    ¬ p ∣ (q : ℤ).natAbs := by
  rw [Int.natAbs_natCast]
  intro h
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp.out hq).mp h)

lemma hilb_two_eq (a b : ℤ) :
    hilb 2 a b = hf2 (vp 2 a) (vp 2 b) (up 2 a : ZMod (2 ^ 3)) (up 2 b : ZMod (2 ^ 3)) := by
  unfold hilb hform; rw [if_pos rfl]

lemma hilb_odd_eq (p : ℕ) [Fact p.Prime] (h2 : p ≠ 2) (a b : ℤ) :
    hilb p a b = hfo p (vp p a) (vp p b) (up p a) (up p b) := by
  unfold hilb hform; rw [if_neg h2]

lemma hilb_zero_of_not_dvd (p : ℕ) [Fact p.Prime] (a b : ℤ) (h2 : p ≠ 2) (ha : ¬ p ∣ a.natAbs)
    (hb : ¬ p ∣ b.natAbs) : hilb p a b = 0 := by
  rw [hilb_odd_eq p h2, vp_of_not_dvd p ha, vp_of_not_dvd p hb]; simp [hfo]

lemma hilbN_support (p : ℕ) (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hp : p ∉ (2 * a * b).natAbs.primeFactors) : hilbN p a b = 0 := by
  by_cases hpp : p.Prime
  · haveI : Fact p.Prime := ⟨hpp⟩
    rw [hilbN_eq]
    have hne : (2 * a * b).natAbs ≠ 0 := by simp [ha, hb]
    rw [Nat.mem_primeFactors] at hp
    have hnd : ¬ p ∣ (2 * a * b).natAbs := fun h => hp ⟨hpp, h, hne⟩
    rw [Int.natAbs_mul, Int.natAbs_mul] at hnd
    apply hilb_zero_of_not_dvd
    · rintro rfl; exact hnd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by norm_num) _) _)
    · exact fun h => hnd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _)
    · exact fun h => hnd (dvd_mul_of_dvd_right h _)
  · rw [hilbN, dif_neg hpp]

/-- Sum of all local symbols (real place + all primes). -/
def G (a b : ℤ) : ZMod 2 := hinf a b + ∑ p ∈ (2 * a * b).natAbs.primeFactors, hilbN p a b

lemma G_eq (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (F : Finset ℕ)
    (hF : ∀ p, p.Prime → p ∣ (2 * a * b).natAbs → p ∈ F) :
    G a b = hinf a b + ∑ p ∈ F, hilbN p a b := by
  unfold G; congr 1
  refine Finset.sum_subset (fun p hp => ?_) (fun p _ hp => hilbN_support p a b ha hb hp)
  rw [Nat.mem_primeFactors] at hp
  exact hF p hp.1 hp.2.1

lemma e8_mul : ∀ u v : ZMod (2 ^ 3), u.val % 2 = 1 → v.val % 2 = 1 → e8 (u * v) = e8 u + e8 v := by
  decide
lemma w8_mul : ∀ u v : ZMod (2 ^ 3), u.val % 2 = 1 → v.val % 2 = 1 → w8 (u * v) = w8 u + w8 v := by
  decide

lemma up_odd {b : ℤ} (hb : b ≠ 0) : (up 2 b) % 2 = 1 := by
  have h := up_not_dvd 2 hb
  have h' : ¬ (2 : ℤ) ∣ up 2 b := by exact_mod_cast h
  omega

lemma hilb_mul_right (p : ℕ) [Fact p.Prime] (a b b' : ℤ) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hilb p a (b * b') = hilb p a b + hilb p a b' := by
  by_cases h2 : p = 2
  · subst h2
    rw [hilb_two_eq, hilb_two_eq, hilb_two_eq, vp_mul 2 hb hb', up_mul]
    simp only [hf2, Int.cast_mul, Nat.cast_add]
    rw [e8_mul _ _ (odd_val8 _ (up_odd hb)) (odd_val8 _ (up_odd hb')),
      w8_mul _ _ (odd_val8 _ (up_odd hb)) (odd_val8 _ (up_odd hb'))]
    ring
  · rw [hilb_odd_eq p h2, hilb_odd_eq p h2, hilb_odd_eq p h2, vp_mul p hb hb', up_mul]
    simp only [hfo, Nat.cast_add]
    rw [lg_mul (up_not_dvd p hb) (up_not_dvd p hb')]
    ring

lemma hilb_symm (p : ℕ) [Fact p.Prime] (a b : ℤ) : hilb p a b = hilb p b a := by
  unfold hilb hform
  split_ifs
  · simp only [hf2]; ring
  · simp only [hfo]; ring

lemma hilbN_mul_right (p : ℕ) (a b b' : ℤ) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hilbN p a (b * b') = hilbN p a b + hilbN p a b' := by
  by_cases hpp : p.Prime
  · haveI : Fact p.Prime := ⟨hpp⟩
    rw [hilbN_eq, hilbN_eq, hilbN_eq, hilb_mul_right p a b b' hb hb']
  · rw [hilbN, dif_neg hpp, hilbN, dif_neg hpp, hilbN, dif_neg hpp, add_zero]

lemma hilbN_symm (p : ℕ) (a b : ℤ) : hilbN p a b = hilbN p b a := by
  by_cases hpp : p.Prime
  · haveI : Fact p.Prime := ⟨hpp⟩
    rw [hilbN_eq, hilbN_eq, hilb_symm]
  · rw [hilbN, dif_neg hpp, hilbN, dif_neg hpp]

lemma hinf_mul_right (a b b' : ℤ) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hinf a (b * b') = hinf a b + hinf a b' := by
  unfold hinf
  rcases lt_or_gt_of_ne hb with h1 | h1 <;> rcases lt_or_gt_of_ne hb' with h2 | h2 <;>
    by_cases ha : a < 0
  · have : ¬ b * b' < 0 := not_lt.mpr (mul_pos_of_neg_of_neg h1 h2).le
    simp only [ha, h1, h2, this, and_self, and_false, if_true, if_false]; decide
  · simp only [ha, false_and, if_false]; rfl
  · have : b * b' < 0 := mul_neg_of_neg_of_pos h1 h2
    simp only [ha, h1, this, and_self, if_true, not_lt.mpr h2.le, and_false, if_false, add_zero]
  · simp only [ha, false_and, if_false]; rfl
  · have : b * b' < 0 := mul_neg_of_pos_of_neg h1 h2
    simp only [ha, h2, this, and_self, if_true, not_lt.mpr h1.le, and_false, if_false, zero_add]
  · simp only [ha, false_and, if_false]; rfl
  · have : ¬ b * b' < 0 := not_lt.mpr (mul_pos h1 h2).le
    simp only [ha, this, not_lt.mpr h1.le, not_lt.mpr h2.le, and_false, if_false, add_zero]
  · simp only [ha, false_and, if_false]; rfl

lemma hinf_symm (a b : ℤ) : hinf a b = hinf b a := by
  unfold hinf; simp only [and_comm]

lemma G_mul_right (a b b' : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    G a (b * b') = G a b + G a b' := by
  have hn : (2 * a * (b * b')).natAbs ≠ 0 := by simp [ha, hb, hb']
  set F := (2 * a * (b * b')).natAbs.primeFactors
  have h1 : ∀ p, p.Prime → p ∣ (2 * a * b).natAbs → p ∈ F := by
    intro p hp hd
    rw [Nat.mem_primeFactors]
    refine ⟨hp, dvd_trans hd ?_, hn⟩
    rw [Int.natAbs_dvd_natAbs]; exact ⟨b', by ring⟩
  have h2 : ∀ p, p.Prime → p ∣ (2 * a * b').natAbs → p ∈ F := by
    intro p hp hd
    rw [Nat.mem_primeFactors]
    refine ⟨hp, dvd_trans hd ?_, hn⟩
    rw [Int.natAbs_dvd_natAbs]; exact ⟨b, by ring⟩
  rw [G_eq a b ha hb F h1, G_eq a b' ha hb' F h2]
  unfold G
  rw [hinf_mul_right a b b' hb hb', Finset.sum_congr rfl (fun p _ => hilbN_mul_right p a b b' hb hb'),
    Finset.sum_add_distrib]
  ring

lemma G_symm (a b : ℤ) : G a b = G b a := by
  unfold G
  rw [show 2 * b * a = 2 * a * b by ring, hinf_symm]
  congr 1
  exact Finset.sum_congr rfl (fun p _ => hilbN_symm p a b)

lemma zero_of_additive (f : ℤ → ZMod 2) (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → f (a * b) = f a + f b)
    (hneg : f (-1) = 0) (hprime : ∀ q : ℕ, q.Prime → f q = 0) : ∀ a, a ≠ 0 → f a = 0 := by
  have h1 : f 1 = 0 := by
    have := hmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one, CharTwo.add_self_eq_zero] at this
    exact this
  have hnat : ∀ n : ℕ, n ≠ 0 → f n = 0 := by
    intro n
    induction n using Nat.recOnMul with
    | zero => intro h; exact absurd rfl h
    | one => intro _; simpa using h1
    | prime p hp => intro _; exact hprime p hp
    | mul a b iha ihb =>
      intro hab
      have ha : a ≠ 0 := fun h => hab (by rw [h, zero_mul])
      have hb : b ≠ 0 := fun h => hab (by rw [h, mul_zero])
      push_cast
      rw [hmul _ _ (by exact_mod_cast ha) (by exact_mod_cast hb), iha ha, ihb hb, add_zero]
  intro a ha
  have hn := Int.natAbs_ne_zero.mpr ha
  rcases Int.natAbs_eq a with h | h
  · rw [h]; exact hnat _ hn
  · rw [h, neg_eq_neg_one_mul, hmul _ _ (by norm_num) (by exact_mod_cast hn), hneg, hnat _ hn, add_zero]

/-! ### Base cases -/

lemma odd_cases8 (q : ℤ) (hq : q % 2 = 1) :
    (q % 8 = 1 ∧ (q : ZMod (2 ^ 3)) = 1) ∨ (q % 8 = 3 ∧ (q : ZMod (2 ^ 3)) = 3) ∨
    (q % 8 = 5 ∧ (q : ZMod (2 ^ 3)) = 5) ∨ (q % 8 = 7 ∧ (q : ZMod (2 ^ 3)) = 7) := by
  have e : (q : ZMod (2 ^ 3)) = ((q % 8 : ℤ) : ZMod (2 ^ 3)) := by
    rw [← ZMod.intCast_mod q (2 ^ 3)]; norm_num
  have : q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by omega
  rcases this with h | h | h | h <;> rw [h] at e
  · exact Or.inl ⟨h, by rw [e]; rfl⟩
  · exact Or.inr (Or.inl ⟨h, by rw [e]; rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, by rw [e]; rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h, by rw [e]; rfl⟩))

lemma e8_eq (q : ℤ) (hq : q % 2 = 1) : e8 (q : ZMod (2 ^ 3)) = if q % 4 = 1 then 0 else 1 := by
  rcases odd_cases8 q hq with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ <;> rw [e]
  · rw [if_pos (by omega)]; decide
  · rw [if_neg (by omega)]; decide
  · rw [if_pos (by omega)]; decide
  · rw [if_neg (by omega)]; decide

lemma w8_eq (q : ℤ) (hq : q % 2 = 1) :
    w8 (q : ZMod (2 ^ 3)) = if q % 8 = 1 ∨ q % 8 = 7 then 0 else 1 := by
  rcases odd_cases8 q hq with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ <;> rw [e]
  · rw [if_pos (by omega)]; decide
  · rw [if_neg (by omega)]; decide
  · rw [if_neg (by omega)]; decide
  · rw [if_pos (by omega)]; decide

lemma prime_odd_int (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) : (q : ℤ) % 2 = 1 := by
  have := Nat.odd_iff.mp (hq.odd_of_ne_two hq2); omega

lemma lg_neg_one (q : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2) : lg q (-1) = e8 ((q : ℤ) : ZMod (2 ^ 3)) := by
  have hodd := prime_odd_int q hq.out hq2
  rw [e8_eq _ hodd]
  unfold lg
  rw [legendreSym.at_neg_one hq2, ZMod.χ₄_nat_eq_if_mod_four]
  rcases (by omega : q % 4 = 1 ∨ q % 4 = 3) with h | h
  · rw [if_pos (by omega : (q : ℤ) % 4 = 1)]
    simp [show q % 2 ≠ 0 by omega, h]
  · rw [if_neg (by omega : ¬ (q : ℤ) % 4 = 1)]
    simp [show q % 2 ≠ 0 by omega, show ¬ q % 4 = 1 by omega]

lemma lg_two (q : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2) : lg q 2 = w8 ((q : ℤ) : ZMod (2 ^ 3)) := by
  have hodd := prime_odd_int q hq.out hq2
  rw [w8_eq _ hodd]
  unfold lg
  rw [legendreSym.at_two hq2, ZMod.χ₈_nat_eq_if_mod_eight]
  by_cases h : q % 8 = 1 ∨ q % 8 = 7
  · rw [if_pos (by omega : (q : ℤ) % 8 = 1 ∨ (q : ℤ) % 8 = 7)]
    simp [show q % 2 ≠ 0 by omega, h]
  · rw [if_neg (by omega : ¬ ((q : ℤ) % 8 = 1 ∨ (q : ℤ) % 8 = 7))]
    simp only [show q % 2 ≠ 0 by omega, h, if_false]
    decide

lemma lg_one (q : ℕ) [Fact q.Prime] : lg q 1 = 0 := by
  unfold lg; rw [legendreSym.at_one, if_pos rfl]

lemma qr_add (q q' : ℕ) [hq : Fact q.Prime] [hq' : Fact q'.Prime] (h2 : q ≠ 2) (h2' : q' ≠ 2)
    (hne : q ≠ q') :
    lg q q' + lg q' q = (if (q : ℤ) % 4 = 3 ∧ (q' : ℤ) % 4 = 3 then 1 else 0) := by
  have o1 := prime_odd_int q hq.out h2
  have o2 := prime_odd_int q' hq'.out h2'
  have hQR := legendreSym.quadratic_reciprocity h2 h2' hne
  have hpar : legendreSym q' q * legendreSym q q' =
      if (q : ℤ) % 4 = 3 ∧ (q' : ℤ) % 4 = 3 then -1 else 1 := by
    rw [hQR]
    split_ifs with hc
    · apply Odd.neg_one_pow
      apply Nat.odd_mul.mpr
      constructor <;> apply Nat.odd_iff.mpr <;> omega
    · apply Even.neg_one_pow
      apply Nat.even_mul.mpr
      by_cases h1 : (q : ℤ) % 4 = 3
      · right; apply Nat.even_iff.mpr; omega
      · left; apply Nat.even_iff.mpr; omega
  have hA := legendreSym.eq_one_or_neg_one q (a := (q' : ℤ))
    (unit_zmod (p := q) (by exact_mod_cast not_dvd_prime q q' hq'.out hne))
  have hB := legendreSym.eq_one_or_neg_one q' (a := (q : ℤ))
    (unit_zmod (p := q') (by exact_mod_cast not_dvd_prime q' q hq.out (Ne.symm hne)))
  unfold lg
  rcases hA with hA | hA <;> rcases hB with hB | hB <;> rw [hA, hB] at hpar ⊢ <;>
    split_ifs at hpar ⊢ <;> first | rfl | decide | contradiction | (norm_num at hpar) | simp_all


/-! ### Base cases of the product formula -/

lemma dvd_cases {p : ℕ} (hp : p.Prime) {a b : ℤ} (h : p ∣ (2 * a * b).natAbs) :
    p = 2 ∨ p ∣ a.natAbs ∨ p ∣ b.natAbs := by
  rw [Int.natAbs_mul, Int.natAbs_mul] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by simpa using h)
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

lemma not_dvd_neg_one' {p : ℕ} (hp : p.Prime) : ¬ p ∣ (-1 : ℤ).natAbs := by
  simp only [Int.reduceNeg, Int.natAbs_neg, Int.natAbs_one, Nat.dvd_one]; exact hp.one_lt.ne'

lemma eq_of_dvd_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ∣ (q : ℤ).natAbs) : p = q :=
  (Nat.prime_dvd_prime_iff_eq hp hq).mp (by simpa using h)

lemma vp_neg_one (p : ℕ) [Fact p.Prime] : vp p (-1) = 0 := vp_of_not_dvd p (not_dvd_one_natAbs p)
lemma up_neg_one (p : ℕ) [Fact p.Prime] : up p (-1) = -1 := up_of_not_dvd p (not_dvd_one_natAbs p)
lemma vp_ne (p q : ℕ) [Fact p.Prime] (hq : q.Prime) (h : p ≠ q) : vp p q = 0 :=
  vp_of_not_dvd p (not_dvd_prime p q hq h)
lemma up_ne (p q : ℕ) [Fact p.Prime] (hq : q.Prime) (h : p ≠ q) : up p q = q :=
  up_of_not_dvd p (not_dvd_prime p q hq h)

lemma hinf_of_pos_right (a b : ℤ) (hb : 0 < b) : hinf a b = 0 := by
  unfold hinf; rw [if_neg (by omega)]
lemma hinf_of_pos_left (a b : ℤ) (ha : 0 < a) : hinf a b = 0 := by
  unfold hinf; rw [if_neg (by omega)]

lemma e8_m1 : e8 ((-1 : ℤ) : ZMod (2 ^ 3)) = 1 := by decide
lemma w8_m1 : w8 ((-1 : ℤ) : ZMod (2 ^ 3)) = 0 := by decide
lemma e8_1 : e8 ((1 : ℤ) : ZMod (2 ^ 3)) = 0 := by decide
lemma w8_1 : w8 ((1 : ℤ) : ZMod (2 ^ 3)) = 0 := by decide
lemma z2_sq_add (t : ZMod 2) : t * t + t = 0 := by revert t; decide

lemma G_nn : G (-1) (-1) = 0 := by
  rw [G_eq (-1) (-1) (by norm_num) (by norm_num) {2} (fun p hp hd => by
    rcases dvd_cases hp hd with h | h | h
    · simp [h]
    · exact absurd h (not_dvd_neg_one' hp)
    · exact absurd h (not_dvd_neg_one' hp))]
  rw [Finset.sum_singleton, hilbN_eq, hilb_two_eq, vp_neg_one, up_neg_one]
  unfold hinf
  rw [if_pos (by norm_num)]
  simp only [hf2, Nat.cast_zero, zero_mul, add_zero, e8_m1]
  decide

lemma G_np (q : ℕ) (hq : q.Prime) : G (-1) q = 0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hF : ∀ F : Finset ℕ, 2 ∈ F → q ∈ F → ∀ p, p.Prime → p ∣ (2 * (-1) * (q : ℤ)).natAbs → p ∈ F := by
    intro F h2 hqF p hp hd
    rcases dvd_cases hp hd with h | h | h
    · rw [h]; exact h2
    · exact absurd h (not_dvd_neg_one' hp)
    · rw [eq_of_dvd_prime hp hq h]; exact hqF
  obtain rfl | hq2 := eq_or_ne q 2
  · rw [G_eq (-1) _ (by norm_num) hq0 {2} (hF _ (by simp) (by simp)), Finset.sum_singleton,
      hilbN_eq, hilb_two_eq, vp_neg_one, up_neg_one, vp_self, up_self,
      hinf_of_pos_right _ _ (by norm_num)]
    simp only [hf2, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, add_zero, zero_add, e8_m1, e8_1,
      w8_m1, mul_zero]
  · rw [G_eq (-1) _ (by norm_num) hq0 {2, q} (hF _ (by simp) (by simp)), Finset.sum_pair hq2.symm,
      hilbN_eq 2, hilbN_eq q, hilb_two_eq, hilb_odd_eq q hq2, vp_neg_one 2, up_neg_one 2,
      vp_neg_one q, up_neg_one q, vp_self q, up_self q, vp_ne 2 q hq hq2.symm, up_ne 2 q hq hq2.symm,
      hinf_of_pos_right _ _ (by exact_mod_cast hq.pos)]
    simp only [hf2, hfo, e8_m1, lg_one, Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, one_mul,
      mul_one, zero_add, add_zero]
    rw [lg_neg_one q hq2, CharTwo.add_self_eq_zero]

lemma G_2p (q : ℕ) (hq : q.Prime) : G (2 : ℕ) q = 0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have h20 : ((2 : ℕ) : ℤ) ≠ 0 := by norm_num
  have hF : ∀ F : Finset ℕ, 2 ∈ F → q ∈ F →
      ∀ p, p.Prime → p ∣ (2 * ((2 : ℕ) : ℤ) * (q : ℤ)).natAbs → p ∈ F := by
    intro F h2 hqF p hp hd
    rcases dvd_cases hp hd with h | h | h
    · rw [h]; exact h2
    · rw [eq_of_dvd_prime hp Nat.prime_two h]; exact h2
    · rw [eq_of_dvd_prime hp hq h]; exact hqF
  obtain rfl | hq2 := eq_or_ne q 2
  · rw [G_eq _ _ h20 hq0 {2} (hF _ (by simp) (by simp)), Finset.sum_singleton,
      hilbN_eq, hilb_two_eq, vp_self, up_self, hinf_of_pos_right _ _ (by norm_num)]
    simp only [hf2, Nat.cast_one, one_mul, e8_1, w8_1, mul_zero, add_zero]
  · rw [G_eq _ _ h20 hq0 {2, q} (hF _ (by simp) (by simp)), Finset.sum_pair hq2.symm,
      hilbN_eq 2, hilbN_eq q, hilb_two_eq, hilb_odd_eq q hq2, vp_self 2, up_self 2,
      vp_self q, up_self q, vp_ne 2 q hq hq2.symm, up_ne 2 q hq hq2.symm,
      vp_ne q 2 Nat.prime_two hq2, up_ne q 2 Nat.prime_two hq2,
      hinf_of_pos_right _ _ (by exact_mod_cast hq.pos)]
    simp only [hf2, hfo, e8_1, w8_1, lg_one, Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, one_mul,
      mul_one, zero_add, add_zero]
    rw [Nat.cast_ofNat, lg_two q hq2, CharTwo.add_self_eq_zero]

lemma G_pp_odd (q q' : ℕ) (hq : q.Prime) (hq' : q'.Prime) (hq2 : q ≠ 2) (hq2' : q' ≠ 2) :
    G q q' = 0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact q'.Prime := ⟨hq'⟩
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hq0' : (q' : ℤ) ≠ 0 := by exact_mod_cast hq'.ne_zero
  have hF : ∀ F : Finset ℕ, 2 ∈ F → q ∈ F → q' ∈ F →
      ∀ p, p.Prime → p ∣ (2 * (q : ℤ) * (q' : ℤ)).natAbs → p ∈ F := by
    intro F h2 hqF hqF' p hp hd
    rcases dvd_cases hp hd with h | h | h
    · rw [h]; exact h2
    · rw [eq_of_dvd_prime hp hq h]; exact hqF
    · rw [eq_of_dvd_prime hp hq' h]; exact hqF'
  have o1 := prime_odd_int q hq hq2
  have o2 := prime_odd_int q' hq' hq2'
  obtain rfl | hne := eq_or_ne q q'
  · rw [G_eq _ _ hq0 hq0' {2, q} (hF _ (by simp) (by simp) (by simp)), Finset.sum_pair hq2.symm,
      hilbN_eq 2, hilbN_eq q, hilb_two_eq, hilb_odd_eq q hq2,
      vp_self q, up_self q, vp_ne 2 q hq hq2.symm, up_ne 2 q hq hq2.symm,
      hinf_of_pos_right _ _ (by exact_mod_cast hq.pos)]
    simp only [hf2, hfo, lg_one, Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, one_mul,
      mul_one, zero_add, add_zero]
    rw [lg_neg_one q hq2, z2_sq_add]
  · have h2n : 2 ∉ ({q, q'} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hq2.symm, hq2'.symm⟩
    rw [G_eq _ _ hq0 hq0' {2, q, q'} (hF _ (by simp) (by simp) (by simp)), Finset.sum_insert h2n,
      Finset.sum_pair hne,
      hilbN_eq 2, hilbN_eq q, hilbN_eq q', hilb_two_eq, hilb_odd_eq q hq2, hilb_odd_eq q' hq2',
      vp_self q, up_self q, vp_self q', up_self q', vp_ne 2 q hq hq2.symm, up_ne 2 q hq hq2.symm,
      vp_ne 2 q' hq' hq2'.symm, up_ne 2 q' hq' hq2'.symm, vp_ne q q' hq' hne, up_ne q q' hq' hne,
      vp_ne q' q hq (Ne.symm hne), up_ne q' q hq (Ne.symm hne),
      hinf_of_pos_right _ _ (by exact_mod_cast hq'.pos)]
    simp only [hf2, hfo, lg_one, Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, one_mul,
      mul_one, zero_add, add_zero]
    rw [qr_add q q' hq2 hq2' hne, e8_eq _ o1, e8_eq _ o2]
    split_ifs <;> first | decide | (exfalso; omega)

lemma G_pp (q q' : ℕ) (hq : q.Prime) (hq' : q'.Prime) : G q q' = 0 := by
  obtain rfl | hq2 := eq_or_ne q 2
  · exact G_2p q' hq'
  obtain rfl | hq2' := eq_or_ne q' 2
  · rw [G_symm]; exact G_2p q hq
  exact G_pp_odd q q' hq hq' hq2 hq2'

/-- Hilbert reciprocity for nonzero integers. -/
theorem product_formula (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : G a b = 0 := by
  have base : ∀ b0 : ℤ, (b0 = -1 ∨ ∃ q : ℕ, q.Prime ∧ b0 = q) → ∀ a, a ≠ 0 → G a b0 = 0 := by
    intro b0 hb0
    have hb00 : b0 ≠ 0 := by
      rcases hb0 with rfl | ⟨q, hq, rfl⟩
      · norm_num
      · exact_mod_cast hq.ne_zero
    refine zero_of_additive (fun a => G a b0) (fun x y hx hy => ?_) ?_ ?_
    · show G (x * y) b0 = G x b0 + G y b0
      rw [G_symm, G_mul_right b0 x y hb00 hx hy, G_symm b0 x, G_symm b0 y]
    · rcases hb0 with rfl | ⟨q, hq, rfl⟩
      · exact G_nn
      · exact G_np q hq
    · intro q hq
      rcases hb0 with rfl | ⟨q', hq', rfl⟩
      · show G q (-1) = 0
        rw [G_symm]; exact G_np q hq
      · exact G_pp q q' hq hq'
  refine zero_of_additive (fun b => G a b) (fun x y hx hy => G_mul_right a x y ha hx hy) ?_ ?_ b hb
  · exact base (-1) (Or.inl rfl) a ha
  · intro q hq; exact base q (Or.inr ⟨q, hq, rfl⟩) a ha


/-! ## S5a: integer representatives of p-adic square classes -/

section Rep
variable {p : ℕ} [hp : Fact p.Prime]

lemma norm_two_sq_gt : (p : ℝ) ^ (-(3 : ℕ) : ℤ) < ‖(2 : ℤ_[p])‖ ^ 2 := by
  by_cases h2 : p = 2
  · subst h2
    have : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by
      have := PadicInt.norm_p (p := 2); simpa using this
    rw [this]; norm_num
  · have : ‖(2 : ℤ_[p])‖ = 1 := by
      have := int_norm_one (p := p) (k := 2) (prime_int_not_dvd_two h2); simpa using this
    rw [this, one_pow]
    have h1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    exact zpow_lt_one_of_neg₀ h1 (by norm_num)

lemma unit_int_rep (u : ℤ_[p]) (hu : IsUnit u) :
    ∃ m : ℤ, ¬ (p : ℤ) ∣ m ∧ ∃ z : ℤ_[p], z ^ 2 = u * m := by
  set m : ℤ := (PadicInt.appr u 3 : ℤ) with hmdef
  have hle : ‖u - (m : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(3 : ℕ) : ℤ) := by
    rw [PadicInt.norm_le_pow_iff_mem_span_pow]
    have := PadicInt.appr_spec 3 u
    simpa [hmdef] using this
  have hm : ¬ (p : ℤ) ∣ m := by
    intro hd
    have h1 : ‖(m : ℤ_[p])‖ < 1 := (PadicInt.norm_int_lt_one_iff_dvd m).mpr hd
    have h2 : ‖u‖ = 1 := PadicInt.isUnit_iff.mp hu
    have h3 : ‖u - (m : ℤ_[p])‖ < 1 := lt_of_le_of_lt hle (by
      have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
      exact zpow_lt_one_of_neg₀ this (by norm_num))
    have h4 : ‖u‖ ≤ max ‖u - (m : ℤ_[p])‖ ‖(m : ℤ_[p])‖ := by
      calc ‖u‖ = ‖(u - (m : ℤ_[p])) + (m : ℤ_[p])‖ := by rw [sub_add_cancel]
        _ ≤ _ := PadicInt.nonarchimedean _ _
    rw [h2] at h4
    exact absurd h4 (not_le.mpr (max_lt h3 h1))
  refine ⟨m, hm, ?_⟩
  obtain ⟨z, hz, -⟩ := hensel_quad (p := p) 1 (-(u * m)) (m : ℤ_[p]) (by
    have e1 : (1 : ℤ_[p]) * (m : ℤ_[p]) ^ 2 + -(u * m) = (m : ℤ_[p]) * ((m : ℤ_[p]) - u) := by ring
    rw [e1, norm_mul, int_norm_one hm, one_mul, norm_sub_rev, mul_one, norm_mul, int_norm_one hm,
      mul_one]
    exact lt_of_le_of_lt hle norm_two_sq_gt)
  exact ⟨z, by linear_combination hz⟩

/-- Every nonzero `p`-adic number times a nonzero square is an integer. -/
lemma padic_int_rep (c : ℚ_[p]) (hc : c ≠ 0) :
    ∃ r : ℤ, r ≠ 0 ∧ ∃ s : ℚ_[p], s ≠ 0 ∧ c * s ^ 2 = r := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ‖c‖ (one_lt_pow₀ h1 (two_ne_zero) : (1 : ℝ) < p ^ 2)
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hnorm : ‖c * (p : ℚ_[p]) ^ (2 * N)‖ ≤ 1 := by
    rw [norm_mul, norm_pow, Padic.norm_p, pow_mul, inv_pow, inv_pow]
    have hpos : (0 : ℝ) < ((p : ℝ) ^ 2) ^ N := by positivity
    rw [mul_inv_le_iff₀ hpos, one_mul]; exact hN.le
  set d : ℤ_[p] := ⟨c * (p : ℚ_[p]) ^ (2 * N), hnorm⟩ with hd
  have hdc : (d : ℚ_[p]) = c * (p : ℚ_[p]) ^ (2 * N) := rfl
  have hd0 : d ≠ 0 := by
    intro h; apply hc
    have : (d : ℚ_[p]) = 0 := by rw [h]; rfl
    rw [hdc] at this
    exact (mul_eq_zero.mp this).resolve_right (pow_ne_zero _ hp0)
  have hspec := PadicInt.unitCoeff_spec hd0
  obtain ⟨m, hm, z, hz⟩ := unit_int_rep (PadicInt.unitCoeff hd0 : ℤ_[p]) (Units.isUnit _)
  have hm0 : (m : ℚ_[p]) ≠ 0 := by
    intro h; apply hm; rw [show m = 0 by exact_mod_cast h]; exact dvd_zero _
  have hzn : ‖z‖ ^ 2 = 1 := by
    rw [← norm_pow, hz, norm_mul, PadicInt.isUnit_iff.mp (Units.isUnit _), int_norm_one hm, one_mul]
  have hz0 : (z : ℚ_[p]) ≠ 0 := by
    rw [PadicInt.coe_ne_zero]; rintro rfl; rw [norm_zero] at hzn; norm_num at hzn
  refine ⟨(p : ℤ) ^ d.valuation * m, mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))
    (by exact_mod_cast hm0), (p : ℚ_[p]) ^ N * m / z, ?_, ?_⟩
  · exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hp0) hm0) hz0
  · have e1 := congrArg ((↑) : ℤ_[p] → ℚ_[p]) hspec
    have e2 := congrArg ((↑) : ℤ_[p] → ℚ_[p]) hz
    push_cast at e1 e2
    rw [hdc] at e1
    push_cast
    rw [div_pow, mul_div_assoc', div_eq_iff (pow_ne_zero 2 hz0), e2]
    linear_combination (m : ℚ_[p]) ^ 2 * e1
end Rep

/-! ## S5b: same-class integers, isotropy predicates, the ternary lemma -/

/-- `x` and `r` have the same `p`-adic square class data (parity of valuation, unit part mod `p^3`). -/
def cls (p : ℕ) (x r : ℤ) : Prop := vp p x % 2 = vp p r % 2 ∧ (p : ℤ) ^ 3 ∣ up p x - up p r

section Cls
variable {p : ℕ} [hp : Fact p.Prime]

lemma cls_sq (x r : ℤ) (hx : x ≠ 0) (hr : r ≠ 0) (h : cls p x r) : IsSquare ((x * r : ℤ) : ℚ_[p]) := by
  obtain ⟨hv, hu⟩ := h
  have hux := up_not_dvd p hx
  have hur := up_not_dvd p hr
  have hsq : IsSquare ((up p x * up p r : ℤ) : ℚ_[p]) := by
    by_cases h2 : p = 2
    · subst h2
      apply two_adic_sq
      have h8 : (8 : ℤ) ∣ up 2 x - up 2 r := by simpa using hu
      have hodd : up 2 r % 2 = 1 := by
        have : ¬ (2 : ℤ) ∣ up 2 r := by exact_mod_cast hur
        omega
      obtain ⟨k, hk⟩ : ∃ k, up 2 r = 2 * k + 1 := ⟨up 2 r / 2, by omega⟩
      obtain ⟨j, hj⟩ := h8
      obtain ⟨t, ht⟩ := Int.even_mul_succ_self k
      have e : up 2 x * up 2 r = 8 * (t + j * (2 * k + 1)) + 1 := by
        have hx' : up 2 x = up 2 r + 8 * j := by linarith
        rw [hx', hk]; linear_combination 4 * ht
      rw [e]; omega
    · apply padic_sq_of_sq_mod h2 (up p x * up p r) (up p r) (not_dvd_mul hux hur)
      have h1 : (p : ℤ) ∣ up p x - up p r := dvd_trans (dvd_pow_self _ (by norm_num)) hu
      have e : up p r ^ 2 - up p x * up p r = -(up p r * (up p x - up p r)) := by ring
      rw [e]; exact (Dvd.dvd.mul_left h1 _).neg_right
  obtain ⟨w, hw⟩ := hsq
  obtain ⟨k, hk⟩ : ∃ k, vp p x + vp p r = 2 * k := ⟨(vp p x + vp p r) / 2, by omega⟩
  refine ⟨(p : ℚ_[p]) ^ k * w, ?_⟩
  have hdx := decomp p x
  have hdr := decomp p r
  calc ((x * r : ℤ) : ℚ_[p])
      = (p : ℚ_[p]) ^ (vp p x + vp p r) * ((up p x * up p r : ℤ) : ℚ_[p]) := by
        conv_lhs => rw [hdx, hdr]
        push_cast; ring
    _ = _ := by rw [hk, hw, pow_mul]; ring

lemma cls_ratio (x r : ℤ) (hx : x ≠ 0) (hr : r ≠ 0) (h : cls p x r) :
    ∃ t : ℚ_[p], t ≠ 0 ∧ (x : ℚ_[p]) = r * t ^ 2 := by
  obtain ⟨s, hs⟩ := cls_sq x r hx hr h
  have hr0 : (r : ℚ_[p]) ≠ 0 := by exact_mod_cast hr
  have hx0 : (x : ℚ_[p]) ≠ 0 := by exact_mod_cast hx
  push_cast at hs
  have hs0 : s ≠ 0 := by
    rintro rfl; rw [mul_zero] at hs; exact mul_ne_zero hx0 hr0 hs
  refine ⟨s / r, div_ne_zero hs0 hr0, ?_⟩
  rw [div_pow, mul_div_assoc', eq_div_iff (pow_ne_zero 2 hr0)]
  linear_combination (r : ℚ_[p]) * hs

end Cls

/-- The diagonal form `∑ a i * x i ^ 2` has a nontrivial zero over `K`. -/
def Iso (K : Type*) [Field K] {n : ℕ} (a : Fin n → K) : Prop :=
  ∃ x : Fin n → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0

lemma iso_scale {K : Type*} [Field K] {n : ℕ} (a a' s : Fin n → K) (hs : ∀ i, s i ≠ 0)
    (h : ∀ i, a' i * s i ^ 2 = a i) (H : Iso K a) : Iso K a' := by
  obtain ⟨x, hx0, hx⟩ := H
  refine ⟨fun i => s i * x i, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
    exact Function.ne_iff.mpr ⟨i, mul_ne_zero (hs i) hi⟩
  · rw [← hx]
    exact Finset.sum_congr rfl (fun i _ => by rw [← h i]; ring)

lemma vec3_ne {K : Type*} [Field K] (x y z : K) (h : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) : ![x, y, z] ≠ 0 := by
  intro h0
  rcases h with h | h | h
  · exact h (by simpa using congrFun h0 0)
  · exact h (by simpa using congrFun h0 1)
  · exact h (by simpa using congrFun h0 2)

lemma iso3_T {K : Type*} [Field K] (a b c : K) (hc : c ≠ 0) :
    Iso K ![a, b, -c] ↔ T K (a * c) (b * c) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hv
    refine ⟨v 0, v 1, c * v 2, ?_, by linear_combination (-c) * hv⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (mul_ne_zero hc hi))
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨![x * c, y * c, z], vec3_ne _ _ _ ?_, ?_⟩
    · rcases hne with h1 | h1 | h1
      · exact Or.inl (mul_ne_zero h1 hc)
      · exact Or.inr (Or.inl (mul_ne_zero h1 hc))
      · exact Or.inr (Or.inr h1)
    · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination (-c) * h

/-- Product formula: if every place but `ℓ` has trivial symbol, so does `ℓ`. -/
lemma last_place (A B : ℤ) (hA : A ≠ 0) (hB : B ≠ 0) (ℓ : ℕ) (hR : hinf A B = 0)
    (hP : ∀ p : ℕ, p.Prime → p ≠ ℓ → hilbN p A B = 0) : hilbN ℓ A B = 0 := by
  have hP' : ∀ p, p ≠ ℓ → hilbN p A B = 0 := by
    intro p hp
    by_cases hpp : p.Prime
    · exact hP p hpp hp
    · rw [hilbN, dif_neg hpp]
  have h := product_formula A B hA hB
  rw [G_eq A B hA hB (insert ℓ (2 * A * B).natAbs.primeFactors) (fun p hp hd => by
    rw [Finset.mem_insert, Nat.mem_primeFactors]
    exact Or.inr ⟨hp, hd, by simp [hA, hB]⟩), hR, zero_add,
    Finset.sum_eq_single_of_mem ℓ (Finset.mem_insert_self _ _) (fun p _ hne => hP' p hne)] at h
  exact h

/-- Ternary lemma: `<a, b, -x>` isotropic at `ℝ` and at all primes `p ≠ ℓ` dividing `2abx`
  is isotropic at every prime. -/
theorem tern (a b x : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0) (ℓ : ℕ)
    (hR : Iso ℝ ![(a : ℝ), b, -(x : ℝ)])
    (hS : ∀ (p : ℕ) [Fact p.Prime], p ≠ ℓ → p ∣ (2 * a * b * x).natAbs →
      Iso ℚ_[p] ![(a : ℚ_[p]), b, -(x : ℚ_[p])]) :
    ∀ (p : ℕ) [Fact p.Prime], Iso ℚ_[p] ![(a : ℚ_[p]), b, -(x : ℚ_[p])] := by
  have hax : a * x ≠ 0 := mul_ne_zero ha hx
  have hbx : b * x ≠ 0 := mul_ne_zero hb hx
  have hTp : ∀ (p : ℕ) [Fact p.Prime], Iso ℚ_[p] ![(a : ℚ_[p]), b, -(x : ℚ_[p])] ↔
      hilb p (a * x) (b * x) = 0 := by
    intro p _
    rw [iso3_T _ _ _ (by exact_mod_cast hx), ← T_iff_hilb p _ _ hax hbx]; push_cast; rfl
  have hoff : ∀ (p : ℕ) [Fact p.Prime], p ≠ ℓ → hilb p (a * x) (b * x) = 0 := by
    intro p hpf hpl
    by_cases hd : p ∣ (2 * a * b * x).natAbs
    · exact (hTp p).mp (hS p hpl hd)
    · have hnd : ∀ y : ℤ, y ∣ 2 * a * b * x → ¬ p ∣ y.natAbs := fun y hy hpy =>
        hd (dvd_trans hpy (Int.natAbs_dvd_natAbs.mpr hy))
      apply hilb_zero_of_not_dvd
      · rintro rfl; exact hnd 2 ⟨a * b * x, by ring⟩ (by norm_num)
      · exact hnd _ ⟨2 * b, by ring⟩
      · exact hnd _ ⟨2 * a, by ring⟩
  intro p _
  by_cases hpl : p = ℓ
  · subst hpl
    rw [hTp, ← hilbN_eq]
    apply last_place _ _ hax hbx
    · rw [← T_real_iff _ _ hax hbx]
      have := (iso3_T _ _ _ (by exact_mod_cast hx)).mp hR
      push_cast; exact this
    · intro q hq hqp
      haveI : Fact q.Prime := ⟨hq⟩
      rw [hilbN_eq]; exact hoff q hqp
  · exact (hTp p).mpr (hoff p hpl)

/-! ## S5c: field lemmas for splitting `f = g ⊕ h` -/

lemma sum_split {K : Type*} [Field K] {m : ℕ} (a v : Fin (m + 2) → K) :
    ∑ i, a i * v i ^ 2 = a 0 * v 0 ^ 2 + (a 1 * v 1 ^ 2 + ∑ i : Fin m, a i.succ.succ * v i.succ.succ ^ 2) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.succ_zero_eq_one]

lemma sum_cons {K : Type*} [Field K] {m : ℕ} (c y : K) (h w : Fin m → K) :
    ∑ i, (Fin.cons c h : Fin (m + 1) → K) i * (Fin.cons y w : Fin (m + 1) → K) i ^ 2 =
      c * y ^ 2 + ∑ i, h i * w i ^ 2 := by
  rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]

lemma sum3 {K : Type*} [Field K] (a b c x y z : K) :
    ∑ i, ![a, b, c] i * ![x, y, z] i ^ 2 = a * x ^ 2 + b * y ^ 2 + c * z ^ 2 := by
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

lemma sum3' {K : Type*} [Field K] (a b c : K) (v : Fin 3 → K) :
    ∑ i, ![a, b, c] i * v i ^ 2 = a * v 0 ^ 2 + b * v 1 ^ 2 + c * v 2 ^ 2 := by
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

lemma cons_ne_zero_of_head {K : Type*} [Field K] {m : ℕ} (y : K) (w : Fin m → K) (hy : y ≠ 0) :
    (Fin.cons y w : Fin (m + 1) → K) ≠ 0 := fun h => hy (by simpa using congrFun h 0)

lemma cons_ne_zero_of_tail {K : Type*} [Field K] {m : ℕ} (y : K) (w : Fin m → K) (hw : w ≠ 0) :
    (Fin.cons y w : Fin (m + 1) → K) ≠ 0 := by
  intro h; apply hw; funext i; simpa using congrFun h i.succ

/-- A nontrivial zero of `g ⊕ h` gives a common nonzero value `c` of `g` and `-h`. -/
theorem common_value {K : Type*} [Field K] (m : ℕ) (hm : 1 ≤ m) (a : Fin (m + 2) → K)
    (ha : ∀ i, a i ≠ 0) (H : Iso K a) :
    ∃ c : K, c ≠ 0 ∧ Iso K ![a 0, a 1, -c] ∧
      Iso K (Fin.cons c (fun i : Fin m => a i.succ.succ) : Fin (m + 1) → K) := by
  obtain ⟨v, hv0, hv⟩ := H
  rw [sum_split] at hv
  by_cases hc : a 0 * v 0 ^ 2 + a 1 * v 1 ^ 2 = 0
  · by_cases hg : v 0 = 0 ∧ v 1 = 0
    · refine ⟨a 0, ha 0, ⟨![1, 0, 1], vec3_ne _ _ _ (Or.inl one_ne_zero), by rw [sum3]; ring⟩,
        ⟨Fin.cons 0 (fun i => v i.succ.succ), cons_ne_zero_of_tail _ _ ?_, ?_⟩⟩
      · intro hw
        apply hv0; funext j
        refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) j
        · exact hg.1
        · simpa [Fin.succ_zero_eq_one] using hg.2
        · simpa using congrFun hw k
      · rw [sum_cons]; linear_combination hv - hc
    · set k : Fin m := ⟨0, hm⟩
      refine ⟨-a k.succ.succ, neg_ne_zero.mpr (ha _), ⟨![v 0, v 1, 0], vec3_ne _ _ _ ?_, ?_⟩,
        ⟨Fin.cons 1 (fun i => if i = k then 1 else 0), cons_ne_zero_of_head _ _ one_ne_zero, ?_⟩⟩
      · by_cases h0 : v 0 = 0
        · exact Or.inr (Or.inl (fun h1 => hg ⟨h0, h1⟩))
        · exact Or.inl h0
      · rw [sum3]; linear_combination hc
      · rw [sum_cons, Finset.sum_eq_single k (fun i _ hi => by simp [hi]) (by simp)]
        simp
  · refine ⟨a 0 * v 0 ^ 2 + a 1 * v 1 ^ 2, hc, ⟨![v 0, v 1, 1], vec3_ne _ _ _ (Or.inr (Or.inr one_ne_zero)),
      by rw [sum3]; ring⟩, ⟨Fin.cons 1 (fun i => v i.succ.succ), cons_ne_zero_of_head _ _ one_ne_zero, ?_⟩⟩
    rw [sum_cons]; linear_combination hv

/-- If `g` represents `x` and `h` represents `-x`, then `g ⊕ h` is isotropic. -/
theorem combine {K : Type*} [Field K] (m : ℕ) (a : Fin (m + 2) → K) (x : K) (hx : x ≠ 0)
    (H1 : Iso K ![a 0, a 1, -x])
    (H2 : Iso K (Fin.cons x (fun i : Fin m => a i.succ.succ) : Fin (m + 1) → K)) : Iso K a := by
  obtain ⟨y, hy0, hy⟩ := H1
  obtain ⟨z, hz0, hz⟩ := H2
  rw [sum3'] at hy
  have hz' := hz
  rw [← Fin.cons_self_tail z, sum_cons] at hz'
  by_cases hy2 : y 2 = 0
  · refine ⟨Fin.cons (y 0) (Fin.cons (y 1) 0), ?_, ?_⟩
    · intro h
      apply hy0; funext j; fin_cases j
      · simpa using congrFun h 0
      · simpa using congrFun h 1
      · simpa using hy2
    · rw [sum_split]; simp only [Fin.cons_zero, Fin.cons_one, Fin.cons_succ, Pi.zero_apply]
      have e0 : ∑ i : Fin m, a i.succ.succ * (0 : K) ^ 2 = 0 := by simp
      rw [e0]; rw [hy2] at hy; linear_combination hy
  · refine ⟨Fin.cons (y 0 * z 0) (Fin.cons (y 1 * z 0) (fun i => y 2 * Fin.tail z i)), ?_, ?_⟩
    · by_cases hz00 : z 0 = 0
      · have htail : Fin.tail z ≠ 0 := by
          intro h; apply hz0; rw [← Fin.cons_self_tail z, h, hz00]; funext j
          refine Fin.cases ?_ (fun j => ?_) j <;> simp
        obtain ⟨i, hi⟩ := Function.ne_iff.mp htail
        intro h
        have := congrFun h i.succ.succ
        simp only [Fin.cons_succ, Pi.zero_apply] at this
        exact mul_ne_zero hy2 hi this
      · have hg : y 0 ≠ 0 ∨ y 1 ≠ 0 := by
          by_contra hcon
          push_neg at hcon
          rw [hcon.1, hcon.2] at hy
          exact mul_ne_zero hx (pow_ne_zero 2 hy2) (by linear_combination -hy)
        intro h
        rcases hg with hg | hg
        · exact mul_ne_zero hg hz00 (by simpa using congrFun h 0)
        · exact mul_ne_zero hg hz00 (by simpa using congrFun h 1)
    · rw [sum_split]; simp only [Fin.cons_zero, Fin.cons_one, Fin.cons_succ]
      have e : ∑ i : Fin m, a i.succ.succ * (y 2 * Fin.tail z i) ^ 2 =
          y 2 ^ 2 * ∑ i : Fin m, a i.succ.succ * Fin.tail z i ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [e]
      linear_combination (z 0) ^ 2 * hy + (y 2) ^ 2 * hz'

/-! ## S5d: constructing `x = ε · ∏ p^(e p) · ℓ` with prescribed classes (CRT + Dirichlet) -/

lemma vp_up_of_eq (p : ℕ) [hp : Fact p.Prime] (x u : ℤ) (e : ℕ) (hx : x = (p : ℤ) ^ e * u)
    (hu : ¬ (p : ℤ) ∣ u) : vp p x = e ∧ up p x = u := by
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero _)
  have hv : vp p x = e := by
    unfold vp
    rw [hx, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast,
      Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) (Int.natAbs_ne_zero.mpr hu0),
      Finsupp.add_apply, hp.out.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (fun h => hu (Int.natCast_dvd.mpr h)), add_zero]
  refine ⟨hv, ?_⟩
  have hd := decomp p x
  rw [hv] at hd
  have hp0 : ((p : ℤ)) ^ e ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  exact mul_left_cancel₀ hp0 (hd.symm.trans hx)

theorem construct_x (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (r : ℕ → ℤ) (hr : ∀ p ∈ S, r p ≠ 0)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ x : ℤ, ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ S ∧ x ≠ 0 ∧ 0 < ε * x ∧ (∀ p ∈ S, cls p x (r p)) ∧
      (∀ q : ℕ, q.Prime → q ∉ S → q ∣ x.natAbs → q = ℓ) := by
  classical
  set e : ℕ → ℕ := fun p => vp p (r p) % 2 with he
  have hεε : ε * ε = 1 := by rcases hε with h | h <;> subst h <;> norm_num
  have hεu : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ ε := by
    intro p hp hd
    have h1 : (p : ℤ) ∣ 1 := by rw [← hεε]; exact dvd_mul_of_dvd_left hd _
    have : p ∣ 1 := by exact_mod_cast h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  set cp : ℕ → ℤ := fun p => ∏ q ∈ S.erase p, (q : ℤ) ^ (e q) with hcpdef
  have hnd_prime : ∀ p ∈ S, ∀ q ∈ S, q ≠ p → ∀ n : ℕ, ¬ (p : ℤ) ∣ (q : ℤ) ^ n := by
    intro p hpS q hqS hne n hd
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (hS p hpS)
    have h1 : (p : ℤ) ∣ q := hpr.dvd_of_dvd_pow hd
    have h2 : p ∣ q := by exact_mod_cast h1
    exact hne ((Nat.prime_dvd_prime_iff_eq (hS p hpS) (hS q hqS)).mp h2).symm
  have hcp : ∀ p ∈ S, ¬ (p : ℤ) ∣ cp p := by
    intro p hpS hd
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (hS p hpS)
    obtain ⟨q, hq, hdq⟩ := (Prime.dvd_finset_prod_iff hpr _).mp hd
    have hq' := Finset.mem_erase.mp hq
    exact hnd_prime p hpS q hq'.2 hq'.1 _ hdq
  have ht : ∀ p ∈ S, ∃ t : ℤ, (p : ℤ) ^ 3 ∣ ε * cp p * t - up p (r p) := by
    intro p hpS
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (hS p hpS)
    have hcop : IsCoprime (ε * cp p) ((p : ℤ) ^ 3) := by
      apply IsCoprime.pow_right
      rw [isCoprime_comm, Prime.coprime_iff_not_dvd hpr]
      intro h
      rcases hpr.dvd_or_dvd h with h | h
      · exact hεu p (hS p hpS) h
      · exact hcp p hpS h
    obtain ⟨u, v, huv⟩ := hcop
    exact ⟨u * up p (r p), ⟨-(v * up p (r p)), by linear_combination (up p (r p)) * huv⟩⟩
  choose! t ht using ht
  have htu : ∀ p ∈ S, ¬ (p : ℤ) ∣ t p := by
    intro p hpS hd
    haveI : Fact p.Prime := ⟨hS p hpS⟩
    apply up_not_dvd p (hr p hpS)
    have h1 : (p : ℤ) ∣ ε * cp p * t p - up p (r p) := dvd_trans (dvd_pow_self _ (by norm_num)) (ht p hpS)
    have h2 : (p : ℤ) ∣ ε * cp p * t p := dvd_mul_of_dvd_right hd _
    have := dvd_sub h2 h1
    simpa using this
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset (fun p => (t p % ((p : ℤ) ^ 3)).toNat) (fun p => p ^ 3) S
    (fun p hp => pow_ne_zero _ (hS p hp).ne_zero)
    (fun p hp q hq hne => Nat.Coprime.pow 3 3 ((Nat.coprime_primes (hS p hp) (hS q hq)).mpr hne))
  have hkt : ∀ p ∈ S, (p : ℤ) ^ 3 ∣ (k : ℤ) - t p := by
    intro p hpS
    have h1 := (Nat.modEq_iff_dvd.mp (hk p hpS))
    have hp3 : (0 : ℤ) < (p : ℤ) ^ 3 := by have := (hS p hpS).pos; positivity
    have h2 : (((t p % ((p : ℤ) ^ 3)).toNat : ℕ) : ℤ) = t p % ((p : ℤ) ^ 3) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ hp3.ne')
    rw [h2] at h1
    push_cast at h1
    have h3 : (p : ℤ) ^ 3 ∣ t p % ((p : ℤ) ^ 3) - t p := by
      rw [Int.emod_def]; exact ⟨-(t p / (p : ℤ) ^ 3), by ring⟩
    have := dvd_sub h3 h1
    rw [show t p % (p : ℤ) ^ 3 - t p - (t p % (p : ℤ) ^ 3 - (k : ℤ)) = (k : ℤ) - t p by ring] at this
    exact this
  set M : ℕ := ∏ p ∈ S, p ^ 3 with hM
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hS p hp).ne_zero)
  have hkM : k.Coprime M := by
    apply Nat.Coprime.prod_right
    intro p hpS
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd (hS p hpS)]
    intro hd
    apply htu p hpS
    have h1 : (p : ℤ) ∣ (k : ℤ) := by exact_mod_cast hd
    have h2 : (p : ℤ) ∣ (k : ℤ) - t p := dvd_trans (dvd_pow_self _ (by norm_num)) (hkt p hpS)
    have := dvd_sub h1 h2
    simpa using this
  obtain ⟨ℓ, hℓgt, hℓ, hℓk⟩ := Nat.forall_exists_prime_gt_and_modEq (S.sup id) hM0 hkM
  have hℓS : ℓ ∉ S := by
    intro h
    have := Finset.le_sup (f := id) h
    simp only [id] at this
    omega
  have hℓt : ∀ p ∈ S, (p : ℤ) ^ 3 ∣ (ℓ : ℤ) - t p := by
    intro p hpS
    have h1 : (M : ℤ) ∣ (k : ℤ) - ℓ := Nat.modEq_iff_dvd.mp hℓk
    have h2 : ((p : ℤ) ^ 3) ∣ (M : ℤ) := by
      rw [hM]; push_cast; exact Finset.dvd_prod_of_mem _ hpS
    have := dvd_sub (hkt p hpS) (dvd_trans h2 h1)
    rw [show (k : ℤ) - t p - ((k : ℤ) - ℓ) = (ℓ : ℤ) - t p by ring] at this
    exact this
  have hℓnd : ∀ p ∈ S, ¬ (p : ℤ) ∣ (ℓ : ℤ) := by
    intro p hpS hd
    have : p ∣ ℓ := by exact_mod_cast hd
    have := (Nat.prime_dvd_prime_iff_eq (hS p hpS) hℓ).mp this
    exact hℓS (this ▸ hpS)
  set C : ℤ := ∏ q ∈ S, (q : ℤ) ^ (e q) with hC
  have hCpos : 0 < C := Finset.prod_pos (fun q hq => pow_pos (by exact_mod_cast (hS q hq).pos) _)
  have hℓpos : (0 : ℤ) < ℓ := by exact_mod_cast hℓ.pos
  have hpos : 0 < ε * (ε * C * ℓ) := by
    rw [show ε * (ε * C * ℓ) = (ε * ε) * C * ℓ by ring, hεε, one_mul]; exact mul_pos hCpos hℓpos
  refine ⟨ε * C * ℓ, ℓ, hℓ, hℓS, ?_, hpos, ?_, ?_⟩
  · intro h; rw [h, mul_zero] at hpos; exact lt_irrefl _ hpos
  · intro p hpS
    haveI : Fact p.Prime := ⟨hS p hpS⟩
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (hS p hpS)
    have hx : ε * C * ℓ = (p : ℤ) ^ (e p) * (ε * cp p * ℓ) := by
      rw [hC, ← Finset.mul_prod_erase S (fun q => (q : ℤ) ^ (e q)) hpS]; ring
    have hu : ¬ (p : ℤ) ∣ ε * cp p * ℓ := by
      intro h
      rcases hpr.dvd_or_dvd h with h | h
      · rcases hpr.dvd_or_dvd h with h | h
        · exact hεu p (hS p hpS) h
        · exact hcp p hpS h
      · exact hℓnd p hpS h
    obtain ⟨hv, hup⟩ := vp_up_of_eq p _ _ _ hx hu
    refine ⟨by rw [hv, he]; simp, ?_⟩
    rw [hup]
    have := dvd_add (ht p hpS) (Dvd.dvd.mul_left (hℓt p hpS) (ε * cp p))
    rw [show ε * cp p * t p - up p (r p) + ε * cp p * ((ℓ : ℤ) - t p) = ε * cp p * ℓ - up p (r p) by ring]
      at this
    exact this
  · intro q hq hqS hd
    have hqr : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
    have hd' : (q : ℤ) ∣ ε * C * ℓ := Int.natCast_dvd.mpr hd
    rcases hqr.dvd_or_dvd hd' with h | h
    · rcases hqr.dvd_or_dvd h with h | h
      · exact absurd h (hεu q hq)
      · exfalso
        obtain ⟨p, hpS, hdp⟩ := (Prime.dvd_finset_prod_iff hqr _).mp h
        have h1 : (q : ℤ) ∣ p := hqr.dvd_of_dvd_pow hdp
        have h2 : q ∣ p := by exact_mod_cast h1
        have := (Nat.prime_dvd_prime_iff_eq hq (hS p hpS)).mp h2
        exact hqS (this ▸ hpS)
    · have : q ∣ ℓ := by exact_mod_cast h
      exact (Nat.prime_dvd_prime_iff_eq hq hℓ).mp this

/-! ## S6: the step `n - 1 → n` for `n ≥ 4` -/

/-- Hasse–Minkowski for diagonal forms with nonzero integer coefficients in `n` variables. -/
def HMz (n : ℕ) : Prop := ∀ A : Fin n → ℤ, (∀ i, A i ≠ 0) →
  Iso ℝ (fun i => (A i : ℝ)) → (∀ (p : ℕ) [Fact p.Prime], Iso ℚ_[p] (fun i => (A i : ℚ_[p]))) →
  Iso ℚ (fun i => (A i : ℚ))

lemma cast_vec3 {K : Type*} [Field K] (a b c : ℤ) :
    (fun i => ((![a, b, c] : Fin 3 → ℤ) i : K)) = ![(a : K), (b : K), (c : K)] := by
  funext i; fin_cases i <;> rfl

lemma cast_cons {K : Type*} [Field K] {m : ℕ} (x : ℤ) (h : Fin m → ℤ) :
    (fun i => ((Fin.cons x h : Fin (m + 1) → ℤ) i : K)) = Fin.cons (x : K) (fun i => (h i : K)) := by
  funext i; refine Fin.cases rfl (fun i => rfl) i

lemma iso_vec3_iff_T {K : Type*} [Field K] [CharZero K] (a b c : ℤ) (hc : c ≠ 0) :
    Iso K (fun i => ((![a, b, -c] : Fin 3 → ℤ) i : K)) ↔ T K ((a * c : ℤ) : K) ((b * c : ℤ) : K) := by
  rw [cast_vec3, Int.cast_neg, iso3_T _ _ _ (by exact_mod_cast hc), Int.cast_mul, Int.cast_mul]

theorem hmz_three : HMz 3 := by
  intro A hA hR hP
  set c := -A 2 with hcdef
  have hc : c ≠ 0 := neg_ne_zero.mpr (hA 2)
  have hA' : A = ![A 0, A 1, -c] := by
    funext i; fin_cases i <;> simp [hcdef]
  rw [hA'] at hR hP ⊢
  rw [iso_vec3_iff_T _ _ _ hc] at hR ⊢
  apply legendre_ternary _ _ (mul_ne_zero (hA 0) hc) (mul_ne_zero (hA 1) hc) hR
  intro p _ _
  exact (iso_vec3_iff_T _ _ _ hc).mp (hP p)

lemma rep_transfer {K : Type*} [Field K] {m : ℕ} (a0 a1 : K) (h : Fin m → K) (c x t : K) (ht : t ≠ 0)
    (hxc : x = c * t ^ 2) (H1 : Iso K ![a0, a1, -c]) (H2 : Iso K (Fin.cons c h : Fin (m + 1) → K)) :
    Iso K ![a0, a1, -x] ∧ Iso K (Fin.cons x h : Fin (m + 1) → K) := by
  constructor
  · refine iso_scale _ _ ![1, 1, 1 / t] (fun i => ?_) (fun i => ?_) H1
    · fin_cases i
      · exact one_ne_zero
      · exact one_ne_zero
      · exact one_div_ne_zero ht
    · fin_cases i
      · show a0 * 1 ^ 2 = a0; ring
      · show a1 * 1 ^ 2 = a1; ring
      · show -x * (1 / t) ^ 2 = -c
        rw [hxc]; field_simp
  · refine iso_scale _ _ (Fin.cons (1 / t) (fun _ => 1)) (fun i => ?_) (fun i => ?_) H2
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact one_div_ne_zero ht
      · exact one_ne_zero
    · refine Fin.cases ?_ (fun j => ?_) i
      · show x * (1 / t) ^ 2 = c
        rw [hxc]; field_simp
      · show h j * 1 ^ 2 = h j; ring

lemma iso_cons3 {K : Type*} [Field K] (x : K) (w : Fin 2 → K) :
    Iso K (Fin.cons x w : Fin 3 → K) ↔ Iso K ![w 0, w 1, x] := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    refine ⟨![v 1, v 2, v 0], ?_, ?_⟩
    · intro h; apply hv0; funext j; fin_cases j
      · simpa using congrFun h 2
      · simpa using congrFun h 0
      · simpa using congrFun h 1
    · rw [sum3]; rw [Fin.sum_univ_three] at hv
      simp only [Fin.cons_zero] at hv
      have e1 : (Fin.cons x w : Fin 3 → K) 1 = w 0 := rfl
      have e2 : (Fin.cons x w : Fin 3 → K) 2 = w 1 := rfl
      rw [e1, e2] at hv; linear_combination hv
  · rintro ⟨v, hv0, hv⟩
    refine ⟨![v 2, v 0, v 1], ?_, ?_⟩
    · intro h; apply hv0; funext j; fin_cases j
      · simpa using congrFun h 1
      · simpa using congrFun h 2
      · simpa using congrFun h 0
    · rw [sum3'] at hv; rw [Fin.sum_univ_three]
      simp only [Fin.cons_zero]
      have e1 : (Fin.cons x w : Fin 3 → K) 1 = w 0 := rfl
      have e2 : (Fin.cons x w : Fin 3 → K) 2 = w 1 := rfl
      rw [e1, e2]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      linear_combination hv

theorem hm_step (m : ℕ) (hm : 2 ≤ m) (H3 : HMz 3) (IH : HMz (m + 1)) : HMz (m + 2) := by
  intro A hA hR hP
  classical
  set h : Fin m → ℤ := fun i => A i.succ.succ with hh
  set S : Finset ℕ := (2 * ∏ i, A i).natAbs.primeFactors with hSdef
  have hprod : (2 * ∏ i, A i) ≠ 0 :=
    mul_ne_zero two_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hA i))
  have hS : ∀ p ∈ S, p.Prime := fun p hp => (Nat.mem_primeFactors.mp hp).1
  have hmemS : ∀ p : ℕ, p.Prime → p ∣ (2 * ∏ i, A i).natAbs → p ∈ S := fun p hp hd =>
    Nat.mem_primeFactors.mpr ⟨hp, hd, Int.natAbs_ne_zero.mpr hprod⟩
  have h2S : 2 ∈ S := hmemS 2 Nat.prime_two (by rw [Int.natAbs_mul]; exact dvd_mul_right _ _)
  have hAdvd : ∀ i, ∀ p : ℕ, p.Prime → p ∣ (A i).natAbs → p ∈ S := fun i p hp hd =>
    hmemS p hp (dvd_trans hd (Int.natAbs_dvd_natAbs.mpr
      (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _)))
  have key : ∀ p ∈ S, ∃ r : ℤ, r ≠ 0 ∧ ∀ [Fact p.Prime],
      Iso ℚ_[p] ![(A 0 : ℚ_[p]), (A 1 : ℚ_[p]), -(r : ℚ_[p])] ∧
      Iso ℚ_[p] (Fin.cons (r : ℚ_[p]) (fun i => (h i : ℚ_[p])) : Fin (m + 1) → ℚ_[p]) := by
    intro p hpS
    haveI : Fact p.Prime := ⟨hS p hpS⟩
    obtain ⟨c, hc0, H1, H2⟩ := common_value m (by omega) (fun i => (A i : ℚ_[p]))
      (fun i => by exact_mod_cast hA i) (hP p)
    obtain ⟨r, hr0, s, hs0, hcs⟩ := padic_int_rep c hc0
    refine ⟨r, hr0, ?_⟩
    intro _
    exact rep_transfer _ _ _ c (r : ℚ_[p]) s hs0 hcs.symm H1 H2
  choose! r hr0 hrI using key
  obtain ⟨cR, hcR0, HR1, HR2⟩ := common_value m (by omega) (fun i => (A i : ℝ))
    (fun i => by exact_mod_cast hA i) hR
  set ε : ℤ := if 0 < cR then 1 else -1 with hεdef
  have hε : ε = 1 ∨ ε = -1 := by by_cases hc : 0 < cR <;> simp [hεdef, hc]
  obtain ⟨x, ℓ, hℓ, hℓS, hx0, hεx, hcls, hxprimes⟩ := construct_x S hS r hr0 ε hε
  have locS : ∀ p ∈ S, ∀ [Fact p.Prime],
      Iso ℚ_[p] ![(A 0 : ℚ_[p]), (A 1 : ℚ_[p]), -(x : ℚ_[p])] ∧
      Iso ℚ_[p] (Fin.cons (x : ℚ_[p]) (fun i => (h i : ℚ_[p])) : Fin (m + 1) → ℚ_[p]) := by
    intro p hpS _
    obtain ⟨t, ht0, hxt⟩ := cls_ratio x (r p) hx0 (hr0 p hpS) (hcls p hpS)
    obtain ⟨H1, H2⟩ := hrI p hpS
    exact rep_transfer _ _ _ _ _ t ht0 hxt H1 H2
  have locR : Iso ℝ ![(A 0 : ℝ), (A 1 : ℝ), -(x : ℝ)] ∧
      Iso ℝ (Fin.cons (x : ℝ) (fun i => (h i : ℝ)) : Fin (m + 1) → ℝ) := by
    have hq : 0 < (x : ℝ) / cR := by
      by_cases hc : 0 < cR
      · have e : ε = 1 := by simp [hεdef, hc]
        rw [e, one_mul] at hεx
        exact div_pos (by exact_mod_cast hεx) hc
      · have e : ε = -1 := by simp [hεdef, hc]
        rw [e] at hεx
        have hc' : cR < 0 := lt_of_le_of_ne (not_lt.mp hc) hcR0
        have hx' : x < 0 := by linarith
        exact div_pos_of_neg_of_neg (by exact_mod_cast hx') hc'
    refine rep_transfer _ _ _ cR (x : ℝ) (Real.sqrt ((x : ℝ) / cR)) (Real.sqrt_ne_zero'.mpr hq) ?_ HR1 HR2
    rw [Real.sq_sqrt hq.le]; field_simp
  have inS : ∀ (a b y : ℤ), (∀ p : ℕ, p.Prime → p ∣ a.natAbs → p ∈ S) →
      (∀ p : ℕ, p.Prime → p ∣ b.natAbs → p ∈ S) → y.natAbs = x.natAbs →
      ∀ p : ℕ, p.Prime → p ≠ ℓ → p ∣ (2 * a * b * y).natAbs → p ∈ S := by
    intro a b y ha hb hy p hp hpl hd
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, hy] at hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
    · rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
      · rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
        · have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by simpa using hd)
          rw [this]; exact h2S
        · exact ha p hp hd
      · exact hb p hp hd
    · by_contra hpS; exact hpl (hxprimes p hp hpS hd)
  have gpart : Iso ℚ ![(A 0 : ℚ), (A 1 : ℚ), -(x : ℚ)] := by
    have hall := tern (A 0) (A 1) x (hA 0) (hA 1) hx0 ℓ locR.1
      (fun p _ hpl hd => (locS p (inS _ _ _ (hAdvd 0) (hAdvd 1) rfl p Fact.out hpl hd)).1)
    have := H3 ![A 0, A 1, -x] (fun i => by fin_cases i <;> simp [hA, hx0])
      (by rw [cast_vec3, Int.cast_neg]; exact locR.1)
      (fun p _ => by rw [cast_vec3, Int.cast_neg]; exact hall p)
    rw [cast_vec3, Int.cast_neg] at this; exact this
  have hloc : ∀ (p : ℕ) [Fact p.Prime],
      Iso ℚ_[p] (Fin.cons (x : ℚ_[p]) (fun i => (h i : ℚ_[p])) : Fin (m + 1) → ℚ_[p]) := by
    rcases (by omega : m = 2 ∨ 3 ≤ m) with hm2 | hm3
    · subst hm2
      have e : ∀ (K : Type) [Field K], -(((-x : ℤ)) : K) = (x : K) := by intro K _; push_cast; ring
      intro p _
      rw [iso_cons3]
      have hall := tern (h 0) (h 1) (-x) (hA _) (hA _) (neg_ne_zero.mpr hx0) ℓ
        (by rw [e]; exact (iso_cons3 _ _).mp locR.2)
        (fun q _ hql hd => by
          rw [e]
          exact (iso_cons3 _ _).mp (locS q (inS _ _ _ (hAdvd _) (hAdvd _) (Int.natAbs_neg x) q Fact.out
            hql hd)).2)
      have := hall p
      rw [e] at this; exact this
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      intro p _
      by_cases hpS : p ∈ S
      · exact (locS p hpS).2
      · have hp2 : p ≠ 2 := fun h2 => hpS (h2 ▸ h2S)
        have hnd : ∀ i, ¬ (p : ℤ) ∣ A i := fun i hd =>
          hpS (hAdvd i p Fact.out (Int.natCast_dvd.mp hd))
        obtain ⟨X, Y, Z, hZ, hXYZ⟩ := ternary_units_isotropic hp2 (h 0) (h 1) (h 2) (hnd _) (hnd _) (hnd _)
        refine ⟨Fin.cons 0 (Fin.cons X (Fin.cons Y (Fin.cons Z 0))), ?_, ?_⟩
        · exact cons_ne_zero_of_tail _ _ (cons_ne_zero_of_tail _ _ (cons_ne_zero_of_tail _ _
            (cons_ne_zero_of_head _ _ hZ)))
        · rw [sum_cons, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, Pi.zero_apply]
          have e0 : ∑ i : Fin k, (h i.succ.succ.succ : ℚ_[p]) * (0 : ℚ_[p]) ^ 2 = 0 := by simp
          rw [e0]
          simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
          linear_combination hXYZ
  have hpart : Iso ℚ (Fin.cons (x : ℚ) (fun i => (h i : ℚ)) : Fin (m + 1) → ℚ) := by
    have := IH (Fin.cons x h)
      (fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp [hx0, hA, hh])
      (by rw [cast_cons]; exact locR.2) (fun p _ => by rw [cast_cons]; exact hloc p)
    rw [cast_cons] at this; exact this
  exact combine m (fun i => (A i : ℚ)) (x : ℚ) (by exact_mod_cast hx0) gpart hpart

theorem hmz_all : ∀ n, 3 ≤ n → HMz n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases (by omega : n = 3 ∨ 4 ≤ n) with rfl | h4
    · exact hmz_three
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      exact hm_step m (by omega) hmz_three (ih (m + 1) (by omega) (by omega))

theorem hmd_of_hmz (n : ℕ) (H : HMz n) (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0)
    (hR : Iso ℝ (fun i => (a i : ℝ))) (hP : ∀ (p : ℕ) [Fact p.Prime], Iso ℚ_[p] (fun i => (a i : ℚ_[p]))) :
    Iso ℚ a := by
  set A : Fin n → ℤ := fun i => (a i).num * (a i).den with hAdef
  have hA : ∀ i, A i ≠ 0 := fun i =>
    mul_ne_zero (Rat.num_ne_zero.mpr (ha i)) (by exact_mod_cast (a i).den_nz)
  have key : ∀ (K : Type) [Field K] [CharZero K], ∀ i,
      ((A i : ℤ) : K) * (1 / ((a i).den : K)) ^ 2 = ((a i : ℚ) : K) := by
    intro K _ _ i
    have hd : ((a i).den : K) ≠ 0 := by exact_mod_cast (a i).den_nz
    rw [Rat.cast_def, hAdef]; push_cast; field_simp
  have tr : ∀ (K : Type) [Field K] [CharZero K], Iso K (fun i => ((a i : ℚ) : K)) →
      Iso K (fun i => ((A i : ℤ) : K)) := by
    intro K _ _ hK
    refine iso_scale _ _ (fun i => 1 / ((a i).den : K)) (fun i => ?_) (key K) hK
    exact one_div_ne_zero (by exact_mod_cast (a i).den_nz)
  have hQ := H A hA (tr ℝ hR) (fun p _ => tr ℚ_[p] (hP p))
  refine iso_scale _ _ (fun i => ((a i).den : ℚ)) (fun i => by exact_mod_cast (a i).den_nz)
    (fun i => ?_) hQ
  show a i * ((a i).den : ℚ) ^ 2 = (((a i).num * (a i).den : ℤ) : ℚ)
  push_cast
  rw [sq, ← mul_assoc, Rat.mul_den_eq_num]


lemma padic_sq_val_even {p : ℕ} [Fact p.Prime] (q : ℚ) (hq : q ≠ 0) (h : IsSquare (q : ℚ_[p])) :
    Even (padicValRat p q) := by
  obtain ⟨y, hy⟩ := h
  have hy0 : y ≠ 0 := by
    rintro rfl; simp at hy; exact hq hy
  rw [← Padic.valuation_ratCast, hy, Padic.valuation_mul hy0 hy0]; exact ⟨_, rfl⟩

lemma nat_isSquare_of_even_val (m : ℕ) (hm : m ≠ 0) (h : ∀ p : ℕ, p.Prime → Even (padicValNat p m)) :
    IsSquare m := by
  obtain ⟨a, b, hab, hsf⟩ := Nat.sq_mul_squarefree m
  by_cases ha1 : a = 1
  · subst ha1; exact ⟨b, by rw [← hab]; ring⟩
  · exfalso
    obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd ha1
    have ha0 : a ≠ 0 := by rintro rfl; simp at hab; exact hm hab.symm
    have hb0 : b ≠ 0 := by rintro rfl; simp at hab; exact hm hab.symm
    haveI : Fact p.Prime := ⟨hp⟩
    have hva : padicValNat p a = 1 := by
      have h1 : 1 ≤ padicValNat p a := one_le_padicValNat_of_dvd ha0 hpa
      have h2 : padicValNat p a < 2 := by
        by_contra hc; push Not at hc
        have h3 : p ^ 2 ∣ a := (padicValNat_dvd_iff_le ha0).mpr hc
        exact hp.ne_one (Nat.isUnit_iff.mp (hsf p (by simpa [pow_two] using h3)))
      omega
    have := h p hp
    rw [← hab, pow_two, padicValNat.mul (mul_ne_zero hb0 hb0) ha0, padicValNat.mul hb0 hb0, hva] at this
    obtain ⟨k, hk⟩ := this; omega

lemma rat_isSquare_of_local (q : ℚ) (hq : 0 < q)
    (h : ∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩; IsSquare (q : ℚ_[p])) :
    IsSquare q := by
  have hq0 : q ≠ 0 := hq.ne'
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq0
  set m := q.num.natAbs * q.den with hm
  have hm0 : m ≠ 0 := mul_ne_zero (Int.natAbs_ne_zero.mpr hnum) q.den_nz
  have hev : ∀ p : ℕ, p.Prime → Even (padicValNat p m) := by
    intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    have e := padic_sq_val_even q hq0 (h p hp)
    have hdef : padicValRat p q = (padicValNat p q.num.natAbs : ℤ) - padicValNat p q.den := rfl
    rw [hm, padicValNat.mul (Int.natAbs_ne_zero.mpr hnum) q.den_nz]
    rw [hdef] at e
    rw [← Int.even_coe_nat, Nat.cast_add]
    have : (padicValNat p q.num.natAbs : ℤ) + padicValNat p q.den
        = ((padicValNat p q.num.natAbs : ℤ) - padicValNat p q.den) + 2 * padicValNat p q.den := by ring
    rw [this]; exact e.add (even_two_mul _)
  obtain ⟨r, hr⟩ := nat_isSquare_of_even_val m hm0 hev
  refine ⟨(r : ℚ) / q.den, ?_⟩
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq
  have e1 : ((q.num.natAbs : ℕ) : ℚ) = q.num := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hnum_pos.le]
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hmr : (m : ℚ) = r * r := by exact_mod_cast hr
  rw [hm, Nat.cast_mul, e1] at hmr
  rw [div_mul_div_comm, ← hmr, eq_div_iff (mul_ne_zero hden hden), ← mul_assoc, Rat.mul_den_eq_num]

lemma binary_iff {K : Type*} [Field K] (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∃ x y : K, (x ≠ 0 ∨ y ≠ 0) ∧ a * x ^ 2 + b * y ^ 2 = 0) ↔ IsSquare (-(a * b)) := by
  constructor
  · rintro ⟨x, y, hxy, h⟩
    have hy : y ≠ 0 := by
      rintro rfl
      rcases hxy with hx | hx
      · simp [ha, hx] at h
      · exact hx rfl
    refine ⟨a * x / y, ?_⟩
    have e : a * x / y * (a * x / y) = a ^ 2 * x ^ 2 / y ^ 2 := by ring
    rw [e, eq_div_iff (pow_ne_zero 2 hy)]
    linear_combination (-a) * h
  · rintro ⟨s, hs⟩
    exact ⟨s, a, Or.inr ha, by linear_combination (-a) * hs⟩

lemma fin2_ne_zero {K : Type*} [Field K] (x : Fin 2 → K) : x ≠ 0 ↔ (x 0 ≠ 0 ∨ x 1 ≠ 0) := by
  constructor
  · intro h; by_contra hc; push Not at hc; apply h; funext i; fin_cases i <;> simp [hc.1, hc.2]
  · rintro (h | h) rfl <;> simp at h

lemma binary_vec_iff {K : Type*} [Field K] (c : Fin 2 → K) (hc : ∀ i, c i ≠ 0) :
    (∃ x : Fin 2 → K, x ≠ 0 ∧ ∑ i, c i * x i ^ 2 = 0) ↔ IsSquare (-(c 0 * c 1)) := by
  rw [← binary_iff (c 0) (c 1) (hc 0) (hc 1)]
  constructor
  · rintro ⟨x, hx0, hx⟩
    exact ⟨x 0, x 1, (fin2_ne_zero x).mp hx0, by simpa [Fin.sum_univ_two] using hx⟩
  · rintro ⟨x, y, hxy, h⟩
    refine ⟨![x, y], (fin2_ne_zero _).mpr (by simpa using hxy), by simpa [Fin.sum_univ_two] using h⟩

/-- Hasse-Minkowski (local => global) for diagonal forms in at most two variables. -/
theorem hm_diag_le_two (n : ℕ) (hn : n ≤ 2) (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0)
    (hR : ∃ x : Fin n → ℝ, x ≠ 0 ∧ ∑ i, (a i : ℝ) * x i ^ 2 = 0)
    (hP : ∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
          ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧ ∑ i, (a i : ℚ_[p]) * x i ^ 2 = 0) :
    ∃ x : Fin n → ℚ, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  obtain ⟨x, hx0, hx⟩ := hR
  interval_cases n
  · exact absurd (Subsingleton.elim x 0) hx0
  · exfalso; apply hx0; funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp only [Fin.sum_univ_one] at hx
    have := ha 0
    simpa [this] using hx
  · have hR2 : IsSquare (-((a 0 : ℝ) * (a 1 : ℝ))) :=
      (binary_vec_iff (fun i => (a i : ℝ)) (fun i => by exact_mod_cast ha i)).mp ⟨x, hx0, hx⟩
    have hpos : 0 < -(a 0 * a 1) := by
      obtain ⟨s, hs⟩ := hR2
      have h0 : (0 : ℝ) ≤ -((a 0 : ℝ) * (a 1 : ℝ)) := by rw [hs]; exact mul_self_nonneg s
      have h1 : -(a 0 * a 1) ≠ 0 := by
        simpa using mul_ne_zero (ha 0) (ha 1)
      have h2 : (0 : ℚ) ≤ -(a 0 * a 1) := by exact_mod_cast h0
      exact lt_of_le_of_ne h2 (Ne.symm h1)
    have hsq : IsSquare (-(a 0 * a 1)) := by
      apply rat_isSquare_of_local _ hpos
      intro p hp
      haveI : Fact p.Prime := ⟨hp⟩
      have := (binary_vec_iff (fun i => (a i : ℚ_[p])) (fun i => by exact_mod_cast ha i)).mp (hP p hp)
      simpa using this
    exact (binary_vec_iff a ha).mpr hsq


/-! ## Assembly -/

theorem hm_diag : ∀ (n : ℕ) (a : Fin n → ℚ), (∀ i, a i ≠ 0) →
    (∃ x : Fin n → ℝ, x ≠ 0 ∧ ∑ i, (a i : ℝ) * x i ^ 2 = 0) →
    (∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
        ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧ ∑ i, (a i : ℚ_[p]) * x i ^ 2 = 0) →
    ∃ x : Fin n → ℚ, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  intro n a ha hR hP
  by_cases hn : n ≤ 2
  · exact hm_diag_le_two n hn a ha hR hP
  · exact hmd_of_hmz n (hmz_all n (by omega)) a ha hR (fun p _ => hP p Fact.out)


open Matrix

lemma qform_eq_dot {K : Type*} [CommRing K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    ∑ i, ∑ j, M i j * x i * x j = x ⬝ᵥ (M *ᵥ x) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

lemma diag_dot {K : Type*} [CommRing K] {n : ℕ} (d : Fin n → K) (y : Fin n → K) :
    y ⬝ᵥ (diagonal d *ᵥ y) = ∑ i, d i * y i ^ 2 := by
  simp only [dotProduct, mulVec_diagonal]; apply Finset.sum_congr rfl; intro i _; ring

lemma dot_congr {K : Type*} [CommRing K] {n : ℕ} (A V : Matrix (Fin n) (Fin n) K) (y : Fin n → K) :
    (V *ᵥ y) ⬝ᵥ (A *ᵥ (V *ᵥ y)) = y ⬝ᵥ ((Vᵀ * A * V) *ᵥ y) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec y Vᵀ, vecMul_transpose]

/-- Diagonalisation of a symmetric rational matrix by congruence. -/
lemma exists_diag (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (hA : A.IsSymm) :
    ∃ V : Matrix (Fin n) (Fin n) ℚ, V.det ≠ 0 ∧ ∃ d : Fin n → ℚ, Vᵀ * A * V = diagonal d := by
  have hB : (Matrix.toBilin' A).IsSymm := by
    rw [LinearMap.BilinForm.isSymm_def]
    intro x y
    simp only [Matrix.toBilin'_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    rw [show A j i = A i j from by
      have := congrFun (congrFun hA i) j; simpa [Matrix.transpose_apply] using this]
    ring
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.mp hB)
  have hn : Module.finrank ℚ (Fin n → ℚ) = n := Module.finrank_fin_fun ℚ
  let w : Module.Basis (Fin n) ℚ (Fin n → ℚ) := v.reindex (finCongr hn)
  refine ⟨(Pi.basisFun ℚ (Fin n)).toMatrix w, ?_, fun i => Matrix.toBilin' A (w i) (w i), ?_⟩
  · intro h0
    have h1 := Module.Basis.toMatrix_mul_toMatrix_flip (Pi.basisFun ℚ (Fin n)) w
    have h2 := congrArg Matrix.det h1
    rw [det_mul, h0, zero_mul, det_one] at h2
    exact zero_ne_one h2
  · ext i j
    have key : ((Pi.basisFun ℚ (Fin n)).toMatrix w)ᵀ * A * (Pi.basisFun ℚ (Fin n)).toMatrix w
        = Matrix.of fun i j => Matrix.toBilin' A (w i) (w j) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr,
        Matrix.toBilin'_apply, Matrix.of_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [key, Matrix.of_apply, diagonal_apply]
    split_ifs with hij
    · rw [hij]
    · have : w i = v ((finCongr hn).symm i) := by simp [w, Module.Basis.reindex_apply]
      have : w j = v ((finCongr hn).symm j) := by simp [w, Module.Basis.reindex_apply]
      simp only [w, Module.Basis.reindex_apply]
      exact hv (fun h => hij ((finCongr hn).symm.injective h))

/-- Transfer of isotropy along a congruence, over any field receiving `ℚ`. -/
lemma iso_transfer {K : Type*} [Field K] (f : ℚ →+* K) {n : ℕ} (A V : Matrix (Fin n) (Fin n) ℚ)
    (hV : V.det ≠ 0) (d : Fin n → ℚ) (hd : Vᵀ * A * V = diagonal d) :
    (∃ x : Fin n → K, x ≠ 0 ∧ x ⬝ᵥ ((A.map f) *ᵥ x) = 0) ↔
      (∃ y : Fin n → K, y ≠ 0 ∧ ∑ i, f (d i) * y i ^ 2 = 0) := by
  have hVK : (V.map f).det ≠ 0 := by
    have h := f.map_det V
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]; exact (map_ne_zero f).mpr hV
  have hdK : (V.map f)ᵀ * A.map f * V.map f = diagonal (fun i => f (d i)) := by
    rw [← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hd, diagonal_map (map_zero f)]
  constructor
  · rintro ⟨x, hx0, hx⟩
    refine ⟨(V.map f)⁻¹ *ᵥ x, ?_, ?_⟩
    · intro h0
      apply hx0
      have : (V.map f) *ᵥ ((V.map f)⁻¹ *ᵥ x) = x := by
        rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hVK), one_mulVec]
      rw [← this, h0, mulVec_zero]
    · have hxe : (V.map f) *ᵥ ((V.map f)⁻¹ *ᵥ x) = x := by
        rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hVK), one_mulVec]
      rw [← diag_dot, ← hdK, ← dot_congr, hxe, hx]
  · rintro ⟨y, hy0, hy⟩
    refine ⟨(V.map f) *ᵥ y, fun h => hy0 (eq_zero_of_mulVec_eq_zero hVK h), ?_⟩
    rw [dot_congr, hdK, diag_dot, hy]


/-- Integer zero from a rational zero (clearing denominators). -/
lemma int_zero_of_rat_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℚ) (hx0 : x ≠ 0)
    (hx : ∑ i, ∑ j, (A i j : ℚ) * x i * x j = 0) :
    ∃ z : Fin n → ℤ, z ≠ 0 ∧ ∑ i, ∑ j, A i j * z i * z j = 0 := by
  set N : ℕ := ∏ j, (x j).den with hN
  have hN0 : (N : ℚ) ≠ 0 := by
    rw [hN]; push_cast; exact Finset.prod_ne_zero_iff.mpr (fun j _ => by exact_mod_cast (x j).den_nz)
  have hz : ∀ i, ∃ z : ℤ, (z : ℚ) = N * x i := by
    intro i
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun j => (x j).den) (Finset.mem_univ i)
    refine ⟨k * (x i).num, ?_⟩
    rw [hN, hk]; push_cast
    rw [← Rat.mul_den_eq_num (x i)]; ring
  choose z hzq using hz
  refine ⟨z, ?_, ?_⟩
  · intro h0; apply hx0; funext i
    have := hzq i; rw [h0] at this; simp at this
    rcases this with h | h
    · exact absurd (by exact_mod_cast h) hN0
    · simpa using h
  · have : ((∑ i, ∑ j, A i j * z i * z j : ℤ) : ℚ) = (N : ℚ) ^ 2 * ∑ i, ∑ j, (A i j : ℚ) * x i * x j := by
      push_cast; simp only [hzq, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
    rw [hx, mul_zero] at this; exact_mod_cast this

lemma cast_ne_zero_vec {K : Type*} [Field K] [CharZero K] {n : ℕ} (x : Fin n → ℤ) (hx : x ≠ 0) :
    (fun i => (x i : K)) ≠ 0 := by
  intro h; apply hx; funext i; have := congrFun h i; simpa using this

/-- The parent statement from the diagonal local-global principle. -/
theorem parent_of_diag
    (H : ∀ (n : ℕ) (a : Fin n → ℚ), (∀ i, a i ≠ 0) →
      (∃ x : Fin n → ℝ, x ≠ 0 ∧ ∑ i, (a i : ℝ) * x i ^ 2 = 0) →
      (∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
          ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧ ∑ i, (a i : ℚ_[p]) * x i ^ 2 = 0) →
      ∃ x : Fin n → ℚ, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hsymm : A.IsSymm) (hdet : A.det ≠ 0) :
    (∃ x : Fin n → ℤ, x ≠ 0 ∧ ∑ i, ∑ j, A i j * x i * x j = 0) ↔
      ((∃ x : Fin n → ℝ, x ≠ 0 ∧ ∑ i, ∑ j, (A i j : ℝ) * x i * x j = 0) ∧
        ∀ (p : ℕ) (hp : p.Prime),
          letI : Fact p.Prime := ⟨hp⟩
          ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧ ∑ i, ∑ j, (A i j : ℚ_[p]) * x i * x j = 0) := by
  constructor
  · rintro ⟨x, hx0, hx⟩
    refine ⟨⟨fun i => (x i : ℝ), cast_ne_zero_vec x hx0, ?_⟩, fun p hp => ?_⟩
    · have h := congrArg (fun t : ℤ => (t : ℝ)) hx
      push_cast at h; simpa using h
    · haveI : Fact p.Prime := ⟨hp⟩
      have h := congrArg (fun t : ℤ => (t : ℚ_[p])) hx
      push_cast at h
      exact ⟨fun i => (x i : ℚ_[p]), cast_ne_zero_vec x hx0, by simpa using h⟩
  · rintro ⟨hR, hP⟩
    set Aq : Matrix (Fin n) (Fin n) ℚ := A.map (Int.cast) with hAq
    have hAqs : Aq.IsSymm := by
      rw [hAq, Matrix.IsSymm, ← Matrix.transpose_map, hsymm.eq]
    obtain ⟨V, hV, d, hd⟩ := exists_diag n Aq hAqs
    have hd0 : ∀ i, d i ≠ 0 := by
      have h1 := congrArg Matrix.det hd
      rw [det_mul, det_mul, det_transpose, det_diagonal] at h1
      have hAq0 : Aq.det ≠ 0 := by
        rw [hAq]
        have h := (Int.castRingHom ℚ).map_det A
        rw [RingHom.mapMatrix_apply] at h
        rw [show A.map (Int.cast : ℤ → ℚ) = A.map (Int.castRingHom ℚ) from rfl, ← h]
        simpa using hdet
      have hp0 : ∏ i, d i ≠ 0 := by
        rw [← h1]; exact mul_ne_zero (mul_ne_zero hV hAq0) hV
      intro i; exact Finset.prod_ne_zero_iff.mp hp0 i (Finset.mem_univ i)
    have hmap : ∀ {K : Type} [Field K] [CharZero K],
        (Aq.map (Rat.castHom K)) = A.map (Int.cast : ℤ → K) := by
      intro K _ _; ext i j; simp [hAq]
    have key : ∀ {K : Type} [Field K] [CharZero K],
        (∃ x : Fin n → K, x ≠ 0 ∧ ∑ i, ∑ j, (A i j : K) * x i * x j = 0) ↔
          (∃ y : Fin n → K, y ≠ 0 ∧ ∑ i, (d i : K) * y i ^ 2 = 0) := by
      intro K _ _
      have := iso_transfer (Rat.castHom K) Aq V hV d hd
      simp only [eq_ratCast, hmap] at this
      have e : ∀ x : Fin n → K, ∑ i, ∑ j, (A i j : K) * x i * x j
          = x ⬝ᵥ ((A.map (Int.cast : ℤ → K)) *ᵥ x) := by
        intro x; rw [← qform_eq_dot]; rfl
      simp only [e]; exact this
    obtain ⟨y, hy0, hy⟩ := H n d hd0 (key.mp hR) (fun p hp => by
      letI : Fact p.Prime := ⟨hp⟩
      exact key.mp (hP p hp))
    have hq : ∃ x : Fin n → ℚ, x ≠ 0 ∧ ∑ i, ∑ j, (A i j : ℚ) * x i * x j = 0 := by
      apply key.mpr
      exact ⟨y, hy0, by simpa using hy⟩
    obtain ⟨x, hx0, hx⟩ := hq
    exact int_zero_of_rat_zero A x hx0 hx

end HMlib

theorem solution
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hsymm : A.IsSymm) (hdet : A.det ≠ 0) :
    (∃ x : Fin n → ℤ, x ≠ 0 ∧ ∑ i, ∑ j, A i j * x i * x j = 0) ↔
      ((∃ x : Fin n → ℝ, x ≠ 0 ∧ ∑ i, ∑ j, (A i j : ℝ) * x i * x j = 0) ∧
        ∀ (p : ℕ) (hp : p.Prime),
          letI : Fact p.Prime := ⟨hp⟩
          ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧ ∑ i, ∑ j, (A i j : ℚ_[p]) * x i * x j = 0) := by
  exact HMlib.parent_of_diag HMlib.hm_diag n A hsymm hdet
