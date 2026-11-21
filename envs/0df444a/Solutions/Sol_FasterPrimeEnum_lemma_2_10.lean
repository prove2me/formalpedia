-- Prove2me | solution 1 for FasterPrimeEnum.lemma_2_10
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-20T15:09:42.830428+00:00
-- url     : https://prove2.me/submissions/896bc4c2-ece9-4dfc-b9b0-097817106bbd

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace FasterPrimeEnum

open Zsqrtd Module

noncomputable section

/-- The `ℤ`-basis `{1, √d}` of `ℤ√d`. -/
def zbasis (d : ℤ) : Basis (Fin 2) ℤ (ℤ√d) :=
  Basis.ofEquivFun
    { toFun := fun x => ![x.re, x.im]
      invFun := fun f => ⟨f 0, f 1⟩
      left_inv := by intro x; ext <;> simp
      right_inv := by intro f; ext i; fin_cases i <;> simp
      map_add' := by intro x y; ext i; fin_cases i <;> simp
      map_smul' := by intro a x; ext i; fin_cases i <;> simp }

@[simp] lemma zbasis_repr_apply (d : ℤ) (x : ℤ√d) (i : Fin 2) :
    (zbasis d).repr x i = ![x.re, x.im] i := by
  simp [zbasis]

lemma zbasis_zero (d : ℤ) : zbasis d 0 = (1 : ℤ√d) := by
  simp [zbasis, Basis.coe_ofEquivFun, Zsqrtd.ext_iff]

lemma zbasis_one (d : ℤ) : zbasis d 1 = (Zsqrtd.sqrtd : ℤ√d) := by
  simp [zbasis, Basis.coe_ofEquivFun, Zsqrtd.ext_iff]

lemma det_zbasis_mul (d : ℤ) (θ : ℤ√d) :
    (zbasis d).det (fun i => θ * zbasis d i) = Zsqrtd.norm θ := by
  rw [Basis.det_apply]
  have hmat : (zbasis d).toMatrix (fun i => θ * zbasis d i)
      = !![θ.re, d * θ.im; θ.im, θ.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Basis.toMatrix_apply, zbasis_repr_apply, zbasis_zero, zbasis_one]
  rw [hmat, Matrix.det_fin_two]
  simp [Zsqrtd.norm]

/-- The cardinality of `ℤ√d ⧸ (θ)` equals `|norm θ|`, for `θ ≠ 0`. -/
lemma natCard_quot_span (d : ℤ) [IsDomain (ℤ√d)] (θ : ℤ√d) (hθ : θ ≠ 0) :
    Nat.card (ℤ√d ⧸ Ideal.span {θ}) = (Zsqrtd.norm θ).natAbs := by
  have h := AddSubgroup.index_eq_natAbs_det (zbasis d) (Ideal.span {θ}).toAddSubgroup
    (Ideal.basisSpanSingleton (zbasis d) hθ)
  have hcard : Nat.card (ℤ√d ⧸ Ideal.span {θ}) = (Ideal.span {θ}).toAddSubgroup.index := rfl
  rw [hcard, h]
  congr 1
  change (zbasis d).det (fun i => θ * zbasis d i) = Zsqrtd.norm θ
  exact det_zbasis_mul d θ

/-! ## The Gaussian integers `ℤ[i] = ℤ√(-1)` -/

instance instNoZeroDivisorsGaussianInt : NoZeroDivisors (ℤ√(-1)) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b hab
    have h : Zsqrtd.norm (a * b) = 0 := by rw [hab]; exact Zsqrtd.norm_zero
    rw [Zsqrtd.norm_mul] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact Or.inl ((Zsqrtd.norm_eq_zero_iff (d := -1) (by norm_num) a).mp h')
    · exact Or.inr ((Zsqrtd.norm_eq_zero_iff (d := -1) (by norm_num) b).mp h')

instance instIsDomainGaussianInt : IsDomain (ℤ√(-1)) := NoZeroDivisors.to_isDomain _

lemma zmod2_sq (x : ZMod 2) : x ^ 2 = x := by
  have h : x = 0 ∨ x = 1 := by revert x; decide
  rcases h with rfl | rfl <;> decide

lemma zmod2_nat_odd (n : ℕ) (hn : n % 2 = 1) : (n : ZMod 2) = 1 := by
  have h : (n : ZMod 2) = ((1 : ℕ) : ZMod 2) := by
    rw [ZMod.natCast_eq_natCast_iff']
    simpa using hn
  simpa using h

/-- Parity split for `a ^ 2 + c ^ 2 = n` with `n` odd. -/
lemma parity_of_sq_add_sq {a c n : ℤ} (h : a ^ 2 + c ^ 2 = n) (hn : (n : ZMod 2) = 1) :
    (Odd a ∧ Even c) ∨ (Even a ∧ Odd c) := by
  have h' : ((a ^ 2 + c ^ 2 : ℤ) : ZMod 2) = (n : ZMod 2) := by rw [h]
  push_cast at h'
  rw [hn] at h'
  rw [zmod2_sq, zmod2_sq] at h'
  rcases Int.even_or_odd a with ha | ha <;> rcases Int.even_or_odd c with hc | hc
  · rw [ZMod.intCast_eq_zero_iff_even.mpr ha, ZMod.intCast_eq_zero_iff_even.mpr hc] at h'
    exact absurd h' (by decide)
  · exact Or.inr ⟨ha, hc⟩
  · exact Or.inl ⟨ha, hc⟩
  · rw [ZMod.intCast_eq_one_iff_odd.mpr ha, ZMod.intCast_eq_one_iff_odd.mpr hc] at h'
    exact absurd h' (by decide)

/-- If `a ^ 2 + 4 * b ^ 2 = n` with `n` odd then `a` is odd. -/
lemma odd_of_sq_add_four_sq {a b n : ℤ} (h : a ^ 2 + 4 * b ^ 2 = n) (hn : (n : ZMod 2) = 1) :
    Odd a := by
  have h' : ((a ^ 2 + 4 * b ^ 2 : ℤ) : ZMod 2) = (n : ZMod 2) := by rw [h]
  push_cast at h'
  rw [hn] at h'
  have h4 : (4 : ZMod 2) = 0 := by decide
  rw [h4, zero_mul, add_zero, zmod2_sq] at h'
  exact ZMod.intCast_eq_one_iff_odd.mp h'

lemma norm_mk_two (a b : ℤ) : (⟨a, 2 * b⟩ : ℤ√(-1)).norm = a ^ 2 + 4 * b ^ 2 := by
  rw [Zsqrtd.norm_def]
  simp only [Zsqrtd.re, Zsqrtd.im]
  ring

lemma isUnit_I : IsUnit (⟨0, 1⟩ : ℤ√(-1)) := by
  rw [← Zsqrtd.norm_eq_one_iff' (d := -1) (by norm_num)]
  simp [Zsqrtd.norm]

/-- The only elements of `ℤ[i]` of norm `1`. -/
lemma unit_cases (u : ℤ√(-1)) (hu : Zsqrtd.norm u = 1) :
    u = 1 ∨ u = -1 ∨ u = ⟨0, 1⟩ ∨ u = ⟨0, -1⟩ := by
  have h : u.re ^ 2 + u.im ^ 2 = 1 := by
    have hh := hu
    rw [Zsqrtd.norm_def] at hh
    nlinarith
  have hr : u.re = -1 ∨ u.re = 0 ∨ u.re = 1 := by
    have h1 : -1 ≤ u.re := by nlinarith [sq_nonneg u.im]
    have h2 : u.re ≤ 1 := by nlinarith [sq_nonneg u.im]
    omega
  have hi : u.im = -1 ∨ u.im = 0 ∨ u.im = 1 := by
    have h1 : -1 ≤ u.im := by nlinarith [sq_nonneg u.re]
    have h2 : u.im ≤ 1 := by nlinarith [sq_nonneg u.re]
    omega
  have hu_eq : u = ⟨u.re, u.im⟩ := by cases u; rfl
  rcases hr with h1 | h1 | h1 <;> rcases hi with h2 | h2 | h2 <;>
    rw [hu_eq, h1, h2] at h ⊢
  all_goals
    first
      | decide
      | (exfalso; norm_num at h)

end

end FasterPrimeEnum

open FasterPrimeEnum Zsqrtd Module

theorem solution (n : ℕ) (hn : n % 2 = 1) :
    Set.BijOn (fun ab : ℤ × ℤ => Ideal.span {(⟨ab.1, 2 * ab.2⟩ : ℤ√(-1))})
      {ab : ℤ × ℤ | ab.1 ^ 2 + 4 * ab.2 ^ 2 = (n : ℤ) ∧ 1 ≤ ab.1}
      {I : Ideal (ℤ√(-1)) | Nat.card (ℤ√(-1) ⧸ I) = n} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, b⟩ ⟨h1, h2⟩
    simp only at h1 h2
    have hne : (⟨a, 2 * b⟩ : ℤ√(-1)) ≠ 0 := by
      intro h
      have ha : a = 0 := by simpa using congrArg Zsqrtd.re h
      omega
    have hnorm : (⟨a, 2 * b⟩ : ℤ√(-1)).norm = (n : ℤ) := by
      rw [norm_mk_two]
      exact h1
    have hstep : Nat.card (ℤ√(-1) ⧸ Ideal.span {(⟨a, 2 * b⟩ : ℤ√(-1))}) =
        (Zsqrtd.norm (⟨a, 2 * b⟩ : ℤ√(-1))).natAbs := natCard_quot_span (-1) _ hne
    change Nat.card (ℤ√(-1) ⧸ Ideal.span {(⟨a, 2 * b⟩ : ℤ√(-1))}) = n
    rw [hstep, hnorm, Int.natAbs_natCast]
  · rintro ⟨a, b⟩ ⟨h1, h2⟩ ⟨a', b'⟩ ⟨h1', h2'⟩ heq
    simp only at h1 h2 h1' h2'
    have heq' : Ideal.span {(⟨a, 2 * b⟩ : ℤ√(-1))} = Ideal.span {(⟨a', 2 * b'⟩ : ℤ√(-1))} := heq
    have hn1 : (⟨a, 2 * b⟩ : ℤ√(-1)).norm = (n : ℤ) := by rw [norm_mk_two]; exact h1
    have hn1' : (⟨a', 2 * b'⟩ : ℤ√(-1)).norm = (n : ℤ) := by rw [norm_mk_two]; exact h1'
    have hne : (⟨a, 2 * b⟩ : ℤ√(-1)) ≠ 0 := by
      intro h
      have ha : a = 0 := by simpa using congrArg Zsqrtd.re h
      omega
    have hne' : (⟨a', 2 * b'⟩ : ℤ√(-1)) ≠ 0 := by
      intro h
      have ha : a' = 0 := by simpa using congrArg Zsqrtd.re h
      omega
    have hassoc : Associated (⟨a, 2 * b⟩ : ℤ√(-1)) (⟨a', 2 * b'⟩ : ℤ√(-1)) :=
      Ideal.span_singleton_eq_span_singleton.mp heq'
    obtain ⟨u, hu⟩ := hassoc
    have hnu : Zsqrtd.norm (u : ℤ√(-1)) = 1 := by
      have h := congrArg Zsqrtd.norm hu
      rw [Zsqrtd.norm_mul, hn1, hn1'] at h
      have hnz : (n : ℤ) ≠ 0 := by omega
      have h2' : (n : ℤ) * Zsqrtd.norm (u : ℤ√(-1)) = (n : ℤ) * 1 := by simpa using h
      simpa using mul_left_cancel₀ hnz h2'
    rcases unit_cases (u : ℤ√(-1)) hnu with hu1 | hu1 | hu1 | hu1
    · rw [hu1] at hu
      simp only [mul_one, Zsqrtd.ext_iff, Zsqrtd.re, Zsqrtd.im] at hu
      obtain ⟨hre, him⟩ := hu
      have hbb : b = b' := by omega
      subst hre
      subst hbb
      rfl
    · rw [hu1] at hu
      simp only [Zsqrtd.ext_iff, Zsqrtd.re, Zsqrtd.im, Zsqrtd.re_mul, Zsqrtd.im_mul,
        Zsqrtd.re_neg, Zsqrtd.im_neg, Zsqrtd.re_one, Zsqrtd.im_one, mul_neg, mul_one,
        add_zero, zero_mul, neg_mul] at hu
      obtain ⟨hre, him⟩ := hu
      omega
    · rw [hu1] at hu
      simp only [Zsqrtd.ext_iff, Zsqrtd.re, Zsqrtd.im, Zsqrtd.re_mul, Zsqrtd.im_mul,
        Zsqrtd.re_one, Zsqrtd.im_one, mul_zero, mul_one, add_zero, zero_add, neg_mul] at hu
      obtain ⟨hre, him⟩ := hu
      have ha2 : a = 2 * b' := by omega
      have hdvd : (2 : ℤ) ∣ (n : ℤ) := by
        refine ⟨2 * (b' ^ 2 + b ^ 2), ?_⟩
        nlinarith [h1, ha2]
      have hnz : (n : ZMod 2) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (n : ℤ) 2).mpr hdvd
      have hn2 : (n : ZMod 2) = 1 := zmod2_nat_odd n hn
      omega
    · rw [hu1] at hu
      simp only [Zsqrtd.ext_iff, Zsqrtd.re, Zsqrtd.im, Zsqrtd.re_mul, Zsqrtd.im_mul,
        Zsqrtd.re_one, Zsqrtd.im_one, mul_zero, mul_one, add_zero, zero_add, neg_mul] at hu
      obtain ⟨hre, him⟩ := hu
      have ha2 : a = -2 * b' := by omega
      have hdvd : (2 : ℤ) ∣ (n : ℤ) := by
        refine ⟨2 * (b' ^ 2 + b ^ 2), ?_⟩
        nlinarith [h1, ha2]
      have hnz : (n : ZMod 2) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (n : ℤ) 2).mpr hdvd
      have hn2 : (n : ZMod 2) = 1 := zmod2_nat_odd n hn
      omega
  · intro I hI
    let θ : ℤ√(-1) := Submodule.IsPrincipal.generator I
    have hspan : Ideal.span {θ} = I := Ideal.span_singleton_generator I
    have hcard : Nat.card (ℤ√(-1) ⧸ Ideal.span {θ}) = n := by rw [hspan]; exact hI
    have hθne : θ ≠ 0 := by
      intro h0
      have h2 : Nat.card (ℤ√(-1) ⧸ Ideal.span {(0 : ℤ√(-1))}) = n := by
        rw [← h0]; exact hcard
      rw [Set.singleton_zero, Ideal.span_zero] at h2
      have h3 : Nat.card (ℤ√(-1) ⧸ (⊥ : Ideal (ℤ√(-1)))) = 0 := by
        rw [← Submodule.cardQuot_apply]
        exact Submodule.cardQuot_bot ℤ (ℤ√(-1))
      rw [h3] at h2
      omega
    have hnormabs : (Zsqrtd.norm θ).natAbs = n := by
      rw [← natCard_quot_span (-1) θ hθne]
      exact hcard
    have hnorm : Zsqrtd.norm θ = (n : ℤ) := by
      have hnn : 0 ≤ Zsqrtd.norm θ := Zsqrtd.norm_nonneg (d := -1) (by norm_num) θ
      have hcast : ((Zsqrtd.norm θ).natAbs : ℤ) = Zsqrtd.norm θ := Int.natAbs_of_nonneg hnn
      rw [hnormabs] at hcast
      exact hcast.symm
    set a := θ.re with ha
    set c := θ.im with hc
    have hθ_eq : θ = ⟨a, c⟩ := by ext <;> simp [ha, hc]
    have hsq : a ^ 2 + c ^ 2 = (n : ℤ) := by
      have hh := hnorm
      rw [hθ_eq, Zsqrtd.norm_def] at hh
      nlinarith
    have hn2 : (n : ZMod 2) = 1 := zmod2_nat_odd n hn
    rcases parity_of_sq_add_sq hsq hn2 with ⟨haodd, hceven⟩ | ⟨haeven, hcodd⟩
    · obtain ⟨b, hb⟩ := even_iff_two_dvd.mp hceven
      rw [hb] at hsq
      have han0 : a ≠ 0 := by
        obtain ⟨k, hk⟩ := haodd
        omega
      rcases lt_or_gt_of_ne han0 with ha_neg | ha_pos
      · refine ⟨(-a, -b), ⟨?_, ?_⟩, ?_⟩
        · nlinarith [hsq]
        · omega
        · change Ideal.span {(⟨-a, 2 * -b⟩ : ℤ√(-1))} = I
          have h1 : (⟨-a, 2 * -b⟩ : ℤ√(-1)) = -θ := by
            rw [hθ_eq, hb]
            ext <;> simp
          rw [h1, Ideal.span_singleton_neg, hspan]
      · refine ⟨(a, b), ⟨?_, ?_⟩, ?_⟩
        · nlinarith [hsq]
        · omega
        · change Ideal.span {(⟨a, 2 * b⟩ : ℤ√(-1))} = I
          have h1 : (⟨a, 2 * b⟩ : ℤ√(-1)) = θ := by
            rw [hθ_eq, hb]
          rw [h1, hspan]
    · obtain ⟨b, hb⟩ := even_iff_two_dvd.mp haeven
      rw [hb] at hsq
      have hcn0 : c ≠ 0 := by
        obtain ⟨k, hk⟩ := hcodd
        omega
      rcases lt_or_gt_of_ne hcn0 with hc_neg | hc_pos
      · refine ⟨(-c, b), ⟨?_, ?_⟩, ?_⟩
        · nlinarith [hsq]
        · omega
        · change Ideal.span {(⟨-c, 2 * b⟩ : ℤ√(-1))} = I
          have h1 : (⟨-c, 2 * b⟩ : ℤ√(-1)) = (⟨0, 1⟩ : ℤ√(-1)) * θ := by
            rw [hθ_eq, hb]
            ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
          rw [h1, Ideal.span_singleton_mul_left_unit isUnit_I, hspan]
      · refine ⟨(c, -b), ⟨?_, ?_⟩, ?_⟩
        · nlinarith [hsq]
        · omega
        · change Ideal.span {(⟨c, 2 * -b⟩ : ℤ√(-1))} = I
          have h1 : (⟨c, 2 * -b⟩ : ℤ√(-1)) = -(⟨0, 1⟩ : ℤ√(-1)) * θ := by
            rw [hθ_eq, hb]
            ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
          rw [h1, Ideal.span_singleton_mul_left_unit isUnit_I.neg, hspan]
