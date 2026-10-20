-- Prove2me | solution 1 for DerivativeChainPrivate.compressedRealDefectRadius
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-19T08:38:09.544765+00:00
-- url     : https://prove2.me/submissions/522cdc2d-bdcb-422f-b110-3a67259e7f1d

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial

theorem real_splits_derivative (p : Polynomial ℝ) (hp : p.Splits) :
    p.derivative.Splits := by
  apply Polynomial.splits_iff_card_roots.mpr
  have hcount := p.card_roots_le_derivative
  have hdegree := Polynomial.natDegree_derivative p
  have hbound := Polynomial.card_roots' p.derivative
  have hsplit := hp.natDegree_eq_card_roots
  omega

theorem weighted_derivative_factor (q : Polynomial ℝ) (r k : ℕ) :
    (X ^ (r + 1) * q ^ (k + 1)).derivative =
      X ^ r * q ^ k * (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative) := by
  simp only [derivative_mul, derivative_pow, derivative_X, mul_one,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [pow_succ q k, pow_succ X r]
  ring

theorem real_splits_weighted_derivative (q : Polynomial ℝ) (hq : q.Splits)
    (r k : ℕ) :
    (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative).Splits := by
  by_cases hqzero : q = 0
  · simp [hqzero, Polynomial.Splits.zero]
  let b : Polynomial ℝ := C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative
  by_cases hb : b = 0
  · simpa only [b, hb] using (Polynomial.Splits.zero : (0 : Polynomial ℝ).Splits)
  have hs := real_splits_derivative (X ^ (r + 1) * q ^ (k + 1))
    ((Polynomial.Splits.X_pow (r + 1)).mul (hq.pow (k + 1)))
  rw [weighted_derivative_factor] at hs
  have hne : X ^ r * q ^ k * b ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hqzero)) hb
  exact hs.of_dvd hne ⟨X ^ r * q ^ k, by ring⟩

theorem weighted_positive_parent (q : Polynomial ℝ) (hq : q ≠ 0) (hs : q.Splits)
    (r k : ℕ) (y : ℝ) (hy : 0 < y)
    (hz : (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative).eval y = 0) :
    ∃ x ∈ q.roots, y ≤ x := by
  classical
  by_contra h
  push Not at h
  have hqy : q.eval y ≠ 0 := by
    intro heq
    have hm := (Polynomial.mem_roots hq).mpr heq
    exact (not_lt_of_ge (le_refl y)) (h y hm)
  let s := (q.roots.map fun x => 1 / (y - x)).sum
  have hsnonneg : 0 ≤ s := by
    apply Multiset.sum_nonneg
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp ha
    exact le_of_lt (one_div_pos.mpr (sub_pos.mpr (h x hx)))
  have hd : q.derivative.eval y = q.eval y * s := hs.eval_derivative_eq_eval_mul_sum hqy
  simp only [eval_add, eval_mul, eval_C, eval_X] at hz
  rw [hd] at hz
  have heq : q.eval y * ((r + 1 : ℝ) + (k + 1 : ℝ) * y * s) = 0 := by
    nlinarith [hz]
  have hb := (mul_eq_zero.mp heq).resolve_left hqy
  have hprod : 0 ≤ (k + 1 : ℝ) * y * s :=
    mul_nonneg (mul_nonneg (by positivity) hy.le) hsnonneg
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  nlinarith

theorem weighted_negative_parent (q : Polynomial ℝ) (hq : q ≠ 0) (hs : q.Splits)
    (r k : ℕ) (y : ℝ) (hy : y < 0)
    (hz : (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative).eval y = 0) :
    ∃ x ∈ q.roots, x ≤ y := by
  classical
  by_contra h
  push Not at h
  have hqy : q.eval y ≠ 0 := by
    intro heq
    have hm := (Polynomial.mem_roots hq).mpr heq
    exact (not_lt_of_ge (le_refl y)) (h y hm)
  let s := (q.roots.map fun x => 1 / (y - x)).sum
  have hsnonpos : s ≤ 0 := by
    have hneg : 0 ≤ (q.roots.map fun x => -(1 / (y - x))).sum := by
      apply Multiset.sum_nonneg
      intro a ha
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp ha
      exact neg_nonneg.mpr (le_of_lt (one_div_neg.mpr (sub_neg.mpr (h x hx))))
    have heq : (q.roots.map fun x => -(1 / (y - x))).sum = -s := by
      simp [s, Multiset.sum_map_neg]
    linarith
  have hd : q.derivative.eval y = q.eval y * s := hs.eval_derivative_eq_eval_mul_sum hqy
  simp only [eval_add, eval_mul, eval_C, eval_X] at hz
  rw [hd] at hz
  have heq : q.eval y * ((r + 1 : ℝ) + (k + 1 : ℝ) * y * s) = 0 := by
    nlinarith [hz]
  have hb := (mul_eq_zero.mp heq).resolve_left hqy
  have hprod : 0 ≤ (k + 1 : ℝ) * y * s :=
    mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) hy.le)
      hsnonpos
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  nlinarith

theorem derivative_positive_parent (q : Polynomial ℝ) (hq : q ≠ 0) (hs : q.Splits)
    (hdeg : 0 < q.natDegree) (y : ℝ) (hz : q.derivative.eval y = 0) :
    ∃ x ∈ q.roots, y ≤ x := by
  classical
  by_contra h
  push Not at h
  have hqy : q.eval y ≠ 0 := by
    intro heq
    exact (lt_irrefl y) (h y ((Polynomial.mem_roots hq).mpr heq))
  let s := (q.roots.map fun x => 1 / (y - x)).sum
  have hterms : ∀ a ∈ (q.roots.map fun x => 1 / (y - x)), 0 ≤ a := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp ha
    exact (one_div_pos.mpr (sub_pos.mpr (h x hx))).le
  have hnonempty : q.roots ≠ 0 := by
    intro heq
    have hc := hs.natDegree_eq_card_roots
    simp only [heq, Multiset.card_zero] at hc
    omega
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hnonempty
  have hle : 1 / (y - x) ≤ s :=
    Multiset.single_le_sum hterms _ (Multiset.mem_map.mpr ⟨x, hx, rfl⟩)
  have hd := hs.eval_derivative_eq_eval_mul_sum hqy
  rw [hz] at hd
  have hs0 : s = 0 := (mul_eq_zero.mp hd.symm).resolve_left hqy
  have hpos := one_div_pos.mpr (sub_pos.mpr (h x hx))
  linarith

theorem derivative_negative_parent (q : Polynomial ℝ) (hq : q ≠ 0) (hs : q.Splits)
    (hdeg : 0 < q.natDegree) (y : ℝ) (hz : q.derivative.eval y = 0) :
    ∃ x ∈ q.roots, x ≤ y := by
  classical
  by_contra h
  push Not at h
  have hqy : q.eval y ≠ 0 := by
    intro heq
    exact (lt_irrefl y) (h y ((Polynomial.mem_roots hq).mpr heq))
  let s := (q.roots.map fun x => -(1 / (y - x))).sum
  have hterms : ∀ a ∈ (q.roots.map fun x => -(1 / (y - x))), 0 ≤ a := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp ha
    exact neg_nonneg.mpr (one_div_neg.mpr (sub_neg.mpr (h x hx))).le
  have hnonempty : q.roots ≠ 0 := by
    intro heq
    have hc := hs.natDegree_eq_card_roots
    simp only [heq, Multiset.card_zero] at hc
    omega
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hnonempty
  have hle : -(1 / (y - x)) ≤ s :=
    Multiset.single_le_sum hterms _ (Multiset.mem_map.mpr ⟨x, hx, rfl⟩)
  have hd := hs.eval_derivative_eq_eval_mul_sum hqy
  rw [hz] at hd
  have hs0 : s = 0 := by
    have heq : (q.roots.map fun x => -(1 / (y - x))).sum =
        -(q.roots.map fun x => 1 / (y - x)).sum := by simp [Multiset.sum_map_neg]
    dsimp only [s]
    rw [heq, (mul_eq_zero.mp hd.symm).resolve_left hqy, neg_zero]
  have hpos := neg_pos.mpr (one_div_neg.mpr (sub_neg.mpr (h x hx)))
  linarith

end DerivativeChainPrivate



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial

noncomputable def spokePoly (k r : ℕ) (q : Polynomial ℝ) : Polynomial ℂ :=
  X ^ r * (q.map Complex.ofRealHom).comp (X ^ k)

theorem spoke_derivative_succ (k r : ℕ) (q : Polynomial ℝ) :
    (spokePoly (k + 1) (r + 1) q).derivative =
      spokePoly (k + 1) r
        (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative) := by
  simp only [spokePoly, derivative_mul, derivative_pow, derivative_X, mul_one,
    Nat.add_sub_cancel, derivative_comp, derivative_map, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.add_comp,
    Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
  rw [pow_succ (X : Polynomial ℂ) r, pow_succ (X : Polynomial ℂ) k]
  simp only [map_add, map_natCast, map_one]
  push_cast
  ring

theorem spoke_derivative_zero (k : ℕ) (q : Polynomial ℝ) :
    (spokePoly (k + 1) 0 q).derivative =
      spokePoly (k + 1) k (C (k + 1 : ℝ) * q.derivative) := by
  simp only [spokePoly, pow_zero, one_mul, derivative_comp, derivative_pow,
    derivative_X, mul_one, Nat.add_sub_cancel, derivative_map,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.mul_comp, Polynomial.C_comp]
  simp only [map_add, map_natCast, map_one]
  push_cast
  ring

theorem spoke_natDegree (k r : ℕ) (q : Polynomial ℝ) (hq : q ≠ 0) (hk : 0 < k) :
    (spokePoly k r q).natDegree = r + k * q.natDegree := by
  have hmap : q.map Complex.ofRealHom ≠ 0 := Polynomial.map_ne_zero hq
  have hcomp : (q.map Complex.ofRealHom).comp (X ^ k) ≠ 0 := by
    rw [ne_eq, Polynomial.comp_eq_zero_iff]
    simp only [hmap, false_or]
    intro h
    have hdegree := congrArg Polynomial.natDegree h.2
    simp only [natDegree_X_pow, natDegree_C] at hdegree
    omega
  rw [spokePoly, natDegree_mul (pow_ne_zero _ X_ne_zero) hcomp,
    natDegree_X_pow, natDegree_comp, natDegree_map, natDegree_X_pow]
  ring

theorem spoke_derivative_closed (k r : ℕ) (q : Polynomial ℝ) (hk : 2 ≤ k)
    (hr : r < k) (hq : q.Splits) :
    ∃ s < k, ∃ v : Polynomial ℝ, v.Splits ∧
      (spokePoly k r q).derivative = spokePoly k s v := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  cases r with
  | zero =>
    exact ⟨j, by omega, C (j + 1 : ℝ) * q.derivative,
      (real_splits_derivative q hq).C_mul _, spoke_derivative_zero j q⟩
  | succ s =>
    exact ⟨s, by omega, C (s + 1 : ℝ) * q + C (j + 1 : ℝ) * X * q.derivative,
      real_splits_weighted_derivative q hq s j, spoke_derivative_succ j s q⟩

theorem spoke_eval_real_power (k r : ℕ) (q : Polynomial ℝ) (w : ℂ) (y : ℝ)
    (hw : w ^ k = (y : ℂ)) :
    (spokePoly k r q).eval w = w ^ r * ((q.eval y : ℝ) : ℂ) := by
  simp only [spokePoly, eval_mul, eval_pow, eval_X, eval_comp, hw]
  exact congrArg (fun z : ℂ => w ^ r * z)
    (Polynomial.eval_map_apply (f := Complex.ofRealHom) (p := q) y)

theorem spoke_nonzero (k r : ℕ) (q : Polynomial ℝ) (hq : q ≠ 0) (hk : 0 < k) :
    spokePoly k r q ≠ 0 := by
  apply mul_ne_zero (pow_ne_zero _ X_ne_zero)
  rw [ne_eq, Polynomial.comp_eq_zero_iff]
  simp only [Polynomial.map_ne_zero hq, false_or]
  intro h
  have hdegree := congrArg Polynomial.natDegree h.2
  simp only [natDegree_X_pow, natDegree_C] at hdegree
  omega

theorem spoke_root_power_real (k r : ℕ) (q : Polynomial ℝ) (hq : q.Splits)
    (hqne : q ≠ 0) (w : ℂ) (hw : w ≠ 0) (hz : (spokePoly k r q).eval w = 0) :
    ∃ y : ℝ, w ^ k = (y : ℂ) := by
  have heval : (q.map Complex.ofRealHom).eval (w ^ k) = 0 := by
    simp only [spokePoly, eval_mul, eval_pow, eval_X, eval_comp] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hw)
  obtain ⟨y, hy⟩ := hq.mem_range_of_isRoot hqne heval
  exact ⟨y, hy.symm⟩

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem spoke_derivative_parent_power (k r : ℕ) (q : Polynomial ℝ)
    (hk : 2 ≤ k) (hr : r < k) (hq : q.Splits) (hqne : q ≠ 0)
    (hdegree : 2 ≤ (spokePoly k r q).natDegree) (w : ℂ) (hw : w ≠ 0)
    (hz : (spokePoly k r q).derivative.eval w = 0) :
    ∃ y x : ℝ, w ^ k = (y : ℂ) ∧ q.eval x = 0 ∧
      ((0 < y ∧ y ≤ x) ∨ (y < 0 ∧ x ≤ y)) := by
  obtain ⟨s, hs, v, hv, heq⟩ := spoke_derivative_closed k r q hk hr hq
  have hvne : v ≠ 0 := by
    intro hvzero
    have hdne : (spokePoly k r q).derivative ≠ 0 := by
      intro h
      have := Polynomial.derivative_eq_zero.mp h
      omega
    apply hdne
    rw [heq, hvzero]
    simp [spokePoly]
  obtain ⟨y, hy⟩ := spoke_root_power_real k s v hv hvne w hw (by rwa [← heq])
  have hyne : y ≠ 0 := by
    intro hzero
    have : w ^ k = 0 := by simp [hy, hzero]
    exact pow_ne_zero k hw this
  have hchild (b : Polynomial ℝ) (t : ℕ)
      (h : (spokePoly k t b).eval w = 0) : b.eval y = 0 := by
    rw [spoke_eval_real_power k t b w y hy] at h
    have hc := (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hw)
    exact Complex.ofReal_eq_zero.mp hc
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  cases r with
  | zero =>
    have hd : q.derivative.eval y = 0 := by
      rw [spoke_derivative_zero] at hz
      have ht := hchild (C (j + 1 : ℝ) * q.derivative) j hz
      simp only [eval_mul, eval_C] at ht
      exact (mul_eq_zero.mp ht).resolve_left (by positivity)
    have hqdeg : 0 < q.natDegree := by
      rw [spoke_natDegree _ _ _ hqne (by omega)] at hdegree
      by_contra h
      have : q.natDegree = 0 := by omega
      simp [this] at hdegree
    rcases lt_or_gt_of_ne hyne with hneg | hpos
    · obtain ⟨x, hx, hxy⟩ := derivative_negative_parent q hqne hq hqdeg y hd
      exact ⟨y, x, hy, (Polynomial.mem_roots hqne).mp hx, Or.inr ⟨hneg, hxy⟩⟩
    · obtain ⟨x, hx, hxy⟩ := derivative_positive_parent q hqne hq hqdeg y hd
      exact ⟨y, x, hy, (Polynomial.mem_roots hqne).mp hx, Or.inl ⟨hpos, hxy⟩⟩
  | succ t =>
    rw [spoke_derivative_succ] at hz
    have ht := hchild (C (t + 1 : ℝ) * q + C (j + 1 : ℝ) * X * q.derivative) t hz
    rcases lt_or_gt_of_ne hyne with hneg | hpos
    · obtain ⟨x, hx, hxy⟩ := weighted_negative_parent q hqne hq t j y hneg ht
      exact ⟨y, x, hy, (Polynomial.mem_roots hqne).mp hx, Or.inr ⟨hneg, hxy⟩⟩
    · obtain ⟨x, hx, hxy⟩ := weighted_positive_parent q hqne hq t j y hpos ht
      exact ⟨y, x, hy, (Polynomial.mem_roots hqne).mp hx, Or.inl ⟨hpos, hxy⟩⟩

theorem spoke_derivative_ray_parent (k r : ℕ) (q : Polynomial ℝ)
    (hk : 2 ≤ k) (hr : r < k) (hq : q.Splits) (hqne : q ≠ 0)
    (hdegree : 2 ≤ (spokePoly k r q).natDegree) (w : ℂ) (hw : w ≠ 0)
    (hz : (spokePoly k r q).derivative.eval w = 0) :
    ∃ t : ℝ, 1 ≤ t ∧ (spokePoly k r q).eval ((t : ℂ) * w) = 0 := by
  obtain ⟨y, x, hy, hx, hsign⟩ :=
    spoke_derivative_parent_power k r q hk hr hq hqne hdegree w hw hz
  have hyne : y ≠ 0 := by
    intro h
    have : w ^ k = 0 := by simp [hy, h]
    exact pow_ne_zero _ hw this
  have hratio : 1 ≤ x / y := by
    rcases hsign with ⟨hypos, hxy⟩ | ⟨hyneg, hxy⟩
    · exact (le_div_iff₀ hypos).mpr (by simpa using hxy)
    · exact (le_div_iff_of_neg hyneg).mpr (by simpa using hxy)
  let t : ℝ := (x / y) ^ ((k : ℝ)⁻¹)
  have ht : 1 ≤ t := Real.one_le_rpow hratio (by positivity)
  have htpow : t ^ k = x / y := Real.rpow_inv_natCast_pow (by linarith) (by omega)
  have hpower : ((t : ℂ) * w) ^ k = (x : ℂ) := by
    rw [mul_pow, ← Complex.ofReal_pow, htpow, hy, ← Complex.ofReal_mul]
    congr 1
    exact div_mul_cancel₀ x hyne
  refine ⟨t, ht, ?_⟩
  rw [spoke_eval_real_power k r q _ x hpower, hx]
  simp

theorem spoke_linear_root_zero (k r : ℕ) (q : Polynomial ℝ) (hk : 2 ≤ k)
    (hqne : q ≠ 0) (hdegree : (spokePoly k r q).natDegree = 1) :
    (spokePoly k r q).eval 0 = 0 := by
  have hdeg := spoke_natDegree k r q hqne (by omega)
  have hqdeg : q.natDegree = 0 := by nlinarith
  have hr : r = 1 := by rw [hqdeg, mul_zero, add_zero] at hdeg; omega
  simp [spokePoly, hr]

end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate
open Polynomial

theorem spoke_geodesic (n k r : ℕ) (q : Polynomial ℝ) (hk : 2 ≤ k)
    (hr : r < k) (hq : q.Splits) (hqne : q ≠ 0)
    (hdegree : (spokePoly k r q).natDegree = n + 1) :
    ∃ z : ℕ → ℂ, z 0 = 0 ∧
      (∀ i < n + 1, (Polynomial.derivative^[n - i] (spokePoly k r q)).eval (z i) = 0) ∧
      (∀ i < n, ‖z (i + 1) - z i‖ = ‖z (i + 1)‖ - ‖z i‖) := by
  induction n generalizing r q with
  | zero =>
    refine ⟨fun _ => 0, rfl, ?_, ?_⟩
    · intro i hi
      have : i = 0 := by omega
      subst i
      simpa using spoke_linear_root_zero k r q hk hqne hdegree
    · intro i hi; omega
  | succ n ih =>
    let p := spokePoly k r q
    have hpdeg : p.natDegree = n + 2 := by simpa [p, Nat.add_assoc] using hdegree
    obtain ⟨s, hs, v, hv, heq⟩ := spoke_derivative_closed k r q hk hr hq
    have hvne : v ≠ 0 := by
      intro hvzero
      have hp0 : p.derivative ≠ 0 := by
        intro h
        have := Polynomial.derivative_eq_zero.mp h
        omega
      apply hp0
      change (spokePoly k r q).derivative = 0
      rw [heq, hvzero]
      simp [spokePoly]
    have hvdeg : (spokePoly k s v).natDegree = n + 1 := by
      rw [← heq, Polynomial.natDegree_derivative]
      change p.natDegree - 1 = n + 1
      omega
    obtain ⟨z, hz0, hzroots, hzsteps⟩ := ih s v hs hv hvne hvdeg
    have hw : p.derivative.eval (z n) = 0 := by
      have h := hzroots n (by omega)
      simpa only [Nat.sub_self, Function.iterate_zero, id_eq, ← heq] using h
    obtain ⟨a, ha, hstep⟩ : ∃ a : ℂ, p.eval a = 0 ∧
        ‖a - z n‖ = ‖a‖ - ‖z n‖ := by
      by_cases hzero : z n = 0
      · obtain ⟨a, ha⟩ := Complex.exists_root (f := p)
          (Polynomial.natDegree_pos_iff_degree_pos.mp (by omega))
        exact ⟨a, ha, by simp [hzero]⟩
      · obtain ⟨t, ht, htroot⟩ :=
          spoke_derivative_ray_parent k r q hk hr hq hqne (by omega) (z n) hzero hw
        refine ⟨(t : ℂ) * z n, htroot, ?_⟩
        have ht0 : 0 ≤ t := by linarith
        have ht1 : 0 ≤ t - 1 := by linarith
        calc
          ‖(t : ℂ) * z n - z n‖ = ‖((t - 1 : ℝ) : ℂ) * z n‖ := by
            congr 1
            push_cast
            ring
          _ = (t - 1) * ‖z n‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht1]
          _ = ‖(t : ℂ) * z n‖ - ‖z n‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
            ring
    let w (i : ℕ) := if i = n + 1 then a else z i
    refine ⟨w, by simp [w, hz0], ?_, ?_⟩
    · intro i hi
      by_cases hieq : i = n + 1
      · subst i
        simpa [w, p] using ha
      · have hin : i < n + 1 := by omega
        have h := hzroots i hin
        rw [← heq] at h
        have hexp : n + 1 - i = (n - i) + 1 := by omega
        simpa only [w, if_neg hieq, hexp, Function.iterate_succ_apply] using h
    · intro i hi
      by_cases hieq : i = n
      · subst i
        simpa [w] using hstep
      · have hin : i < n := by omega
        simpa [w, hieq, show i ≠ n + 1 by omega] using hzsteps i hin



end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate

theorem card_real_roots_interval_le_derivative (p : Polynomial ℝ) (A B : ℝ) :
    (p.roots.filter (fun x => A ≤ x ∧ x ≤ B)).card ≤
      (p.derivative.roots.filter (fun x => A ≤ x ∧ x ≤ B)).card + 1 := by
  classical
  rcases eq_or_ne p.derivative 0 with hd | hd
  · rw [Polynomial.eq_C_of_derivative_eq_zero hd]
    simp
  have hp : p ≠ 0 := ne_of_apply_ne Polynomial.derivative (by rwa [Polynomial.derivative_zero])
  let s := p.roots.filter (fun x => A ≤ x ∧ x ≤ B)
  let t := p.derivative.roots.filter (fun x => A ≤ x ∧ x ≤ B)
  have hs (x : ℝ) (hx : x ∈ s.toFinset) : x ∈ p.roots ∧ (A ≤ x ∧ x ≤ B) := by
    simpa only [s, Multiset.mem_toFinset, Multiset.mem_filter] using hx
  have ht (x : ℝ) (hx : x ∈ t.toFinset) : x ∈ p.derivative.roots ∧ (A ≤ x ∧ x ≤ B) := by
    simpa only [t, Multiset.mem_toFinset, Multiset.mem_filter] using hx
  have hcard : s.toFinset.card ≤ (t.toFinset \ s.toFinset).card + 1 := by
    refine Finset.card_le_sdiff_of_interleaved ?_
    intro x hx y hy hxy _
    obtain ⟨z, hz, hzero⟩ := exists_deriv_eq_zero hxy p.continuousOn
      (((Polynomial.mem_roots hp).mp (hs x hx).1).trans
        ((Polynomial.mem_roots hp).mp (hs y hy).1).symm)
    refine ⟨z, ?_, hz⟩
    rw [Multiset.mem_toFinset, Multiset.mem_filter]
    refine ⟨?_, (hs x hx).2.1.trans hz.1.le, hz.2.le.trans (hs y hy).2.2⟩
    rwa [Polynomial.mem_roots hd, Polynomial.IsRoot, ← p.deriv]
  have hscount (x : ℝ) (hx : x ∈ s.toFinset) :
      s.count x = p.rootMultiplicity x := by
    dsimp [s]
    rw [Multiset.count_filter_of_pos (p := fun y : ℝ => A ≤ y ∧ y ≤ B)
      (a := x) (hs x hx).2, Polynomial.count_roots]
  have htcount (x : ℝ) (hx : x ∈ s.toFinset) :
      t.count x = p.derivative.rootMultiplicity x := by
    dsimp [t]
    rw [Multiset.count_filter_of_pos (p := fun y : ℝ => A ≤ y ∧ y ≤ B)
      (a := x) (hs x hx).2, Polynomial.count_roots]
  change s.card ≤ t.card + 1
  calc
    s.card = ∑ x ∈ s.toFinset, s.count x := (Multiset.toFinset_sum_count_eq _).symm
    _ = ∑ x ∈ s.toFinset, (s.count x - 1 + 1) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (Nat.sub_add_cancel (Nat.succ_le_iff.mpr
        (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hx)))).symm
    _ = (∑ x ∈ s.toFinset, (p.rootMultiplicity x - 1)) + s.toFinset.card := by
      simp only [Finset.sum_add_distrib, Finset.card_eq_sum_ones]
      congr 1
      exact Finset.sum_congr rfl (fun x hx => by rw [hscount x hx])
    _ ≤ (∑ x ∈ s.toFinset, t.count x) + ((t.toFinset \ s.toFinset).card + 1) := by
      apply add_le_add _ hcard
      apply Finset.sum_le_sum
      intro x hx
      rw [htcount x hx]
      exact Polynomial.rootMultiplicity_sub_one_le_derivative_rootMultiplicity p x
    _ ≤ (∑ x ∈ s.toFinset, t.count x) +
        ((∑ x ∈ t.toFinset \ s.toFinset, t.count x) + 1) := by
      gcongr
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_le_sum
      intro x hx
      exact Nat.succ_le_iff.mpr (Multiset.count_pos.mpr
        (Multiset.mem_toFinset.mp (Finset.mem_sdiff.mp hx).1))
    _ = t.card + 1 := by
      rw [← add_assoc, ← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_self_eq_union, ← Multiset.toFinset_sum_count_eq,
        ← Finset.sum_subset Finset.subset_union_right]
      intro x _ hx
      simpa only [Multiset.mem_toFinset, Multiset.count_eq_zero] using hx

theorem real_derivative_roots_interval_of_count_eq (p : Polynomial ℝ) (A B : ℝ)
    (hparent : ∀ x ∈ p.roots, A ≤ x ∧ x ≤ B)
    (hcount : p.roots.card = p.derivative.roots.card + 1) :
    ∀ x ∈ p.derivative.roots, A ≤ x ∧ x ≤ B := by
  classical
  have h := card_real_roots_interval_le_derivative p A B
  rw [Multiset.filter_eq_self.mpr hparent, hcount] at h
  have heq : p.derivative.roots.filter (fun x => A ≤ x ∧ x ≤ B) = p.derivative.roots := by
    apply Multiset.eq_of_le_of_card_le (Multiset.filter_le _ _)
    omega
  exact Multiset.filter_eq_self.mp heq

end DerivativeChainPrivate



set_option autoImplicit false

namespace DerivativeChainPrivate

theorem real_root_defect_zero_or_two (p : Polynomial ℝ)
    (h : p.natDegree - p.roots.card ≤ 2) :
    p.natDegree - p.roots.card = 0 ∨ p.natDegree - p.roots.card = 2 := by
  obtain ⟨q, _, hdegree, hroots⟩ := p.exists_prod_multiset_X_sub_C_mul
  have hq : q.natDegree ≤ 2 := by omega
  have hnot : q.natDegree ≠ 1 := by
    intro hone
    have hcard := (Polynomial.Splits.of_natDegree_eq_one hone).natDegree_eq_card_roots
    rw [hroots] at hcard
    simp only [Multiset.card_zero] at hcard
    omega
  omega





end DerivativeChainPrivate



set_option autoImplicit false

namespace DerivativeChainPrivate

theorem derivative_root_norm_le {P : Polynomial ℂ} (hP : 0 < P.degree)
    (R : ℝ) (hR : ∀ w ∈ P.roots, ‖w‖ ≤ R) {z : ℂ}
    (hz : P.derivative.eval z = 0) : ‖z‖ ≤ R := by
  have hp : P ≠ 0 := by rintro rfl; simp at hP
  have hd : P.derivative ≠ 0 := Polynomial.derivative_eq_zero.not.mpr
    (Nat.ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mpr hP))
  have hm : z ∈ P.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval]
    exact ⟨hd, hz⟩
  have hs : P.rootSet ℂ ⊆ Metric.closedBall (0 : ℂ) R := by
    intro w hw
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval] at hw
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hR w ((Polynomial.mem_roots hp).mpr hw.2)
  have hmem := (convexHull_min hs (convex_closedBall (0 : ℂ) R))
    (P.rootSet_derivative_subset_convexHull_rootSet hP hm)
  simpa only [Metric.mem_closedBall, dist_zero_right] using hmem







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem weighted_real_root_count (q : Polynomial ℝ) (hq : q ≠ 0) (r k : ℕ) :
    let b := C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative
    b.natDegree = q.natDegree ∧ q.roots.card ≤ b.roots.card := by
  classical
  dsimp only
  let b := C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative
  let p := X ^ (r + 1) * q ^ (k + 1)
  have hpdeg : p.natDegree = r + 1 + (k + 1) * q.natDegree := by
    dsimp [p]
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hq),
      natDegree_X_pow, natDegree_pow]
  have hd : p.derivative ≠ 0 := by
    intro h
    have hz := Polynomial.derivative_eq_zero.mp h
    rw [hpdeg] at hz
    omega
  have hb : b ≠ 0 := by
    intro h
    apply hd
    rw [show p.derivative = X ^ r * q ^ k * b from weighted_derivative_factor q r k, h]
    simp
  have hfactor : p.derivative = X ^ r * q ^ k * b := weighted_derivative_factor q r k
  have hbdeg : b.natDegree = q.natDegree := by
    have heq := congrArg Polynomial.natDegree hfactor
    rw [Polynomial.natDegree_derivative, hpdeg,
      natDegree_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hq)) hb,
      natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hq),
      natDegree_X_pow, natDegree_pow] at heq
    simp only [Nat.add_mul, Nat.one_mul] at heq
    omega
  have hcount := p.card_roots_le_derivative
  have hpne : p ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hq)
  have hpcount : p.roots.card = r + 1 + (k + 1) * q.roots.card := by
    dsimp [p]
    rw [roots_mul hpne, Multiset.card_add, roots_X_pow, Multiset.card_nsmul, Multiset.card_singleton, mul_one,
      roots_pow, Multiset.card_nsmul]
  have hdcount : p.derivative.roots.card = r + k * q.roots.card + b.roots.card := by
    rw [hfactor, roots_mul (by rw [← hfactor]; exact hd), Multiset.card_add,
      roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hq)),
      Multiset.card_add, roots_X_pow, Multiset.card_nsmul, Multiset.card_singleton, mul_one,
      roots_pow, Multiset.card_nsmul]
  refine ⟨hbdeg, ?_⟩
  rw [hpcount, hdcount] at hcount
  nlinarith

theorem weighted_real_root_defect (q : Polynomial ℝ) (r k : ℕ) :
    let b := C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative
    b.natDegree - b.roots.card ≤ q.natDegree - q.roots.card := by
  by_cases hq : q = 0
  · simp [hq]
  obtain ⟨hdegree, hcount⟩ := weighted_real_root_count q hq r k
  dsimp only at hdegree hcount ⊢
  rw [hdegree]
  omega

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem derivative_real_parents_of_count (p : Polynomial ℝ)
    (hcount : p.roots.card = p.derivative.roots.card + 1) (y : ℝ)
    (hy : y ∈ p.derivative.roots) :
    ∃ lo ∈ p.roots, ∃ hi ∈ p.roots, lo ≤ y ∧ y ≤ hi := by
  classical
  have hne : p.roots ≠ 0 := by intro h; simp [h] at hcount
  let s := p.roots.toFinset
  have hs : s.Nonempty := Multiset.toFinset_nonempty.mpr hne
  have h := real_derivative_roots_interval_of_count_eq p (s.min' hs) (s.max' hs)
    (fun x hx => ⟨Finset.min'_le _ x (Multiset.mem_toFinset.mpr hx),
      Finset.le_max' _ x (Multiset.mem_toFinset.mpr hx)⟩) hcount y hy
  exact ⟨s.min' hs, Multiset.mem_toFinset.mp (Finset.min'_mem _ hs),
    s.max' hs, Multiset.mem_toFinset.mp (Finset.max'_mem _ hs), h⟩

theorem weighted_stable_real_parent (q : Polynomial ℝ) (hq : q ≠ 0) (r k : ℕ)
    (hcount : (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative).roots.card =
      q.roots.card) (y : ℝ)
    (hy : (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative).eval y = 0)
    (hyne : y ≠ 0) :
    ∃ x ∈ q.roots, (0 < y ∧ y ≤ x) ∨ (y < 0 ∧ x ≤ y) := by
  classical
  let b := C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative
  let p : Polynomial ℝ := X ^ (r + 1) * q ^ (k + 1)
  have hfactor : p.derivative = X ^ r * q ^ k * b := weighted_derivative_factor q r k
  have hpdeg : p.natDegree = r + 1 + (k + 1) * q.natDegree := by
    dsimp [p]
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hq),
      natDegree_X_pow, natDegree_pow]
  have hd : p.derivative ≠ 0 := by
    intro h; have hz := Polynomial.derivative_eq_zero.mp h; rw [hpdeg] at hz; omega
  have hp : p ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hq)
  have hc : p.roots.card = p.derivative.roots.card + 1 := by
    rw [hfactor, roots_mul hp, roots_mul (by rw [← hfactor]; exact hd),
      roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hq))]
    simp only [Multiset.card_add, roots_pow, roots_X, Multiset.card_nsmul,
      Multiset.card_singleton, mul_one]
    have hb : b.roots.card = q.roots.card := hcount
    rw [hb]
    ring
  have hyd : y ∈ p.derivative.roots := by
    apply (Polynomial.mem_roots hd).mpr
    change p.derivative.eval y = 0
    rw [hfactor, eval_mul, show b.eval y = 0 from hy, mul_zero]
  obtain ⟨lo, hlo, hi, hhi, hloy, hyhi⟩ := derivative_real_parents_of_count p hc y hyd
  have hroot (x : ℝ) (hx : x ∈ p.roots) (hxne : x ≠ 0) : x ∈ q.roots := by
    have hz := Polynomial.isRoot_of_mem_roots hx
    change (X ^ (r + 1) * q ^ (k + 1)).eval x = 0 at hz
    simp only [eval_mul, eval_pow, eval_X] at hz
    have hpow := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hxne)
    exact (Polynomial.mem_roots hq).mpr (eq_zero_of_pow_eq_zero hpow)
  rcases lt_or_gt_of_ne hyne with hneg | hpos
  · exact ⟨lo, hroot lo hlo (by linarith), Or.inr ⟨hneg, hloy⟩⟩
  · exact ⟨hi, hroot hi hhi (by linarith), Or.inl ⟨hpos, hyhi⟩⟩

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem compressed_quadratic_orbit_radius (A B : ℝ) (hdisc : A ^ 2 < 4 * B)
    (d : ℕ) (w : ℂ)
    (hroot : (w ^ d) ^ 2 + (A : ℂ) * w ^ d + (B : ℂ) = 0) :
    ‖w‖ ^ (2 * d) = B := by
  let u := w ^ d
  have hre := congrArg Complex.re hroot
  have him := congrArg Complex.im hroot
  change (u ^ 2 + (A : ℂ) * u + (B : ℂ)).re = 0 at hre
  change (u ^ 2 + (A : ℂ) * u + (B : ℂ)).im = 0 at him
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.mul_im,
    add_zero] at hre him
  have hni : u.im ≠ 0 := by
    intro hz
    rw [hz] at hre
    nlinarith [sq_nonneg (2 * u.re + A)]
  have hlinear : 2 * u.re + A = 0 := by
    have hp : u.im * (2 * u.re + A) = 0 := by nlinarith [him]
    exact (mul_eq_zero.mp hp).resolve_left hni
  have hn : ‖u‖ ^ 2 = B := by
    have hnorm := Complex.sq_norm_sub_sq_re u
    have hprod : (2 * u.re + A) * u.re = 0 := by rw [hlinear]; ring
    nlinarith [hre]
  rw [show 2 * d = d * 2 by omega, pow_mul, ← norm_pow]
  exact hn

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem choose_blocks_power_lower (M q d : ℕ) :
    (M.choose q) ^ d ≤ (M * d).choose (q * d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hterm : (M * d).choose (q * d) * M.choose q ≤
        (M * d + M).choose (q * d + q) := by
      rw [Nat.add_choose_eq]
      exact Finset.single_le_sum (fun ij _ => Nat.zero_le
        ((M * d).choose ij.1 * M.choose ij.2))
        (show (q * d, q) ∈ Finset.HasAntidiagonal.antidiagonal (q * d + q) by simp)
    calc
      (M.choose q) ^ (d + 1) = (M.choose q) ^ d * M.choose q := pow_succ _ _
      _ ≤ (M * d).choose (q * d) * M.choose q := Nat.mul_le_mul_right _ ih
      _ ≤ (M * (d + 1)).choose (q * (d + 1)) := by
        simpa [Nat.mul_add] using hterm





theorem quadratic_radius_from_coefficient_bound (x : ℝ) (n M d : ℕ)
    (hx : 0 ≤ x) (hM : 3 ≤ M) (hd : 2 ≤ d) (hn : M * d ≤ n)
    (hcoeff : (n.choose (2 * d) : ℝ) * x ^ (2 * d) ≤ M.choose 2) :
    x ≤ 4 / 5 := by
  have hc : (3 : ℝ) ≤ M.choose 2 := by
    exact_mod_cast (show 3 ≤ M.choose 2 from by
      simpa using Nat.choose_le_choose 2 hM)
  have hchoose : ((M.choose 2 : ℝ) ^ d) ≤ n.choose (2 * d) := by
    exact_mod_cast ((choose_blocks_power_lower M 2 d).trans
      (Nat.choose_le_choose (2 * d) hn))
  have hbound : ((M.choose 2 : ℝ) * x ^ 2) ^ d ≤ M.choose 2 := by
    rw [mul_pow, ← pow_mul]
    exact (mul_le_mul_of_nonneg_right hchoose (by positivity)).trans hcoeff
  by_contra h
  have hlarge : 4 / 5 < x := lt_of_not_ge h
  have hx2 : 16 / 25 < x ^ 2 := by nlinarith
  have hx4 : 256 / 625 < (x ^ 2) ^ 2 := by nlinarith [sq_nonneg (x ^ 2 - 16 / 25)]
  have hcpos : (0 : ℝ) < M.choose 2 := by linarith
  have hcprod : 3 * x ^ 2 ≤ (M.choose 2 : ℝ) * x ^ 2 :=
    mul_le_mul_of_nonneg_right hc (sq_nonneg x)
  have hbase : 1 ≤ (M.choose 2 : ℝ) * x ^ 2 := by nlinarith
  have hpow := (pow_le_pow_right₀ hbase hd).trans hbound
  have hmul : 3 * (x ^ 2) ^ 2 ≤ (M.choose 2 : ℝ) * (x ^ 2) ^ 2 :=
    mul_le_mul_of_nonneg_right hc (sq_nonneg (x ^ 2))
  have hgt : 0 < (M.choose 2 : ℝ) * (x ^ 2) ^ 2 - 1 := by nlinarith
  nlinarith [mul_pos hcpos hgt]

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem equal_radius_detour (w z : ℂ)
    (hsupport : ‖z‖ ^ 2 ≤ (w * starRingEnd ℂ z).re) :
    ‖z‖ + ‖w - z‖ ≤ Real.sqrt 2 * ‖w‖ := by
  have hid : ‖w - z‖ ^ 2 = ‖w‖ ^ 2 + ‖z‖ ^ 2 -
      2 * (w * starRingEnd ℂ z).re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have htwo : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have htwo2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnonneg : 0 ≤ ‖z‖ + ‖w - z‖ := by positivity
  have hsq : (‖z‖ + ‖w - z‖) ^ 2 ≤ 2 * ‖w‖ ^ 2 := by
    nlinarith [sq_nonneg (‖z‖ - ‖w - z‖)]
  have hright : 0 ≤ Real.sqrt 2 * ‖w‖ := by positivity
  nlinarith [sq_nonneg (‖z‖ + ‖w - z‖ + Real.sqrt 2 * ‖w‖)]

theorem compressed_quadratic_detour_budget (a R cost : ℝ)
    (ha : 0 ≤ a) (hsmall : a ≤ (4 / 5 : ℝ) * R)
    (hcost : cost ≤ Real.sqrt 2 * a) :
    cost + a + R ≤ 3 * R := by
  have hsqrt : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    norm_num
  nlinarith



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem derivative_supporting_parent (p : Polynomial ℂ) (hdegree : 2 ≤ p.natDegree)
    (z : ℂ) (hz : p.derivative.eval z = 0) :
    ∃ w : ℂ, p.eval w = 0 ∧ ‖z‖ ^ 2 ≤ (w * starRingEnd ℂ z).re := by
  have hp : p ≠ 0 := by intro h; simp [h] at hdegree
  have hd : p.derivative ≠ 0 := by
    intro h; have hh := Polynomial.derivative_eq_zero.mp h; omega
  have hzset : z ∈ p.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval]
    exact ⟨hd, hz⟩
  have hzconv := p.rootSet_derivative_subset_convexHull_rootSet
    (Polynomial.natDegree_pos_iff_degree_pos.mp (by omega)) hzset
  by_contra h
  push Not at h
  have hlin : IsLinearMap ℝ (fun w : ℂ => (w * starRingEnd ℂ z).re) := by
    constructor
    · intro a b; simp [add_mul]
    · intro a b
      change ((a : ℂ) * b * starRingEnd ℂ z).re = a * (b * starRingEnd ℂ z).re
      rw [mul_assoc, Complex.mul_re]
      simp
  have hsubset : p.rootSet ℂ ⊆ {w | (w * starRingEnd ℂ z).re < ‖z‖ ^ 2} := by
    intro w hw
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval] at hw
    exact h w hw.2
  have hbad := (convexHull_min hsubset (convex_halfSpace_lt hlin (‖z‖ ^ 2))) hzconv
  have heq : (z * starRingEnd ℂ z).re = ‖z‖ ^ 2 := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm,
      Complex.normSq_apply]
    ring
  change (z * starRingEnd ℂ z).re < ‖z‖ ^ 2 at hbad
  rw [heq] at hbad
  exact (lt_irrefl _) hbad



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem unit_root_monic_coeff_bound (p : Polynomial ℂ) (hp : p.Monic)
    (hdisk : ∀ z ∈ p.roots, ‖z‖ ≤ 1) (j : ℕ) :
    ‖p.coeff j‖ ≤ p.natDegree.choose j := by
  have hm : p.mahlerMeasure = 1 := by
    rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hp.leadingCoeff]
    simp only [norm_one, one_mul]
    have hmap : p.roots.map (fun z => max 1 ‖z‖) = p.roots.map (fun _ => (1 : ℝ)) :=
      Multiset.map_congr rfl (fun z hz => max_eq_left (hdisk z hz))
    rw [hmap]
    simp
  simpa only [hm, mul_one] using p.norm_coeff_le_choose_mul_mahlerMeasure j

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem compressed_quotient_unit_roots (d r : ℕ) (q : Polynomial ℝ) (hd : 0 < d)
    (hdisk : ∀ w : ℂ, (spokePoly d r q).eval w = 0 → ‖w‖ ≤ 1) :
    ∀ y ∈ (q.map Complex.ofRealHom).roots, ‖y‖ ≤ 1 := by
  intro y hy
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq y hd
  have hy0 : (q.map Complex.ofRealHom).eval y = 0 := Polynomial.isRoot_of_mem_roots hy
  have hp0 : (spokePoly d r q).eval w = 0 := by
    simp only [spokePoly, eval_mul, eval_pow, eval_X, eval_comp, hw, hy0, mul_zero]
  have hnorm := hdisk w hp0
  rw [← hw, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) hnorm

theorem compressed_source_second_coeff_bound (d r : ℕ) (q : Polynomial ℝ)
    (hd : 0 < d) (hq : q.Monic) (hdegree : 2 ≤ q.natDegree)
    (hdisk : ∀ w : ℂ, (spokePoly d r q).eval w = 0 → ‖w‖ ≤ 1) :
    |q.coeff (q.natDegree - 2)| ≤ q.natDegree.choose 2 := by
  have h := unit_root_monic_coeff_bound (q.map Complex.ofRealHom) (hq.map _)
    (compressed_quotient_unit_roots d r q hd hdisk) (q.natDegree - 2)
  rw [natDegree_map, coeff_map] at h
  change ‖((q.coeff (q.natDegree - 2) : ℝ) : ℂ)‖ ≤ _ at h
  rw [Complex.norm_real, Real.norm_eq_abs,
    Nat.choose_symm (by omega : 2 ≤ q.natDegree)] at h
  exact h

theorem monic_derivative_row_coeff_ratio (p : Polynomial ℂ) (hp : p.Monic)
    (m : ℕ) (hm : m ≤ p.natDegree) :
    (p.natDegree.choose m : ℂ) *
      ((Polynomial.derivative^[p.natDegree - m]) p).coeff 0 =
    p.coeff (p.natDegree - m) *
      ((Polynomial.derivative^[p.natDegree - m]) p).coeff m := by
  simp only [coeff_iterate_derivative, zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  rw [Nat.add_sub_of_le hm, hp.coeff_natDegree, mul_one,
    Nat.descFactorial_eq_factorial_mul_choose,
    Nat.choose_symm hm]
  push_cast
  ring

theorem compressed_source_gap_coeff (d r : ℕ) (q : Polynomial ℝ)
    (hd : 0 < d) (hdegree : 2 ≤ q.natDegree) :
    (spokePoly d r q).coeff (r + d * q.natDegree - 2 * d) =
      ((q.coeff (q.natDegree - 2) : ℝ) : ℂ) := by
  have hind : r + d * q.natDegree - 2 * d = (q.natDegree - 2) * d + r := by
    have h : q.natDegree - 2 + 2 = q.natDegree := by omega
    have heq : r + d * q.natDegree = (q.natDegree - 2) * d + r + 2 * d := by nlinarith
    omega
  rw [hind, spokePoly, coeff_X_pow_mul,
    ← Polynomial.expand_eq_comp_X_pow,
    Polynomial.coeff_expand_mul hd, Polynomial.coeff_map]
  rfl

theorem monic_of_spoke_monic (d r : ℕ) (q : Polynomial ℝ) (hd : 0 < d)
    (hmonic : (spokePoly d r q).Monic) : q.Monic := by
  have heq := hmonic.leadingCoeff
  rw [spokePoly, leadingCoeff_mul, leadingCoeff_X_pow, one_mul,
    leadingCoeff_comp (by simpa using Nat.ne_of_gt hd), leadingCoeff_X_pow,
    one_pow, mul_one] at heq
  have hqmap : (q.map Complex.ofRealHom).Monic := heq
  exact (Polynomial.monic_map_iff (f := Complex.ofRealHom)).mp hqmap

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem compressed_quadratic_row_radius (d r : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hq : q.Monic) (hM : 3 ≤ q.natDegree)
    (hdisk : ∀ w : ℂ, (spokePoly d r q).eval w = 0 → ‖w‖ ≤ 1)
    (A B : ℝ) (hdisc : A ^ 2 < 4 * B) (c : ℂ) (hc : c ≠ 0)
    (hshape : (Polynomial.derivative^[r + d * q.natDegree - 2 * d]) (spokePoly d r q) =
      C c * (X ^ (2 * d) + C (A : ℂ) * X ^ d + C (B : ℂ))) :
    ∀ w : ℂ,
      ((Polynomial.derivative^[r + d * q.natDegree - 2 * d]) (spokePoly d r q)).eval w = 0 →
      ‖w‖ ≤ 4 / 5 := by
  let p := spokePoly d r q
  let n := r + d * q.natDegree
  have hdeg : p.natDegree = n := spoke_natDegree d r q hq.ne_zero (by omega)
  have hmonic : p.Monic := by
    exact (monic_X_pow r).mul ((hq.map Complex.ofRealHom).comp (monic_X_pow d) (by simp; omega))
  have hm : 2 * d ≤ p.natDegree := by rw [hdeg]; dsimp [n]; nlinarith
  have hratio := monic_derivative_row_coeff_ratio p hmonic (2 * d) hm
  rw [hdeg] at hratio
  have hcoeff : p.coeff (n - 2 * d) = ((q.coeff (q.natDegree - 2) : ℝ) : ℂ) :=
    compressed_source_gap_coeff d r q (by omega) (by omega)
  rw [hcoeff] at hratio
  have hcoeff0 : ((Polynomial.derivative^[n - 2 * d]) p).coeff 0 = c * (B : ℂ) := by
    rw [show (Polynomial.derivative^[n - 2 * d]) p = _ from hshape]
    simp [coeff_C_mul, coeff_add, coeff_X_pow, coeff_C,
      show d ≠ 0 by omega, show 0 ≠ d by omega]
  have hcoefftop : ((Polynomial.derivative^[n - 2 * d]) p).coeff (2 * d) = c := by
    rw [show (Polynomial.derivative^[n - 2 * d]) p = _ from hshape]
    simp [coeff_C_mul, coeff_add, coeff_X_pow, coeff_C,
      show 2 * d ≠ d by omega, show 2 * d ≠ 0 by omega]
  rw [hcoeff0, hcoefftop] at hratio
  have hB : (n.choose (2 * d) : ℝ) * B = q.coeff (q.natDegree - 2) := by
    have heq : c * ((n.choose (2 * d) : ℂ) * (B : ℂ)) =
        c * ((q.coeff (q.natDegree - 2) : ℝ) : ℂ) := by
      calc
        _ = (n.choose (2 * d) : ℂ) * (c * (B : ℂ)) := by ring
        _ = ((q.coeff (q.natDegree - 2) : ℝ) : ℂ) * c := hratio
        _ = _ := by ring
    have hh := mul_left_cancel₀ hc heq
    exact_mod_cast hh
  intro w hw
  have heq : (w ^ d) ^ 2 + (A : ℂ) * w ^ d + (B : ℂ) = 0 := by
    rw [hshape, eval_mul, eval_C] at hw
    have hz := (mul_eq_zero.mp hw).resolve_left hc
    simpa [eval_add, eval_mul, eval_C, eval_pow, eval_X, pow_mul, Nat.mul_comm] using hz
  have hradius := compressed_quadratic_orbit_radius A B hdisc d w heq
  apply quadratic_radius_from_coefficient_bound ‖w‖ n q.natDegree d (norm_nonneg _) hM hd
    (by dsimp [n]; nlinarith)
  rw [hradius, hB]
  exact (le_abs_self _).trans (compressed_source_second_coeff_bound d r q (by omega) hq (by omega) hdisk)

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem real_defect_derivative_bound (q : Polynomial ℝ) :
    q.derivative.natDegree - q.derivative.roots.card ≤ q.natDegree - q.roots.card := by
  have h := q.card_roots_le_derivative
  have hd := Polynomial.natDegree_derivative q
  have hq := Polynomial.card_roots' q
  have hqd := Polynomial.card_roots' q.derivative
  omega

theorem real_defect_C_mul (q : Polynomial ℝ) (c : ℝ) (hc : c ≠ 0) :
    (C c * q).natDegree - (C c * q).roots.card = q.natDegree - q.roots.card := by
  rw [natDegree_C_mul hc, roots_C_mul q hc]

theorem spoke_derivative_real_defect (d r : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) :
    ∃ s < d, ∃ v : Polynomial ℝ,
      (spokePoly d r q).derivative = spokePoly d s v ∧
      v.natDegree - v.roots.card ≤ q.natDegree - q.roots.card := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  cases r with
  | zero =>
    refine ⟨k, by omega, C (k + 1 : ℝ) * q.derivative, spoke_derivative_zero k q, ?_⟩
    rw [real_defect_C_mul _ _ (by positivity)]
    exact real_defect_derivative_bound q
  | succ r =>
    exact ⟨r, by omega, C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative,
      spoke_derivative_succ k r q, weighted_real_root_defect q r k⟩

theorem spoke_iterated_real_defect (t d r : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) :
    ∃ s < d, ∃ v : Polynomial ℝ,
      (Polynomial.derivative^[t]) (spokePoly d r q) = spokePoly d s v ∧
      v.natDegree - v.roots.card ≤ q.natDegree - q.roots.card := by
  induction t generalizing r q with
  | zero => exact ⟨r, hr, q, rfl, le_rfl⟩
  | succ t ih =>
    obtain ⟨s, hs, v, hderiv, hdefect⟩ := spoke_derivative_real_defect d r q hd hr
    obtain ⟨u, hu, w, hrow, hbound⟩ := ih s v hs
    refine ⟨u, hu, w, ?_, hbound.trans hdefect⟩
    rw [Function.iterate_succ_apply, hderiv]
    exact hrow

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem spoke_representation_unique (d r s : ℕ) (q v : Polynomial ℝ)
    (hd : 0 < d) (hr : r < d) (hs : s < d) (hq : q ≠ 0) (hv : v ≠ 0)
    (heq : spokePoly d r q = spokePoly d s v) : r = s ∧ q = v := by
  have hdeg := congrArg Polynomial.natDegree heq
  rw [spoke_natDegree _ _ _ hq hd, spoke_natDegree _ _ _ hv hd] at hdeg
  have hrem := congrArg (fun n => n % d) hdeg
  simp only [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero,
    Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs] at hrem
  refine ⟨hrem, ?_⟩
  subst s
  have hcomp : (q.map Complex.ofRealHom).comp (X ^ d) =
      (v.map Complex.ofRealHom).comp (X ^ d) :=
    mul_left_cancel₀ (pow_ne_zero r X_ne_zero) heq
  have hmap : q.map Complex.ofRealHom = v.map Complex.ofRealHom :=
    (Polynomial.expand_injective hd) hcomp
  exact Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective hmap

theorem spoke_defect_step_monotone (d r s : ℕ) (q v : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (hs : s < d) (hv : v ≠ 0)
    (heq : (spokePoly d r q).derivative = spokePoly d s v) :
    v.natDegree - v.roots.card ≤ q.natDegree - q.roots.card := by
  obtain ⟨t, ht, u, hu, hdefect⟩ := spoke_derivative_real_defect d r q hd hr
  have hpoly : spokePoly d s v = spokePoly d t u := heq.symm.trans hu
  have hu0 : u ≠ 0 := by
    intro hzero
    have hp := spoke_nonzero d s v hv (by omega)
    apply hp
    rw [hpoly, hzero]
    simp [spokePoly]
  have huniq := spoke_representation_unique d s t v u (by omega) hs ht hv hu0 hpoly
  simpa only [huniq.2] using hdefect

theorem complex_iterate_natDegree (p : Polynomial ℂ) (t : ℕ) :
    ((Polynomial.derivative^[t]) p).natDegree = p.natDegree - t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', Polynomial.natDegree_derivative, ih]
    omega

theorem compressed_actual_row (d r : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (n : ℕ) (hdegree : (spokePoly d r q).natDegree = n)
    (m : ℕ) (hm0 : 0 < m) (hm : m ≤ n) :
    ∃ v : Polynomial ℝ,
      (Polynomial.derivative^[n - m]) (spokePoly d r q) = spokePoly d (m % d) v ∧
      v.natDegree = m / d ∧
      v.natDegree - v.roots.card ≤ q.natDegree - q.roots.card := by
  obtain ⟨s, hs, v, hrow, hdefect⟩ := spoke_iterated_real_defect (n - m) d r q hd hr
  have hrowdeg : ((Polynomial.derivative^[n - m]) (spokePoly d r q)).natDegree = m := by
    rw [complex_iterate_natDegree, hdegree]
    omega
  have hv : v ≠ 0 := by
    intro hzero
    rw [hrow, hzero] at hrowdeg
    simp [spokePoly] at hrowdeg
    omega
  have hsum : s + d * v.natDegree = m := by
    rw [hrow, spoke_natDegree d s v hv (by omega)] at hrowdeg
    exact hrowdeg
  have hsmod : s = m % d := by
    rw [← hsum]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hs]
  have hvdeg : v.natDegree = m / d := by
    rw [← hsum, Nat.add_mul_div_left s v.natDegree (by omega : 0 < d)]
    simp [Nat.div_eq_of_lt hs]
  exact ⟨v, by simpa only [hsmod] using hrow, hvdeg, hdefect⟩

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem compressed_row_family (d r : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (n : ℕ) (hdegree : (spokePoly d r q).natDegree = n) :
    ∃ Q : ℕ → Polynomial ℝ,
      (∀ m, 0 < m → m ≤ n →
        (Polynomial.derivative^[n - m]) (spokePoly d r q) = spokePoly d (m % d) (Q m) ∧
        (Q m).natDegree = m / d ∧ Q m ≠ 0 ∧
        (Q m).natDegree - (Q m).roots.card ≤ q.natDegree - q.roots.card) ∧
      (∀ m, 0 < m → m < n →
        (Q m).natDegree - (Q m).roots.card ≤
        (Q (m + 1)).natDegree - (Q (m + 1)).roots.card) := by
  classical
  let Q (m : ℕ) := if hm : 0 < m ∧ m ≤ n then
    Classical.choose (compressed_actual_row d r q hd hr n hdegree m hm.1 hm.2) else 0
  have hQ (m : ℕ) (hm0 : 0 < m) (hm : m ≤ n) :
      (Polynomial.derivative^[n - m]) (spokePoly d r q) = spokePoly d (m % d) (Q m) ∧
      (Q m).natDegree = m / d ∧ Q m ≠ 0 ∧
      (Q m).natDegree - (Q m).roots.card ≤ q.natDegree - q.roots.card := by
    have hh := Classical.choose_spec (compressed_actual_row d r q hd hr n hdegree m hm0 hm)
    have hval : Q m = Classical.choose
        (compressed_actual_row d r q hd hr n hdegree m hm0 hm) := by simp [Q, hm0, hm]
    rw [← hval] at hh
    have hne : Q m ≠ 0 := by
      intro hz
      have hdeg := congrArg Polynomial.natDegree hh.1
      rw [complex_iterate_natDegree, hdegree, hz] at hdeg
      simp [spokePoly] at hdeg
      omega
    exact ⟨hh.1, hh.2.1, hne, hh.2.2⟩
  refine ⟨Q, hQ, ?_⟩
  intro m hm0 hm
  have hlo := hQ m hm0 hm.le
  have hhi := hQ (m + 1) (by omega) (by omega)
  have hstep : (spokePoly d ((m + 1) % d) (Q (m + 1))).derivative =
      spokePoly d (m % d) (Q m) := by
    rw [← hhi.1, ← hlo.1, show n - m = (n - (m + 1)) + 1 by omega,
      Function.iterate_succ_apply']
  exact spoke_defect_step_monotone d _ _ _ _ hd (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega)) hlo.2.2.1 hstep

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem spoke_derivative_stable_parent_power (d r : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (hq : q ≠ 0)
    (hcount : if r = 0 then q.roots.card = q.derivative.roots.card + 1 else
      (C (r : ℝ) * q + C (d : ℝ) * X * q.derivative).roots.card = q.roots.card)
    (w : ℂ) (y : ℝ) (hw : w ≠ 0) (hy : w ^ d = (y : ℂ))
    (hz : (spokePoly d r q).derivative.eval w = 0) :
    ∃ x : ℝ, q.eval x = 0 ∧ ((0 < y ∧ y ≤ x) ∨ (y < 0 ∧ x ≤ y)) := by
  have hyne : y ≠ 0 := by
    intro h
    have : w ^ d = 0 := by simp [hy, h]
    exact pow_ne_zero d hw this
  have hchild (b : Polynomial ℝ) (t : ℕ)
      (h : (spokePoly d t b).eval w = 0) : b.eval y = 0 := by
    rw [spoke_eval_real_power d t b w y hy] at h
    have hc := (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hw)
    exact Complex.ofReal_eq_zero.mp hc
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  cases r with
  | zero =>
    simp only [ite_true] at hcount
    have hderiv : q.derivative ≠ 0 := by
      intro hzero
      have hdeg := Polynomial.derivative_eq_zero.mp hzero
      have hcard := Polynomial.card_roots' q
      simp only [hzero, Polynomial.roots_zero, Multiset.card_zero] at hcount
      have hc0 : q.roots.card = 0 := by omega
      rw [hc0] at hcount
      omega
    rw [spoke_derivative_zero] at hz
    have ht := hchild (C (k + 1 : ℝ) * q.derivative) k hz
    have hdy : q.derivative.eval y = 0 := by
      simp only [eval_mul, eval_C] at ht
      exact (mul_eq_zero.mp ht).resolve_left (by positivity)
    obtain ⟨lo, hlo, hi, hhi, hloy, hyhi⟩ := derivative_real_parents_of_count q hcount y
      ((Polynomial.mem_roots hderiv).mpr hdy)
    rcases lt_or_gt_of_ne hyne with hneg | hpos
    · exact ⟨lo, Polynomial.isRoot_of_mem_roots hlo, Or.inr ⟨hneg, hloy⟩⟩
    · exact ⟨hi, Polynomial.isRoot_of_mem_roots hhi, Or.inl ⟨hpos, hyhi⟩⟩
  | succ s =>
    simp only [Nat.succ_ne_zero, if_false] at hcount
    rw [spoke_derivative_succ] at hz
    have ht := hchild (C (s + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative) s hz
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] at hcount
    obtain ⟨x, hx, hsign⟩ := weighted_stable_real_parent q hq s k hcount y ht hyne
    exact ⟨x, Polynomial.isRoot_of_mem_roots hx, hsign⟩

theorem spoke_derivative_stable_ray_parent (d r : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (hq : q ≠ 0)
    (hcount : if r = 0 then q.roots.card = q.derivative.roots.card + 1 else
      (C (r : ℝ) * q + C (d : ℝ) * X * q.derivative).roots.card = q.roots.card)
    (w : ℂ) (y : ℝ) (hw : w ≠ 0) (hy : w ^ d = (y : ℂ))
    (hz : (spokePoly d r q).derivative.eval w = 0) :
    ∃ v : ℂ, (spokePoly d r q).eval v = 0 ∧
      (∃ x : ℝ, v ^ d = (x : ℂ)) ∧ ‖v - w‖ = ‖v‖ - ‖w‖ := by
  obtain ⟨x, hx, hsign⟩ :=
    spoke_derivative_stable_parent_power d r q hd hr hq hcount w y hw hy hz
  have hyne : y ≠ 0 := by
    intro h
    have : w ^ d = 0 := by simp [hy, h]
    exact pow_ne_zero _ hw this
  have hratio : 1 ≤ x / y := by
    rcases hsign with ⟨hpos, hxy⟩ | ⟨hneg, hxy⟩
    · exact (le_div_iff₀ hpos).mpr (by simpa using hxy)
    · exact (le_div_iff_of_neg hneg).mpr (by simpa using hxy)
  let t : ℝ := (x / y) ^ ((d : ℝ)⁻¹)
  have ht : 1 ≤ t := Real.one_le_rpow hratio (by positivity)
  have htpow : t ^ d = x / y := Real.rpow_inv_natCast_pow (by linarith) (by omega)
  have hvpow : ((t : ℂ) * w) ^ d = (x : ℂ) := by
    rw [mul_pow, ← Complex.ofReal_pow, htpow, hy, ← Complex.ofReal_mul]
    congr 1
    exact div_mul_cancel₀ x hyne
  refine ⟨(t : ℂ) * w, ?_, ⟨x, hvpow⟩, ?_⟩
  · rw [spoke_eval_real_power d r q _ x hvpow, hx, Complex.ofReal_zero, mul_zero]
  · have ht0 : 0 ≤ t := by linarith
    have ht1 : 0 ≤ t - 1 := by linarith
    calc
      ‖(t : ℂ) * w - w‖ = ‖((t - 1 : ℝ) : ℂ) * w‖ := by congr 1; push_cast; ring
      _ = (t - 1) * ‖w‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht1]
      _ = ‖(t : ℂ) * w‖ - ‖w‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
        ring

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem spoke_equal_defect_counts (d r s : ℕ) (q v : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (hs : s < d) (hq : q ≠ 0) (hv : v ≠ 0)
    (heq : (spokePoly d r q).derivative = spokePoly d s v)
    (hdefect : v.natDegree - v.roots.card = q.natDegree - q.roots.card) :
    if r = 0 then q.roots.card = q.derivative.roots.card + 1 else
      (C (r : ℝ) * q + C (d : ℝ) * X * q.derivative).roots.card = q.roots.card := by
  have huniq (t : ℕ) (u : Polynomial ℝ) (ht : t < d)
      (hderiv : (spokePoly d r q).derivative = spokePoly d t u) : v = u := by
    have hpoly : spokePoly d s v = spokePoly d t u := heq.symm.trans hderiv
    have hu : u ≠ 0 := by
      intro hz
      apply spoke_nonzero d s v hv (by omega)
      rw [hpoly, hz]; simp [spokePoly]
    exact (spoke_representation_unique d s t v u (by omega) hs ht hv hu hpoly).2
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  cases r with
  | zero =>
    simp only [ite_true]
    have hveq : v = C (k + 1 : ℝ) * q.derivative :=
      huniq k _ (by omega) (spoke_derivative_zero k q)
    rw [hveq, real_defect_C_mul _ _ (by positivity)] at hdefect
    have hderiv : q.derivative ≠ 0 := by
      intro hz
      apply hv
      simp [hveq, hz]
    have hdq : 0 < q.natDegree := by
      have hh := Polynomial.derivative_ne_zero.mp hderiv
      omega
    have hqcard := Polynomial.card_roots' q
    have hdcard := Polynomial.card_roots' q.derivative
    rw [Polynomial.natDegree_derivative] at hdcard hdefect
    omega
  | succ r =>
    simp only [Nat.succ_ne_zero, if_false]
    have hveq : v = C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative :=
      huniq r _ (by omega) (spoke_derivative_succ k r q)
    obtain ⟨hdeg, hcard⟩ := weighted_real_root_count q hq r k
    rw [hveq] at hdefect
    rw [hdeg] at hdefect
    have hqcard := Polynomial.card_roots' q
    have hvc := Polynomial.card_roots' (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative)
    rw [hdeg] at hvc
    have hh : (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative).roots.card =
        q.roots.card := by omega
    simpa only [Nat.cast_succ] using hh

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators



theorem chainCost_le_radial_excess {n : ℕ} (z : ℕ → ℂ) (E : ℕ → ℝ)
    (hstep : ∀ i < n - 1,
      ‖z (i + 1) - z i‖ ≤ ‖z (i + 1)‖ - ‖z i‖ + E i) :
    chainCost (fun i : Fin n => z i.val) ≤
      ‖z (n - 1)‖ - ‖z 0‖ + ∑ i ∈ Finset.range (n - 1), E i := by
  calc
    _ ≤ ∑ i : Fin (n - 1), (‖z (i.val + 1)‖ - ‖z i.val‖ + E i.val) := by
      apply Finset.sum_le_sum
      intro i _
      exact hstep i.val i.isLt
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun i => ‖z (i + 1)‖ - ‖z i‖ + E i),
        Finset.sum_add_distrib, Finset.sum_range_sub (fun i => ‖z i‖) (n - 1)]

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators

theorem chainCost_paste (n k : ℕ) (hk : 0 < k) (hkn : k < n)
    (f g : ℕ → ℂ) :
    chainCost (fun i : Fin n => if i.val < k then f i.val else g (i.val - k)) =
      chainCost (fun i : Fin k => f i.val) + ‖g 0 - f (k - 1)‖ +
        chainCost (fun i : Fin (n - k) => g i.val) := by
  let z (i : ℕ) := if i < k then f i else g (i - k)
  have hsum (m : ℕ) (v : ℕ → ℂ) : chainCost (fun i : Fin m => v i.val) =
      ∑ i ∈ Finset.range (m - 1), ‖v (i + 1) - v i‖ := by
    unfold chainCost
    exact Fin.sum_univ_eq_sum_range (fun i => ‖v (i + 1) - v i‖) (m - 1)
  change chainCost (fun i : Fin n => z i.val) = _
  rw [hsum, show n - 1 = (k - 1) + (1 + (n - k - 1)) by omega, Finset.sum_range_add]
  have hfirst : (∑ i ∈ Finset.range (k - 1), ‖z (i + 1) - z i‖) =
      chainCost (fun i : Fin k => f i.val) := by
    rw [hsum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi0 := Finset.mem_range.mp hi
    simp only [z, if_pos (show i + 1 < k by omega), if_pos (show i < k by omega)]
  rw [hfirst, Finset.sum_range_add]
  have hjoin : (∑ i ∈ Finset.range 1, ‖z (k - 1 + i + 1) - z (k - 1 + i)‖) =
      ‖g 0 - f (k - 1)‖ := by
    simp [z, show k - 1 + 1 = k by omega,
      show k - 1 < k by omega]
  rw [hjoin, add_assoc]
  congr 1
  rw [hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [z, if_neg (show ¬k - 1 + (1 + i) + 1 < k by omega),
    if_neg (show ¬k - 1 + (1 + i) < k by omega)]
  rw [show k - 1 + (1 + i) + 1 - k = i + 1 by omega,
    show k - 1 + (1 + i) - k = i by omega]

theorem chainCost_of_radial_path {n : ℕ} (z : ℕ → ℂ)
    (hstep : ∀ i < n - 1, ‖z (i + 1) - z i‖ = ‖z (i + 1)‖ - ‖z i‖) :
    chainCost (fun i : Fin n => z i.val) = ‖z (n - 1)‖ - ‖z 0‖ := by
  unfold chainCost
  calc
    _ = ∑ i : Fin (n - 1), (‖z (i.val + 1)‖ - ‖z i.val‖) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hstep i.val i.isLt
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun i => ‖z (i + 1)‖ - ‖z i‖)]
      exact Finset.sum_range_sub (fun i => ‖z i‖) (n - 1)

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem spoke_stable_extension (d r s : ℕ) (q v : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (hs : s < d) (hq : q ≠ 0) (hv : v ≠ 0)
    (heq : (spokePoly d r q).derivative = spokePoly d s v)
    (hdefect : v.natDegree - v.roots.card = q.natDegree - q.roots.card)
    (hreal : q.roots ≠ 0) (w : ℂ) (hw : (spokePoly d s v).eval w = 0)
    (hpower : ∃ y : ℝ, w ^ d = (y : ℂ)) :
    ∃ u : ℂ, (spokePoly d r q).eval u = 0 ∧
      (∃ x : ℝ, u ^ d = (x : ℂ)) ∧ ‖u - w‖ = ‖u‖ - ‖w‖ := by
  by_cases hw0 : w = 0
  · obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hreal
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ) (by omega : 0 < d)
    refine ⟨u, ?_, ⟨x, hu⟩, by simp [hw0]⟩
    rw [spoke_eval_real_power d r q u x hu, Polynomial.isRoot_of_mem_roots hx,
      Complex.ofReal_zero, mul_zero]
  · obtain ⟨y, hy⟩ := hpower
    have hc := spoke_equal_defect_counts d r s q v hd hr hs hq hv heq hdefect
    exact spoke_derivative_stable_ray_parent d r q hd hr hq hc w y hw0 hy (by rwa [heq])



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem spoke_zero_in_quadratic_block (d m : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hm : 2 * d < m) (hm3 : m < 3 * d) :
    (spokePoly d (m % d) q).eval 0 = 0 := by
  have hrem : m % d = m - 2 * d := by
    conv_lhs => rw [show m = 2 * d + (m - 2 * d) by omega]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (show m - 2 * d < d by omega)]
  have hrem0 : m % d ≠ 0 := by rw [hrem]; omega
  simp [spokePoly, hrem0]



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem actual_row_unit_roots (p : Polynomial ℂ) (n : ℕ) (hdegree : p.natDegree = n)
    (hdisk : ∀ w : ℂ, p.eval w = 0 → ‖w‖ ≤ 1) (m : ℕ)
    (hm0 : 0 < m) (hm : m ≤ n) :
    ∀ w : ℂ, ((Polynomial.derivative^[n - m]) p).eval w = 0 → ‖w‖ ≤ 1 := by
  have hiter : ∀ t : ℕ, t < n → ∀ w : ℂ,
      ((Polynomial.derivative^[t]) p).eval w = 0 → ‖w‖ ≤ 1 := by
    intro t
    induction t with
    | zero => simpa using fun _ => hdisk
    | succ t ih =>
      intro ht w hw
      have hpos : 0 < ((Polynomial.derivative^[t]) p).degree := by
        rw [← Polynomial.natDegree_pos_iff_degree_pos, complex_iterate_natDegree, hdegree]
        omega
      rw [Function.iterate_succ_apply'] at hw
      exact derivative_root_norm_le hpos 1
        (fun x hx => ih (by omega) x (Polynomial.isRoot_of_mem_roots hx)) hw
  exact hiter (n - m) (by omega)

theorem actual_real_compressed_prefix (p : Polynomial ℂ) (n d m : ℕ)
    (hdegree : p.natDegree = n) (hd : 2 ≤ d) (hm0 : 0 < m) (hm : m ≤ n)
    (q : Polynomial ℝ) (hq : q ≠ 0) (hsplit : q.Splits)
    (hrow : (Polynomial.derivative^[n - m]) p = spokePoly d (m % d) q) :
    ∃ z : ℕ → ℂ, z 0 = 0 ∧
      (∀ i < m, ((Polynomial.derivative^[n - (i + 1)]) p).eval (z i) = 0) ∧
      (∀ i < m - 1, ‖z (i + 1) - z i‖ = ‖z (i + 1)‖ - ‖z i‖) ∧
      chainCost (fun i : Fin m => z i.val) = ‖z (m - 1)‖ := by
  have hrowdeg : (spokePoly d (m % d) q).natDegree = m - 1 + 1 := by
    rw [← hrow, complex_iterate_natDegree, hdegree]
    omega
  obtain ⟨z, hz0, hzroots, hzsteps⟩ := spoke_geodesic (m - 1) d (m % d) q hd
    (Nat.mod_lt _ (by omega)) hsplit hq hrowdeg
  refine ⟨z, hz0, ?_, hzsteps, ?_⟩
  · intro i hi
    have h := hzroots i (by omega)
    rw [← hrow, ← Function.iterate_add_apply] at h
    have hexp : m - 1 - i + (n - m) = n - (i + 1) := by omega
    simpa only [hexp] using h
  · rw [chainCost_of_radial_path z hzsteps, hz0, norm_zero, sub_zero]

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem real_quadratic_no_real_shape (q : Polynomial ℝ) (hdegree : q.natDegree = 2)
    (hreal : q.roots.card = 0) :
    ∃ c A B : ℝ, c ≠ 0 ∧ A ^ 2 < 4 * B ∧
      q = C c * (X ^ 2 + C A * X + C B) := by
  have hq : q ≠ 0 := by intro hz; simp [hz] at hdegree
  let c := q.coeff 2
  have hc : c ≠ 0 := by
    dsimp [c]
    rw [← hdegree, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hq
  let A := q.coeff 1 / c
  let B := q.coeff 0 / c
  have hA : c * A = q.coeff 1 := mul_div_cancel₀ _ hc
  have hB : c * B = q.coeff 0 := mul_div_cancel₀ _ hc
  have hshape : q = C c * (X ^ 2 + C A * X + C B) := by
    have hh := q.as_sum_range' 3 (by omega : q.natDegree < 3)
    have hpoly : q = C (q.coeff 0) + C (q.coeff 1) * X + C c * X ^ 2 := by
      simpa [Finset.sum_range_succ, ← Polynomial.C_mul_X_pow_eq_monomial, c, add_assoc] using hh
    rw [hpoly]
    calc
      _ = C c * X ^ 2 + C (c * A) * X + C (c * B) := by rw [hA, hB]; ring
      _ = _ := by simp only [map_mul]; ring
  have hnoreal (x : ℝ) : x ^ 2 + A * x + B ≠ 0 := by
    intro hx
    have hz : q.eval x = 0 := by
      rw [hshape]
      simp only [eval_mul, eval_C, eval_add, eval_pow, eval_X]
      rw [hx, mul_zero]
    have hm := (Polynomial.mem_roots hq).mpr hz
    have : q.roots = 0 := Multiset.card_eq_zero.mp hreal
    simpa [this] using hm
  have hdisc : A ^ 2 < 4 * B := by
    by_contra h
    have hnonneg : 0 ≤ discrim (1 : ℝ) A B := by simp only [discrim]; nlinarith
    obtain ⟨x, hx⟩ := exists_quadratic_eq_zero (a := (1 : ℝ)) (b := A) (c := B)
      one_ne_zero ⟨Real.sqrt (discrim 1 A B), by rw [← pow_two, Real.sq_sqrt hnonneg]⟩
    exact hnoreal x (by simpa only [one_mul, pow_two] using hx)
  exact ⟨c, A, B, hc, hdisc, hshape⟩

theorem spoke_quadratic_shape (d : ℕ) (c A B : ℝ) :
    spokePoly d 0 (C c * (X ^ 2 + C A * X + C B)) =
      C (c : ℂ) * (X ^ (2 * d) + C (A : ℂ) * X ^ d + C (B : ℂ)) := by
  simp only [spokePoly, pow_zero, one_mul, Polynomial.map_mul, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.mul_comp,
    Polynomial.add_comp, Polynomial.pow_comp, Polynomial.X_comp, Polynomial.C_comp]
  rw [← pow_mul, Nat.mul_comm d 2]
  rfl

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem paste_actual_chains (F : ℕ → Polynomial ℂ) (n k : ℕ) (hk : 0 < k)
    (hkn : k < n) (f g : ℕ → ℂ)
    (hf : ∀ i < k, (F (i + 1)).eval (f i) = 0)
    (hg : ∀ i < n - k, (F (k + 1 + i)).eval (g i) = 0) :
    ∃ z : ℕ → ℂ, (∀ i < n, (F (i + 1)).eval (z i) = 0) ∧
      chainCost (fun i : Fin n => z i.val) =
        chainCost (fun i : Fin k => f i.val) + ‖g 0 - f (k - 1)‖ +
          chainCost (fun i : Fin (n - k) => g i.val) ∧
      (∀ i, z i = if i < k then f i else g (i - k)) := by
  let z (i : ℕ) := if i < k then f i else g (i - k)
  refine ⟨z, ?_, chainCost_paste n k hk hkn f g, fun _ => rfl⟩
  intro i hi
  by_cases hik : i < k
  · simpa only [z, if_pos hik] using hf i hik
  · have h := hg (i - k) (by omega)
    have heq : k + 1 + (i - k) = i + 1 := by omega
    simpa only [z, if_neg hik, heq] using h

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem fromRoots_div_factor {n : ℕ} (a : Fin n → ℂ) (c : ℂ) (hc : c ≠ 0) :
    fromRoots (fun i => a i / c) = C (c⁻¹ ^ n) * (fromRoots a).comp (C c * X) := by
  have hfactor (i : Fin n) : X - C (a i / c) =
      C c⁻¹ * (X - C (a i)).comp (C c * X) := by
    rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
      mul_sub, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hc,
      Polynomial.C_1, one_mul, ← Polynomial.C_mul]
    congr 1
    rw [div_eq_mul_inv, mul_comm]
  simp only [fromRoots, hfactor, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← Polynomial.C_pow, ← Polynomial.prod_comp]

theorem iterate_derivative_comp_scale (p : Polynomial ℂ) (c : ℂ) (t : ℕ) :
    (Polynomial.derivative^[t]) (p.comp (C c * X)) =
      C (c ^ t) * ((Polynomial.derivative^[t]) p).comp (C c * X) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, Polynomial.derivative_C_mul,
      Polynomial.derivative_comp]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul,
      Polynomial.derivative_X, mul_one, zero_add, Function.iterate_succ_apply']
    rw [pow_succ, Polynomial.C_mul]
    ring

theorem rescale_chain {n : ℕ} (a z : Fin n → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hz : IsChain (fun i => a i / c) z) : IsChain a (fun i => c * z i) := by
  intro i
  have h := hz i
  rw [row, fromRoots_div_factor a c hc, Polynomial.iterate_derivative_C_mul,
    iterate_derivative_comp_scale] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_X] at h
  have hcoef : c⁻¹ ^ n * c ^ (n - (i.val + 1)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (inv_ne_zero hc)) (pow_ne_zero _ hc)
  have heq : (c⁻¹ ^ n * c ^ (n - (i.val + 1))) *
      ((Polynomial.derivative^[n - (i.val + 1)]) (fromRoots a)).eval (c * z i) = 0 := by
    simpa only [mul_assoc] using h
  exact (mul_eq_zero.mp heq).resolve_left hcoef

theorem chainCost_scale {n : ℕ} (z : Fin n → ℂ) (c : ℂ) :
    chainCost (fun i => c * z i) = ‖c‖ * chainCost z := by
  simp only [chainCost, ← mul_sub, norm_mul, Finset.mul_sum]

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem spoke_comp_scale (d r n : ℕ) (q : Polynomial ℝ) (R : ℝ) :
    C (((R⁻¹ ^ n : ℝ) : ℂ)) * (spokePoly d r q).comp (C (R : ℂ) * X) =
      spokePoly d r (C (R⁻¹ ^ n * R ^ r) * q.comp (C (R ^ d) * X)) := by
  simp only [spokePoly, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp,
    Polynomial.comp_assoc, Polynomial.map_mul, Polynomial.map_comp, Polynomial.map_C,
    Polynomial.map_X, Polynomial.C_comp, mul_pow,
    ← Polynomial.C_pow]
  simp only [Complex.ofRealHom_eq_coe]
  push_cast
  simp only [Polynomial.C_mul]
  ring

theorem real_defect_comp_scale (q : Polynomial ℝ) (R : ℝ) (hR : R ≠ 0) :
    (q.comp (C R * X)).natDegree - (q.comp (C R * X)).roots.card =
      q.natDegree - q.roots.card := by
  have hdeg : (q.comp (C R * X)).natDegree = q.natDegree := by
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_C_mul hR, Polynomial.natDegree_X, mul_one]
  have hcard : (q.comp (C R * X)).roots.card = q.roots.card := by
    have hh := congrArg Multiset.card
      (q.map_roots_comp_C_mul_X_add_C R 0 (isUnit_iff_ne_zero.mpr hR))
    simpa only [Polynomial.C_0, add_zero, Multiset.card_map] using hh
  rw [hdeg, hcard]

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Set

theorem log_cos_quadratic_bound (x : ℝ) (hx : |x| < Real.pi / 2) :
    Real.log (Real.cos x) + x ^ 2 / 2 ≤ 0 := by
  have hpositive (y : ℝ) (hy : 0 ≤ y) (hmax : y < Real.pi / 2) :
      Real.log (Real.cos y) + y ^ 2 / 2 ≤ 0 := by
    let f (t : ℝ) := Real.log (Real.cos t) + t ^ 2 / 2
    have hcos (t : ℝ) (ht : t ∈ Icc 0 y) : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, ht.1], by linarith [ht.2]⟩
    have hderiv (t : ℝ) (ht : t ∈ Icc 0 y) :
        HasDerivAt f (t - Real.tan t) t := by
      have h := ((Real.hasDerivAt_cos t).log (ne_of_gt (hcos t ht))).add
        (((hasDerivAt_id t).pow 2).div_const 2)
      convert! h using 1 <;> simp [f, Real.tan_eq_sin_div_cos] <;> ring
    have hanti : AntitoneOn f (Icc 0 y) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (𝕜 := ℝ) 0 y)
      · exact (Real.continuous_cos.continuousOn.log (fun t ht => ne_of_gt (hcos t ht))).add
          (by fun_prop)
      · intro t ht
        exact (hderiv t (interior_subset ht)).hasDerivWithinAt
      · intro t ht
        have ht' : t ∈ Icc 0 y := interior_subset ht
        by_cases ht0 : t = 0
        · simp [ht0]
        · have htan := Real.lt_tan (lt_of_le_of_ne ht'.1 (Ne.symm ht0)) (show t < Real.pi / 2 by linarith [ht'.2])
          linarith
    have hh := hanti (show 0 ∈ Icc 0 y by simp [hy]) (show y ∈ Icc 0 y by simp [hy]) hy
    simpa [f] using hh
  have h := hpositive |x| (abs_nonneg x) hx
  simpa [Real.cos_abs, sq_abs] using h


theorem supporting_argument_charge (z : ℂ) (hz : 1 ≤ z.re) :
    z.arg ^ 2 ≤ 2 * Real.log ‖z‖ := by
  have hzpos : 0 < z.re := by linarith
  have hne : z ≠ 0 := by intro h; norm_num [h] at hz
  have hnormpos : 0 < ‖z‖ := norm_pos_iff.mpr hne
  have hcospos : 0 < Real.cos z.arg := by
    rw [Complex.cos_arg hne]
    exact div_pos hzpos hnormpos
  have harg : |z.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hzpos)
  have hquad := log_cos_quadratic_bound z.arg harg
  have hcomp : 1 / ‖z‖ ≤ Real.cos z.arg := by
    rw [Complex.cos_arg hne]
    exact div_le_div_of_nonneg_right hz hnormpos.le
  have hlog := Real.log_le_log (one_div_pos.mpr hnormpos) hcomp
  rw [Real.log_div one_ne_zero (ne_of_gt hnormpos), Real.log_one, zero_sub] at hlog
  linarith

theorem symmetric_log_bound (x : ℝ) (hx : 1 ≤ x) :
    2 * x * Real.log x ≤ x ^ 2 - 1 := by
  let f (t : ℝ) := t - t⁻¹ - 2 * Real.log t
  have hderiv (t : ℝ) (ht : 1 ≤ t) :
      HasDerivAt f (1 + t⁻¹ ^ 2 - 2 * t⁻¹) t := by
    have htne : t ≠ 0 := by linarith
    have h := ((hasDerivAt_id t).sub (hasDerivAt_inv htne)).sub
      ((Real.hasDerivAt_log htne).const_mul 2)
    convert! h using 1 <;> simp [f, div_eq_mul_inv] <;> ring
  have hm : MonotoneOn f (Ici 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (𝕜 := ℝ) 1)
    · intro t ht
      exact (hderiv t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hderiv t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      nlinarith [sq_nonneg (t⁻¹ - 1)]
  have hh := hm (show 1 ∈ Ici (1 : ℝ) by simp) hx hx
  have hbase : 0 ≤ f x := by simpa [f] using hh
  have hxpos : 0 < x := by linarith
  have hm := mul_nonneg hxpos.le hbase
  have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hxpos)
  dsimp [f] at hm
  nlinarith

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem principal_root_energy (t : ℂ) (ht : 1 ≤ t.re) (d : ℕ) (hd : 0 < d) :
    let u := t ^ (((d : ℝ)⁻¹ : ℝ) : ℂ)
    1 ≤ ‖u‖ ∧ u ^ d = t ∧
      (d : ℝ) * ‖u - 1‖ ^ 2 ≤ (d : ℝ) * (‖u‖ - 1) ^ 2 + (‖u‖ ^ 2 - 1) := by
  let u := t ^ (((d : ℝ)⁻¹ : ℝ) : ℂ)
  let a := ‖u‖
  let delta := t.arg / (d : ℝ)
  let s := Complex.log t * (((d : ℝ)⁻¹ : ℝ) : ℂ)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have htne : t ≠ 0 := by intro hz; norm_num [hz] at ht
  have htnorm : 1 ≤ ‖t‖ := ht.trans (Complex.re_le_norm t)
  have htnormpos : 0 < ‖t‖ := by linarith
  have ha : 1 ≤ a := by
    dsimp [a, u]
    rw [Complex.norm_cpow_real]
    exact Real.one_le_rpow htnorm (inv_nonneg.mpr hdpos.le)
  have hupow : u ^ d = t := by
    dsimp [u]
    convert Complex.cpow_nat_inv_pow t (Nat.ne_of_gt hd) using 1 <;> simp
  have heq : u = Complex.exp s := Complex.cpow_def_of_ne_zero htne _
  have hsre : s.re = Real.log ‖t‖ / (d : ℝ) := by
    simp only [s, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.log_re, div_eq_mul_inv]
  have hsim : s.im = delta := by
    simp only [s, delta, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add, Complex.log_im, div_eq_mul_inv]
  have hare : u.re = a * Real.cos delta := by
    rw [heq]
    change (Complex.exp s).re = ‖u‖ * Real.cos delta
    rw [heq, Complex.exp_re, Complex.norm_exp, hsim]
  have hloga : (d : ℝ) * Real.log a = Real.log ‖t‖ := by
    dsimp [a, u]
    rw [Complex.norm_cpow_real, Real.log_rpow htnormpos]
    field_simp
  have hdelta : (d : ℝ) * delta ^ 2 ≤ 2 * Real.log a := by
    apply (mul_le_mul_iff_right₀ hdpos).mp
    have harg := supporting_argument_charge t ht
    have heq : (d : ℝ) ^ 2 * delta ^ 2 = t.arg ^ 2 := by
      dsimp [delta]
      field_simp
    nlinarith only [harg, heq, hloga]
  have hnormid : ‖u - 1‖ ^ 2 = a ^ 2 + 1 - 2 * u.re := by
    dsimp [a]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
    ring
  have hcos : 2 * (1 - Real.cos delta) ≤ delta ^ 2 := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := delta)]
  have hchord : ‖u - 1‖ ^ 2 ≤ (a - 1) ^ 2 + a * delta ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hcos (show 0 ≤ a by linarith)
    nlinarith only [hnormid, hare, hm]
  have hlog := symmetric_log_bound a ha
  have hangular : (d : ℝ) * a * delta ^ 2 ≤ a ^ 2 - 1 := by
    have hm := mul_le_mul_of_nonneg_left hdelta (show 0 ≤ a by linarith)
    nlinarith only [hm, hlog]
  refine ⟨ha, hupow, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hchord hdpos.le
  change (d : ℝ) * ‖u - 1‖ ^ 2 ≤ (d : ℝ) * (a - 1) ^ 2 + (a ^ 2 - 1)
  nlinarith only [hm, hangular]

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem spoke_derivative_support_parent (d r : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (hq : q ≠ 0) (hqdeg : 0 < q.natDegree)
    (w : ℂ) (hw : w ≠ 0) (hz : (spokePoly d r q).derivative.eval w = 0) :
    ∃ x : ℂ, (q.map Complex.ofRealHom).eval x = 0 ∧
      ‖w ^ d‖ ^ 2 ≤ (x * starRingEnd ℂ (w ^ d)).re := by
  let y := w ^ d
  let Q := q.map Complex.ofRealHom
  let P : Polynomial ℂ := X ^ r * Q ^ d
  have hQ : Q ≠ 0 := Polynomial.map_ne_zero hq
  have hPdeg : 2 ≤ P.natDegree := by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hQ), natDegree_X_pow,
      natDegree_pow, natDegree_map]
    nlinarith
  have hchild (s : ℕ) (b : Polynomial ℝ)
      (heq : (spokePoly d r q).derivative = spokePoly d s b) :
      (b.map Complex.ofRealHom).eval y = 0 := by
    rw [heq] at hz
    simp only [spokePoly, eval_mul, eval_pow, eval_X, eval_comp] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hw)
  have hPy : P.derivative.eval y = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
    cases r with
    | zero =>
      have hc := hchild k (C (k + 1 : ℝ) * q.derivative) (spoke_derivative_zero k q)
      have hqdy : (q.derivative.map Complex.ofRealHom).eval y = 0 := by
        simp only [Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C,
          Complex.ofRealHom_eq_coe] at hc
        exact (mul_eq_zero.mp hc).resolve_left (by exact_mod_cast (show (k + 1 : ℝ) ≠ 0 by positivity))
      simp only [P, pow_zero, one_mul, derivative_pow, Nat.add_sub_cancel,
        eval_mul, eval_C, eval_pow]
      rw [show derivative Q = q.derivative.map Complex.ofRealHom from derivative_map q Complex.ofRealHom,
        hqdy, mul_zero]
    | succ s =>
      let b := C (s + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative
      have hc := hchild s b (spoke_derivative_succ k s q)
      have hfactor : P.derivative = X ^ s * Q ^ k * b.map Complex.ofRealHom := by
        have hh := congrArg (Polynomial.map Complex.ofRealHom) (weighted_derivative_factor q s k)
        rw [← Polynomial.derivative_map] at hh
        simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Q, P, b] using hh
      rw [hfactor, eval_mul, hc, mul_zero]
  obtain ⟨x, hx, hs⟩ := derivative_supporting_parent P hPdeg y hPy
  have hy : y ≠ 0 := pow_ne_zero d hw
  have hxne : x ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul, Complex.zero_re] at hs
    nlinarith [sq_pos_of_pos (norm_pos_iff.mpr hy)]
  have hqx : Q.eval x = 0 := by
    simp only [P, eval_mul, eval_pow, eval_X] at hx
    exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hx).resolve_left (pow_ne_zero _ hxne))
  exact ⟨x, hqx, hs⟩

theorem spoke_derivative_energy_parent (d r : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (hq : q ≠ 0) (hqdeg : 0 < q.natDegree)
    (w : ℂ) (hw : w ≠ 0) (hz : (spokePoly d r q).derivative.eval w = 0) :
    ∃ v : ℂ, (spokePoly d r q).eval v = 0 ∧ ‖w‖ ≤ ‖v‖ ∧
      (d : ℝ) * ‖v - w‖ ^ 2 ≤
        (d : ℝ) * (‖v‖ - ‖w‖) ^ 2 + (‖v‖ ^ 2 - ‖w‖ ^ 2) := by
  obtain ⟨x, hx, hs⟩ := spoke_derivative_support_parent d r q hd hr hq hqdeg w hw hz
  let y := w ^ d
  let t := x / y
  have hy : y ≠ 0 := pow_ne_zero _ hw
  have ht : 1 ≤ t.re := by
    rw [Complex.div_re, ← add_div]
    apply (one_le_div (Complex.normSq_pos.mpr hy)).mpr
    simpa only [Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add,
      Complex.sq_norm] using hs
  let u := t ^ (((d : ℝ)⁻¹ : ℝ) : ℂ)
  obtain ⟨ha, hupow, henergy⟩ := principal_root_energy t ht d (by omega)
  let v := u * w
  have hvpower : v ^ d = x := by
    dsimp [v]
    rw [mul_pow, show u ^ d = t from hupow]
    change (x / y) * y = x
    exact div_mul_cancel₀ x hy
  have hvroot : (spokePoly d r q).eval v = 0 := by
    simp only [spokePoly, eval_mul, eval_pow, eval_X, eval_comp, hvpower, hx, mul_zero]
  have hvnorm : ‖v‖ = ‖u‖ * ‖w‖ := norm_mul u w
  refine ⟨v, hvroot, ?_, ?_⟩
  · rw [hvnorm]
    nlinarith [norm_nonneg w]
  · have hdiff : v - w = (u - 1) * w := by dsimp [v]; ring
    calc
      (d : ℝ) * ‖v - w‖ ^ 2 = ‖w‖ ^ 2 * ((d : ℝ) * ‖u - 1‖ ^ 2) := by
        rw [hdiff, norm_mul]; ring
      _ ≤ ‖w‖ ^ 2 * ((d : ℝ) * (‖u‖ - 1) ^ 2 + (‖u‖ ^ 2 - 1)) :=
        mul_le_mul_of_nonneg_left henergy (sq_nonneg _)
      _ = _ := by rw [hvnorm]; ring

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem energy_budget_step (h k c a b e : ℝ) (hh : 0 < h) (hk : 1 ≤ k)
    (hc : k ≤ c) (hrel : c ^ 2 = k ^ 2 + 2 * h)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) (he : 0 ≤ e)
    (henergy : e ^ 2 ≤ (a - b) ^ 2 + h * (a ^ 2 - b ^ 2)) :
    k * b + e ≤ c * a := by
  have hdelta0 : 0 ≤ c - k := sub_nonneg.mpr hc
  have hdelta : c - k ≤ h := by
    have hm := mul_le_mul_of_nonneg_right (show 2 ≤ c + k by linarith) hdelta0
    nlinarith only [hm, hrel]
  have hdet : 0 ≤ h ^ 2 - (c - k) ^ 2 := by nlinarith only [hh, hdelta0, hdelta]
  let A := k ^ 2 - 1 + h
  have hA : 0 < A := by dsimp [A]; nlinarith only [hk, hh]
  have hid : A * ((c * a - k * b) ^ 2 - ((a - b) ^ 2 + h * (a ^ 2 - b ^ 2))) =
      (A * b - (c * k - 1) * a) ^ 2 + (h ^ 2 - (c - k) ^ 2) * a ^ 2 := by
    dsimp [A]
    linear_combination h * a ^ 2 * hrel
  have hprod : 0 ≤ A * ((c * a - k * b) ^ 2 - ((a - b) ^ 2 + h * (a ^ 2 - b ^ 2))) := by
    rw [hid]
    exact add_nonneg (sq_nonneg _) (mul_nonneg hdet (sq_nonneg _))
  have hdiff := (mul_nonneg_iff_of_pos_left hA).mp hprod
  have hright : 0 ≤ c * a - k * b := by
    have h1 := mul_nonneg (show 0 ≤ k by linarith) (sub_nonneg.mpr hba)
    have h2 := mul_nonneg (sub_nonneg.mpr hc) ha
    nlinarith only [h1, h2]
  have hsq : e ^ 2 ≤ (c * a - k * b) ^ 2 := by linarith only [henergy, hdiff]
  have hle := (sq_le_sq₀ he hright).mp hsq
  linarith only [hle]

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem finite_weighted_length (F : ℕ → ℂ → Prop) (c : ℕ → ℝ) (n : ℕ)
    (a : ℂ) (ha : F 0 a) (hc0 : c 0 = 1)
    (hstep : ∀ i < n, ∀ w : ℂ, F i w →
      ∃ v : ℂ, F (i + 1) v ∧ c i * ‖w‖ + ‖v - w‖ ≤ c (i + 1) * ‖v‖) :
    ∃ z : ℕ → ℂ, z 0 = a ∧ (∀ i ≤ n, F i (z i)) ∧
      ‖a‖ + chainCost (fun i : Fin (n + 1) => z i.val) ≤ c n * ‖z n‖ := by
  induction n with
  | zero =>
    refine ⟨fun _ => a, rfl, ?_, ?_⟩
    · intro i hi
      have heq : i = 0 := by omega
      subst i
      exact ha
    · simp [chainCost, hc0]
  | succ n ih =>
    obtain ⟨z, hz0, hroots, hcost⟩ := ih (fun i hi => hstep i (by omega))
    obtain ⟨v, hv, hedge⟩ := hstep n (by omega) (z n) (hroots n le_rfl)
    let w (i : ℕ) := if i < n + 1 then z i else v
    refine ⟨w, by simp [w, hz0], ?_, ?_⟩
    · intro i hi
      by_cases hit : i < n + 1
      · exact (show F i (w i) from by simpa only [w, if_pos hit] using hroots i (by omega))
      · have heq : i = n + 1 := by omega
        simpa [w, heq] using hv
    · have hh := chainCost_paste (n + 2) (n + 1) (by omega) (by omega) z (fun _ => v)
      change ‖a‖ + chainCost (fun i : Fin (n + 2) => w i.val) ≤ c (n + 1) * ‖w (n + 1)‖
      rw [show w (n + 1) = v by simp [w]]
      have hcostw : chainCost (fun i : Fin (n + 2) => w i.val) =
          chainCost (fun i : Fin (n + 1) => z i.val) + ‖v - z n‖ := by
        simpa [w, chainCost] using hh
      rw [hcostw]
      linarith only [hcost, hedge]

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem real_compressed_rotational_prefix (d r n : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (hdegree : (spokePoly d r q).natDegree = n) (hn : d ≤ n)
    (hdisk : ∀ w : ℂ, (spokePoly d r q).eval w = 0 → ‖w‖ ≤ 1) :
    ∃ z : ℕ → ℂ,
      (∀ i < n, ((Polynomial.derivative^[n - (i + 1)]) (spokePoly d r q)).eval (z i) = 0) ∧
      chainCost (fun i : Fin n => z i.val) ≤ Real.sqrt (1 + 2 * (n - d : ℕ) / (d : ℝ)) := by
  let p := spokePoly d r q
  let F (m : ℕ) := (Polynomial.derivative^[n - m]) p
  obtain ⟨Q, hQ, hstep⟩ := compressed_row_family d r q hd hr n hdegree
  have hrow (m : ℕ) (hm0 : 0 < m) (hm : m ≤ n) : F m = spokePoly d (m % d) (Q m) := (hQ m hm0 hm).1
  have hdeg (m : ℕ) (hm : m ≤ n) : (F m).natDegree = m := by
    rw [complex_iterate_natDegree, hdegree]; omega
  have hderiv (m : ℕ) (hm : m < n) : (F (m + 1)).derivative = F m := by
    dsimp [F]
    rw [show n - m = n - (m + 1) + 1 by omega, Function.iterate_succ_apply']
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdne := ne_of_gt hdpos
  let c (i : ℕ) := Real.sqrt (1 + 2 * (i : ℝ) / (d : ℝ))
  have hcsq (i : ℕ) : c i ^ 2 = 1 + 2 * (i : ℝ) / (d : ℝ) := Real.sq_sqrt (by positivity)
  have hc (i : ℕ) : 1 ≤ c i := by
    have h0 : 0 ≤ c i := Real.sqrt_nonneg _
    have hh := hcsq i
    have hterm : 0 ≤ 2 * (i : ℝ) / (d : ℝ) := by positivity
    nlinarith only [h0, hh, hterm]
  have hcle (i : ℕ) : c i ≤ c (i + 1) := by
    apply Real.sqrt_le_sqrt
    push_cast
    have hInv : 0 < (d : ℝ)⁻¹ := inv_pos.mpr hdpos
    simp only [div_eq_mul_inv]
    nlinarith only [hInv]
  have hcrel (i : ℕ) : c (i + 1) ^ 2 = c i ^ 2 + 2 * (1 / (d : ℝ)) := by
    rw [hcsq, hcsq]
    push_cast
    ring
  obtain ⟨a, ha⟩ := Complex.exists_root (f := F d)
    (Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [hdeg _ hn]; omega))
  have hExtend (i : ℕ) (hi : i < n - d) (w : ℂ) (hw : (F (d + i)).eval w = 0) :
      ∃ v : ℂ, (F (d + (i + 1))).eval v = 0 ∧
        c i * ‖w‖ + ‖v - w‖ ≤ c (i + 1) * ‖v‖ := by
    have hm : d + i + 1 ≤ n := by omega
    by_cases hw0 : w = 0
    · obtain ⟨v, hv⟩ := Complex.exists_root (f := F (d + (i + 1)))
        (Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [hdeg _ (by omega)]; omega))
      refine ⟨v, hv, ?_⟩
      simp only [hw0, norm_zero, sub_zero, mul_zero, zero_add]
      nlinarith [hc (i + 1), norm_nonneg v]
    · have hqp : 0 < (Q (d + i + 1)).natDegree := by
        rw [(hQ _ (by omega) hm).2.1]
        apply Nat.div_pos (by omega) (by omega)
      have hparent : (spokePoly d ((d + i + 1) % d) (Q (d + i + 1))).derivative.eval w = 0 := by
        rw [← hrow _ (by omega) hm, hderiv _ (by omega)]
        exact hw
      obtain ⟨v, hv, hmono, hE⟩ := spoke_derivative_energy_parent d _ _ hd
        (Nat.mod_lt _ (by omega)) (hQ _ (by omega) hm).2.2.1 hqp w hw0 hparent
      have hv' : (F (d + (i + 1))).eval v = 0 := by
        rw [show d + (i + 1) = d + i + 1 by omega, hrow _ (by omega) hm]
        exact hv
      have henergy : ‖v - w‖ ^ 2 ≤ (‖v‖ - ‖w‖) ^ 2 +
          (1 / (d : ℝ)) * (‖v‖ ^ 2 - ‖w‖ ^ 2) := by
        apply (mul_le_mul_iff_right₀ hdpos).mp
        calc
          (d : ℝ) * ‖v - w‖ ^ 2 ≤ (d : ℝ) * (‖v‖ - ‖w‖) ^ 2 + (‖v‖ ^ 2 - ‖w‖ ^ 2) := hE
          _ = _ := by field_simp
      exact ⟨v, hv', energy_budget_step (1 / (d : ℝ)) (c i) (c (i + 1)) ‖v‖ ‖w‖ ‖v - w‖
        (by positivity) (hc i) (hcle i) (hcrel i) (norm_nonneg _) (norm_nonneg _) hmono
        (norm_nonneg _) henergy⟩
  obtain ⟨z, hz0, hzroots, hzcost⟩ := finite_weighted_length (fun i w => (F (d + i)).eval w = 0)
    c (n - d) a (by simpa using ha) (by simp [c]) hExtend
  have hzero (m : ℕ) (hm0 : 0 < m) (hmd : m < d) : (F m).eval 0 = 0 := by
    rw [hrow m hm0 (by omega)]
    simp [spokePoly, Nat.mod_eq_of_lt hmd, Nat.ne_of_gt hm0]
  obtain ⟨w, hwroots, hwcost, hwvalue⟩ := paste_actual_chains F n (d - 1) (by omega) (by omega)
    (fun _ => 0) z (by intro i hi; exact hzero _ (by omega) (by omega))
    (by
      intro i hi
      have hh := hzroots i (by omega)
      simpa only [show d - 1 + 1 + i = d + i by omega] using hh)
  refine ⟨w, hwroots, ?_⟩
  have htailcost : ‖a‖ + chainCost (fun i : Fin (n - (d - 1)) => z i.val) ≤ c (n - d) * ‖z (n - d)‖ := by
    rw [show n - (d - 1) = n - d + 1 by omega]
    exact hzcost
  have hzlast := hzroots (n - d) le_rfl
  rw [Nat.add_sub_of_le hn] at hzlast
  have hunit : ‖z (n - d)‖ ≤ 1 := actual_row_unit_roots p n hdegree hdisk n (by omega) le_rfl _ hzlast
  rw [hwcost, hz0]
  simp only [chainCost, sub_zero, norm_zero, zero_add, Finset.sum_const_zero]
  change ‖a‖ + chainCost (fun i : Fin (n - (d - 1)) => z i.val) ≤ c (n - d)
  nlinarith only [htailcost, hunit, hc (n - d)]

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem actual_rotational_prefix (p : Polynomial ℂ) (n d m : ℕ)
    (hdegree : p.natDegree = n) (hd : 2 ≤ d) (hmd : d ≤ m) (hm : m ≤ n)
    (hdisk : ∀ w : ℂ, p.eval w = 0 → ‖w‖ ≤ 1)
    (q : Polynomial ℝ) (hrow : (Polynomial.derivative^[n - m]) p = spokePoly d (m % d) q) :
    ∃ z : ℕ → ℂ,
      (∀ i < m, ((Polynomial.derivative^[n - (i + 1)]) p).eval (z i) = 0) ∧
      chainCost (fun i : Fin m => z i.val) ≤ Real.sqrt (1 + 2 * (m - d : ℕ) / (d : ℝ)) := by
  have hdeg : (spokePoly d (m % d) q).natDegree = m := by
    rw [← hrow, complex_iterate_natDegree, hdegree]; omega
  have hunit : ∀ w : ℂ, (spokePoly d (m % d) q).eval w = 0 → ‖w‖ ≤ 1 := by
    rw [← hrow]
    exact actual_row_unit_roots p n hdegree hdisk m (by omega) hm
  obtain ⟨z, hzroots, hzcost⟩ := real_compressed_rotational_prefix d (m % d) m q hd
    (Nat.mod_lt _ (by omega)) hdeg hmd hunit
  refine ⟨z, ?_, hzcost⟩
  intro i hi
  have h := hzroots i hi
  rw [← hrow, ← Function.iterate_add_apply] at h
  have hexp : m - (i + 1) + (n - m) = n - (i + 1) := by omega
  simpa only [hexp] using h

theorem rotational_even_block_budget (d s : ℕ) (hd : 0 < d) (hs : 2 ≤ s) :
    Real.sqrt (1 + 2 * (2 * s * d - d : ℕ) / (d : ℝ)) ≤ 2 * (s : ℝ) - 1 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hnat : 2 * s * d - d = (2 * s - 1) * d := by rw [Nat.sub_mul, one_mul]
  rw [hnat, Nat.cast_mul, mul_div_assoc, mul_div_cancel_right₀ _ (ne_of_gt hdpos)]
  apply Real.sqrt_le_iff.mpr
  have hsreal : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hcast : ((2 * s - 1 : ℕ) : ℝ) = 2 * (s : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [hcast]
  exact ⟨by linarith, by nlinarith [sq_nonneg ((s : ℝ) - 2)]⟩

theorem rotational_quotient_budget (d n M : ℕ) (hd : 0 < d) (hn : d ≤ n)
    (hM : n / d ≤ M) :
    Real.sqrt (1 + 2 * (n - d : ℕ) / (d : ℝ)) ≤ (M : ℝ) + 1 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hprod := Nat.mul_le_mul_right d hM
  have hmod := Nat.mod_lt n hd
  have hdecomp := Nat.div_add_mod n d
  have hsub := Nat.sub_add_cancel hn
  have hbd : n - d ≤ M * d := by nlinarith
  have hcast : ((n - d : ℕ) : ℝ) ≤ (M : ℝ) * d := by exact_mod_cast hbd
  have hdiv : ((n - d : ℕ) : ℝ) / d ≤ M := (div_le_iff₀ hdpos).mpr hcast
  apply Real.sqrt_le_iff.mpr
  have harg : 1 + 2 * ((n - d : ℕ) : ℝ) / d ≤ 1 + 2 * (M : ℝ) := by rw [mul_div_assoc]; linarith only [hdiv]
  have hpoly : 1 + 2 * (M : ℝ) ≤ ((M : ℝ) + 1) ^ 2 := by nlinarith only [sq_nonneg (M : ℝ)]
  exact ⟨by positivity, harg.trans hpoly⟩

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem real_root_defect_even (p : Polynomial ℝ) : Even (p.natDegree - p.roots.card) := by
  obtain ⟨q, heq, hdegree, hroots⟩ := p.exists_prod_multiset_X_sub_C_mul
  have hdiff : p.natDegree - p.roots.card = q.natDegree := by omega
  rw [hdiff]
  rcases Nat.even_or_odd q.natDegree with heven | hodd
  · exact heven
  · have hq : q ≠ 0 := by intro hz; simp [hz] at hodd
    have hnone (x : ℝ) : ¬q.IsRoot x := by
      intro hx
      have hm := (Polynomial.mem_roots hq).mpr hx
      simpa [hroots] using hm
    have hcontra (f : Polynomial ℝ) (hf : ∀ x, ¬f.IsRoot x)
        (ho : Odd f.natDegree) (hlc : 0 ≤ f.leadingCoeff) : False := by
      have hp := Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
        (P := f) (x := 0) (fun y hy => False.elim (hf y hy)) hlc
      have hn := Polynomial.zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg
        (P := f) (x := 0) (fun y hy => False.elim (hf y hy)) hlc
      have hn' : 0 < -f.eval 0 := by
        simpa only [Int.cast_negOnePow_natCast, ho.neg_one_pow, neg_one_mul] using hn
      linarith
    by_cases hlc : 0 ≤ q.leadingCoeff
    · exact False.elim (hcontra q hnone hodd hlc)
    · have hnodd : Odd (-q).natDegree := by simpa using hodd
      have hnnone (x : ℝ) : ¬(-q).IsRoot x := by simpa using hnone x
      exact False.elim (hcontra (-q) hnnone hnodd (by simpa using (le_of_lt (lt_of_not_ge hlc))))

theorem even_strict_jump_two (a b : ℕ) (ha : Even a) (hb : Even b) (hab : a < b) :
    a + 2 ≤ b := by
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hb
  omega

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem finite_budget_extension (F : ℕ → ℂ → Prop) (n : ℕ) (a : ℂ) (ha : F 0 a)
    (E : ℕ → ℝ) (hstep : ∀ i < n, ∀ w : ℂ, F i w →
      ∃ v : ℂ, F (i + 1) v ∧ ‖v - w‖ ≤ ‖v‖ - ‖w‖ + E i) :
    ∃ z : ℕ → ℂ, z 0 = a ∧ (∀ i ≤ n, F i (z i)) ∧
      (∀ i < n, ‖z (i + 1) - z i‖ ≤ ‖z (i + 1)‖ - ‖z i‖ + E i) := by
  induction n with
  | zero =>
    refine ⟨fun _ => a, rfl, ?_, ?_⟩
    · intro i hi
      have heq : i = 0 := by omega
      subst i
      exact ha
    · intro i hi; omega
  | succ n ih =>
    obtain ⟨z, hz0, hroots, hsteps⟩ := ih (fun i hi => hstep i (by omega))
    obtain ⟨v, hv, hedge⟩ := hstep n (by omega) (z n) (hroots n le_rfl)
    let w (i : ℕ) := if i = n + 1 then v else z i
    refine ⟨w, by simp [w, hz0], ?_, ?_⟩
    · intro i hi
      by_cases heq : i = n + 1
      · simpa [w, heq] using hv
      · simpa only [w, if_neg heq] using hroots i (by omega)
    · intro i hi
      by_cases heq : i = n
      · simpa [w, heq] using hedge
      · simpa only [w, if_neg (show i + 1 ≠ n + 1 by omega),
          if_neg (show i ≠ n + 1 by omega)] using hsteps i (by omega)

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial
open scoped BigOperators

theorem spoke_real_lift_exists (d r : ℕ) (q : Polynomial ℝ) (hd : 0 < d)
    (hreal : q.roots ≠ 0) :
    ∃ u : ℂ, (spokePoly d r q).eval u = 0 ∧ ∃ x : ℝ, u ^ d = (x : ℂ) := by
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hreal
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ) hd
  refine ⟨u, ?_, ⟨x, hu⟩⟩
  rw [spoke_eval_real_power d r q u x hu, Polynomial.isRoot_of_mem_roots hx,
    Complex.ofReal_zero, mul_zero]

theorem spoke_charged_extension (d r s : ℕ) (q v : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (hs : s < d) (hq : q ≠ 0) (hv : v ≠ 0)
    (heq : (spokePoly d r q).derivative = spokePoly d s v)
    (hreal : q.roots ≠ 0) (w : ℂ) (hw : (spokePoly d s v).eval w = 0)
    (hwunit : ‖w‖ ≤ 1) (hpower : ∃ y : ℝ, w ^ d = (y : ℂ)) :
    ∃ u : ℂ, (spokePoly d r q).eval u = 0 ∧ (∃ x : ℝ, u ^ d = (x : ℂ)) ∧
      ‖u - w‖ ≤ ‖u‖ - ‖w‖ +
        ((q.natDegree - q.roots.card : ℕ) : ℝ) - ((v.natDegree - v.roots.card : ℕ) : ℝ) := by
  have hmono := spoke_defect_step_monotone d r s q v hd hr hs hv heq
  by_cases hequal : v.natDegree - v.roots.card = q.natDegree - q.roots.card
  · obtain ⟨u, hu, hupow, hedge⟩ := spoke_stable_extension d r s q v hd hr hs hq hv
      heq hequal hreal w hw hpower
    exact ⟨u, hu, hupow, by rw [hequal, hedge]; linarith⟩
  · have hjump := even_strict_jump_two _ _ (real_root_defect_even v) (real_root_defect_even q)
      (lt_of_le_of_ne hmono hequal)
    have hcast : ((v.natDegree - v.roots.card : ℕ) : ℝ) + 2 ≤
        ((q.natDegree - q.roots.card : ℕ) : ℝ) := by exact_mod_cast hjump
    obtain ⟨u, hu, hupow⟩ := spoke_real_lift_exists d r q (by omega) hreal
    refine ⟨u, hu, hupow, ?_⟩
    have htriangle := norm_sub_le u w
    linarith

theorem compressed_charged_suffix (d n k : ℕ) (F : ℕ → Polynomial ℂ)
    (Q : ℕ → Polynomial ℝ) (hd : 2 ≤ d) (hkn : k ≤ n)
    (hrow : ∀ m, k ≤ m → m ≤ n → F m = spokePoly d (m % d) (Q m))
    (hne : ∀ m, k ≤ m → m ≤ n → Q m ≠ 0)
    (hderiv : ∀ m, k ≤ m → m < n → (F (m + 1)).derivative = F m)
    (hreal : ∀ m, k < m → m ≤ n → (Q m).roots ≠ 0)
    (hdisk : ∀ m, k ≤ m → m ≤ n → ∀ w : ℂ, (F m).eval w = 0 → ‖w‖ ≤ 1)
    (a : ℂ) (ha : (F k).eval a = 0) (hapower : ∃ y : ℝ, a ^ d = (y : ℂ)) :
    ∃ z : ℕ → ℂ, z 0 = a ∧
      (∀ i ≤ n - k, (F (k + i)).eval (z i) = 0 ∧ ∃ y : ℝ, (z i) ^ d = (y : ℂ)) ∧
      chainCost (fun i : Fin (n - k + 1) => z i.val) ≤
        1 - ‖a‖ + ((Q n).natDegree - (Q n).roots.card : ℕ) -
          ((Q k).natDegree - (Q k).roots.card : ℕ) := by
  let C (m : ℕ) : ℝ := ((Q m).natDegree - (Q m).roots.card : ℕ)
  let E (i : ℕ) := C (k + i + 1) - C (k + i)
  have hstep (i : ℕ) (hi : i < n - k) (w : ℂ)
      (hw : (F (k + i)).eval w = 0 ∧ ∃ y : ℝ, w ^ d = (y : ℂ)) :
      ∃ u : ℂ, ((F (k + (i + 1))).eval u = 0 ∧ ∃ x : ℝ, u ^ d = (x : ℂ)) ∧
        ‖u - w‖ ≤ ‖u‖ - ‖w‖ + E i := by
    have hm : k + i < n := by omega
    have heq : (spokePoly d ((k + i + 1) % d) (Q (k + i + 1))).derivative =
        spokePoly d ((k + i) % d) (Q (k + i)) := by
      rw [← hrow _ (by omega) (by omega), ← hrow _ (by omega) (by omega)]
      exact hderiv _ (by omega) hm
    obtain ⟨u, hu, hupow, hedge⟩ := spoke_charged_extension d _ _ _ _ hd
      (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
      (hne _ (by omega) (by omega)) (hne _ (by omega) (by omega)) heq
      (hreal _ (by omega) (by omega)) w (by rw [← hrow _ (by omega) (by omega)]; exact hw.1)
      (hdisk _ (by omega) (by omega) w hw.1) hw.2
    refine ⟨u, ⟨?_, hupow⟩, ?_⟩
    · rw [show k + (i + 1) = k + i + 1 by omega, hrow _ (by omega) (by omega)]
      exact hu
    · change ‖u - w‖ ≤ ‖u‖ - ‖w‖ + (C (k + i + 1) - C (k + i))
      dsimp only [C]
      linarith only [hedge]
  obtain ⟨z, hz0, hzroots, hzsteps⟩ := finite_budget_extension
    (fun i w => (F (k + i)).eval w = 0 ∧ ∃ y : ℝ, w ^ d = (y : ℂ))
    (n - k) a (by simpa using And.intro ha hapower) E hstep
  refine ⟨z, hz0, hzroots, ?_⟩
  have hcost := chainCost_le_radial_excess (n := n - k + 1) z E
    (by intro i hi; exact hzsteps i (by omega))
  have hsum : (∑ i ∈ Finset.range (n - k + 1 - 1), E i) = C n - C k := by
    simp only [Nat.add_sub_cancel, E]
    have hh := Finset.sum_range_sub (fun i => C (k + i)) (n - k)
    simpa only [Nat.add_assoc, Nat.add_zero, Nat.add_sub_of_le hkn] using hh
  rw [hsum, hz0, show n - k + 1 - 1 = n - k by omega] at hcost
  have hh := (hzroots (n - k) le_rfl).1
  rw [Nat.add_sub_of_le hkn] at hh
  have hnorm := hdisk n hkn le_rfl _ hh
  change chainCost (fun i : Fin (n - k + 1) => z i.val) ≤ 1 - ‖a‖ + C n - C k
  linarith only [hcost, hnorm]

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem spoke_zero_inside_block (d b m : ℕ) (q : Polynomial ℝ)
    (hbd : d ∣ b) (hbm : b < m) (hmd : m < b + d) :
    (spokePoly d (m % d) q).eval 0 = 0 := by
  have hrem : m % d = m - b := by
    conv_lhs => rw [show m = b + (m - b) by omega]
    simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hbd, Nat.mod_eq_of_lt (show m - b < d by omega)]
  have hrem0 : m % d ≠ 0 := by rw [hrem]; omega
  simp [spokePoly, hrem0]

theorem zero_pad_charged_suffix (d n k j : ℕ) (F : ℕ → Polynomial ℂ)
    (Q : ℕ → Polynomial ℝ) (hd : 2 ≤ d) (hkj : k < j) (hjn : j < n)
    (hrow : ∀ m, k < m → m ≤ n → F m = spokePoly d (m % d) (Q m))
    (hne : ∀ m, k < m → m ≤ n → Q m ≠ 0)
    (hderiv : ∀ m, k < m → m < n → (F (m + 1)).derivative = F m)
    (hreal : ∀ m, j < m → m ≤ n → (Q m).roots ≠ 0)
    (hdisk : ∀ m, k < m → m ≤ n → ∀ w : ℂ, (F m).eval w = 0 → ‖w‖ ≤ 1)
    (hzero : ∀ m, k < m → m ≤ j → (F m).eval 0 = 0) :
    ∃ g : ℕ → ℂ, g 0 = 0 ∧
      (∀ i < n - k, (F (k + 1 + i)).eval (g i) = 0) ∧
      chainCost (fun i : Fin (n - k) => g i.val) ≤
        1 + ((Q n).natDegree - (Q n).roots.card : ℕ) -
          ((Q j).natDegree - (Q j).roots.card : ℕ) := by
  obtain ⟨z, hz0, hzroots, hzcost⟩ := compressed_charged_suffix d n j F Q hd hjn.le
    (fun m hm hm' => hrow m (by omega) hm')
    (fun m hm hm' => hne m (by omega) hm')
    (fun m hm hm' => hderiv m (by omega) hm') hreal
    (fun m hm hm' => hdisk m (by omega) hm') 0 (hzero j hkj le_rfl)
    ⟨0, by simp [Nat.ne_of_gt (show 0 < d by omega)]⟩
  simp only [norm_zero, sub_zero] at hzcost
  let t := j - k - 1
  let g (i : ℕ) := if i < t then 0 else z (i - t)
  have ht : k + 1 + t = j := by dsimp [t]; omega
  have hg0 : g 0 = 0 := by
    by_cases ht0 : t = 0
    · simp [g, ht0, hz0]
    · simp [g, show 0 < t by omega]
  have hgroots (i : ℕ) (hi : i < n - k) : (F (k + 1 + i)).eval (g i) = 0 := by
    by_cases hit : i < t
    · rw [show g i = 0 from if_pos hit]
      exact hzero _ (by omega) (by omega)
    · have hh := (hzroots (i - t) (by omega)).1
      have heq : j + (i - t) = k + 1 + i := by omega
      simpa only [g, if_neg hit, heq] using hh
  refine ⟨g, hg0, hgroots, ?_⟩
  have hcostg : chainCost (fun i : Fin (n - k) => g i.val) =
      chainCost (fun i : Fin (n - j + 1) => z i.val) := by
    by_cases ht0 : t = 0
    · have hgeq : g = z := by apply _root_.funext; intro i; simp [g, ht0]
      rw [hgeq, show n - k = n - j + 1 by omega]
    · have hh := chainCost_paste (n - k) t (by omega) (by omega) (fun _ => 0) z
      have hc0 : chainCost (fun _ : Fin t => (0 : ℂ)) = 0 := by simp [chainCost]
      rw [show n - k - t = n - j + 1 by omega] at hh
      simpa only [g, hc0, hz0, sub_self, norm_zero, zero_add] using hh
  rw [hcostg]
  exact hzcost

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem actual_quadratic_reset_prefix (d r n : ℕ) (q v : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (hq : q.Monic) (hn : 3 * d ≤ n)
    (hdegree : (spokePoly d r q).natDegree = n)
    (hdisk : ∀ w : ℂ, (spokePoly d r q).eval w = 0 → ‖w‖ ≤ 1)
    (hvdeg : v.natDegree = 2) (hvroot : v.roots.card = 0)
    (hrow : (Polynomial.derivative^[n - 2 * d]) (spokePoly d r q) = spokePoly d 0 v)
    (f : ℕ → ℂ)
    (hf : ∀ i < 2 * d - 1,
      ((Polynomial.derivative^[n - (i + 1)]) (spokePoly d r q)).eval (f i) = 0)
    (hfcost : chainCost (fun i : Fin (2 * d - 1) => f i.val) = ‖f (2 * d - 2)‖) :
    ∃ z : ℕ → ℂ,
      (∀ i < 2 * d, ((Polynomial.derivative^[n - (i + 1)]) (spokePoly d r q)).eval (z i) = 0) ∧
      chainCost (fun i : Fin (2 * d) => z i.val) + ‖z (2 * d - 1)‖ ≤ 2 := by
  let p := spokePoly d r q
  let F (m : ℕ) := (Polynomial.derivative^[n - m]) p
  obtain ⟨c, A, B, hc, hdisc, hshape⟩ := real_quadratic_no_real_shape v hvdeg hvroot
  have hpolyshape : F (2 * d) =
      C (c : ℂ) * (X ^ (2 * d) + C (A : ℂ) * X ^ d + C (B : ℂ)) := by
    dsimp only [F, p]
    rw [hrow, hshape, spoke_quadratic_shape]
  have hchild : (F (2 * d)).derivative.eval (f (2 * d - 2)) = 0 := by
    have heq : (F (2 * d)).derivative = F (2 * d - 1) := by
      dsimp [F]
      rw [show n - (2 * d - 1) = n - 2 * d + 1 by omega, Function.iterate_succ_apply']
    rw [heq]
    have hh := hf (2 * d - 2) (by omega)
    simpa only [show 2 * d - 2 + 1 = 2 * d - 1 by omega] using hh
  have hFdeg : 2 ≤ (F (2 * d)).natDegree := by
    rw [complex_iterate_natDegree, hdegree]; omega
  obtain ⟨w, hw, hs⟩ := derivative_supporting_parent (F (2 * d)) hFdeg _ hchild
  have hM : 3 ≤ q.natDegree := by
    have hg := spoke_natDegree d r q hq.ne_zero (by omega)
    rw [hdegree] at hg
    by_contra h
    have hm : q.natDegree ≤ 2 := by omega
    have hmul := Nat.mul_le_mul_left d hm
    omega
  have hndeg : r + d * q.natDegree = n := by
    rw [← spoke_natDegree d r q hq.ne_zero (by omega), hdegree]
  have hwsmall : ‖w‖ ≤ 4 / 5 := compressed_quadratic_row_radius d r q hd hq hM hdisk
    A B hdisc (c : ℂ) (Complex.ofReal_ne_zero.mpr hc)
    (by simpa only [hndeg] using hpolyshape) w (by simpa only [hndeg] using hw)
  obtain ⟨z, hzroots, hzcost, hzvalue⟩ := paste_actual_chains F (2 * d) (2 * d - 1)
    (by omega) (by omega) f (fun _ => w) hf (by
      intro i hi
      have hi0 : i = 0 := by omega
      simpa only [hi0, add_zero, show 2 * d - 1 + 1 = 2 * d by omega] using hw)
  have hprefix : chainCost (fun i : Fin (2 * d) => z i.val) ≤ Real.sqrt 2 * ‖w‖ := by
    rw [hzcost, hfcost]
    simpa [chainCost, Nat.sub_sub] using equal_radius_detour w (f (2 * d - 2)) hs
  have hend : z (2 * d - 1) = w := by rw [hzvalue]; simp
  refine ⟨z, hzroots, ?_⟩
  rw [hend]
  have hb := compressed_quadratic_detour_budget ‖w‖ 1
    (chainCost (fun i : Fin (2 * d) => z i.val)) (norm_nonneg _)
    (by simpa using hwsmall) hprefix
  linarith

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem last_rootless_block_arithmetic (d j : ℕ) (a b : Polynomial ℝ)
    (hd : 0 < d) (hj : d ≤ j)
    (ha : a.natDegree = j / d) (hb : b.natDegree = (j + 1) / d)
    (hzero : a.roots = 0) (hreal : b.roots ≠ 0)
    (hmono : a.natDegree - a.roots.card ≤ b.natDegree - b.roots.card) :
    ∃ s : ℕ, 1 ≤ s ∧ a.natDegree = 2 * s ∧ j + 1 = (2 * s + 1) * d := by
  have hmod : (j + 1) % d = 0 := by
    by_contra hne
    have hdiv := Nat.succ_div_of_mod_ne_zero hne
    have hsame : b.natDegree = a.natDegree := by rw [hb, hdiv, ha]
    have hcard : b.roots.card ≠ 0 := by
      intro hz
      exact hreal (Multiset.card_eq_zero.mp hz)
    have hapos : 0 < a.natDegree := by rw [ha]; exact Nat.div_pos hj hd
    rw [hzero, Multiset.card_zero, Nat.sub_zero, hsame] at hmono
    have hbd := Polynomial.card_roots' b
    rw [hsame] at hbd
    omega
  have heven := real_root_defect_even a
  rw [hzero, Multiset.card_zero, Nat.sub_zero] at heven
  obtain ⟨s, hs⟩ := heven
  have hapos : 0 < a.natDegree := by rw [ha]; exact Nat.div_pos hj hd
  refine ⟨s, by omega, by omega, ?_⟩
  have hdiv := Nat.succ_div_of_mod_eq_zero hmod
  calc
    j + 1 = d * ((j + 1) / d) + (j + 1) % d := (Nat.div_add_mod (j + 1) d).symm
    _ = d * (s + s + 1) := by rw [hmod, hdiv, ← ha, hs]; simp
    _ = (2 * s + 1) * d := by ring

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem last_quadratic_block_chain (d r n : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (hq : q.Monic) (hn : 3 * d ≤ n)
    (hdegree : (spokePoly d r q).natDegree = n)
    (hdisk : ∀ w : ℂ, (spokePoly d r q).eval w = 0 → ‖w‖ ≤ 1)
    (Q : ℕ → Polynomial ℝ)
    (hQ : ∀ m, 0 < m → m ≤ n →
      (Polynomial.derivative^[n - m]) (spokePoly d r q) = spokePoly d (m % d) (Q m) ∧
      (Q m).natDegree = m / d ∧ Q m ≠ 0)
    (hmono : ∀ a b, 0 < a → a ≤ b → b ≤ n →
      (Q a).natDegree - (Q a).roots.card ≤ (Q b).natDegree - (Q b).roots.card)
    (hC : (Q (3 * d - 1)).natDegree - (Q (3 * d - 1)).roots.card = 2)
    (hreal : ∀ m, 3 * d - 1 < m → m ≤ n → (Q m).roots ≠ 0) :
    ∃ z : ℕ → ℂ,
      (∀ i < n, ((Polynomial.derivative^[n - (i + 1)]) (spokePoly d r q)).eval (z i) = 0) ∧
      chainCost (fun i : Fin n => z i.val) ≤ 1 + ((Q n).natDegree - (Q n).roots.card : ℕ) := by
  let p := spokePoly d r q
  let F (m : ℕ) := (Polynomial.derivative^[n - m]) p
  let C (m : ℕ) := (Q m).natDegree - (Q m).roots.card
  let j := 3 * d - 1
  have hjn : j < n := by dsimp [j]; omega
  have hrow (m : ℕ) (hm0 : 0 < m) (hm : m ≤ n) : F m = spokePoly d (m % d) (Q m) := (hQ m hm0 hm).1
  have hFderiv (m : ℕ) (hm : m < n) : (F (m + 1)).derivative = F m := by
    dsimp [F]
    rw [show n - m = n - (m + 1) + 1 by omega, Function.iterate_succ_apply']
  have hFdisk (m : ℕ) (hm0 : 0 < m) (hm : m ≤ n) :
      ∀ w : ℂ, (F m).eval w = 0 → ‖w‖ ≤ 1 := actual_row_unit_roots p n hdegree hdisk m hm0 hm
  have hex : ∃ t, 0 < t ∧ t ≤ j ∧ C t = 2 := ⟨j, by dsimp [j]; omega, le_rfl, hC⟩
  let t := Nat.find hex
  have ht := Nat.find_spec hex
  change 0 < t ∧ t ≤ j ∧ C t = 2 at ht
  have hbefore (m : ℕ) (hm0 : 0 < m) (hmt : m < t) : C m = 0 := by
    have hmC := hmono m j hm0 (by omega) hjn.le
    change C m ≤ C j at hmC
    rw [show C j = 2 from hC] at hmC
    rcases real_root_defect_zero_or_two (Q m) hmC with hh | hh
    · exact hh
    · exact False.elim ((Nat.find_min hex hmt) ⟨hm0, by omega, hh⟩)
  have ht2 : 2 * d ≤ t := by
    have hdeg := (hQ t ht.1 (by omega)).2.1
    have hdef := ht.2.2
    dsimp only [C] at hdef
    have hdiv : 2 ≤ t / d := by omega
    exact (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hdiv
  have hsplit : (Q (t - 1)).Splits := by
    apply Polynomial.splits_iff_card_roots.mpr
    have hz := hbefore (t - 1) (by omega) (by omega)
    have hc := Polynomial.card_roots' (Q (t - 1))
    dsimp only [C] at hz
    omega
  obtain ⟨f, hf0, hf, hfsteps, hfcost⟩ := actual_real_compressed_prefix p n d (t - 1) hdegree
    hd (by omega) (by omega) (Q (t - 1)) (hQ _ (by omega) (by omega)).2.2 hsplit
    (hrow _ (by omega) (by omega))
  by_cases hteq : t = 2 * d
  · rw [hteq] at hf hfcost
    have hvdeg : (Q (2 * d)).natDegree = 2 := by
      rw [(hQ _ (by omega) (by omega)).2.1, Nat.mul_div_cancel _ (by omega : 0 < d)]
    have hvroot : (Q (2 * d)).roots.card = 0 := by
      have hh := ht.2.2
      change (Q t).natDegree - (Q t).roots.card = 2 at hh
      rw [hteq, hvdeg] at hh
      omega
    obtain ⟨h, hhroots, hhcost⟩ := actual_quadratic_reset_prefix d r n q (Q (2 * d)) hd hr hq
      hn hdegree hdisk hvdeg hvroot (by simpa using hrow (2 * d) (by omega) (by omega)) f hf
      (by simpa only [Nat.sub_sub] using hfcost)
    obtain ⟨g, hg0, hg, hgcost⟩ := zero_pad_charged_suffix d n (2 * d) j F Q hd
      (by dsimp [j]; omega) hjn
      (fun m hm hm' => hrow m (by omega) hm')
      (fun m hm hm' => (hQ m (by omega) hm').2.2)
      (fun m hm hm' => hFderiv m hm') hreal
      (fun m hm hm' => hFdisk m (by omega) hm')
      (by
        intro m hm hm'
        rw [hrow m (by omega) (by omega)]
        exact spoke_zero_in_quadratic_block d m (Q m) hd hm (by dsimp [j] at hm'; omega))
    obtain ⟨z, hzroots, hzcost, hzvalue⟩ := paste_actual_chains F n (2 * d) (by omega) (by omega) h g hhroots hg
    refine ⟨z, hzroots, ?_⟩
    rw [hzcost, hg0, zero_sub, norm_neg]
    change chainCost (fun i : Fin (2 * d) => h i.val) + ‖h (2 * d - 1)‖ +
      chainCost (fun i : Fin (n - 2 * d) => g i.val) ≤ 1 + (C n : ℝ)
    change chainCost (fun i : Fin (n - 2 * d) => g i.val) ≤ 1 + (C n : ℝ) - (C j : ℝ) at hgcost
    rw [show C j = 2 from hC] at hgcost
    push_cast at hgcost
    linarith only [hhcost, hgcost]
  · have htlarge : 2 * d < t := by omega
    obtain ⟨g, hg0, hg, hgcost⟩ := zero_pad_charged_suffix d n (t - 1) j F Q hd
      (by omega) hjn
      (fun m hm hm' => hrow m (by omega) hm')
      (fun m hm hm' => (hQ m (by omega) hm').2.2)
      (fun m hm hm' => hFderiv m hm') hreal
      (fun m hm hm' => hFdisk m (by omega) hm')
      (by
        intro m hm hm'
        rw [hrow m (by omega) (by omega)]
        exact spoke_zero_in_quadratic_block d m (Q m) hd (by omega) (by dsimp [j] at hm'; omega))
    have hfunit : ‖f (t - 1 - 1)‖ ≤ 1 := by
      have hh := hf (t - 1 - 1) (by omega)
      exact hFdisk (t - 1) (by omega) (by omega) _
        (by simpa only [show t - 1 - 1 + 1 = t - 1 by omega] using hh)
    obtain ⟨z, hzroots, hzcost, hzvalue⟩ := paste_actual_chains F n (t - 1) (by omega) (by omega) f g hf hg
    refine ⟨z, hzroots, ?_⟩
    rw [hzcost, hfcost, hg0, zero_sub, norm_neg]
    change chainCost (fun i : Fin (n - (t - 1)) => g i.val) ≤ 1 + (C n : ℝ) - (C j : ℝ) at hgcost
    rw [show C j = 2 from hC] at hgcost
    push_cast at hgcost
    change ‖f (t - 1 - 1)‖ + ‖f (t - 1 - 1)‖ +
      chainCost (fun i : Fin (n - (t - 1)) => g i.val) ≤ 1 + (C n : ℝ)
    linarith only [hfunit, hgcost]

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem compressed_defect_unit_chain (d r n : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (hn : 0 < n) (hq : q.Monic)
    (hdegree : (spokePoly d r q).natDegree = n)
    (hdisk : ∀ w : ℂ, (spokePoly d r q).eval w = 0 → ‖w‖ ≤ 1) :
    ∃ z : ℕ → ℂ,
      (∀ i < n, ((Polynomial.derivative^[n - (i + 1)]) (spokePoly d r q)).eval (z i) = 0) ∧
      chainCost (fun i : Fin n => z i.val) ≤ 1 + ((q.natDegree - q.roots.card : ℕ) : ℝ) := by
  let p := spokePoly d r q
  let F (m : ℕ) := (Polynomial.derivative^[n - m]) p
  obtain ⟨Q, hQ, hstep⟩ := compressed_row_family d r q hd hr n hdegree
  let C (m : ℕ) := (Q m).natDegree - (Q m).roots.card
  have hrow (m : ℕ) (hm0 : 0 < m) (hm : m ≤ n) : F m = spokePoly d (m % d) (Q m) := (hQ m hm0 hm).1
  have hFderiv (m : ℕ) (hm : m < n) : (F (m + 1)).derivative = F m := by
    dsimp [F]
    rw [show n - m = n - (m + 1) + 1 by omega, Function.iterate_succ_apply']
  have hFdisk (m : ℕ) (hm0 : 0 < m) (hm : m ≤ n) :
      ∀ w : ℂ, (F m).eval w = 0 → ‖w‖ ≤ 1 := actual_row_unit_roots p n hdegree hdisk m hm0 hm
  have hmono (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ n) : C a ≤ C b := by
    revert hb
    induction b, hab using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ b hab ih =>
      intro hb
      exact (ih (by omega)).trans (hstep b (by omega) (by omega))
  have hGoal : 1 + (C n : ℝ) ≤ 1 + ((q.natDegree - q.roots.card : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_left (hQ n hn le_rfl).2.2.2 1
  have hzeroSmall (m : ℕ) (hm0 : 0 < m) (hmn : m ≤ n) (hmd : m < d) : (F m).eval 0 = 0 := by
    rw [hrow m hm0 hmn]
    simp [spokePoly, Nat.mod_eq_of_lt hmd, Nat.ne_of_gt hm0]
  by_cases hnd : n < d
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i hi
      exact hzeroSmall _ (by omega) (by omega) (by omega)
    · simp only [chainCost, sub_self, norm_zero, Finset.sum_const_zero]
      positivity
  have hdn : d ≤ n := by omega
  by_cases hnone : ∀ m, d ≤ m → m ≤ n → (Q m).roots ≠ 0
  · have hCbase : C (d - 1) = 0 := by
      dsimp only [C]
      rw [(hQ (d - 1) (by omega) (by omega)).2.1, Nat.div_eq_of_lt (by omega)]
      simp
    obtain ⟨g, hg0, hgroots, hgcost⟩ := zero_pad_charged_suffix d n 0 (d - 1) F Q hd
      (by omega) (by omega) hrow
      (fun m hm0 hm => (hQ m hm0 hm).2.2.1)
      (fun m hm0 hm => hFderiv m hm)
      (fun m hm hm' => hnone m (by omega) hm') hFdisk
      (fun m hm0 hm => hzeroSmall m hm0 (by omega) (by omega))
    refine ⟨g, ?_, le_trans ?_ hGoal⟩
    · intro i hi
      simpa only [show 0 + 1 + i = i + 1 by omega, F, p] using hgroots i (by omega)
    · change chainCost (fun i : Fin n => g i.val) ≤ 1 + (C n : ℝ)
      change chainCost (fun i : Fin n => g i.val) ≤ 1 + (C n : ℝ) - (C (d - 1) : ℝ) at hgcost
      simpa only [hCbase, Nat.cast_zero, sub_zero] using hgcost
  push Not at hnone
  obtain ⟨m, hmd, hmn, hmzero⟩ := hnone
  let S := (Finset.range (n + 1)).filter (fun m => d ≤ m ∧ (Q m).roots = 0)
  have hS : S.Nonempty := ⟨m, by simp only [S, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hmd, hmzero⟩⟩
  let j := S.max' hS
  have hjmem : j ∈ S := Finset.max'_mem _ hS
  obtain ⟨hjrange, hjd, hjzero⟩ := Finset.mem_filter.mp hjmem
  have hjn : j ≤ n := by have hh := Finset.mem_range.mp hjrange; omega
  have hj0 : 0 < j := by omega
  have hreal (b : ℕ) (hjb : j < b) (hbn : b ≤ n) : (Q b).roots ≠ 0 := by
    intro hz
    have hmem : b ∈ S := by simp only [S, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, by omega, hz⟩
    have hmax := Finset.le_max' S b hmem
    change b ≤ j at hmax
    omega
  have hCj : C j = (Q j).natDegree := by dsimp only [C]; rw [hjzero, Multiset.card_zero, Nat.sub_zero]
  by_cases hjeq : j = n
  · obtain ⟨z, hzroots, hzcost⟩ := real_compressed_rotational_prefix d r n q hd hr hdegree hdn hdisk
    have hM : n / d ≤ C n := by
      rw [hjeq, (hQ n hn le_rfl).2.1] at hCj
      omega
    have hb := rotational_quotient_budget d n (C n) (by omega) hdn hM
    refine ⟨z, hzroots, le_trans ?_ hGoal⟩
    linarith only [hzcost, hb]
  have hjlt : j < n := by omega
  obtain ⟨s, hspos, hsdeg, hshape⟩ := last_rootless_block_arithmetic d j (Q j) (Q (j + 1))
    (by omega) hjd (hQ j hj0 hjn).2.1 (hQ (j + 1) (by omega) (by omega)).2.1
    hjzero (hreal _ (by omega) (by omega)) (hstep j hj0 hjlt)
  have hCj' : C j = 2 * s := hCj.trans hsdeg
  by_cases hsone : s = 1
  · have hjexact : j = 3 * d - 1 := by norm_num [hsone] at hshape; omega
    have hn3 : 3 * d ≤ n := by omega
    obtain ⟨z, hzroots, hzcost⟩ := last_quadratic_block_chain d r n q hd hr hq hn3 hdegree hdisk Q
      (fun b hb0 hbn => ⟨(hQ b hb0 hbn).1, (hQ b hb0 hbn).2.1, (hQ b hb0 hbn).2.2.1⟩)
      hmono (by change C (3 * d - 1) = 2; rw [← hjexact]; simpa only [hsone, Nat.mul_one] using hCj')
      (fun b hbj hbn => hreal b (by simpa only [hjexact] using hbj) hbn)
    exact ⟨z, hzroots, hzcost.trans hGoal⟩
  have hs2 : 2 ≤ s := by omega
  let b := 2 * s * d
  have hjbd : j + 1 = b + d := by dsimp [b]; nlinarith only [hshape]
  have hbpos : 0 < b := by dsimp [b]; positivity
  have hbj : b < j := by omega
  have hdb : d ≤ b := by
    have hh := Nat.mul_le_mul_right d (show 1 ≤ 2 * s by omega)
    simpa only [one_mul, b] using hh
  obtain ⟨f, hfroots, hfcost⟩ := actual_rotational_prefix p n d b hdegree hd hdb (by omega) hdisk
    (Q b) (hrow b hbpos (by omega))
  have hfbound : chainCost (fun i : Fin b => f i.val) ≤ 2 * (s : ℝ) - 1 :=
    hfcost.trans (rotational_even_block_budget d s (by omega) hs2)
  obtain ⟨g, hg0, hgroots, hgcost⟩ := zero_pad_charged_suffix d n b j F Q hd hbj hjlt
    (fun a ha han => hrow a (by omega) han)
    (fun a ha han => (hQ a (by omega) han).2.2.1)
    (fun a ha han => hFderiv a han) hreal
    (fun a ha han => hFdisk a (by omega) han)
    (by
      intro a ha haj
      rw [hrow a (by omega) (by omega)]
      exact spoke_zero_inside_block d b a (Q a) (by dsimp [b]; exact dvd_mul_left d (2 * s)) ha (by omega))
  have hfunit : ‖f (b - 1)‖ ≤ 1 := by
    have hh := hfroots (b - 1) (by omega)
    exact hFdisk b hbpos (by omega) _ (by simpa only [Nat.sub_add_cancel hbpos] using hh)
  obtain ⟨z, hzroots, hzcost, hzvalue⟩ := paste_actual_chains F n b hbpos (by omega) f g hfroots hgroots
  refine ⟨z, hzroots, le_trans ?_ hGoal⟩
  rw [hzcost, hg0, zero_sub, norm_neg]
  change chainCost (fun i : Fin (n - b) => g i.val) ≤ 1 + (C n : ℝ) - (C j : ℝ) at hgcost
  rw [hCj'] at hgcost
  push_cast at hgcost
  linarith only [hfbound, hfunit, hgcost]

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem compressedRealDefectUnit {n : ℕ} (a : Fin n → ℂ) (hn : 1 ≤ n)
    (ha : ∀ i, ‖a i‖ ≤ 1) (d r : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d)
    (hp : fromRoots a = X ^ r * (q.map Complex.ofRealHom).comp (X ^ d)) :
    ∃ z : Fin n → ℂ, IsChain a z ∧
      chainCost z ≤ 1 + ((q.natDegree - q.roots.card : ℕ) : ℝ) := by
  have hrootdegree : (fromRoots a).natDegree = n := by
    simp [fromRoots, Polynomial.natDegree_prod_of_monic, Polynomial.monic_X_sub_C]
  have hdegree : (spokePoly d r q).natDegree = n := by
    rw [show spokePoly d r q = fromRoots a from hp.symm, hrootdegree]
  have hq : q.Monic := monic_of_spoke_monic d r q (by omega)
    (by rw [show spokePoly d r q = fromRoots a from hp.symm];
        exact Polynomial.monic_prod_X_sub_C a Finset.univ)
  have hdisk : ∀ w : ℂ, (spokePoly d r q).eval w = 0 → ‖w‖ ≤ 1 := by
    intro w hw
    rw [show spokePoly d r q = fromRoots a from hp.symm] at hw
    simp only [fromRoots, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at hw
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hw
    rw [sub_eq_zero.mp hi]
    exact ha i
  obtain ⟨z, hz, hcost⟩ := compressed_defect_unit_chain d r n q hd hr (by omega) hq hdegree hdisk
  refine ⟨fun i => z i.val, ?_, hcost⟩
  intro i
  rw [row, hp]
  exact hz i.val i.isLt

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution {n : ℕ} (a : Fin n → ℂ) (hn : 1 ≤ n)
    (R : ℝ) (hR : 0 ≤ R) (ha : ∀ i, ‖a i‖ ≤ R) (d r : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d)
    (hp : fromRoots a = X ^ r * (q.map Complex.ofRealHom).comp (X ^ d)) :
    ∃ z : Fin n → ℂ, IsChain a z ∧
      chainCost z ≤ (1 + ((q.natDegree - q.roots.card : ℕ) : ℝ)) * R := by
  by_cases hRzero : R = 0
  · have ha0 : a = fun _ => 0 := by
      apply _root_.funext
      intro i
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa only [hRzero] using ha i) (norm_nonneg _)
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i
      rw [row, ha0]
      have hp0 : fromRoots (fun _ : Fin n => (0 : ℂ)) = X ^ n := by simp [fromRoots]
      rw [hp0, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
      simp [Polynomial.coeff_X_pow, show n - (i.val + 1) ≠ n by omega]
    · simp [chainCost, hRzero]
  have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hRzero)
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hRzero
  let b (i : Fin n) := a i / (R : ℂ)
  let qn := C (R⁻¹ ^ n * R ^ r) * q.comp (C (R ^ d) * X)
  have hb : ∀ i, ‖b i‖ ≤ 1 := by
    intro i
    dsimp [b]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]
    exact (div_le_one hRpos).mpr (ha i)
  have hqn : qn.natDegree - qn.roots.card = q.natDegree - q.roots.card := by
    dsimp [qn]
    rw [real_defect_C_mul _ _ (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hRzero))
      (pow_ne_zero _ hRzero)), real_defect_comp_scale _ _ (pow_ne_zero _ hRzero)]
  have hbp : fromRoots b = X ^ r * (qn.map Complex.ofRealHom).comp (X ^ d) := by
    dsimp [b]
    rw [fromRoots_div_factor a (R : ℂ) hRc, hp]
    have heq := spoke_comp_scale d r n q R
    simpa only [Complex.ofReal_pow, Complex.ofReal_inv, spokePoly, qn] using heq
  obtain ⟨z, hz, hcost⟩ := compressedRealDefectUnit b hn hb d r qn hd hr hbp
  refine ⟨fun i => (R : ℂ) * z i, rescale_chain a z (R : ℂ) hRc hz, ?_⟩
  rw [chainCost_scale, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]
  rw [hqn] at hcost
  have hh := mul_le_mul_of_nonneg_left hcost hR
  linarith only [hh]
