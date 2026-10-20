-- Prove2me | solution 1 for DerivativeChainPrivate.compressedOnePairThree
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-19T05:30:09.335752+00:00
-- url     : https://prove2.me/submissions/e73fa979-359a-4936-921a-2a695a864c93

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

theorem finite_radial_extension (F : ℕ → ℂ → Prop) (n : ℕ) (a : ℂ) (ha : F 0 a)
    (hstep : ∀ i < n, ∀ w : ℂ, F i w →
      ∃ v : ℂ, F (i + 1) v ∧ ‖v - w‖ = ‖v‖ - ‖w‖) :
    ∃ z : ℕ → ℂ, z 0 = a ∧ (∀ i ≤ n, F i (z i)) ∧
      (∀ i < n, ‖z (i + 1) - z i‖ = ‖z (i + 1)‖ - ‖z i‖) := by
  induction n with
  | zero =>
    refine ⟨fun _ => a, rfl, ?_, ?_⟩
    · intro i hi
      have heq : i = 0 := by omega
      subst i
      exact ha
    · intro i hi
      omega
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

theorem compressed_stable_suffix (d n k : ℕ) (F : ℕ → Polynomial ℂ)
    (Q : ℕ → Polynomial ℝ) (hd : 2 ≤ d) (hkn : k ≤ n)
    (hrow : ∀ m, k ≤ m → m ≤ n → F m = spokePoly d (m % d) (Q m))
    (hne : ∀ m, k ≤ m → m ≤ n → Q m ≠ 0)
    (hderiv : ∀ m, k ≤ m → m < n → (F (m + 1)).derivative = F m)
    (hdefect : ∀ m, k ≤ m → m < n →
      (Q m).natDegree - (Q m).roots.card =
        (Q (m + 1)).natDegree - (Q (m + 1)).roots.card)
    (hreal : ∀ m, k < m → m ≤ n → (Q m).roots ≠ 0)
    (a : ℂ) (ha : (F k).eval a = 0) (hapower : ∃ y : ℝ, a ^ d = (y : ℂ)) :
    ∃ z : ℕ → ℂ, z 0 = a ∧
      (∀ i ≤ n - k, (F (k + i)).eval (z i) = 0 ∧ ∃ y : ℝ, (z i) ^ d = (y : ℂ)) ∧
      (∀ i < n - k, ‖z (i + 1) - z i‖ = ‖z (i + 1)‖ - ‖z i‖) := by
  apply finite_radial_extension (fun i w => (F (k + i)).eval w = 0 ∧
    ∃ y : ℝ, w ^ d = (y : ℂ)) (n - k) a (by simpa using And.intro ha hapower)
  intro i hi w hw
  have hm : k + i < n := by omega
  have heq : (spokePoly d ((k + i + 1) % d) (Q (k + i + 1))).derivative =
      spokePoly d ((k + i) % d) (Q (k + i)) := by
    rw [← hrow _ (by omega) (by omega), ← hrow _ (by omega) (by omega)]
    exact hderiv _ (by omega) hm
  have hwroot : (spokePoly d ((k + i) % d) (Q (k + i))).eval w = 0 := by
    rw [← hrow _ (by omega) (by omega)]
    exact hw.1
  obtain ⟨u, hu, hupower, hedge⟩ := spoke_stable_extension d _ _ _ _ hd
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (hne _ (by omega) (by omega)) (hne _ (by omega) (by omega)) heq
    (hdefect _ (by omega) hm) (hreal _ (by omega) (by omega)) w hwroot hw.2
  refine ⟨u, ⟨?_, hupower⟩, hedge⟩
  rw [show k + (i + 1) = k + i + 1 by omega, hrow _ (by omega) (by omega)]
  exact hu

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

theorem zero_block_stable_suffix (d n k : ℕ) (F : ℕ → Polynomial ℂ)
    (Q : ℕ → Polynomial ℝ) (hd : 2 ≤ d) (hk : 2 * d ≤ k)
    (hk3 : k < 3 * d - 1) (hkn : k < n)
    (hrow : ∀ m, 0 < m → m ≤ n → F m = spokePoly d (m % d) (Q m))
    (hne : ∀ m, 0 < m → m ≤ n → Q m ≠ 0)
    (hdegree : ∀ m, 0 < m → m ≤ n → (Q m).natDegree = m / d)
    (hderiv : ∀ m, 0 < m → m < n → (F (m + 1)).derivative = F m)
    (hdefect : ∀ m, 3 * d - 1 ≤ m → m ≤ n →
      (Q m).natDegree - (Q m).roots.card = 2)
    (hdisk : ∀ m, 0 < m → m ≤ n → ∀ w : ℂ, (F m).eval w = 0 → ‖w‖ ≤ 1) :
    ∃ g : ℕ → ℂ, g 0 = 0 ∧
      (∀ i < n - k, (F (k + 1 + i)).eval (g i) = 0) ∧
      (∀ i < n - k - 1, ‖g (i + 1) - g i‖ = ‖g (i + 1)‖ - ‖g i‖) ∧
      chainCost (fun i : Fin (n - k) => g i.val) ≤ 1 := by
  have hz (m : ℕ) (hm : k < m) (hmn : m ≤ n) (hm3 : m < 3 * d) : (F m).eval 0 = 0 := by
    rw [hrow m (by omega) hmn]
    exact spoke_zero_in_quadratic_block d m (Q m) hd (by omega) hm3
  by_cases hn3 : n < 3 * d
  · refine ⟨fun _ => 0, rfl, ?_, ?_, ?_⟩
    · intro i hi
      exact hz _ (by omega) (by omega) (by omega)
    · intro i hi; simp
    · simp [chainCost]
  have hn3' : 3 * d - 1 ≤ n := by omega
  have hreal (m : ℕ) (hm : 3 * d - 1 < m) (hmn : m ≤ n) : (Q m).roots ≠ 0 := by
    have hdeg := hdegree m (by omega) hmn
    have hdef := hdefect m (by omega) hmn
    have hdiv : 3 ≤ m / d := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr (by omega)
    intro hz
    simp only [hz, Multiset.card_zero, Nat.sub_zero] at hdef
    omega
  have hbase : (F (3 * d - 1)).eval 0 = 0 := hz _ (by omega) hn3' (by omega)
  obtain ⟨z, hz0, hzroots, hzsteps⟩ := compressed_stable_suffix d n (3 * d - 1) F Q hd hn3'
    (fun m hm hmn => hrow m (by omega) hmn)
    (fun m hm hmn => hne m (by omega) hmn)
    (fun m hm hmn => hderiv m (by omega) hmn)
    (fun m hm hmn => (hdefect m hm hmn.le).trans (hdefect (m + 1) (by omega) (by omega)).symm)
    hreal 0 hbase ⟨0, by simp [Nat.ne_of_gt (show 0 < d by omega)]⟩
  let t := 3 * d - k - 2
  let g (i : ℕ) := if i < t then 0 else z (i - t)
  have ht : k + 1 + t = 3 * d - 1 := by dsimp [t]; omega
  have hg0 : g 0 = 0 := by
    by_cases ht0 : t = 0
    · simp [g, ht0, hz0]
    · simp [g, show 0 < t by omega]
  have hgroots (i : ℕ) (hi : i < n - k) : (F (k + 1 + i)).eval (g i) = 0 := by
    by_cases hit : i < t
    · rw [show g i = 0 from if_pos hit]
      exact hz _ (by omega) (by omega) (by omega)
    · have hzi := (hzroots (i - t) (by omega)).1
      have heq : 3 * d - 1 + (i - t) = k + 1 + i := by omega
      simpa only [g, if_neg hit, heq] using hzi
  have hgsteps (i : ℕ) (hi : i < n - k - 1) :
      ‖g (i + 1) - g i‖ = ‖g (i + 1)‖ - ‖g i‖ := by
    by_cases hi1 : i + 1 < t
    · simp [g, hi1, show i < t by omega]
    · by_cases hit : i < t
      · have heq : i + 1 = t := by omega
        simp [g, hit, heq, hz0]
      · have hzi := hzsteps (i - t) (by omega)
        simpa only [g, if_neg hi1, if_neg hit,
          show i + 1 - t = i - t + 1 by omega] using hzi
  refine ⟨g, hg0, hgroots, hgsteps, ?_⟩
  rw [chainCost_of_radial_path g hgsteps, hg0, norm_zero, sub_zero]
  have heval := hgroots (n - k - 1) (by omega)
  have heq : k + 1 + (n - k - 1) = n := by omega
  rw [heq] at heval
  exact hdisk n (by omega) le_rfl _ heval

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

theorem quadratic_event_chain (d r n : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (hq : q.Monic)
    (hdegree : (spokePoly d r q).natDegree = n) (hn : 2 * d ≤ n)
    (hdisk : ∀ w : ℂ, (spokePoly d r q).eval w = 0 → ‖w‖ ≤ 1)
    (Q : ℕ → Polynomial ℝ)
    (hQ : ∀ m, 0 < m → m ≤ n →
      (Polynomial.derivative^[n - m]) (spokePoly d r q) = spokePoly d (m % d) (Q m) ∧
      (Q m).natDegree = m / d ∧ Q m ≠ 0)
    (hC : ∀ m, 2 * d ≤ m → m ≤ n → (Q m).natDegree - (Q m).roots.card = 2)
    (f : ℕ → ℂ)
    (hf : ∀ i < 2 * d - 1,
      ((Polynomial.derivative^[n - (i + 1)]) (spokePoly d r q)).eval (f i) = 0)
    (hfcost : chainCost (fun i : Fin (2 * d - 1) => f i.val) = ‖f (2 * d - 2)‖) :
    ∃ z : ℕ → ℂ,
      (∀ i < n, ((Polynomial.derivative^[n - (i + 1)]) (spokePoly d r q)).eval (z i) = 0) ∧
      chainCost (fun i : Fin n => z i.val) ≤ 3 := by
  let p := spokePoly d r q
  let F (m : ℕ) := (Polynomial.derivative^[n - m]) p
  have hFdegree (m : ℕ) (hm : m ≤ n) : (F m).natDegree = m := by
    rw [complex_iterate_natDegree, hdegree]; omega
  have hFderiv (m : ℕ) (hm : m < n) : (F (m + 1)).derivative = F m := by
    dsimp [F]
    rw [show n - m = n - (m + 1) + 1 by omega, Function.iterate_succ_apply']
  have hFdisk (m : ℕ) (hm0 : 0 < m) (hm : m ≤ n) :
      ∀ w : ℂ, (F m).eval w = 0 → ‖w‖ ≤ 1 := actual_row_unit_roots p n hdegree hdisk m hm0 hm
  have hrow (m : ℕ) (hm0 : 0 < m) (hm : m ≤ n) : F m = spokePoly d (m % d) (Q m) :=
    (hQ m hm0 hm).1
  have hdeg2 : (Q (2 * d)).natDegree = 2 := by
    rw [(hQ (2 * d) (by omega) hn).2.1, Nat.mul_div_cancel _ (by omega : 0 < d)]
  have hreal : (Q (2 * d)).roots.card = 0 := by
    have h := hC (2 * d) le_rfl hn
    rw [hdeg2] at h
    omega
  obtain ⟨c, A, B, hc, hdisc, hshape⟩ := real_quadratic_no_real_shape (Q (2 * d)) hdeg2 hreal
  have hpolyshape : F (2 * d) =
      C (c : ℂ) * (X ^ (2 * d) + C (A : ℂ) * X ^ d + C (B : ℂ)) := by
    rw [hrow _ (by omega) hn, show 2 * d % d = 0 by simp, hshape, spoke_quadratic_shape]
  have hchild : (F (2 * d)).derivative.eval (f (2 * d - 2)) = 0 := by
    have hh := hFderiv (2 * d - 1) (by omega)
    rw [show 2 * d - 1 + 1 = 2 * d by omega] at hh
    rw [hh]
    have hh := hf (2 * d - 2) (by omega)
    simpa only [show 2 * d - 2 + 1 = 2 * d - 1 by omega] using hh
  obtain ⟨w, hw, hs⟩ := derivative_supporting_parent (F (2 * d))
    (by rw [hFdegree _ hn]; omega) (f (2 * d - 2)) hchild
  have hdetour := equal_radius_detour w (f (2 * d - 2)) hs
  have hwunit : ‖w‖ ≤ 1 := hFdisk (2 * d) (by omega) hn w hw
  have hsqrt : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by apply Real.sqrt_le_iff.mpr; norm_num
  obtain ⟨h, hhroots, hhcost, hhvalue⟩ := paste_actual_chains F (2 * d) (2 * d - 1)
    (by omega) (by omega) f (fun _ => w) hf (by
      intro i hi
      have hi0 : i = 0 := by omega
      simpa only [hi0, add_zero, show 2 * d - 1 + 1 = 2 * d by omega] using hw)
  have hhbound : chainCost (fun i : Fin (2 * d) => h i.val) ≤ Real.sqrt 2 * ‖w‖ := by
    rw [hhcost, hfcost]
    simpa [chainCost, Nat.sub_sub] using hdetour
  by_cases hnevent : n = 2 * d
  · refine ⟨h, ?_, ?_⟩
    · simpa only [F, p, hnevent] using hhroots
    · rw [hnevent]
      nlinarith only [hhbound, hwunit, hsqrt, norm_nonneg w, Real.sqrt_nonneg 2]
  have hnlarge : 2 * d < n := by omega
  have htail : ∃ g : ℕ → ℂ, g 0 = 0 ∧
      (∀ i < n - 2 * d, (F (2 * d + 1 + i)).eval (g i) = 0) ∧
      chainCost (fun i : Fin (n - 2 * d) => g i.val) ≤ (if n < 3 * d then 0 else 1) := by
    by_cases hn3 : n < 3 * d
    · refine ⟨fun _ => 0, rfl, ?_, ?_⟩
      · intro i hi
        rw [hrow _ (by omega) (by omega)]
        exact spoke_zero_in_quadratic_block d _ _ hd (by omega) (by omega)
      · simp [hn3, chainCost]
    · obtain ⟨g, hg0, hgroots, hgsteps, hgcost⟩ := zero_block_stable_suffix d n (2 * d) F Q hd
        le_rfl (by omega) hnlarge hrow
        (fun m hm0 hm => (hQ m hm0 hm).2.2)
        (fun m hm0 hm => (hQ m hm0 hm).2.1)
        (fun m hm0 hm => hFderiv m hm)
        (fun m hm hm' => hC m (by omega) hm') hFdisk
      exact ⟨g, hg0, hgroots, by simpa [hn3] using hgcost⟩
  obtain ⟨g, hg0, hgroots, hgcost⟩ := htail
  obtain ⟨z, hzroots, hzcost, hzvalue⟩ := paste_actual_chains F n (2 * d) (by omega) hnlarge h g hhroots hgroots
  refine ⟨z, hzroots, ?_⟩
  have hhend : h (2 * d - 1) = w := by
    rw [hhvalue]
    simp
  rw [hzcost, hg0, hhend, zero_sub, norm_neg]
  by_cases hn3 : n < 3 * d
  · rw [if_pos hn3] at hgcost
    nlinarith only [hhbound, hgcost, hwunit, hsqrt, norm_nonneg w, Real.sqrt_nonneg 2]
  · rw [if_neg hn3] at hgcost
    have hM : 3 ≤ q.natDegree := by
      have hdeg := spoke_natDegree d r q hq.ne_zero (by omega)
      rw [hdegree] at hdeg
      by_contra h
      have hMq : q.natDegree ≤ 2 := by omega
      have hmul := Nat.mul_le_mul_left d hMq
      omega
    have hndeg : r + d * q.natDegree = n := by
      rw [← spoke_natDegree d r q hq.ne_zero (by omega), hdegree]
    have hwsmall : ‖w‖ ≤ 4 / 5 :=
      compressed_quadratic_row_radius d r q hd hq hM hdisk A B hdisc (c : ℂ)
        (Complex.ofReal_ne_zero.mpr hc) (by simpa only [hndeg] using hpolyshape) w
        (by simpa only [hndeg] using hw)
    have hbudget := compressed_quadratic_detour_budget ‖w‖ 1
      (chainCost (fun i : Fin (2 * d) => h i.val)) (norm_nonneg _)
      (by simpa using hwsmall) hhbound
    linarith

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem compressed_one_pair_unit_chain (d r n : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (hn : 0 < n) (hq : q.Monic)
    (hdegree : (spokePoly d r q).natDegree = n)
    (hdefect : q.natDegree - q.roots.card ≤ 2)
    (hdisk : ∀ w : ℂ, (spokePoly d r q).eval w = 0 → ‖w‖ ≤ 1) :
    ∃ z : ℕ → ℂ,
      (∀ i < n, ((Polynomial.derivative^[n - (i + 1)]) (spokePoly d r q)).eval (z i) = 0) ∧
      chainCost (fun i : Fin n => z i.val) ≤ 3 := by
  let p := spokePoly d r q
  let F (m : ℕ) := (Polynomial.derivative^[n - m]) p
  obtain ⟨Q, hQ, hstep⟩ := compressed_row_family d r q hd hr n hdegree
  let C (m : ℕ) := (Q m).natDegree - (Q m).roots.card
  have hrow (m : ℕ) (hm0 : 0 < m) (hm : m ≤ n) : F m = spokePoly d (m % d) (Q m) :=
    (hQ m hm0 hm).1
  have hbound (m : ℕ) (hm0 : 0 < m) (hm : m ≤ n) : C m ≤ 2 :=
    ((hQ m hm0 hm).2.2.2).trans hdefect
  have hcases (m : ℕ) (hm0 : 0 < m) (hm : m ≤ n) : C m = 0 ∨ C m = 2 :=
    real_root_defect_zero_or_two (Q m) (hbound m hm0 hm)
  have hmono (i j : ℕ) (hi0 : 0 < i) (hij : i ≤ j) (hjn : j ≤ n) : C i ≤ C j := by
    revert hjn
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hij ih =>
      intro hjn
      exact (ih (by omega)).trans (hstep j (by omega) (by omega))
  have hFderiv (m : ℕ) (hm : m < n) : (F (m + 1)).derivative = F m := by
    dsimp [F]
    rw [show n - m = n - (m + 1) + 1 by omega, Function.iterate_succ_apply']
  have hFdisk (m : ℕ) (hm0 : 0 < m) (hm : m ≤ n) :
      ∀ w : ℂ, (F m).eval w = 0 → ‖w‖ ≤ 1 := actual_row_unit_roots p n hdegree hdisk m hm0 hm
  by_cases hCn : C n = 0
  · have hsplit : (Q n).Splits := by
      apply Polynomial.splits_iff_card_roots.mpr
      have hc := Polynomial.card_roots' (Q n)
      dsimp only [C] at hCn
      omega
    obtain ⟨z, hz0, hzroots, hzsteps, hzcost⟩ := actual_real_compressed_prefix p n d n hdegree
      hd hn le_rfl (Q n) (hQ n hn le_rfl).2.2.1 hsplit (hrow n hn le_rfl)
    refine ⟨z, hzroots, ?_⟩
    rw [hzcost]
    have hh := hzroots (n - 1) (by omega)
    have heq : n - 1 + 1 = n := by omega
    have hnorm := hFdisk n hn le_rfl (z (n - 1)) (by simpa only [heq] using hh)
    linarith
  have hex : ∃ j, 0 < j ∧ j ≤ n ∧ C j = 2 := by
    exact ⟨n, hn, le_rfl, (hcases n hn le_rfl).resolve_left hCn⟩
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  change 0 < j ∧ j ≤ n ∧ C j = 2 at hj
  have hbefore (m : ℕ) (hm0 : 0 < m) (hmj : m < j) : C m = 0 := by
    rcases hcases m hm0 (by omega) with hh | hh
    · exact hh
    · exact False.elim ((Nat.find_min hex hmj) ⟨hm0, by omega, hh⟩)
  have hafter (m : ℕ) (hjm : j ≤ m) (hm : m ≤ n) : C m = 2 := by
    have hlo := hmono j m hj.1 hjm hm
    have hhi := hbound m (by omega) hm
    rw [hj.2.2] at hlo
    omega
  have hj2 : 2 * d ≤ j := by
    have hdeg := (hQ j hj.1 hj.2.1).2.1
    have hc := hj.2.2
    dsimp only [C] at hc
    have hdiv : 2 ≤ j / d := by omega
    exact (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hdiv
  have hsplit : (Q (j - 1)).Splits := by
    apply Polynomial.splits_iff_card_roots.mpr
    have hzero := hbefore (j - 1) (by omega) (by omega)
    have hc := Polynomial.card_roots' (Q (j - 1))
    dsimp only [C] at hzero
    omega
  obtain ⟨f, hf0, hf, hfsteps, hfcost⟩ := actual_real_compressed_prefix p n d (j - 1) hdegree
    hd (by omega) (by omega) (Q (j - 1)) (hQ (j - 1) (by omega) (by omega)).2.2.1 hsplit
    (hrow (j - 1) (by omega) (by omega))
  have hfcost' : chainCost (fun i : Fin (j - 1) => f i.val) = ‖f (j - 2)‖ := by
    simpa only [Nat.sub_sub] using hfcost
  have hfunit : ‖f (j - 2)‖ ≤ 1 := by
    have hh := hf (j - 2) (by omega)
    exact hFdisk (j - 1) (by omega) (by omega) _
      (by simpa only [show j - 2 + 1 = j - 1 by omega] using hh)
  by_cases hjeq : j = 2 * d
  · rw [hjeq] at hfcost'
    exact quadratic_event_chain d r n q hd hr hq hdegree (by omega) hdisk Q
      (fun m hm0 hm => ⟨(hQ m hm0 hm).1, (hQ m hm0 hm).2.1, (hQ m hm0 hm).2.2.1⟩)
      (fun m hm hm' => hafter m (by omega) hm') f
      (by simpa only [hjeq] using hf) hfcost'
  have hjlarge : 2 * d < j := by omega
  by_cases hj3 : j < 3 * d
  · obtain ⟨g, hg0, hg, hgsteps, hgcost⟩ := zero_block_stable_suffix d n (j - 1) F Q hd
      (by omega) (by omega) (by omega) hrow
      (fun m hm0 hm => (hQ m hm0 hm).2.2.1)
      (fun m hm0 hm => (hQ m hm0 hm).2.1)
      (fun m hm0 hm => hFderiv m hm)
      (fun m hm hm' => hafter m (by omega) hm') hFdisk
    obtain ⟨z, hz, hcost, hzvalue⟩ := paste_actual_chains F n (j - 1) (by omega) (by omega) f g hf hg
    refine ⟨z, hz, ?_⟩
    rw [hcost, hfcost', hg0, zero_sub, norm_neg,
      show j - 1 - 1 = j - 2 by omega]
    linarith
  have hreal (m : ℕ) (hjm : j ≤ m) (hm : m ≤ n) : (Q m).roots ≠ 0 := by
    have hdeg := (hQ m (by omega) hm).2.1
    have hc := hafter m hjm hm
    have hdiv : 3 ≤ m / d := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr (by omega)
    intro hz
    dsimp only [C] at hc
    simp only [hz, Multiset.card_zero, Nat.sub_zero] at hc
    omega
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero (hreal j le_rfl hj.2.1)
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ) (by omega : 0 < d)
  have haroot : (F j).eval a = 0 := by
    rw [hrow j hj.1 hj.2.1, spoke_eval_real_power d (j % d) (Q j) a x ha,
      Polynomial.isRoot_of_mem_roots hx, Complex.ofReal_zero, mul_zero]
  obtain ⟨g, hg0, hgroots, hgsteps⟩ := compressed_stable_suffix d n j F Q hd hj.2.1
    (fun m hm hm' => hrow m (by omega) hm')
    (fun m hm hm' => (hQ m (by omega) hm').2.2.1)
    (fun m hm hm' => hFderiv m hm')
    (fun m hm hm' => (hafter m hm hm'.le).trans (hafter (m + 1) (by omega) (by omega)).symm)
    (fun m hm hm' => hreal m hm.le hm') a haroot ⟨x, ha⟩
  have hgcost : chainCost (fun i : Fin (n - (j - 1)) => g i.val) = ‖g (n - j)‖ - ‖g 0‖ := by
    rw [chainCost_of_radial_path g (by intro i hi; exact hgsteps i (by omega)),
      show n - (j - 1) - 1 = n - j by omega]
  have hgend : ‖g (n - j)‖ ≤ 1 := by
    have hh := (hgroots (n - j) le_rfl).1
    have heq : j + (n - j) = n := by omega
    rw [heq] at hh
    exact hFdisk n hn le_rfl _ hh
  obtain ⟨z, hz, hcost, hzvalue⟩ := paste_actual_chains F n (j - 1) (by omega) (by omega) f g hf
    (by
      intro i hi
      have hh := (hgroots i (by omega)).1
      simpa only [show j - 1 + 1 + i = j + i by omega] using hh)
  refine ⟨z, hz, ?_⟩
  rw [hcost, hfcost', hgcost, show j - 1 - 1 = j - 2 by omega]
  have htriangle := norm_sub_le (g 0) (f (j - 2))
  linarith

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution {n : ℕ} (a : Fin n → ℂ) (hn : 1 ≤ n)
    (ha : ∀ i, ‖a i‖ ≤ 1) (d r : ℕ) (q : Polynomial ℝ)
    (hd : 2 ≤ d) (hr : r < d) (hc : q.natDegree - q.roots.card ≤ 2)
    (hp : fromRoots a = X ^ r * (q.map Complex.ofRealHom).comp (X ^ d)) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ chainCost z ≤ 3 := by
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
  obtain ⟨z, hz, hcost⟩ := compressed_one_pair_unit_chain d r n q hd hr (by omega)
    hq hdegree hc hdisk
  refine ⟨fun i => z i.val, ?_, hcost⟩
  intro i
  rw [row, hp]
  exact hz i.val i.isLt
