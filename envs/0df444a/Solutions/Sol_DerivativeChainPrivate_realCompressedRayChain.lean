-- Prove2me | solution 1 for DerivativeChainPrivate.realCompressedRayChain
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-18T06:02:26.232881+00:00
-- url     : https://prove2.me/submissions/046e7a4c-8093-4ba1-903c-f3622614a1b6

import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
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

theorem real_compressed_ray_chain {n : ℕ} (a : Fin n → ℂ) (hn : 1 ≤ n)
    (ha : ∀ i, ‖a i‖ ≤ 1) (k r : ℕ) (q : Polynomial ℝ)
    (hk : 2 ≤ k) (hr : r < k) (hq : q.Splits)
    (hp : fromRoots a = spokePoly k r q) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ chainCost z ≤ 1 := by
  classical
  have hpdeg : (fromRoots a).natDegree = n := by
    simp [fromRoots, Polynomial.natDegree_prod_of_monic, Polynomial.monic_X_sub_C]
  have hqne : q ≠ 0 := by
    intro hzero
    rw [hp, hzero] at hpdeg
    simp [spokePoly] at hpdeg
    omega
  obtain ⟨z, hz0, hzroots, hzsteps⟩ :=
    spoke_geodesic (n - 1) k r q hk hr hq hqne (by rw [← hp, hpdeg]; omega)
  refine ⟨fun i => z i.val, ?_, ?_⟩
  · intro i
    have h := hzroots i.val (by omega)
    have hexp : n - 1 - i.val = n - (i.val + 1) := by omega
    simpa only [row, hp, hexp] using h
  · have hend : (fromRoots a).eval (z (n - 1)) = 0 := by
      have h := hzroots (n - 1) (by omega)
      simpa [← hp] using h
    simp only [fromRoots, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at hend
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hend
    have hnorm : ‖z (n - 1)‖ ≤ 1 := by rw [sub_eq_zero.mp hi]; exact ha i
    calc
      chainCost (fun i : Fin n => z i.val) =
          ∑ i : Fin (n - 1), (‖z (i.val + 1)‖ - ‖z i.val‖) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hzsteps i.val i.isLt
      _ = ‖z (n - 1)‖ - ‖z 0‖ := by
        rw [Fin.sum_univ_eq_sum_range (fun i => ‖z (i + 1)‖ - ‖z i‖)]
        exact Finset.sum_range_sub (fun i => ‖z i‖) (n - 1)
      _ ≤ 1 := by simpa [hz0] using hnorm

end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution {n : ℕ} (a : Fin n → ℂ) (hn : 1 ≤ n)
    (ha : ∀ i, ‖a i‖ ≤ 1) (k r : ℕ) (q : Polynomial ℝ)
    (hk : 2 ≤ k) (hr : r < k) (hq : q.Splits)
    (hp : fromRoots a = Polynomial.X ^ r *
      (q.map Complex.ofRealHom).comp (Polynomial.X ^ k)) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ chainCost z ≤ 1 := by
  exact real_compressed_ray_chain a hn ha k r q hk hr hq hp
