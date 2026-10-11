-- Prove2me | solution 1 for ConservationLaws.nbody_momentum_and_energy_conservation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T22:36:14.264775+00:00
-- url     : https://prove2.me/submissions/0d9495bc-4fc8-47bd-8297-74d3c3bf826e

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false
theorem solution {d N : ℕ} (m : Fin N → ℝ) (hm : ∀ i, 0 < m i)
    (φ : Fin N → Fin N → ℝ → ℝ) (hφsym : ∀ i j, φ i j = φ j i)
    (hφdiff : ∀ i j, ∀ r : ℝ, 0 < r → DifferentiableAt ℝ (φ i j) r)
    (x v a : Fin N → ℝ → EuclideanSpace ℝ (Fin d))
    (hnc : ∀ t i j, i ≠ j → x i t ≠ x j t)
    (hx : ∀ i t, HasDerivAt (x i) (v i t) t)
    (hv : ∀ i t, HasDerivAt (v i) (a i t) t)
    (hnewton : ∀ i t, m i • a i t = ∑ j ∈ Finset.univ.erase i,
      (-(deriv (φ i j) ‖x i t - x j t‖) / ‖x i t - x j t‖) • (x i t - x j t)) :
    (∀ t s, ∑ i, m i • v i t = ∑ i, m i • v i s) ∧
    (∀ t s, (∑ i, (1 / 2 : ℝ) * m i * ‖v i t‖ ^ 2 +
      ∑ i, ∑ j ∈ Finset.Ioi i, φ i j ‖x i t - x j t‖) =
      (∑ i, (1 / 2 : ℝ) * m i * ‖v i s‖ ^ 2 +
      ∑ i, ∑ j ∈ Finset.Ioi i, φ i j ‖x i s - x j s‖)) := by
  classical
  let R (i j : Fin N) (t : ℝ) := ‖x i t - x j t‖
  let G (i j : Fin N) (t : ℝ) : EuclideanSpace ℝ (Fin d) := if i = j then 0 else (-(deriv (φ i j) (R i j t)) / R i j t) • (x i t - x j t)
  have hg (i j : Fin N) (t : ℝ) : G i j t = -G j i t := by
    by_cases hij : i = j
    · subst j; simp [G]
    · have hji : j ≠ i := Ne.symm hij
      have hr : R i j t = R j i t := by simp [R, norm_sub_rev]
      simp only [G, if_neg hij, if_neg hji]
      rw [← hr, ← hφsym i j]; apply (eq_neg_iff_add_eq_zero).2
      rw [← smul_add]
      have hcancel : (x i t - x j t) + (x j t - x i t) = 0 := by abel
      simpa [hcancel]
  have hGnew (i : Fin N) (t : ℝ) : m i • a i t = ∑ j, G i j t := by
    rw [hnewton]
    have hterm : (∑ j ∈ Finset.univ.erase i, (-(deriv (φ i j) (R i j t)) / R i j t) • (x i t - x j t)) = (∑ j ∈ Finset.univ.erase i, G i j t) := by
      apply Finset.sum_congr rfl; intro j hj
      have hne : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
      simp [G, hne]
    change (∑ j ∈ Finset.univ.erase i, (-(deriv (φ i j) (R i j t)) / R i j t) • (x i t - x j t)) = _
    rw [hterm]
    have hh := Finset.sum_erase_add (s := Finset.univ) (f := fun j => G i j t) (Finset.mem_univ i)
    simpa [G] using hh
  have hpforce (t : ℝ) : (∑ i, ∑ j, G i j t) = 0 := by
    let B : EuclideanSpace ℝ (Fin d) := ∑ i, ∑ j, G i j t
    have hn : B = -B := by
      calc
        B = ∑ i, ∑ j, -(G j i t) := by
          apply Finset.sum_congr rfl; intro i hi
          apply Finset.sum_congr rfl; intro j hj; exact hg i j t
        _ = -(∑ i, ∑ j, G j i t) := by simp
        _ = -B := by congr 1; exact Finset.sum_comm
    have htwo : (2 : ℝ) • B = 0 := by
      calc
        (2 : ℝ) • B = B + B := by
          rw [show (2 : ℝ) = 1 + 1 by norm_num, add_smul, one_smul]
        _ = B + -B := congrArg (fun z => B + z) hn
        _ = 0 := add_neg_cancel B
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
  have hpd (t : ℝ) : HasDerivAt (fun q => ∑ i, m i • v i q) 0 t := by
    have hh : HasDerivAt (fun q => ∑ i, m i • v i q) (∑ i, m i • a i t) t := by
      apply HasDerivAt.fun_sum; intro i hi; exact (hv i t).const_smul (m i)
    have hz : (∑ i, m i • a i t) = 0 := by
      calc
        _ = ∑ i, ∑ j, G i j t := by
          apply Finset.sum_congr rfl; intro i hi; exact hGnew i t
        _ = 0 := hpforce t
    simpa only [hz] using hh
  have hpc (t s : ℝ) : (∑ i, m i • v i t) = ∑ i, m i • v i s :=
    is_const_of_deriv_eq_zero (fun q => (hpd q).differentiableAt) (fun q => (hpd q).deriv) t s
  have hR (i j : Fin N) (t : ℝ) (hij : i ≠ j) : HasDerivAt (R i j) (inner ℝ (x i t - x j t) (v i t - v j t) / R i j t) t := by
    have hrne : R i j t ≠ 0 := by
      have he : x i t - x j t ≠ 0 := sub_ne_zero.mpr (hnc t i j hij)
      exact norm_ne_zero_iff.mpr he
    have hsq := ((hx i t).sub (hx j t)).norm_sq
    have hsqrt := hsq.sqrt (by simpa [R] using pow_ne_zero 2 hrne)
    convert hsqrt using 1
    · ext q; simp [R, Real.sqrt_sq_eq_abs]
    · simp only [Real.sqrt_sq_eq_abs, abs_norm]
      dsimp [R] at hrne ⊢
      field_simp [hrne]
  have hUd (t : ℝ) : HasDerivAt
      (fun q => ∑ i, ∑ j ∈ Finset.Ioi i, φ i j (R i j q))
      (∑ i, ∑ j ∈ Finset.Ioi i,
        deriv (φ i j) (R i j t) *
          (inner ℝ (x i t - x j t) (v i t - v j t) / R i j t)) t := by
    apply HasDerivAt.fun_sum; intro i hi
    apply HasDerivAt.fun_sum; intro j hj
    have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
    have hrp : 0 < R i j t := norm_pos_iff.mpr (sub_ne_zero.mpr (hnc t i j hij))
    have hd := (hφdiff i j (R i j t) hrp).hasDerivAt.comp t (hR i j t hij)
    simpa only [Function.comp_def] using hd
  have hKd (t : ℝ) : HasDerivAt (fun q => ∑ i, (1 / 2 : ℝ) * m i * ‖v i q‖ ^ 2)
      (∑ i, inner ℝ (m i • a i t) (v i t)) t := by
    apply HasDerivAt.fun_sum; intro i hi
    have hk := ((hv i t).norm_sq).const_mul ((1 / 2 : ℝ) * m i)
    have heq : ((1 / 2 : ℝ) * m i) * (2 * inner ℝ (v i t) (a i t)) =
        inner ℝ (m i • a i t) (v i t) := by
      calc
        _ = m i * inner ℝ (v i t) (a i t) := by ring
        _ = inner ℝ (m i • a i t) (v i t) := by simp [real_inner_comm, inner_smul_left]
    rw [heq] at hk
    exact hk
  have hpair (t : ℝ) : (∑ i, inner ℝ (m i • a i t) (v i t)) =
      -(∑ i, ∑ j ∈ Finset.Ioi i, deriv (φ i j) (R i j t) *
        (inner ℝ (x i t - x j t) (v i t - v j t) / R i j t)) := by
    calc
      _ = ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (G i j t) (v i t) := by
        apply Finset.sum_congr rfl; intro i hi
        rw [hGnew i t, sum_inner]
        have hh := Finset.sum_erase_add (s := Finset.univ)
          (f := fun j => inner ℝ (G i j t) (v i t)) (Finset.mem_univ i)
        simpa [G] using hh.symm
      _ = ∑ i, ∑ j ∈ Finset.Ioi i, inner ℝ (G i j t) (v i t - v j t) := by
        have hc := Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag (f := fun i j : Fin N => inner ℝ (G j i t) (v j t))
        simp only [Finset.compl_singleton] at hc
        rw [← hc]
        apply Finset.sum_congr rfl; intro i hi
        apply Finset.sum_congr rfl; intro j hj
        rw [hg j i t]
        rw [inner_sub_right]
        simp only [inner_neg_left, sub_eq_add_neg]
      _ = _ := by
        simp only [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro i hi
        apply Finset.sum_congr rfl; intro j hj
        have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
        simp only [G, if_neg hij, real_inner_smul_left]
        ring
  let KE : ℝ → ℝ := fun q => ∑ i, (1 / 2 : ℝ) * m i * ‖v i q‖ ^ 2
  let PE : ℝ → ℝ := fun q => ∑ i, ∑ j ∈ Finset.Ioi i, φ i j (R i j q)
  have hz (q : ℝ) : deriv (KE + PE) q = 0 := by
    have hh := (hKd q).add (hUd q)
    rw [hpair q] at hh; have he := hh.deriv
    simpa only [KE, PE, neg_add_cancel] using he
  have hdiff : Differentiable ℝ (KE + PE) := fun q => ((hKd q).add (hUd q)).differentiableAt
  refine ⟨hpc, ?_⟩
  intro t s
  have he := is_const_of_deriv_eq_zero hdiff hz t s
  simpa only [KE, PE, Pi.add_apply] using he
