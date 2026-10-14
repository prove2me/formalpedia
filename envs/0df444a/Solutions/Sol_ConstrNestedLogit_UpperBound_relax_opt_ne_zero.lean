-- Prove2me | solution 1 for ConstrNestedLogit.UpperBound.relax_opt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:44:14.463445+00:00
-- url     : https://prove2.me/submissions/4a714726-f0cb-4439-956c-e644f53fe7c8

import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_Relaxation
import Definitions.Def_ConstrNestedLogit_UpperBound_Relaxation
import Definitions.Def_ConstrNestedLogit_UpperBound_LP13
open NestedLogitVariants.General ConstrNestedLogit.UpperBound

private def ind {n : ℕ} (S : Finset (Fin n)) (j : Fin n) : ℝ := if j ∈ S then 1 else 0

private lemma ind_feasible {ι : Type*} {n : ℕ} (w : ι → Fin n → ℝ) (c : ι → ℝ)
    (i : ι) (S : Finset (Fin n)) (hS : SpaceFeasible w c i S) :
    RelaxFeasible w c i (ind S) := by
  constructor
  · intro j hj
    by_cases h : j ∈ S <;> simp [ind, h]
  · simpa [ind, SpaceFeasible] using hS

private lemma obj_eq {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι) (u : ℝ) (x : Fin n → ℝ) :
    relaxObj I i u x = (∑ j, I.r i j * I.v i j * x j) - u * (∑ j, I.v i j*x j) := by
  unfold relaxObj
  calc
    _ = ∑ j, ((I.r i j * I.v i j*x j) - u*(I.v i j*x j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.mul_sum]

private lemma v_pos {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι)
    (hvnp : I.vnp i = 0) (hv : ∀ j, 0 < I.v i j) (S : Finset (Fin n)) (hne : S.Nonempty) :
    0 < V I i S := by
  simp only [V, hvnp, zero_add]
  exact Finset.sum_pos (fun j hj => hv j) hne

private lemma obj_ind {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι)
    (hvnp : I.vnp i = 0) (hv : ∀ j, 0 < I.v i j) (S : Finset (Fin n)) (hne : S.Nonempty) (u : ℝ) :
    relaxObj I i u (ind S) = V I i S*(R I i S-u) := by
  have hs := ne_of_gt (v_pos I i hvnp hv S hne)
  rw [obj_eq]
  simp only [ind, mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
  unfold R
  field_simp
  simp only [V, hvnp, zero_add]

private lemma scalar_bound (a s b r z γ : ℝ) (ha : 0<a) (hs : 0<s)
    (hg : 0<γ ∧ γ≤1) (hz : z<r)
    (hopt : s*(r-(γ*z+(1-γ)*r)) ≤ a*(b-(γ*z+(1-γ)*r))) :
    s^γ*(r-z) ≤ a^γ*(b-z) := by
  have hm := Real.geom_mean_le_arith_mean2_weighted hg.1.le
    (sub_nonneg.mpr hg.2) hs.le ha.le (show γ+(1-γ)=1 by ring)
  have he : a^(1-γ)*a^γ = a := by rw [← Real.rpow_add ha]; simp
  have ht := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg ha.le γ)
  rw [mul_assoc, he] at ht
  have hlin : (γ*s+(1-γ)*a)*(r-z) ≤ a*(b-z) := by nlinarith [hopt]
  have h1 := mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr hz.le)
  have h2 := mul_le_mul_of_nonneg_right hlin (Real.rpow_nonneg ha.le γ)
  apply (mul_le_mul_iff_left₀ ha).mp
  nlinarith [h1,h2]


/-- Online Supplement A, proof of Proposition 7 (p. 34): let `S` be a nonempty assortment
satisfying the space constraint of nest `i` with `R_i(S) > z`, and put
`û = γ_i z + (1 − γ_i) R_i(S)` with `γ_i > 0`. Then the zero vector is not an optimal solution of
the linear programming relaxation of the knapsack problem (10) at `u = û`. -/
theorem solution {ι : Type*} {n : ℕ} (I : Instance ι n)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ i j, 0 < I.v i j)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι) (hγ : 0 < I.γ i)
    (S : Finset (Fin n)) (hS : SpaceFeasible w c i S) (hSne : S.Nonempty)
    (z : ℝ) (hRz : z < R I i S) :
    ¬ RelaxOptimal I w c i (I.γ i * z + (1 - I.γ i) * R I i S) 0 := by
  have hs := v_pos I i (hvnp i) (hv i) S hSne
  intro hx
  have ho := hx.2 (ind S) (ind_feasible w c i S hS)
  rw [obj_ind I i (hvnp i) (hv i) S hSne] at ho
  simp only [relaxObj, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at ho
  have hp := mul_pos hs (mul_pos hγ (sub_pos.mpr hRz))
  nlinarith [ho]


