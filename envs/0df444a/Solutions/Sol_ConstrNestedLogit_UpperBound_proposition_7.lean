-- Prove2me | solution 1 for ConstrNestedLogit.UpperBound.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:44:30.902635+00:00
-- url     : https://prove2.me/submissions/c748be7e-c628-431b-b202-12f0fe4a96f4

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


private theorem y_nonneg_local {ι : Type*} [Fintype ι] {n : ℕ} (I : Instance ι n)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ i j, 0 < I.v i j) (hγ : ∀ i, 0 < I.γ i)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (X : ι → Finset (Fin n → ℝ))
    (hw : ∀ i j, 0 < w i j) (hwc : ∀ i j, w i j ≤ c i)
    (hX : IsRelaxSolutionFamily I w c X) (z : ℝ) (y : ι → ℝ) (hzy : LP13Feasible I X z y) :
    ∀ i, 0 ≤ y i := by   classical
  intro i
  let u : ℝ := 1 + ∑ j, |I.r i j|
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hur (j : Fin n) : I.r i j < u := by
    have hs := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => abs_nonneg (I.r i k))
      (Finset.mem_univ j)
    dsimp [u]
    linarith [le_abs_self (I.r i j)]
  obtain ⟨x, hxX, hx⟩ := hX.2 i u hu
  have hxn (j : Fin n) : 0 ≤ x j := (hx.1.1 j (Set.mem_univ j)).1
  have hc : 0 ≤ c i := le_trans (Finset.sum_nonneg (fun j hj => mul_nonneg (hw i j).le (hxn j))) hx.1.2
  have hzero : RelaxFeasible w c i 0 := by
    constructor
    · intro j hj; simp
    · simpa using hc
  have ho := hx.2 0 hzero
  simp only [relaxObj, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at ho
  have hn (j : Fin n) (_ : j ∈ Finset.univ) : I.v i j*(I.r i j-u)*x j ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (hv i j).le (sub_nonpos.mpr (hur j).le)) (hxn j)
  have hs : (∑ j, I.v i j*(I.r i j-u)*x j) = 0 := le_antisymm (Finset.sum_nonpos hn) ho
  have hx0 : x = 0 := by
    funext j
    have hj := (Finset.sum_eq_zero_iff_of_nonpos hn).mp hs j (Finset.mem_univ j)
    exact (mul_eq_zero.mp hj).resolve_left (mul_ne_zero (ne_of_gt (hv i j)) (ne_of_lt (sub_neg.mpr (hur j))))
  rw [hx0] at hxX
  have hy := hzy.2 i 0 hxX
  simpa [F, hvnp i, Real.zero_rpow (ne_of_gt (hγ i))] using hy




private theorem nonzero_local {ι : Type*} {n : ℕ} (I : Instance ι n)
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




private theorem key_local {ι : Type*} {n : ℕ} (I : Instance ι n)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ i j, 0 < I.v i j)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι) (hγ : 0 < I.γ i ∧ I.γ i ≤ 1)
    (S : Finset (Fin n)) (hS : SpaceFeasible w c i S) (hSne : S.Nonempty)
    (z : ℝ) (hRz : z < R I i S) (x : Fin n → ℝ)
    (hx : RelaxOptimal I w c i (I.γ i * z + (1 - I.γ i) * R I i S) x) (hx0 : x ≠ 0) :
    nestWeight I i S * (R I i S - z) ≤ F I i x z := by
  classical
  have hxn (j : Fin n) : 0 ≤ x j := (hx.1.1 j (Set.mem_univ j)).1
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra! h
    apply hx0
    funext j
    exact h j
  have hap : 0 < ∑ j, I.v i j*x j := by
    apply Finset.sum_pos' (fun j hj => mul_nonneg (hv i j).le (hxn j))
    exact ⟨j, Finset.mem_univ j, mul_pos (hv i j) (lt_of_le_of_ne (hxn j) (Ne.symm hj))⟩
  let a := ∑ j, I.v i j*x j
  let b := (∑ j, I.r i j*I.v i j*x j) / a
  have ha : 0<a := hap
  have hb : a*b = ∑ j, I.r i j*I.v i j*x j := by dsimp [b]; field_simp
  have hs := v_pos I i (hvnp i) (hv i) S hSne
  have ho := hx.2 (ind S) (ind_feasible w c i S hS)
  rw [obj_ind I i (hvnp i) (hv i) S hSne, obj_eq] at ho
  have hlo : V I i S*(R I i S-(I.γ i*z+(1-I.γ i)*R I i S)) ≤
      a*(b-(I.γ i*z+(1-I.γ i)*R I i S)) := by
    dsimp only [a] at hb ⊢
    nlinarith [ho, hb]
  have h := scalar_bound a (V I i S) b (R I i S) z (I.γ i) ha hs hγ hRz hlo
  simpa [nestWeight, F, hvnp i, a, b] using h




/-- Online Supplement A, the claim in the proof of Proposition 7 (pp. 33–34): if the vectors `X i`
are feasible for the linear programming relaxation of (10) and include an optimal solution of that
relaxation for every `u ≥ 0`, then every feasible solution `(z, y)` of the linear program (13)
satisfies `y_i ≥ V_i(S_i)^{γ_i} (R_i(S_i) − z)` for every nest `i` and every assortment
`(S_1, …, S_m)` that satisfies the space constraints. -/
private theorem claim_local {ι : Type*} [Fintype ι] {n : ℕ} (I : Instance ι n)
    (hvnp : ∀ i, I.vnp i = 0) (hv0 : 0 < I.v0) (hv : ∀ i j, 0 < I.v i j)
    (hγ : ∀ i, 0 < I.γ i ∧ I.γ i ≤ 1)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (X : ι → Finset (Fin n → ℝ))
    (hw : ∀ i j, 0 < w i j) (hwc : ∀ i j, w i j ≤ c i)
    (hX : IsRelaxSolutionFamily I w c X)
    (S : ι → Finset (Fin n)) (hS : ∀ i, SpaceFeasible w c i (S i))
    (z : ℝ) (y : ι → ℝ) (hzy : LP13Feasible I X z y) :
    ∀ i, nestWeight I i (S i) * (R I i (S i) - z) ≤ y i := by 
  classical
  have hyn := y_nonneg_local I hvnp hv (fun i => (hγ i).1) w c X hw hwc hX z y hzy
  have hz0 : 0 ≤ z := by
    have hy0 : 0 ≤ ∑ i, y i := Finset.sum_nonneg (fun i hi => hyn i)
    have hp : 0 ≤ I.v0*z := hy0.trans hzy.1
    exact nonneg_of_mul_nonneg_right hp hv0
  intro i
  by_cases hsne : (S i).Nonempty
  · by_cases hzR : z < R I i (S i)
    · have hR0 : 0 ≤ R I i (S i) := hz0.trans hzR.le
      have hu : 0 ≤ I.γ i*z+(1-I.γ i)*R I i (S i) :=
        add_nonneg (mul_nonneg (hγ i).1.le hz0) (mul_nonneg (sub_nonneg.mpr (hγ i).2) hR0)
      obtain ⟨x, hxX, hx⟩ := hX.2 i _ hu
      have hx0 : x ≠ 0 := by
        intro h
        subst x
        exact nonzero_local I hvnp hv w c i (hγ i).1 (S i) (hS i) hsne z hzR hx
      exact (key_local I hvnp hv w c i (hγ i) (S i) (hS i) hsne z hzR x hx hx0).trans (hzy.2 i x hxX)
    · have hp : 0 ≤ nestWeight I i (S i) :=
        Real.rpow_nonneg (v_pos I i (hvnp i) (hv i) (S i) hsne).le _
      exact (mul_nonpos_of_nonneg_of_nonpos hp (sub_nonpos.mpr (le_of_not_gt hzR))).trans (hyn i)
  · have he : S i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsne
    simpa [nestWeight, V, he, hvnp i, Real.zero_rpow (ne_of_gt (hγ i).1)] using hyn i




/-- Proposition 7 (Online Supplement A, p. 33): under space constraints, if the vectors `X i`
(the paper's `{x_i^g : g ∈ G_i}`) are feasible for the linear programming relaxation of the
knapsack problem (10) and include an optimal solution of that relaxation for every `u ≥ 0`, and
`(ẑ, ŷ)` is an optimal solution of the linear program (13), then `ẑ ≥ Z*`, where
`Z* = Π(S*_1, …, S*_m)` is the optimal expected revenue of problem (1). -/
theorem solution {ι : Type*} [Fintype ι] {n : ℕ} (I : Instance ι n)
    (hvnp : ∀ i, I.vnp i = 0) (hv0 : 0 < I.v0) (hv : ∀ i j, 0 < I.v i j)
    (hγ : ∀ i, 0 < I.γ i ∧ I.γ i ≤ 1)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (X : ι → Finset (Fin n → ℝ))
    (hw : ∀ i j, 0 < w i j) (hwc : ∀ i j, w i j ≤ c i)
    (hX : IsRelaxSolutionFamily I w c X)
    (Sstar : ι → Finset (Fin n)) (hfeas : ∀ i, SpaceFeasible w c i (Sstar i))
    (hopt : ∀ S : ι → Finset (Fin n), (∀ i, SpaceFeasible w c i (S i)) →
      revenue I S ≤ revenue I Sstar)
    (zhat : ℝ) (yhat : ι → ℝ) (hzy : LP13Optimal I X zhat yhat) :
    revenue I Sstar ≤ zhat := by 
  classical
  have hc := claim_local I hvnp hv0 hv hγ w c X hw hwc hX Sstar hfeas zhat yhat hzy.1
  have hsum := (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hc i)).trans hzy.1.1
  have hn (i : ι) : 0 ≤ nestWeight I i (Sstar i) := by
    apply Real.rpow_nonneg
    simp only [V, hvnp i, zero_add]
    exact Finset.sum_nonneg (fun j hj => (hv i j).le)
  have hden : 0 < I.v0 + ∑ i, nestWeight I i (Sstar i) :=
    add_pos_of_pos_of_nonneg hv0 (Finset.sum_nonneg (fun i hi => hn i))
  rw [revenue, div_le_iff₀ hden]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
  nlinarith [hsum]


