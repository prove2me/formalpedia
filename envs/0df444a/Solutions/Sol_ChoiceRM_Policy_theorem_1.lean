-- Prove2me | solution 1 for ChoiceRM.Policy.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-08T01:24:12.305383+00:00
-- url     : https://prove2.me/submissions/aa0be3e4-aad5-4a10-af82-99ea67585d3a

-- SPDX-License-Identifier: Apache-2.0
-- Complete proof of Prove2Me 4b69dcb4-0547-4b5c-a1da-ac611e6cec15.
-- Complete proof with attributed full marginal-value source and new nondominated frontier and tie-rule proofs.
import Definitions.Def_ChoiceRM_Policy_Value
import Definitions.Def_RevenueManagement_singleResource
import Mathlib

set_option autoImplicit false


-- BEGIN MODULE AttributedMarginals
section
-- Prove2me | solution 1 for RevenueManagement.choice_marginal_values
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T23:51:05.830479+00:00
-- url     : https://prove2.me/submissions/485b8d1d-533a-43b8-93a4-73ac61f65055


namespace RevenueManagement

open Finset

/-! ### Discrete concavity and the max-plus step -/

/-- Discrete concavity on `ℕ` from `1` on: `g(x+1) - g(x) ≤ g(x) - g(x-1)` for `x ≥ 1`. -/
def RMConc (g : ℕ → ℝ) : Prop := ∀ x, 1 ≤ x → g (x + 1) - g x ≤ g x - g (x - 1)

lemma rm_conc_mono {g : ℕ → ℝ} (hg : RMConc g) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    g b - g (b - 1) ≤ g a - g (a - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction n with
  | zero => simp
  | succ m ih =>
    have h1 := hg (a + m) (by omega)
    have e1 : a + (m + 1) = a + m + 1 := by ring
    have e2 : a + m + 1 - 1 = a + m := by omega
    rw [e1, e2]
    exact le_trans h1 (ih (by omega))

/-- `H(x) = max_{0 ≤ u ≤ min d x} (r u + g(x − u))`, the inner maximization of (2.3). -/
noncomputable def rmH (d : ℕ) (r : ℝ) (g : ℕ → ℝ) (x : ℕ) : ℝ :=
  (Finset.range (min d x + 1)).sup' ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
    (fun u => r * u + g (x - u))

lemma rmH_ge (d : ℕ) (r : ℝ) (g : ℕ → ℝ) (x u : ℕ) (hu : u ≤ min d x) :
    r * u + g (x - u) ≤ rmH d r g x := by
  unfold rmH
  exact Finset.le_sup' (fun u : ℕ => r * (u : ℝ) + g (x - u)) (Finset.mem_range.2 (by omega))

lemma rmH_attained (d : ℕ) (r : ℝ) (g : ℕ → ℝ) (x : ℕ) :
    ∃ u, u ≤ min d x ∧ rmH d r g x = r * u + g (x - u) := by
  unfold rmH
  obtain ⟨u, hu, he⟩ := Finset.exists_mem_eq_sup' ⟨0, Finset.mem_range.2 (Nat.succ_pos (min d x))⟩
    (fun u : ℕ => r * (u : ℝ) + g (x - u))
  exact ⟨u, by simp only [Finset.mem_range] at hu; omega, he⟩

lemma rmH_zero (d : ℕ) (r : ℝ) (g : ℕ → ℝ) : rmH d r g 0 = g 0 := by
  apply le_antisymm
  · obtain ⟨u, hu, he⟩ := rmH_attained d r g 0
    have : u = 0 := by omega
    subst this; rw [he]; simp
  · have := rmH_ge d r g 0 0 (by omega); simpa using this

/-- Lemma (A): the marginal value of `H` dominates that of `g`. -/
lemma rmH_delta_ge {g : ℕ → ℝ} (hg : RMConc g) (d : ℕ) (r : ℝ) (x : ℕ) (hx : 1 ≤ x) :
    g x - g (x - 1) ≤ rmH d r g x - rmH d r g (x - 1) := by
  obtain ⟨u, hu, he⟩ := rmH_attained d r g (x - 1)
  have h1 := rmH_ge d r g x u (by omega)
  have h2 := rm_conc_mono hg (a := x - u) (b := x) (by omega) (by omega)
  have e : x - 1 - u = x - u - 1 := by omega
  rw [he, e]
  linarith

/-- Lemma 2-2.A.1: `H` is concave when `g` is. -/
lemma rmH_conc {g : ℕ → ℝ} (hg : RMConc g) (d : ℕ) (r : ℝ) : RMConc (rmH d r g) := by
  intro x hx
  obtain ⟨u1, hu1, he1⟩ := rmH_attained d r g (x + 1)
  obtain ⟨u2, hu2, he2⟩ := rmH_attained d r g (x - 1)
  rcases lt_or_ge u2 u1 with h | h
  · have ha := rmH_ge d r g x (u1 - 1) (by omega)
    have hb := rmH_ge d r g x (u2 + 1) (by omega)
    have e1 : x - (u1 - 1) = x + 1 - u1 := by omega
    have e2 : x - (u2 + 1) = x - 1 - u2 := by omega
    rw [e1] at ha; rw [e2] at hb
    have c1 : ((u1 - 1 : ℕ) : ℝ) = (u1 : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [c1] at ha; push_cast at hb
    rw [he1, he2]; linarith
  · have ha := rmH_ge d r g x u1 (by omega)
    have hb := rmH_ge d r g x u2 (by omega)
    have hc := rm_conc_mono hg (a := x - u2) (b := x + 1 - u1) (by omega) (by omega)
    have e1 : x + 1 - u1 - 1 = x - u1 := by omega
    have e2 : x - u2 - 1 = x - 1 - u2 := by omega
    rw [e1, e2] at hc
    rw [he1, he2]; linarith

lemma rmH_bound (d : ℕ) (r : ℝ) (g : ℕ → ℝ) (x : ℕ) :
    |rmH d r g x| ≤ |r| * x + ∑ k ∈ range (x + 1), |g k| := by
  have hS : ∀ k ≤ x, |g k| ≤ ∑ k ∈ range (x + 1), |g k| := fun k hk =>
    Finset.single_le_sum (f := fun k => |g k|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega))
  obtain ⟨u, hu, he⟩ := rmH_attained d r g x
  have h0 := rmH_ge d r g x 0 (by omega)
  simp only [Nat.cast_zero, mul_zero, zero_add, Nat.sub_zero] at h0
  have hgx := hS x le_rfl
  have hgu := hS (x - u) (by omega)
  have hru : r * u ≤ |r| * x := by
    have : (u : ℝ) ≤ x := by exact_mod_cast (show u ≤ x by omega)
    calc r * u ≤ |r| * u := mul_le_mul_of_nonneg_right (le_abs_self r) (Nat.cast_nonneg _)
      _ ≤ |r| * x := mul_le_mul_of_nonneg_left this (abs_nonneg r)
  have hr0 : 0 ≤ |r| * x := by positivity
  rw [abs_le]
  constructor
  · have := neg_abs_le (g x); linarith
  · have := le_abs_self (g (x - u)); rw [he]; linarith

lemma rm_summable (f : ℕ → ℝ) (hf : IsPmf f) (r : ℝ) (g : ℕ → ℝ) (x : ℕ) :
    Summable (fun d => f d * rmH d r g x) := by
  refine Summable.of_norm_bounded (hf.2.summable.mul_right (|r| * x + ∑ k ∈ range (x + 1), |g k|))
    (fun d => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf.1 d)]
  exact mul_le_mul_of_nonneg_left (rmH_bound d r g x) (hf.1 d)

/-- Expectation of the max-plus step against a pmf: concave, with dominating marginals. -/
lemma rm_expect {g : ℕ → ℝ} (hg : RMConc g) (f : ℕ → ℝ) (hf : IsPmf f) (r : ℝ) :
    RMConc (fun x => ∑' d, f d * rmH d r g x) ∧
      ∀ x, 1 ≤ x → g x - g (x - 1) ≤
        (∑' d, f d * rmH d r g x) - ∑' d, f d * rmH d r g (x - 1) := by
  have hs := rm_summable f hf r g
  have hsub : ∀ a b, (∑' d, f d * rmH d r g a) - ∑' d, f d * rmH d r g b
      = ∑' d, f d * (rmH d r g a - rmH d r g b) := by
    intro a b
    rw [← (hs a).tsum_sub (hs b)]
    congr 1; ext d; ring
  constructor
  · intro x hx
    simp only
    rw [hsub, hsub]
    have e : x + 1 - 1 = x := by omega
    refine Summable.tsum_le_tsum (fun d => ?_) ?_ ?_
    · have := rmH_conc hg d r x hx
      try rw [e] at this
      exact mul_le_mul_of_nonneg_left this (hf.1 d)
    · exact ((hs (x + 1)).sub (hs x)).congr (fun d => by ring)
    · exact ((hs x).sub (hs (x - 1))).congr (fun d => by ring)
  · intro x hx
    rw [hsub]
    have h1 : g x - g (x - 1) = ∑' d, f d * (g x - g (x - 1)) := by
      rw [tsum_mul_right, hf.2.tsum_eq, one_mul]
    rw [h1]
    refine Summable.tsum_le_tsum (fun d => ?_) (hf.2.summable.mul_right _) ?_
    · exact mul_le_mul_of_nonneg_left (rmH_delta_ge hg d r x hx) (hf.1 d)
    · exact ((hs x).sub (hs (x - 1))).congr (fun d => by ring)

/-! ### The static model -/

lemma static_succ (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (j x : ℕ) :
    staticValue p f (j + 1) x = ∑' d, f (j + 1) d * rmH d (p (j + 1)) (staticValue p f j) x := rfl

lemma static_conc (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (hf : ∀ j, IsPmf (f j)) :
    ∀ j, RMConc (staticValue p f j) := by
  intro j
  induction j with
  | zero => intro x _; simp [staticValue]
  | succ j ih =>
    have := (rm_expect ih (f (j + 1)) (hf (j + 1)) (p (j + 1))).1
    intro x hx
    simp only [static_succ]
    exact this x hx

lemma static_mono (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (hf : ∀ j, IsPmf (f j)) (j x : ℕ) (hx : 1 ≤ x) :
    staticDelta p f j x ≤ staticDelta p f (j + 1) x := by
  unfold staticDelta
  rw [static_succ, static_succ]
  exact (rm_expect (static_conc p f hf j) (f (j + 1)) (hf (j + 1)) (p (j + 1))).2 x hx

/-- Stage optimality from a threshold: the objective increases up to `u*` and decreases after. -/
lemma rm_stage_opt {g : ℕ → ℝ} (r : ℝ) (d x ustar : ℕ) (hu : ustar ≤ min d x)
    (hleft : ∀ v, v < ustar → g (x - v) - g (x - v - 1) ≤ r)
    (hright : ∀ v, ustar ≤ v → v < min d x → r ≤ g (x - v) - g (x - v - 1)) :
    ∀ u' ≤ min d x, r * u' + g (x - u') ≤ r * ustar + g (x - ustar) := by
  have step : ∀ v, v < x → r * ((v + 1 : ℕ) : ℝ) + g (x - (v + 1))
      = r * v + g (x - v) + (r - (g (x - v) - g (x - v - 1))) := by
    intro v hv
    have e : x - (v + 1) = x - v - 1 := by omega
    rw [e]; push_cast; ring
  intro u' hu'
  rcases le_or_gt u' ustar with h | h
  · obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le h
    clear h
    induction n generalizing u' with
    | zero => simp at hn; rw [hn]
    | succ m ih =>
      have h1 := ih (u' + 1) (by omega) (by omega)
      have h2 := step u' (by omega)
      have h3 := hleft u' (by omega)
      linarith
  · obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_lt h
    clear h
    induction n generalizing u' with
    | zero =>
      have h2 := step ustar (by omega)
      have h3 := hright ustar le_rfl (by omega)
      rw [hn]; linarith
    | succ m ih =>
      have h1 := ih (u' - 1) (by omega) (by omega)
      have h2 := step (u' - 1) (by omega)
      have h3 := hright (u' - 1) (by omega) (by omega)
      have e : u' - 1 + 1 = u' := by omega
      rw [e] at h2
      linarith

lemma rm_sup_mem {s : Finset ℕ} (h : 1 ≤ s.sup id) : s.sup id ∈ s := by
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; rintro rfl; simp at h
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup s hne id
  rw [he]; exact hi

/-! ### The dynamic model -/

lemma rmH_one (r : ℝ) (g : ℕ → ℝ) (x : ℕ) :
    rmH 1 r g (x + 1) = g (x + 1) + max (r - (g (x + 1) - g x)) 0 := by
  apply le_antisymm
  · obtain ⟨u, hu, he⟩ := rmH_attained 1 r g (x + 1)
    rw [he]
    have : u = 0 ∨ u = 1 := by omega
    rcases this with rfl | rfl
    · simp only [Nat.cast_zero, mul_zero, zero_add, Nat.sub_zero]
      have := le_max_right (r - (g (x + 1) - g x)) 0; linarith
    · have e : x + 1 - 1 = x := by omega
      simp only [Nat.cast_one, mul_one, e]
      have := le_max_left (r - (g (x + 1) - g x)) 0; linarith
  · have h0 := rmH_ge 1 r g (x + 1) 0 (by omega)
    have h1 := rmH_ge 1 r g (x + 1) 1 (by omega)
    have e : x + 1 - 1 = x := by omega
    simp only [Nat.cast_zero, mul_zero, zero_add, Nat.sub_zero] at h0
    simp only [Nat.cast_one, mul_one, e] at h1
    rcases le_total (r - (g (x + 1) - g x)) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith

lemma dyn_zero (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T k : ℕ) : dynValueGo lam p n T k 0 = 0 := by
  cases k <;> simp [dynValueGo]

/-- The dynamic Bellman step as a mixture of max-plus steps. -/
lemma dyn_succ_eq (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T k y : ℕ) :
    dynValueGo lam p n T (k + 1) y
      = ∑ j ∈ Icc 1 n, lam j (T - k) * rmH 1 (p j) (dynValueGo lam p n T k) y
        + (1 - ∑ j ∈ Icc 1 n, lam j (T - k)) * rmH 1 0 (dynValueGo lam p n T k) y := by
  cases y with
  | zero =>
    simp only [rmH_zero, dyn_zero]; simp
  | succ x =>
    simp only [rmH_one]
    simp only [dynValueGo]
    rw [Finset.sum_congr rfl (fun j _ => mul_add (lam j (T - k)) _ _), Finset.sum_add_distrib,
      ← Finset.sum_mul]
    ring

lemma dyn_step (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T : ℕ) (hlam : IsArrivalModel lam n) (k : ℕ)
    (hk : RMConc (dynValueGo lam p n T k)) :
    RMConc (dynValueGo lam p n T (k + 1)) ∧
      ∀ x, 1 ≤ x → dynValueGo lam p n T k x - dynValueGo lam p n T k (x - 1)
        ≤ dynValueGo lam p n T (k + 1) x - dynValueGo lam p n T (k + 1) (x - 1) := by
  set g := dynValueGo lam p n T k with hgdef
  set w := fun j => lam j (T - k) with hw
  have hw0 : ∀ j, 0 ≤ w j := fun j => hlam.1 j _
  have hW : 0 ≤ 1 - ∑ j ∈ Icc 1 n, w j := by have := hlam.2 (T - k); simp only [hw]; linarith
  have hdiff : ∀ a b, dynValueGo lam p n T (k + 1) a - dynValueGo lam p n T (k + 1) b
      = ∑ j ∈ Icc 1 n, w j * (rmH 1 (p j) g a - rmH 1 (p j) g b)
        + (1 - ∑ j ∈ Icc 1 n, w j) * (rmH 1 0 g a - rmH 1 0 g b) := by
    intro a b
    rw [dyn_succ_eq, dyn_succ_eq]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  constructor
  · intro x hx
    rw [hdiff, hdiff]
    have e : x + 1 - 1 = x := by omega
    have h1 : ∑ j ∈ Icc 1 n, w j * (rmH 1 (p j) g (x + 1) - rmH 1 (p j) g x)
        ≤ ∑ j ∈ Icc 1 n, w j * (rmH 1 (p j) g x - rmH 1 (p j) g (x - 1)) := by
      apply Finset.sum_le_sum; intro j _
      have := rmH_conc hk 1 (p j) x hx; try rw [e] at this
      exact mul_le_mul_of_nonneg_left this (hw0 j)
    have h2 := rmH_conc hk 1 0 x hx; try rw [e] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 hW
    linarith
  · intro x hx
    rw [hdiff]
    have h1 : ∑ j ∈ Icc 1 n, w j * (g x - g (x - 1))
        ≤ ∑ j ∈ Icc 1 n, w j * (rmH 1 (p j) g x - rmH 1 (p j) g (x - 1)) := by
      apply Finset.sum_le_sum; intro j _
      exact mul_le_mul_of_nonneg_left (rmH_delta_ge hk 1 (p j) x hx) (hw0 j)
    have h2 := mul_le_mul_of_nonneg_left (rmH_delta_ge hk 1 0 x hx) hW
    rw [← Finset.sum_mul] at h1
    linarith

lemma dyn_conc (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T : ℕ) (hlam : IsArrivalModel lam n) :
    ∀ k, RMConc (dynValueGo lam p n T k) := by
  intro k
  induction k with
  | zero => intro x _; simp [dynValueGo]
  | succ k ih => exact (dyn_step lam p n T hlam k ih).1

/-! ### The choice model -/

/-- `Φ(δ) = max_S λ (R(S) − Q(S) δ)`. -/
noncomputable def choicePhi {n : ℕ} (l : ℝ) (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (δ : ℝ) : ℝ :=
  (Finset.univ : Finset (Finset (Fin n))).sup' Finset.univ_nonempty
    (fun S => l * (expRevenue P p S - purchaseProb P S * δ))

section Phi

variable {n : ℕ} (l : ℝ) (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)

lemma purchaseProb_nonneg (hP : IsChoiceModel P) (S : Finset (Fin n)) : 0 ≤ purchaseProb P S :=
  Finset.sum_nonneg (fun j _ => hP.1 S j)

lemma phi_ge (δ : ℝ) (S : Finset (Fin n)) :
    l * (expRevenue P p S - purchaseProb P S * δ) ≤ choicePhi l P p δ := by
  unfold choicePhi
  exact Finset.le_sup' (fun S => l * (expRevenue P p S - purchaseProb P S * δ)) (Finset.mem_univ S)

lemma phi_nonneg (δ : ℝ) : 0 ≤ choicePhi l P p δ := by
  have := phi_ge l P p δ ∅
  simp [expRevenue, purchaseProb] at this
  exact this

lemma phi_anti (hl : 0 ≤ l) (hP : IsChoiceModel P) {δ1 δ2 : ℝ} (h : δ1 ≤ δ2) :
    choicePhi l P p δ2 ≤ choicePhi l P p δ1 := by
  unfold choicePhi
  apply Finset.sup'_le
  intro S _
  refine le_trans ?_ (phi_ge l P p δ1 S)
  have := purchaseProb_nonneg P hP S
  apply mul_le_mul_of_nonneg_left _ hl
  nlinarith

lemma phi_lip (hl : 0 ≤ l) (hl1 : l ≤ 1) (hP : IsChoiceModel P) {δ1 δ2 : ℝ} (h : δ1 ≤ δ2) :
    choicePhi l P p δ1 ≤ choicePhi l P p δ2 + (δ2 - δ1) := by
  obtain ⟨S, _, he⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Finset (Fin n))))
    Finset.univ_nonempty (fun S => l * (expRevenue P p S - purchaseProb P S * δ1))
  have h1 := phi_ge l P p δ2 S
  unfold choicePhi at *
  rw [he]
  have hq0 := purchaseProb_nonneg P hP S
  have hq1 : purchaseProb P S ≤ 1 := hP.2 S
  have hlq : l * purchaseProb P S ≤ 1 := by nlinarith
  have hd : 0 ≤ δ2 - δ1 := by linarith
  nlinarith

end Phi

lemma choice_zero {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (T k : ℕ) : choiceValueGo lam P p T k 0 = 0 := by
  cases k <;> simp [choiceValueGo]

lemma choice_succ {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (T k y : ℕ) :
    choiceValueGo lam P p T (k + 1) (y + 1)
      = choicePhi (lam (T - k)) P p
          (choiceValueGo lam P p T k (y + 1) - choiceValueGo lam P p T k y)
        + choiceValueGo lam P p T k (y + 1) := by
  simp only [choiceValueGo, choicePhi]

/-- The abstract step of Proposition 2-2.A.4. -/
lemma choice_step_abstract (V V' : ℕ → ℝ) (Φ : ℝ → ℝ) (hΦ0 : ∀ δ, 0 ≤ Φ δ)
    (hanti : ∀ δ1 δ2, δ1 ≤ δ2 → Φ δ2 ≤ Φ δ1)
    (hlip : ∀ δ1 δ2, δ1 ≤ δ2 → Φ δ1 ≤ Φ δ2 + (δ2 - δ1))
    (hV0 : V 0 = 0) (hV'0 : V' 0 = 0) (hV' : ∀ y, V' (y + 1) = Φ (V (y + 1) - V y) + V (y + 1))
    (hV : RMConc V) :
    RMConc V' ∧ ∀ x, 1 ≤ x → V x - V (x - 1) ≤ V' x - V' (x - 1) := by
  constructor
  · intro x hx
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hc := hV (y + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hc
    have h1 := hlip _ _ hc
    cases y with
    | zero =>
      rw [hV' (0 + 1), hV' 0, hV'0]
      have := hΦ0 (V (0 + 1) - V 0)
      simp only [hV0] at hc h1 this ⊢
      linarith
    | succ z =>
      rw [hV' (z + 1 + 1), hV' (z + 1), hV' z]
      have hc2 := hV (z + 1) (by omega)
      simp only [Nat.add_sub_cancel] at hc2
      have h2 := hanti _ _ hc2
      linarith
  · intro x hx
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    cases y with
    | zero =>
      rw [hV' 0, hV'0]
      have := hΦ0 (V (0 + 1) - V 0)
      simp only [hV0] at this ⊢
      linarith
    | succ z =>
      rw [hV' (z + 1), hV' z]
      have hc2 := hV (z + 1) (by omega)
      simp only [Nat.add_sub_cancel] at hc2
      have h2 := hanti _ _ hc2
      linarith

section ChoiceProps

variable {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ) (T : ℕ)
  (hP : IsChoiceModel P) (hlam : ∀ t, 0 ≤ lam t ∧ lam t ≤ 1)
include hP hlam

lemma choice_step (k : ℕ) (hk : RMConc (choiceValueGo lam P p T k)) :
    RMConc (choiceValueGo lam P p T (k + 1)) ∧
      ∀ x, 1 ≤ x → choiceValueGo lam P p T k x - choiceValueGo lam P p T k (x - 1)
        ≤ choiceValueGo lam P p T (k + 1) x - choiceValueGo lam P p T (k + 1) (x - 1) :=
  choice_step_abstract _ _ (choicePhi (lam (T - k)) P p) (phi_nonneg _ P p)
    (fun _ _ h => phi_anti _ P p (hlam _).1 hP h)
    (fun _ _ h => phi_lip _ P p (hlam _).1 (hlam _).2 hP h)
    (choice_zero lam P p T k) (choice_zero lam P p T (k + 1)) (choice_succ lam P p T k) hk

lemma choice_conc (k : ℕ) : RMConc (choiceValueGo lam P p T k) := by
  induction k with
  | zero => intro x _; simp [choiceValueGo]
  | succ k ih => exact (choice_step lam P p T hP hlam k ih).1

lemma choiceDelta_conc (s x x' : ℕ) (hx : 1 ≤ x) (hxx : x ≤ x') :
    choiceDelta lam P p T s x' ≤ choiceDelta lam P p T s x := by
  unfold choiceDelta choiceValue
  exact rm_conc_mono (choice_conc lam P p T hP hlam _) hx hxx

lemma choiceDelta_time (s x : ℕ) (hx : 1 ≤ x) :
    choiceDelta lam P p T (s + 1) x ≤ choiceDelta lam P p T s x := by
  unfold choiceDelta choiceValue
  rcases le_or_gt s T with hs | hs
  · have e1 : T + 1 - s = (T + 1 - (s + 1)) + 1 := by omega
    rw [e1]
    exact (choice_step lam P p T hP hlam _ (choice_conc lam P p T hP hlam _)).2 x hx
  · have e1 : T + 1 - s = 0 := by omega
    have e2 : T + 1 - (s + 1) = 0 := by omega
    rw [e1, e2]

lemma choiceDelta_time' (s s' x : ℕ) (hx : 1 ≤ x) (hss : s ≤ s') :
    choiceDelta lam P p T s' x ≤ choiceDelta lam P p T s x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hss
  clear hss
  induction m with
  | zero => simp
  | succ m ih =>
    exact le_trans (choiceDelta_time lam P p T hP hlam (s + m) x hx) ih

lemma choiceDelta_nonneg (s x : ℕ) (hx : 1 ≤ x) : 0 ≤ choiceDelta lam P p T s x := by
  unfold choiceDelta choiceValue
  generalize T + 1 - s = k
  induction k with
  | zero => simp [choiceValueGo]
  | succ k ih =>
    exact le_trans ih ((choice_step lam P p T hP hlam k (choice_conc lam P p T hP hlam k)).2 x hx)

/-- Proposition 2.3. -/
lemma choice_ineff_not_opt (t x : ℕ) (hx : 1 ≤ x) (hpos : 0 < lam t)
    (S : Finset (Fin n)) (hS : IsInefficient P p S) : ¬ IsChoiceOptimal lam P p T t x S := by
  intro hopt
  obtain ⟨α, hα0, hα1, hαQ, hαR⟩ := hS
  set Δ := choiceDelta lam P p T (t + 1) x with hΔ
  have hΔ0 : 0 ≤ Δ := choiceDelta_nonneg lam P p T hP hlam (t + 1) x hx
  have h1 : ∑ S', α S' * choiceObj lam P p T t x S' ≤ ∑ S', α S' * choiceObj lam P p T t x S :=
    Finset.sum_le_sum (fun S' _ => mul_le_mul_of_nonneg_left (hopt S') (hα0 S'))
  rw [← Finset.sum_mul, hα1, one_mul] at h1
  have h2 : ∑ S', α S' * choiceObj lam P p T t x S'
      = lam t * (∑ S', α S' * expRevenue P p S') - lam t * Δ * (∑ S', α S' * purchaseProb P S') := by
    unfold choiceObj
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro S' _; ring
  rw [h2] at h1
  unfold choiceObj at h1
  rw [← hΔ] at h1
  have h3 : lam t * Δ * (∑ S', α S' * purchaseProb P S') ≤ lam t * Δ * purchaseProb P S :=
    mul_le_mul_of_nonneg_left hαQ (mul_nonneg (le_of_lt hpos) hΔ0)
  have h4 : lam t * expRevenue P p S < lam t * (∑ S', α S' * expRevenue P p S') :=
    mul_lt_mul_of_pos_left hαR hpos
  nlinarith

end ChoiceProps

/-- Ordering of efficient sets. -/
lemma efficient_ordered {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (S S' : Finset (Fin n)) (hS' : IsEfficient P p S')
    (hQ : purchaseProb P S ≤ purchaseProb P S') : expRevenue P p S ≤ expRevenue P p S' := by
  by_contra hlt
  push Not at hlt
  apply hS'
  refine ⟨fun S'' => if S'' = S then 1 else 0, fun S'' => by dsimp only; split_ifs <;> norm_num, ?_, ?_, ?_⟩
  · simp
  · simp only [ite_mul, one_mul, zero_mul]; simpa using hQ
  · simp only [ite_mul, one_mul, zero_mul]; simpa using hlt

/-- The Bellman equation (2.26) in terms of the objective. -/
lemma choice_bellman {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (T t y : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) :
    choiceValue lam P p T t (y + 1)
      = (Finset.univ : Finset (Finset (Fin n))).sup' Finset.univ_nonempty
          (fun S => choiceObj lam P p T t (y + 1) S) + choiceValue lam P p T (t + 1) (y + 1) := by
  unfold choiceObj choiceDelta choiceValue
  rw [show T + 1 - t = (T - t) + 1 by omega, show T + 1 - (t + 1) = T - t by omega, choice_succ]
  unfold choicePhi
  rw [show T - (T - t) = t by omega]
  simp only [Nat.add_sub_cancel]

/-- Monotone comparative statics of `R(S) − Q(S) Δ` in `Δ`. -/
lemma choice_argmax_mono {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (Δ' Δ : ℝ) (hΔ : Δ' ≤ Δ) (S : Finset (Fin n))
    (hS : ∀ S'', expRevenue P p S'' - purchaseProb P S'' * Δ ≤
      expRevenue P p S - purchaseProb P S * Δ) :
    ∃ S', (∀ S'', expRevenue P p S'' - purchaseProb P S'' * Δ' ≤
      expRevenue P p S' - purchaseProb P S' * Δ') ∧ purchaseProb P S ≤ purchaseProb P S' := by
  classical
  set M := (Finset.univ : Finset (Finset (Fin n))).filter (fun S' => ∀ S'',
    expRevenue P p S'' - purchaseProb P S'' * Δ' ≤ expRevenue P p S' - purchaseProb P S' * Δ')
    with hM
  obtain ⟨S0, _, h0⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Finset (Fin n))))
    Finset.univ_nonempty (fun S => expRevenue P p S - purchaseProb P S * Δ')
  have hne : M.Nonempty := ⟨S0, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun S'' => by
    rw [← h0]
    exact Finset.le_sup' (fun S => expRevenue P p S - purchaseProb P S * Δ') (Finset.mem_univ S'')⟩⟩
  obtain ⟨S', hS'M, hmax⟩ := Finset.exists_max_image M (purchaseProb P) hne
  have hS'opt := (Finset.mem_filter.1 hS'M).2
  refine ⟨S', hS'opt, ?_⟩
  by_contra hlt
  push Not at hlt
  have h1 := hS S'
  have h2 := hS'opt S
  have hge : Δ ≤ Δ' := by
    by_contra hc
    push Not at hc
    nlinarith [mul_pos (sub_pos.2 hlt) (sub_pos.2 hc)]
  have hΔeq : Δ' = Δ := le_antisymm hΔ hge
  subst hΔeq
  have hSM : S ∈ M := Finset.mem_filter.2 ⟨Finset.mem_univ _, hS⟩
  have := hmax S hSM
  linarith

end RevenueManagement

open RevenueManagement

theorem RevenueManagement.choice_marginal_values {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ)
    (p : Fin n → ℝ) (T : ℕ) (hP : IsChoiceModel P) (hlam : ∀ t, 0 ≤ lam t ∧ lam t ≤ 1)
    (_hp : ∀ j, 0 ≤ p j) (t x : ℕ) (_ht : 1 ≤ t) (_htT : t ≤ T) (hx : 1 ≤ x) :
    choiceDelta lam P p T t (x + 1) ≤ choiceDelta lam P p T t x ∧
      choiceDelta lam P p T (t + 1) x ≤ choiceDelta lam P p T t x :=
  ⟨choiceDelta_conc lam P p T hP hlam t x (x + 1) hx (by omega),
    choiceDelta_time lam P p T hP hlam t x hx⟩
end
-- END MODULE AttributedMarginals

-- BEGIN MODULE ValueProperties
section
set_option autoImplicit false
namespace ChoiceRM.Policy.Proof
open RevenueManagement
variable {n : ℕ}

lemma deltaV_step (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (P : Finset (Fin n) → Fin n → ℝ) (hP : IsChoiceModel P) (r : Fin n → ℝ)
    (t x : ℕ) (hx : 1 ≤ x) : deltaV lam P r t x ≤ deltaV lam P r (t+1) x := by
  exact (choice_step (fun _ => lam) P r 0 hP (fun _ => ⟨hlam0,hlam1⟩) t
    (choice_conc (fun _ => lam) P r 0 hP (fun _ => ⟨hlam0,hlam1⟩) t)).2 x hx

lemma deltaV_nonneg (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (P : Finset (Fin n) → Fin n → ℝ) (hP : IsChoiceModel P) (r : Fin n → ℝ)
    (t x : ℕ) (hx : 1 ≤ x) : 0 ≤ deltaV lam P r t x := by
  induction t with
  | zero => simp [deltaV,V,choiceValueGo]
  | succ t ih => exact ih.trans (deltaV_step lam hlam0 hlam1 P hP r t x hx)

lemma deltaV_mono_time (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (P : Finset (Fin n) → Fin n → ℝ) (hP : IsChoiceModel P) (r : Fin n → ℝ)
    (x : ℕ) (hx : 1 ≤ x) : Monotone (fun t => deltaV lam P r t x) := by
  exact monotone_nat_of_le_succ (fun t => deltaV_step lam hlam0 hlam1 P hP r t x hx)

lemma deltaV_anti_capacity (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (P : Finset (Fin n) → Fin n → ℝ) (hP : IsChoiceModel P) (r : Fin n → ℝ)
    (t x x' : ℕ) (hx : 1 ≤ x) (hxx' : x ≤ x') :
    deltaV lam P r t x' ≤ deltaV lam P r t x := by
  exact rm_conc_mono (choice_conc (fun _ => lam) P r 0 hP
    (fun _ => ⟨hlam0,hlam1⟩) t) hx hxx'

lemma bellman_of_global_max (lam : ℝ) (hlam : 0 ≤ lam)
    (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ)
    (t x : ℕ) (ht : 1 ≤ t) (hx : 1 ≤ x) (S : Finset (Fin n))
    (hS : ∀ T, expRevenue P r T - purchaseProb P T * deltaV lam P r (t-1) x ≤
      expRevenue P r S - purchaseProb P S * deltaV lam P r (t-1) x) :
    IsOptimalOffer lam P r t x S ∧
      V lam P r t x = lam * (expRevenue P r S - purchaseProb P S * deltaV lam P r (t-1) x) +
        V lam P r (t-1) x := by
  have hopt : IsOptimalOffer lam P r t x S := fun T => mul_le_mul_of_nonneg_left (hS T) hlam
  refine ⟨hopt, ?_⟩
  have he : choicePhi lam P r (deltaV lam P r (t-1) x) =
      lam * (expRevenue P r S - purchaseProb P S * deltaV lam P r (t-1) x) := by
    apply le_antisymm
    · unfold choicePhi
      apply Finset.sup'_le
      intro T _
      exact hopt T
    · exact phi_ge lam P r _ S
  obtain ⟨u,rfl⟩ : ∃ u, t = u+1 := ⟨t-1,by omega⟩
  obtain ⟨y,rfl⟩ : ∃ y, x = y+1 := ⟨x-1,by omega⟩
  simpa only [V,deltaV,Nat.add_sub_cancel] using
    (choice_succ (fun _ => lam) P r 0 u y).trans (congrArg
      (fun a => a + choiceValueGo (fun _ => lam) P r 0 u (y+1)) he)

end ChoiceRM.Policy.Proof
end
-- END MODULE ValueProperties

-- BEGIN MODULE NondominatedMax
section

namespace ChoiceRM.Policy.Proof
open scoped BigOperators

lemma exists_nondominated_max {I : Type*} [Fintype I] [Nonempty I]
    (Q R : I → ℝ) (v : ℝ) (hv : 0 ≤ v) :
    ∃ t : I, (∀ s, R s - Q s * v ≤ R t - Q t * v) ∧
      ¬ ∃ α : I → ℝ, (∀ s, 0 ≤ α s) ∧ ∑ s, α s = 1 ∧
        ((∑ s, α s * Q s ≤ Q t ∧ R t < ∑ s, α s * R s) ∨
          (∑ s, α s * Q s < Q t ∧ R t ≤ ∑ s, α s * R s)) := by
  classical
  let g : I → ℝ := fun s => R s - Q s * v
  obtain ⟨b,_,hb⟩ := Finset.exists_max_image (Finset.univ : Finset I) g Finset.univ_nonempty
  let M : Finset I := Finset.univ.filter (fun s => g s = g b)
  have hbM : b ∈ M := by simp [M]
  obtain ⟨t,ht,hmin⟩ := Finset.exists_min_image M Q ⟨b,hbM⟩
  have htb : g t = g b := (Finset.mem_filter.mp ht).2
  have hmax : ∀ s, g s ≤ g t := fun s => by rw [htb]; exact hb s (Finset.mem_univ s)
  refine ⟨t,hmax,?_⟩
  rintro ⟨α,hα,hαsum,hdom⟩
  let q : ℝ := ∑ s, α s * Q s
  let r : ℝ := ∑ s, α s * R s
  have hq : q ≤ Q t := hdom.elim (fun h => h.1) (fun h => h.1.le)
  have hr : R t ≤ r := hdom.elim (fun h => h.2.le) (fun h => h.2)
  have havg : ∑ s, α s * g s = r - q * v := by
    dsimp [g,r,q]
    rw [Finset.sum_mul,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  have havgle : ∑ s, α s * g s ≤ g t := by
    calc
      _ ≤ ∑ s, α s * g t := Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hmax s) (hα s)
      _ = g t := by rw [← Finset.sum_mul,hαsum,one_mul]
  have havgge : g t ≤ ∑ s, α s * g s := by
    rw [havg]
    dsimp [g]
    have hh := mul_le_mul_of_nonneg_right hq hv
    linarith
  have havgeq : ∑ s, α s * g s = g t := le_antisymm havgle havgge
  have hgap : ∑ s, α s * (g t - g s) = 0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hαsum,one_mul,havgeq,sub_self]
  have hterm : ∀ s, α s * (g t - g s) = 0 := fun s =>
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun s _ => mul_nonneg (hα s) (sub_nonneg.mpr (hmax s)))).mp hgap s (Finset.mem_univ s)
  have hqge : Q t ≤ q := by
    calc
      Q t = ∑ s, α s * Q t := by rw [← Finset.sum_mul,hαsum,one_mul]
      _ ≤ ∑ s, α s * Q s := by
        apply Finset.sum_le_sum
        intro s _
        by_cases hs : α s = 0
        · simp [hs]
        · have hgs : g s = g t := by
            have hh := (mul_eq_zero.mp (hterm s)).resolve_left hs
            linarith
          have hsM : s ∈ M := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hgs.trans htb⟩
          exact mul_le_mul_of_nonneg_left (hmin s hsM) (hα s)
  have hqe : q = Q t := le_antisymm hq hqge
  have hre : r = R t := by
    rw [havg,hqe] at havgeq
    dsimp [g] at havgeq
    linarith
  rcases hdom with hd | hd
  · exact (lt_irrefl (R t)) (by simpa only [← hre] using hd.2)
  · exact (lt_irrefl (Q t)) (by simpa only [← hqe] using hd.1)

end ChoiceRM.Policy.Proof
end
-- END MODULE NondominatedMax

-- BEGIN MODULE Frontier
section

namespace ChoiceRM.Policy.Proof
open RevenueManagement

lemma exists_nondominated_global_max {n : ℕ}
    (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (v : ℝ) (hv : 0 ≤ v) :
    ∃ S, IsNondominated P r S ∧ ∀ T,
      expRevenue P r T - purchaseProb P T * v ≤ expRevenue P r S - purchaseProb P S * v := by
  obtain ⟨S,hmax,hnd⟩ := exists_nondominated_max (purchaseProb P) (expRevenue P r) v hv
  exact ⟨S,hnd,hmax⟩

lemma frontier_max_is_global {n m : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (r : Fin n → ℝ) (Sq : Fin m → Finset (Fin n)) (hSq : IsOrderedNondominated P r Sq)
    (v : ℝ) (hv : 0 ≤ v) (l : Fin m)
    (hl : ∀ i, expRevenue P r (Sq i) - purchaseProb P (Sq i) * v ≤
      expRevenue P r (Sq l) - purchaseProb P (Sq l) * v) :
    ∀ T, expRevenue P r T - purchaseProb P T * v ≤
      expRevenue P r (Sq l) - purchaseProb P (Sq l) * v := by
  obtain ⟨S,hS,hmax⟩ := exists_nondominated_global_max P r v hv
  obtain ⟨i,hi⟩ := hSq.exhaustive S hS
  intro T
  have h := hl i
  rw [hi] at h
  exact (hmax T).trans h

lemma exists_largest_frontier_max {n m : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (r : Fin n → ℝ) (Sq : Fin m → Finset (Fin n)) (hSq : IsOrderedNondominated P r Sq)
    (v : ℝ) (hv : 0 ≤ v) : ∃ k, IsLargestMaximizer P r Sq v k := by
  classical
  obtain ⟨S,hS,hSmax⟩ := exists_nondominated_global_max P r v hv
  obtain ⟨i,hi⟩ := hSq.exhaustive S hS
  let g : Fin m → ℝ := fun j => expRevenue P r (Sq j) - purchaseProb P (Sq j) * v
  let M : Finset (Fin m) := Finset.univ.filter (fun j => ∀ l, g l ≤ g j)
  have hiM : i ∈ M := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,fun l => ?_⟩
    dsimp [g]
    rw [hi]
    exact hSmax (Sq l)
  obtain ⟨k,hk,hindex⟩ := Finset.exists_max_image M id ⟨i,hiM⟩
  have hkmax : ∀ l, g l ≤ g k := (Finset.mem_filter.mp hk).2
  refine ⟨k,hkmax,?_⟩
  intro l he
  have hlM : l ∈ M := Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun j => by
    change g l = g k at he
    rw [he]
    exact hkmax j⟩
  exact hindex l hlM

lemma largest_index_antitone_value {n m : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (r : Fin n → ℝ) (Sq : Fin m → Finset (Fin n))
    (hmono : Monotone (fun k => purchaseProb P (Sq k)))
    (v' v : ℝ) (hv : v' ≤ v) (k k' : Fin m)
    (hk : IsLargestMaximizer P r Sq v k) (hk' : IsLargestMaximizer P r Sq v' k') :
    k ≤ k' := by
  by_contra h
  have hlt : k' < k := lt_of_not_ge h
  have hQ := hmono hlt.le
  have h1 := hk.1 k'
  have h2 := hk'.1 k
  have hp := mul_nonneg (sub_nonneg.mpr hQ) (sub_nonneg.mpr hv)
  have he : expRevenue P r (Sq k) - purchaseProb P (Sq k) * v' =
      expRevenue P r (Sq k') - purchaseProb P (Sq k') * v' := by nlinarith
  exact h (hk'.2 k he)

end ChoiceRM.Policy.Proof
end
-- END MODULE Frontier

-- BEGIN MODULE FullPolicy
section

namespace ChoiceRM.Policy

open RevenueManagement

/-- Theorem 1 (p. 15): choose a nondominated set attaining the stage maximum;
the greatest optimal index rises with capacity and falls with time remaining. -/
theorem theorem_1 {n m : ℕ} (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (P : Finset (Fin n) → Fin n → ℝ) (hP : IsChoiceModel P)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (Sq : Fin m → Finset (Fin n)) (hSq : IsOrderedNondominated P r Sq) :
    (∀ t x, 1 ≤ t → 1 ≤ x →
      ∃ k : Fin m,
        IsLargestMaximizer P r Sq (deltaV lam P r (t - 1) x) k ∧
        (∀ l : Fin m,
          (∀ i : Fin m,
            expRevenue P r (Sq i) - purchaseProb P (Sq i) * deltaV lam P r (t - 1) x ≤
              expRevenue P r (Sq l) - purchaseProb P (Sq l) * deltaV lam P r (t - 1) x) →
          IsOptimalOffer lam P r t x (Sq l)) ∧
        V lam P r t x =
          lam * (expRevenue P r (Sq k) - purchaseProb P (Sq k) *
            deltaV lam P r (t - 1) x) + V lam P r (t - 1) x) ∧
    (∀ t x x' (_hx : 1 ≤ x) (_hxx' : x ≤ x') (_ht : 1 ≤ t)
      (k k' : Fin m),
      IsLargestMaximizer P r Sq (deltaV lam P r (t - 1) x) k →
      IsLargestMaximizer P r Sq (deltaV lam P r (t - 1) x') k' →
      k ≤ k') ∧
    (∀ x t t' (_hx : 1 ≤ x) (_ht : 1 ≤ t) (_htt' : t ≤ t')
      (k k' : Fin m),
      IsLargestMaximizer P r Sq (deltaV lam P r (t - 1) x) k →
      IsLargestMaximizer P r Sq (deltaV lam P r (t' - 1) x) k' →
      k' ≤ k) := by
  have _hr := hr
  refine ⟨?_,?_,?_⟩
  · intro t x ht hx
    have hv := Proof.deltaV_nonneg lam hlam0 hlam1 P hP r (t-1) x hx
    obtain ⟨k,hk⟩ := Proof.exists_largest_frontier_max P r Sq hSq _ hv
    refine ⟨k,hk,?_,?_⟩
    · intro l hl
      exact (Proof.bellman_of_global_max lam hlam0 P r t x ht hx (Sq l)
        (Proof.frontier_max_is_global P r Sq hSq _ hv l hl)).1
    · exact (Proof.bellman_of_global_max lam hlam0 P r t x ht hx (Sq k)
        (Proof.frontier_max_is_global P r Sq hSq _ hv k hk.1)).2
  · intro t x x' hx hxx' _ht k k' hk hk'
    exact Proof.largest_index_antitone_value P r Sq hSq.mono _ _
      (Proof.deltaV_anti_capacity lam hlam0 hlam1 P hP r (t-1) x x' hx hxx') k k' hk hk'
  · intro x t t' hx _ht htt' k k' hk hk'
    exact Proof.largest_index_antitone_value P r Sq hSq.mono _ _
      (Proof.deltaV_mono_time lam hlam0 hlam1 P hP r x hx (Nat.sub_le_sub_right htt' 1))
      k' k hk' hk

end ChoiceRM.Policy

end
-- END MODULE FullPolicy

-- BEGIN MODULE PublicSolution
section
open RevenueManagement ChoiceRM.Policy

theorem solution {n m : ℕ} (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (P : Finset (Fin n) → Fin n → ℝ) (hP : IsChoiceModel P)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (Sq : Fin m → Finset (Fin n)) (hSq : IsOrderedNondominated P r Sq) :
    (∀ t x, 1 ≤ t → 1 ≤ x →
      ∃ k : Fin m,
        IsLargestMaximizer P r Sq (deltaV lam P r (t - 1) x) k ∧
        (∀ l : Fin m,
          (∀ i : Fin m,
            expRevenue P r (Sq i) - purchaseProb P (Sq i) * deltaV lam P r (t - 1) x ≤
              expRevenue P r (Sq l) - purchaseProb P (Sq l) * deltaV lam P r (t - 1) x) →
          IsOptimalOffer lam P r t x (Sq l)) ∧
        V lam P r t x =
          lam * (expRevenue P r (Sq k) - purchaseProb P (Sq k) *
            deltaV lam P r (t - 1) x) + V lam P r (t - 1) x) ∧
    (∀ t x x' (_hx : 1 ≤ x) (_hxx' : x ≤ x') (_ht : 1 ≤ t)
      (k k' : Fin m),
      IsLargestMaximizer P r Sq (deltaV lam P r (t - 1) x) k →
      IsLargestMaximizer P r Sq (deltaV lam P r (t - 1) x') k' →
      k ≤ k') ∧
    (∀ x t t' (_hx : 1 ≤ x) (_ht : 1 ≤ t) (_htt' : t ≤ t')
      (k k' : Fin m),
      IsLargestMaximizer P r Sq (deltaV lam P r (t - 1) x) k →
      IsLargestMaximizer P r Sq (deltaV lam P r (t' - 1) x) k' →
      k' ≤ k) := by
  exact ChoiceRM.Policy.theorem_1 lam hlam0 hlam1 P hP r hr Sq hSq


end
-- END MODULE PublicSolution

#print axioms ChoiceRM.Policy.theorem_1
#print axioms solution
