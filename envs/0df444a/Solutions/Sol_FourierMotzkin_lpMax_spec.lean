-- Prove2me | solution 1 for FourierMotzkin.lpMax_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:44:50.357295+00:00
-- url     : https://prove2.me/submissions/10acfcf7-c5a8-4492-b5cc-5040d51ea10d

import Mathlib
import Definitions.Def_FourierMotzkin_basic

/-!
# Exact LP solving by Fourier–Motzkin elimination

Data (designed to be implementable on a RAM with list/loop primitives):
* a constraint `(a, b) : List ℝ × ℝ` means `Σ_j a_j x_j ≤ b` for `x : ℕ → ℝ`
  (coefficients beyond `a.length` are `0`); a `System` is a `List` of constraints;
* `Sat sys x` : `x` satisfies every constraint of `sys`.

Algorithms:
* `elim j sys` — one FM step (filter + nested loop over (positive, negative) pairs);
* `lpMax c sys` — maximize `c·x`: add `z ≤ c·x` as a fresh variable `z` at index 0
  (`lift`), eliminate the original variables `1..n` (`finalSys`), read off the
  constraints `α z ≤ β` (`bounds`), return `infeasible` / `unbounded` / `opt v`;
* `argmax c sys` — back-substitution through the stored stages (`stages`,
  `backSubst`, `pick`): each eliminated coordinate is set to the largest lower
  bound, else the smallest upper bound, else `0`.

Main results: `elim_sound_complete`, `sat_elim_update`, `coef_elim`, `sat_pick`,
`lpMax_infeasible`, `lpMax_unbounded`, `lpMax_opt`, `argmax_spec`,
`lpMax_of_feasible_bddAbove`, `lpMax_eq_infeasible_iff`, `lpMax_eq_unbounded_iff`.
-/

namespace MTSPFM
open FourierMotzkin

/- `dot a x = Σ_j a_j x_j`; coefficients beyond `a.length` are zero. -/
/- Pointwise `s • a + t • b`, padding the shorter list with zeros. -/
theorem dot_lc (s t : ℝ) (a b : List ℝ) (x : ℕ → ℝ) :
    dot (lc s t a b) x = s * dot a x + t * dot b x := by
  induction a, b using lc.induct generalizing x with
  | case1 => simp [lc, dot]
  | case2 a as ih => simp [lc, dot, ih]; ring
  | case3 b bs ih => simp [lc, dot, ih]; ring
  | case4 a as b bs ih => simp [lc, dot, ih]; ring

theorem getD_lc (s t : ℝ) (a b : List ℝ) (j : ℕ) :
    (lc s t a b).getD j 0 = s * a.getD j 0 + t * b.getD j 0 := by
  induction a, b using lc.induct generalizing j with
  | case1 => simp [lc]
  | case2 a as ih => cases j <;> simp only [lc, List.getD_cons_succ, List.getD_cons_zero,
      List.getD_nil, ih] <;> ring
  | case3 b bs ih => cases j <;> simp only [lc, List.getD_cons_succ, List.getD_cons_zero,
      List.getD_nil, ih] <;> ring
  | case4 a as b bs ih => cases j <;> simp only [lc, List.getD_cons_succ, List.getD_cons_zero, ih]

theorem dot_update (a : List ℝ) (x : ℕ → ℝ) (j : ℕ) (t : ℝ) :
    dot a (Function.update x j t) = dot a x + a.getD j 0 * (t - x j) := by
  induction a generalizing x j with
  | nil => simp [dot]
  | cons c as ih =>
    cases j with
    | zero =>
      have : (fun i => Function.update x 0 t (i + 1)) = fun i => x (i + 1) := by
        funext i; simp
      simp only [dot, this]; simp; ring
    | succ j =>
      have : (fun i => Function.update x (j + 1) t (i + 1)) =
          Function.update (fun i => x (i + 1)) j t := by
        funext i; simp [Function.update_apply]
      simp only [dot, this, ih]; simp; ring

theorem dot_congr (a : List ℝ) (n : ℕ) (x y : ℕ → ℝ) (hn : a.length ≤ n)
    (h : ∀ i < n, x i = y i) : dot a x = dot a y := by
  induction a generalizing n x y with
  | nil => rfl
  | cons c as ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      simp only [dot]
      rw [h 0 (Nat.succ_pos _), ih n _ _ (by simpa using hn) (fun i hi => h (i+1) (by omega))]

theorem dot_zero (a : List ℝ) : dot a (fun _ => 0) = 0 := by
  induction a with
  | nil => rfl
  | cons c as ih => simp [dot, ih]

theorem dot_neg (a : List ℝ) (x : ℕ → ℝ) : dot (a.map (fun r => -r)) x = - dot a x := by
  induction a generalizing x with
  | nil => simp [dot]
  | cons c as ih => simp [dot, ih]; ring


/-! ## Constraints, systems, satisfaction -/

/- A constraint `(a, b)` stands for `Σ_j a_j x_j ≤ b`. -/
/- A system is a finite conjunction of constraints. -/
/- `x` satisfies every constraint of `sys`. -/
/- Coefficient of variable `j` in constraint `c`. -/
/- `max m l₁ l₂ …` -/
/- `min m l₁ l₂ …` -/
theorem le_lmax (m : ℝ) (l : List ℝ) : ∀ w ∈ m :: l, w ≤ lmax m l := by
  induction l with
  | nil => simp [lmax]
  | cons a l ih =>
    intro w hw
    simp only [lmax, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.1 hw with rfl | hw
    · exact le_trans (ih w (by simp)) (le_max_right _ _)
    · rcases List.mem_cons.1 hw with rfl | hw
      · exact le_max_left _ _
      · exact le_trans (ih w (List.mem_cons_of_mem _ hw)) (le_max_right _ _)

theorem lmax_le (m : ℝ) (l : List ℝ) (U : ℝ) (h : ∀ w ∈ m :: l, w ≤ U) : lmax m l ≤ U := by
  induction l with
  | nil => simpa [lmax] using h
  | cons a l ih =>
    simp only [lmax, List.foldr_cons] at ih ⊢
    exact max_le (h a (by simp)) (ih (fun w hw => h w (by
      rcases List.mem_cons.1 hw with rfl | hw <;> simp_all)))

theorem lmin_le (m : ℝ) (l : List ℝ) : ∀ w ∈ m :: l, lmin m l ≤ w := by
  induction l with
  | nil => simp [lmin]
  | cons a l ih =>
    intro w hw
    simp only [lmin, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.1 hw with rfl | hw
    · exact le_trans (min_le_right _ _) (ih w (by simp))
    · rcases List.mem_cons.1 hw with rfl | hw
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih w (List.mem_cons_of_mem _ hw))

theorem le_lmin (m : ℝ) (l : List ℝ) (L : ℝ) (h : ∀ w ∈ m :: l, L ≤ w) : L ≤ lmin m l := by
  induction l with
  | nil => simpa [lmin] using h
  | cons a l ih =>
    simp only [lmin, List.foldr_cons] at ih ⊢
    exact le_min (h a (by simp)) (ih (fun w hw => h w (by
      rcases List.mem_cons.1 hw with rfl | hw <;> simp_all)))

theorem lmin_mem (m : ℝ) (l : List ℝ) : lmin m l ∈ m :: l := by
  induction l with
  | nil => simp [lmin]
  | cons a l ih =>
    simp only [lmin, List.foldr_cons] at ih ⊢
    rcases min_choice a (List.foldr min m l) with h | h <;> rw [h]
    · simp
    · rcases List.mem_cons.1 ih with h' | h' <;> simp [h']

/-! ## One Fourier–Motzkin step -/

/- For `P` with `a^P_j > 0` and `N` with `a^N_j < 0`: the combination
`(-a^N_j)·P + a^P_j·N`, whose `j`-th coefficient vanishes. -/
/- Eliminate variable `j`: keep the constraints with `a_j = 0`, and add all
positive/negative pair combinations. -/
theorem mem_elim {j : ℕ} {sys : System} {c : Constraint} :
    c ∈ elim j sys ↔ (c ∈ sys ∧ coef j c = 0) ∨
      ∃ P ∈ sys, 0 < coef j P ∧ ∃ N ∈ sys, coef j N < 0 ∧ combine j P N = c := by
  simp [elim, List.mem_flatMap, and_assoc]

theorem coef_combine (j : ℕ) (P N : Constraint) : coef j (combine j P N) = 0 := by
  simp only [coef, combine, getD_lc]; ring

theorem dot_combine (j : ℕ) (P N : Constraint) (x : ℕ → ℝ) :
    dot (combine j P N).1 x = (-coef j N) * dot P.1 x + coef j P * dot N.1 x := by
  simp [combine, dot_lc]

/- Every constraint of `elim j sys` has zero `j`-th coefficient. -/
theorem coef_elim {j : ℕ} {sys : System} {c : Constraint} (hc : c ∈ elim j sys) :
    coef j c = 0 := by
  rcases mem_elim.1 hc with ⟨_, h⟩ | ⟨P, _, _, N, _, _, rfl⟩
  · exact h
  · exact coef_combine j P N

/- Satisfaction of `elim j sys` does not depend on coordinate `j`. -/
theorem sat_elim_update (j : ℕ) (sys : System) (x : ℕ → ℝ) (t : ℝ) :
    Sat (elim j sys) (Function.update x j t) ↔ Sat (elim j sys) x := by
  have key : ∀ c ∈ elim j sys, dot c.1 (Function.update x j t) = dot c.1 x := by
    intro c hc
    have := coef_elim hc
    rw [dot_update]; simp only [coef] at this; rw [this]; ring
  constructor
  · intro h c hc; rw [← key c hc]; exact h c hc
  · intro h c hc; rw [key c hc]; exact h c hc

/- Soundness of one step: a solution of `sys` solves `elim j sys`. -/
theorem sat_elim_of_sat {j : ℕ} {sys : System} {x : ℕ → ℝ} (h : Sat sys x) :
    Sat (elim j sys) x := by
  intro c hc
  rcases mem_elim.1 hc with ⟨hc, _⟩ | ⟨P, hP, hPj, N, hN, hNj, rfl⟩
  · exact h c hc
  · rw [dot_combine]
    simp only [combine]
    have h1 := h P hP
    have h2 := h N hN
    have : 0 ≤ -coef j N := by linarith
    nlinarith

/- Residual of constraint `c` at `x` with respect to variable `j`:
`b - Σ_{i ≠ j} a_i x_i`. Then `c` holds at `update x j t` iff `a_j t ≤ resid`. -/
/- Back-substitution value for variable `j`: the largest lower bound if
there is one, else the smallest upper bound if there is one, else `0`. -/
theorem sat_update_iff (j : ℕ) (x : ℕ → ℝ) (t : ℝ) (c : Constraint) :
    dot c.1 (Function.update x j t) ≤ c.2 ↔ coef j c * t ≤ resid j x c := by
  rw [dot_update]; simp only [resid, coef]; constructor <;> intro h <;> linarith

/- Completeness of one step, constructively: if `x` solves `elim j sys`, then
replacing coordinate `j` by `pick j sys x` solves `sys`. -/
theorem sat_pick {j : ℕ} {sys : System} {x : ℕ → ℝ} (h : Sat (elim j sys) x) :
    Sat sys (Function.update x j (pick j sys x)) := by
  -- pairwise compatibility of lower and upper bounds
  have pair : ∀ P ∈ sys, 0 < coef j P → ∀ N ∈ sys, coef j N < 0 →
      resid j x N / coef j N ≤ resid j x P / coef j P := by
    intro P hP hPj N hN hNj
    have hc := h (combine j P N) (mem_elim.2 (Or.inr ⟨P, hP, hPj, N, hN, hNj, rfl⟩))
    rw [dot_combine] at hc
    simp only [combine] at hc
    have key : coef j N * resid j x P ≤ coef j P * resid j x N := by
      simp only [resid]; nlinarith
    rw [← neg_div_neg_eq, div_le_div_iff₀ (by linarith) hPj]
    nlinarith
  have hlow : ∀ N ∈ sys, coef j N < 0 → resid j x N / coef j N ≤ pick j sys x := by
    intro N hN hNj
    have hm : resid j x N / coef j N ∈
        (sys.filter (fun c => decide (coef j c < 0))).map (fun c => resid j x c / coef j c) :=
      List.mem_map.2 ⟨N, List.mem_filter.2 ⟨hN, by simpa using hNj⟩, rfl⟩
    unfold pick
    split
    · next _ _ l ls heq => rw [heq] at hm; exact le_lmax l ls _ hm
    · next _ _ _ _ heq _ => rw [heq] at hm; simp at hm
    · next _ _ heq _ => rw [heq] at hm; simp at hm
  have hup : ∀ P ∈ sys, 0 < coef j P → pick j sys x ≤ resid j x P / coef j P := by
    intro P hP hPj
    have hm : resid j x P / coef j P ∈
        (sys.filter (fun c => decide (0 < coef j c))).map (fun c => resid j x c / coef j c) :=
      List.mem_map.2 ⟨P, List.mem_filter.2 ⟨hP, by simpa using hPj⟩, rfl⟩
    unfold pick
    split
    · next _ _ l ls heq =>
      apply lmax_le
      intro w hw
      rw [← heq] at hw
      obtain ⟨N, hN, rfl⟩ := List.mem_map.1 hw
      obtain ⟨hN, hNj⟩ := List.mem_filter.1 hN
      exact pair P hP hPj N hN (by simpa using hNj)
    · next _ _ u us _ heq => rw [heq] at hm; exact lmin_le u us _ hm
    · next _ _ _ heq => rw [heq] at hm; simp at hm
  intro c hc
  rw [sat_update_iff]
  rcases lt_trichotomy (coef j c) 0 with hneg | hzero | hpos
  · have := hlow c hc hneg
    rwa [div_le_iff_of_neg hneg, mul_comm] at this
  · have := h c (mem_elim.2 (Or.inl ⟨hc, hzero⟩))
    simp only [resid, hzero]; linarith
  · have := hup c hc hpos
    rwa [le_div_iff₀ hpos, mul_comm] at this

/- **One Fourier–Motzkin step is sound and complete.** -/
theorem elim_sound_complete (j : ℕ) (sys : System) (x : ℕ → ℝ) :
    (∃ t, Sat sys (Function.update x j t)) ↔ Sat (elim j sys) x := by
  constructor
  · rintro ⟨t, ht⟩
    exact (sat_elim_update j sys x t).1 (sat_elim_of_sat ht)
  · intro h
    exact ⟨_, sat_pick h⟩


/-! ## Eliminating a sequence of variables, and back-substitution -/

/- Eliminate the variables `js` in order. -/
/- The stored intermediate systems: `(j, S)` with `S` the system just before
eliminating `j`. -/
/- Back-substitution: starting from a solution `p` of the last system, walk
the stages backwards, resetting each eliminated coordinate `j` to
`pick j S p'` (`S` = the system before eliminating `j`). -/
theorem sat_backSubst (js : List ℕ) (s : System) (p : ℕ → ℝ) (h : Sat (elimSeq js s) p) :
    Sat s (backSubst (stages js s) p) := by
  induction js generalizing s with
  | nil => simpa [elimSeq, stages, backSubst] using h
  | cons j js ih =>
    simp only [stages, backSubst]
    exact sat_pick (ih (elim j s) h)

theorem backSubst_of_not_mem (js : List ℕ) (s : System) (p : ℕ → ℝ) (i : ℕ) (hi : i ∉ js) :
    backSubst (stages js s) p i = p i := by
  induction js generalizing s with
  | nil => rfl
  | cons j js ih =>
    simp only [stages, backSubst]
    rw [Function.update_of_ne (fun h => hi (by rw [h]; exact List.mem_cons_self))]
    exact ih (elim j s) (fun h => hi (List.mem_cons_of_mem _ h))

/- Soundness of a sequence of eliminations: a solution of `s`, with the
eliminated coordinates changed arbitrarily, solves `elimSeq js s`. -/
theorem sat_elimSeq (js : List ℕ) (s : System) (y y' : ℕ → ℝ) (h : Sat s y)
    (hy : ∀ i ∉ js, y' i = y i) : Sat (elimSeq js s) y' := by
  induction js generalizing s y with
  | nil =>
    have : y' = y := funext fun i => hy i (by simp)
    simpa [elimSeq, this] using h
  | cons j js ih =>
    simp only [elimSeq]
    apply ih (elim j s) (Function.update y j (y' j))
    · exact (sat_elim_update j s y _).2 (sat_elim_of_sat h)
    · intro i hi
      by_cases hij : i = j
      · subst hij; simp
      · rw [Function.update_of_ne hij]
        exact hy i (by simp [hij, hi])

/-! ## Maximizing a linear objective -/

/- Outcome of the LP solver. -/
/- Shift all variables up by one and put a fresh variable `z` at index `0`,
together with the constraint `z - c·x ≤ 0`. -/
theorem sat_lift (c : List ℝ) (sys : System) (y : ℕ → ℝ) :
    Sat (lift c sys) y ↔ y 0 ≤ dot c (fun i => y (i + 1)) ∧ Sat sys (fun i => y (i + 1)) := by
  simp only [Sat, lift, List.forall_mem_cons, List.forall_mem_map, dot, dot_neg]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, fun p hp => by linarith [h2 p hp]⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, fun p hp => by linarith [h2 p hp]⟩

theorem length_le_foldr_max (L : List (List ℝ)) :
    ∀ a ∈ L, a.length ≤ L.foldr (fun a m => max a.length m) 0 := by
  induction L with
  | nil => simp
  | cons b L ih =>
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact le_max_left _ _
    · exact le_trans (ih a ha) (le_max_right _ _)

/- Number of original variables that occur (max list length). -/
/- After lifting, the original variables are `1, …, nvars`. -/
/- The system in `z` alone obtained by eliminating every original variable. -/
/- `zcons z x = (z, x 0, x 1, …)`. -/
/- The final one-variable constraints `α z ≤ β`, as pairs `(α, β)`. -/
theorem dot_zcons_zero (a : List ℝ) (z : ℝ) : dot a (zcons z (fun _ => 0)) = a.headD 0 * z := by
  cases a with
  | nil => simp [dot]
  | cons a as => simp only [dot, zcons, List.headD_cons]; rw [dot_zero]; ring

theorem sat_final_iff (c : List ℝ) (sys : System) (z : ℝ) :
    Sat (finalSys c sys) (zcons z (fun _ => 0)) ↔ ∀ p ∈ bounds c sys, p.1 * z ≤ p.2 := by
  simp only [Sat, bounds, dot_zcons_zero, List.forall_mem_map]

/- The point recovered by back-substitution from a value `z` of the objective. -/
theorem recover_spec (c : List ℝ) (sys : System) (z : ℝ)
    (h : ∀ p ∈ bounds c sys, p.1 * z ≤ p.2) :
    Sat sys (recover c sys z) ∧ z ≤ dot c (recover c sys z) := by
  have hy := sat_backSubst _ _ _ ((sat_final_iff c sys z).2 h)
  rw [sat_lift] at hy
  have h0 : backSubst (stages (elimOrder c sys) (lift c sys)) (zcons z (fun _ => 0)) 0 = z :=
    backSubst_of_not_mem _ _ _ 0 (by simp [elimOrder])
  rw [h0] at hy
  exact ⟨hy.2, hy.1⟩

/- The final one-variable system describes exactly the values `z` that are
dominated by some feasible objective value. -/
theorem bounds_iff (c : List ℝ) (sys : System) (z : ℝ) :
    (∀ p ∈ bounds c sys, p.1 * z ≤ p.2) ↔ ∃ x, Sat sys x ∧ z ≤ dot c x := by
  constructor
  · intro h; exact ⟨_, recover_spec c sys z h⟩
  · rintro ⟨x, hx, hz⟩
    set n := nvars c sys
    let x' : ℕ → ℝ := fun i => if i < n then x i else 0
    have hagree : ∀ a ∈ c :: sys.map Prod.fst, dot a x' = dot a x := fun a ha =>
      dot_congr a n x' x (length_le_foldr_max _ a ha) (fun i hi => by simp [x', hi])
    have hsat : Sat (lift c sys) (zcons z x') := by
      rw [sat_lift]
      refine ⟨?_, fun p hp => ?_⟩
      · show z ≤ dot c x'
        rw [hagree c (by simp)]; exact hz
      · show dot p.1 x' ≤ p.2
        rw [hagree p.1 (List.mem_cons_of_mem _ (List.mem_map_of_mem hp))]; exact hx p hp
    rw [← sat_final_iff]
    apply sat_elimSeq _ _ _ _ hsat
    intro i hi
    cases i with
    | zero => rfl
    | succ k =>
      simp only [elimOrder, List.mem_range'_1] at hi
      simp only [zcons, x']
      rw [if_neg (by omega)]

/- **The LP solver.** Maximize `c·x` subject to `sys` by eliminating all the
original variables from `sys ∧ z ≤ c·x` and reading off the bounds on `z`. -/
/- **Point recovery** by back-substitution through the stored stages. -/
/- **Infeasible is correct.** -/
theorem lpMax_infeasible {c : List ℝ} {sys : System} (h : lpMax c sys = .infeasible) :
    ∀ x, ¬ Sat sys x := by
  simp only [lpMax] at h
  by_cases hall : (bounds c sys).all (fun p => decide (0 < p.1 ∨ (p.1 = 0 ∧ 0 ≤ p.2))) = true
  · rw [if_pos hall] at h; split at h <;> cases h
  · intro x hx
    simp only [List.all_eq_true, decide_eq_true_eq, not_forall] at hall
    obtain ⟨p, hp, hbad⟩ := hall
    have hF : ∀ z ≤ dot c x, p.1 * z ≤ p.2 := fun z hz => (bounds_iff c sys z).2 ⟨x, hx, hz⟩ p hp
    rcases lt_trichotomy p.1 0 with hneg | hzero | hpos
    · have hz := hF (min (dot c x) ((p.2 + 1) / p.1)) (min_le_left _ _)
      have h1 : p.1 * ((p.2 + 1) / p.1) ≤ p.1 * min (dot c x) ((p.2 + 1) / p.1) :=
        mul_le_mul_of_nonpos_left (min_le_right _ _) hneg.le
      rw [mul_div_cancel₀ _ hneg.ne] at h1
      linarith
    · have := hF (dot c x) le_rfl
      rw [hzero, zero_mul] at this
      exact hbad (Or.inr ⟨hzero, this⟩)
    · exact hbad (Or.inl hpos)

/- **Unbounded is correct.** -/
theorem lpMax_unbounded {c : List ℝ} {sys : System} (h : lpMax c sys = .unbounded) :
    ∀ M, ∃ x, Sat sys x ∧ M < dot c x := by
  simp only [lpMax] at h
  by_cases hall : (bounds c sys).all (fun p => decide (0 < p.1 ∨ (p.1 = 0 ∧ 0 ≤ p.2))) = true
  · rw [if_pos hall] at h
    split at h
    · next heq =>
      intro M
      simp only [List.all_eq_true, decide_eq_true_eq] at hall
      have hF : ∀ p ∈ bounds c sys, p.1 * (M + 1) ≤ p.2 := by
        intro p hp
        rcases hall p hp with hpos | ⟨hzero, hb⟩
        · have : p.2 / p.1 ∈ ((bounds c sys).filter (fun p => decide (0 < p.1))).map
              (fun p => p.2 / p.1) := List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, by simpa⟩, rfl⟩
          rw [heq] at this; simp at this
        · rw [hzero, zero_mul]; exact hb
      obtain ⟨x, hx, hle⟩ := (bounds_iff c sys (M + 1)).1 hF
      exact ⟨x, hx, by linarith⟩
    · cases h
  · rw [if_neg hall] at h; cases h

/- The value returned by `lpMax` is feasible for the final system and is an
upper bound for every feasible objective value. -/
theorem lpMax_opt_aux {c : List ℝ} {sys : System} {v : ℝ} (h : lpMax c sys = .opt v) :
    (∀ p ∈ bounds c sys, p.1 * v ≤ p.2) ∧ ∀ x, Sat sys x → dot c x ≤ v := by
  simp only [lpMax] at h
  by_cases hall : (bounds c sys).all (fun p => decide (0 < p.1 ∨ (p.1 = 0 ∧ 0 ≤ p.2))) = true
  · rw [if_pos hall] at h
    split at h
    · cases h
    · next u us heq =>
      cases h
      simp only [List.all_eq_true, decide_eq_true_eq] at hall
      refine ⟨fun p hp => ?_, fun x hx => ?_⟩
      · rcases hall p hp with hpos | ⟨hzero, hb⟩
        · have hm : p.2 / p.1 ∈ ((bounds c sys).filter (fun p => decide (0 < p.1))).map
              (fun p => p.2 / p.1) := List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, by simpa⟩, rfl⟩
          rw [heq] at hm
          have := lmin_le u us _ hm
          rw [le_div_iff₀ hpos, mul_comm] at this
          exact this
        · rw [hzero, zero_mul]; exact hb
      · have hm := lmin_mem u us
        rw [← heq] at hm
        obtain ⟨p, hp, hpv⟩ := List.mem_map.1 hm
        obtain ⟨hp, hpos⟩ := List.mem_filter.1 hp
        simp only [decide_eq_true_eq] at hpos
        have := (bounds_iff c sys (dot c x)).2 ⟨x, hx, le_rfl⟩ p hp
        rw [← hpv, le_div_iff₀ hpos, mul_comm]
        exact this
  · rw [if_neg hall] at h; cases h

/- **Point recovery is correct**: when `lpMax` returns `opt v`, `argmax` is
feasible and attains `v`. -/
theorem argmax_spec {c : List ℝ} {sys : System} {v : ℝ} (h : lpMax c sys = .opt v) :
    Sat sys (argmax c sys) ∧ dot c (argmax c sys) = v := by
  obtain ⟨hF, hub⟩ := lpMax_opt_aux h
  have hr := recover_spec c sys v hF
  simp only [argmax, h]
  exact ⟨hr.1, le_antisymm (hub _ hr.1) hr.2⟩

/- The set of feasible objective values. -/
/- **Optimum is correct**: `v` is the greatest feasible objective value. -/
theorem lpMax_opt {c : List ℝ} {sys : System} {v : ℝ} (h : lpMax c sys = .opt v) :
    (∃ x, Sat sys x ∧ dot c x = v) ∧ (∀ x, Sat sys x → dot c x ≤ v) ∧
      sSup (objValues c sys) = v := by
  have hg : IsGreatest (objValues c sys) v :=
    ⟨⟨argmax c sys, argmax_spec h⟩, by rintro _ ⟨x, hx, rfl⟩; exact (lpMax_opt_aux h).2 x hx⟩
  exact ⟨⟨argmax c sys, argmax_spec h⟩, (lpMax_opt_aux h).2, hg.csSup_eq⟩

/- **Feasible and bounded ⇒ `lpMax` returns the supremum.** -/
theorem lpMax_of_feasible_bddAbove {c : List ℝ} {sys : System} (hfeas : ∃ x, Sat sys x)
    (hbdd : BddAbove (objValues c sys)) : lpMax c sys = .opt (sSup (objValues c sys)) := by
  cases hr : lpMax c sys with
  | infeasible => obtain ⟨x, hx⟩ := hfeas; exact absurd hx (lpMax_infeasible hr x)
  | unbounded =>
    obtain ⟨M, hM⟩ := hbdd
    obtain ⟨x, hx, hlt⟩ := lpMax_unbounded hr M
    exact absurd (hM ⟨x, hx, rfl⟩) (not_le.2 hlt)
  | opt v => rw [(lpMax_opt hr).2.2]

/- Exact characterization of the three outcomes. -/
theorem lpMax_eq_infeasible_iff (c : List ℝ) (sys : System) :
    lpMax c sys = .infeasible ↔ ¬ ∃ x, Sat sys x := by
  refine ⟨fun h ⟨x, hx⟩ => lpMax_infeasible h x hx, fun h => ?_⟩
  cases hr : lpMax c sys with
  | infeasible => rfl
  | unbounded => exact absurd ((lpMax_unbounded hr 0).imp fun x hx => hx.1) h
  | opt v => exact absurd ⟨_, (argmax_spec hr).1⟩ h

theorem lpMax_eq_unbounded_iff (c : List ℝ) (sys : System) :
    lpMax c sys = .unbounded ↔ (∃ x, Sat sys x) ∧ ¬ BddAbove (objValues c sys) := by
  constructor
  · intro h
    refine ⟨(lpMax_unbounded h 0).imp fun x hx => hx.1, fun ⟨M, hM⟩ => ?_⟩
    obtain ⟨x, hx, hlt⟩ := lpMax_unbounded h M
    exact absurd (hM ⟨x, hx, rfl⟩) (not_le.2 hlt)
  · rintro ⟨hfeas, hnb⟩
    cases hr : lpMax c sys with
    | infeasible => obtain ⟨x, hx⟩ := hfeas; exact absurd hx (lpMax_infeasible hr x)
    | unbounded => rfl
    | opt v =>
      exact absurd ⟨v, by rintro _ ⟨x, hx, rfl⟩; exact (lpMax_opt hr).2.1 x hx⟩ hnb

end MTSPFM

open FourierMotzkin in
theorem solution (c : List ℝ) (sys : System) :
    (lpMax c sys = .infeasible ↔ ¬ ∃ x, Sat sys x) ∧
    (lpMax c sys = .unbounded ↔ (∃ x, Sat sys x) ∧ ¬ BddAbove (objValues c sys)) ∧
    (∀ v, lpMax c sys = .opt v →
      Sat sys (argmax c sys) ∧ dot c (argmax c sys) = v ∧ ∀ x, Sat sys x → dot c x ≤ v) :=
  ⟨MTSPFM.lpMax_eq_infeasible_iff c sys, MTSPFM.lpMax_eq_unbounded_iff c sys, fun v h =>
    ⟨(MTSPFM.argmax_spec h).1, (MTSPFM.argmax_spec h).2, (MTSPFM.lpMax_opt h).2.1⟩⟩
