-- Prove2me | solution 1 for FoundationsML.MaxEnt.maxent_l1_generalization_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T18:10:01.268361+00:00
-- url     : https://prove2.me/submissions/a20c1fd8-c647-4f8b-8c5b-5c0223bc658b

import Mathlib
import Definitions.Def_FoundationsML_MaxEnt_LogLoss
import Definitions.Def_FoundationsML_MaxEnt_EmpiricalLogLoss
import Definitions.Def_FoundationsML_MaxEnt_RademacherComplexity

section HelpersEd7f

/-- Tangent bound for `a ↦ exp a + exp (-a)` at `c = log 2 / 2`, in multiplicative form. -/
theorem tangent_mul_ed7f (a : ℝ) :
    (Real.exp (Real.log 2 / 2) + Real.exp (-(Real.log 2 / 2))) *
        Real.exp ((a - Real.log 2 / 2) / 3) ≤ Real.exp a + Real.exp (-a) := by
  set c := Real.log 2 / 2 with hc
  set E := Real.exp c with hEdef
  have hE : 0 < E := Real.exp_pos c
  have hE2 : E * E = 2 := by
    rw [hEdef, ← Real.exp_add, show c + c = Real.log 2 by rw [hc]; ring]
    exact Real.exp_log (by norm_num)
  have hEinv : Real.exp (-c) = E / 2 := by
    have h1 : E * Real.exp (-c) = 1 := by
      rw [hEdef, ← Real.exp_add]; simp
    field_simp
    nlinarith [h1, hE2]
  set u := a - c with hu
  have hexpa : Real.exp a = E * Real.exp u := by
    rw [hEdef, ← Real.exp_add, hu]; congr 1; ring
  have hexpna : Real.exp (-a) = E / 2 * Real.exp (-u) := by
    rw [← hEinv, ← Real.exp_add, hu]; congr 1; ring
  have hconv := convexOn_exp.2 (Set.mem_univ u) (Set.mem_univ (-u))
    (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num)
  simp only [smul_eq_mul] at hconv
  have hlin : (2 / 3 : ℝ) * u + 1 / 3 * -u = u / 3 := by ring
  rw [hlin] at hconv
  rw [hEinv, hexpa, hexpna]
  have := mul_le_mul_of_nonneg_left hconv hE.le
  nlinarith [this]

/-- Tangent bound for `g a = log (exp a + exp (-a))` at `c = log 2 / 2`. -/
theorem tangent_log_ed7f (a : ℝ) :
    Real.log (Real.exp (Real.log 2 / 2) + Real.exp (-(Real.log 2 / 2))) +
        (a - Real.log 2 / 2) / 3 ≤ Real.log (Real.exp a + Real.exp (-a)) := by
  have hpos : 0 < Real.exp (Real.log 2 / 2) + Real.exp (-(Real.log 2 / 2)) := by positivity
  have h := Real.log_le_log (by positivity) (tangent_mul_ed7f a)
  rw [Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  exact h

theorem gt_log_two_ed7f (b : ℝ) (hb : b ≠ 0) :
    Real.log 2 < Real.log (Real.exp b + Real.exp (-b)) := by
  have h := (Real.one_lt_cosh (x := b)).2 hb
  rw [Real.cosh_eq] at h
  exact Real.log_lt_log (by norm_num) (by linarith)

theorem nonneg_log_ed7f (b : ℝ) : 0 ≤ Real.log (Real.exp b + Real.exp (-b)) := by
  have h := Real.one_le_cosh b
  rw [Real.cosh_eq] at h
  exact Real.log_nonneg (by linarith)

end HelpersEd7f

open MeasureTheory FoundationsML.MaxEnt in
theorem solution : ¬ (∀ {X : Type} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {N : ℕ} (p0 : X → ℝ) (hp0 : ∀ x, 0 < p0 x)
    (Φ : X → Fin N → ℝ) (r : ℝ) (hr : 0 ≤ r) (hΦ : ∀ x j, |Φ x j| ≤ r)
    (H : Set (X → ℝ)) (hHΦ : ∀ j : Fin N, (fun x => Φ x j) ∈ H)
    (D : Measure X) [IsProbabilityMeasure D]
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ),
    let lam := 2 * RademacherComplexity D H m + r * Real.sqrt (Real.log (2 / δ) / (2 * m))
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ ŵ : Fin N → ℝ,
        (∀ w : Fin N → ℝ,
            lam * (∑ j, |ŵ j|) + EmpiricalLogLoss p0 Φ S ŵ ≤
              lam * (∑ j, |w j|) + EmpiricalLogLoss p0 Φ S w) →
        LogLoss p0 Φ D ŵ ≤
          ⨅ w : Fin N → ℝ, (LogLoss p0 Φ D w + 2 * (∑ j, |w j|) * lam)}).toReal) := by
  intro h
  -- the counterexample data
  set D : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure with hDdef
  set δ : ℝ := 2 * Real.exp (-(8 / 9)) with hδdef
  have hδpos : 0 < δ := by positivity
  have hmain := h (X := Bool) (N := 1) (fun _ => (1 : ℝ)) (fun _ => one_pos)
    (fun x _ => if x then (1 : ℝ) else -1) 1 zero_le_one
    (fun x _ => by split_ifs <;> norm_num) Set.univ (fun _ => Set.mem_univ _) D 1 one_pos δ hδpos
  -- Rademacher complexity of `univ` is the junk value `0` (every supremum is unbounded)
  have hR : RademacherComplexity D (Set.univ : Set (Bool → ℝ)) 1 = 0 := by
    have hE : ∀ S : Fin 1 → Bool,
        EmpiricalRademacherComplexity (Set.univ : Set (Bool → ℝ)) S = 0 := by
      intro S
      unfold EmpiricalRademacherComplexity
      rw [Finset.sum_eq_zero, mul_zero]
      intro σ _
      simp only [Set.mem_univ, ciSup_const]
      apply Real.iSup_of_not_bddAbove
      rintro ⟨B, hB⟩
      have hle := hB (Set.mem_range_self
        (fun _ : Bool => (if σ 0 then (1 : ℝ) else -1) * (|B| + 1)))
      simp only [Fin.sum_univ_one, Nat.cast_one, div_one, one_mul] at hle
      have hB' := le_abs_self B
      split_ifs at hle <;> nlinarith
    unfold RademacherComplexity
    simp only [hE, integral_zero]
  have hsqrt : Real.sqrt (Real.log (2 / δ) / (2 * ((1 : ℕ) : ℝ))) = 2 / 3 := by
    have hl : Real.log (2 / δ) = 8 / 9 := by
      rw [hδdef, show (2 : ℝ) / (2 * Real.exp (-(8 / 9))) = Real.exp (8 / 9) by
        rw [Real.exp_neg]; field_simp]
      exact Real.log_exp _
    rw [hl, show (8 / 9 : ℝ) / (2 * ((1 : ℕ) : ℝ)) = (2 / 3) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hδlt : δ < 1 := by
    have h2 : Real.exp (Real.log 2) < Real.exp (8 / 9) :=
      Real.exp_lt_exp.2 (by linarith [Real.log_two_lt_d9])
    rw [Real.exp_log (by norm_num)] at h2
    have h1 : Real.exp (-(8 / 9)) * Real.exp (8 / 9) = 1 := by
      rw [← Real.exp_add]; simp
    have hp := Real.exp_pos (-(8 / 9 : ℝ))
    rw [hδdef]; nlinarith
  -- closed forms for the Gibbs model
  have hZ : ∀ w : Fin 1 → ℝ,
      PartitionFunction (fun _ : Bool => (1 : ℝ)) (fun x _ => if x then (1 : ℝ) else -1) w
        = Real.exp (w 0) + Real.exp (-(w 0)) := by
    intro w
    simp [PartitionFunction]
  have hG : ∀ (w : Fin 1 → ℝ) (x : Bool),
      -Real.log (GibbsDistribution (fun _ : Bool => (1 : ℝ))
          (fun x _ => if x then (1 : ℝ) else -1) w x)
        = Real.log (Real.exp (w 0) + Real.exp (-(w 0))) - w 0 * (if x then (1 : ℝ) else -1) := by
    intro w x
    unfold GibbsDistribution
    rw [hZ w, one_mul, Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp,
      Fin.sum_univ_one]
    ring
  have hELL : ∀ (S : Fin 1 → Bool) (w : Fin 1 → ℝ),
      EmpiricalLogLoss (fun _ : Bool => (1 : ℝ)) (fun x _ => if x then (1 : ℝ) else -1) S w
        = Real.log (Real.exp (w 0) + Real.exp (-(w 0)))
            - w 0 * (if S 0 then (1 : ℝ) else -1) := by
    intro S w
    unfold EmpiricalLogLoss
    rw [Fin.sum_univ_one, hG w (S 0)]
    simp
  have hLD : ∀ w : Fin 1 → ℝ,
      LogLoss (fun _ : Bool => (1 : ℝ)) (fun x _ => if x then (1 : ℝ) else -1) D w
        = Real.log (Real.exp (w 0) + Real.exp (-(w 0))) := by
    intro w
    unfold LogLoss
    rw [integral_fintype Integrable.of_finite]
    simp only [hG, Fintype.sum_bool, smul_eq_mul]
    have hsing : ∀ b : Bool, D.real {b} = 1 / 2 := by
      intro b
      rw [measureReal_def, hDdef, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b),
        PMF.uniformOfFintype_apply]
      simp
    rw [hsing true, hsing false]
    simp only [if_true, Bool.false_eq_true, if_false]
    ring
  -- the event is empty
  have hzero : ∀ s : Set (Fin 1 → Bool), (∀ S ∈ s, False) →
      (Measure.pi (fun _ : Fin 1 => D) s).toReal = 0 := by
    intro s hs
    rw [Set.eq_empty_of_forall_notMem hs, measure_empty, ENNReal.toReal_zero]
  simp only [] at hmain
  rw [hR, hsqrt, hzero _ ?_] at hmain
  · linarith
  intro S hS
  simp only [Set.mem_ofPred_eq] at hS
  set c := Real.log 2 / 2 with hc
  have hc0 : 0 < c := by rw [hc]; have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  set φ : ℝ := if S 0 then (1 : ℝ) else -1 with hφ
  have hφ2 : φ = 1 ∨ φ = -1 := by rw [hφ]; split_ifs <;> simp
  have hfin := hS (fun _ => φ * c) ?_
  · -- the minimizer is worse than the comparator `w = 0`
    simp only [hLD] at hfin
    have hbdd : BddBelow (Set.range fun w : Fin 1 → ℝ =>
        Real.log (Real.exp (w 0) + Real.exp (-(w 0))) +
          2 * (∑ j, |w j|) * (2 * 0 + 1 * (2 / 3))) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨w, rfl⟩
      have h1 := nonneg_log_ed7f (w 0)
      have h2 : 0 ≤ ∑ j, |w j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
      nlinarith
    have hle := ciInf_le hbdd (fun _ => (0 : ℝ))
    simp only [abs_zero, Finset.sum_const_zero, mul_zero, zero_mul, add_zero, neg_zero,
      Real.exp_zero] at hle
    have hne : φ * c ≠ 0 := by
      rcases hφ2 with h' | h' <;> rw [h'] <;> linarith
    have hgt := gt_log_two_ed7f (φ * c) hne
    have h11 : (1 : ℝ) + 1 = 2 := by norm_num
    rw [h11] at hle
    linarith
  · -- `fun _ => φ * c` minimises the empirical objective
    intro w
    rw [hELL, hELL]
    simp only [Fin.sum_univ_one]
    set a := w 0
    have hφS : (if S 0 then (1 : ℝ) else -1) = φ := rfl
    rw [hφS]
    have ha := le_abs_self a
    have ha' := neg_abs_le a
    rcases hφ2 with h' | h'
    · rw [h']
      have ht := tangent_log_ed7f a
      rw [← hc] at ht
      simp only [one_mul, abs_of_pos hc0, mul_one]
      nlinarith
    · rw [h']
      have ht := tangent_log_ed7f (-a)
      rw [← hc, neg_neg, add_comm (Real.exp (-a))] at ht
      have hce : Real.log (Real.exp (-1 * c) + Real.exp (-(-1 * c)))
          = Real.log (Real.exp c + Real.exp (-c)) := by
        rw [neg_one_mul, neg_neg, add_comm]
      rw [hce]
      simp only [neg_one_mul, abs_neg, abs_of_pos hc0]
      nlinarith
