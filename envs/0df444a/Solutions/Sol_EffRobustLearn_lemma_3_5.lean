-- Prove2me | solution 1 for EffRobustLearn.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-27T02:28:18.540444+00:00
-- url     : https://prove2.me/submissions/c1eff1ee-6e7a-4c8d-a763-49369f819153

import Mathlib
import Definitions.Def_EffRobustLearn_feasibleSet

open EffRobustLearn

/-- Every evaluation vector has all coordinates in `{±1}`. -/
theorem evalVec_in_pm1 {X : Type*} {n m : ℕ} (c : X → Bool) (Sinp : Fin n → X × Bool)
    (Sref : Fin m → X) :
    ∀ i, (evalVec (toPM c) Sinp Sref) i ∈ ({(-1 : ℝ), 1} : Set ℝ) := by
  intro i
  dsimp only [evalVec]
  cases i with
  | inl i =>
      by_cases hb : c (Sinp i).1
      · simp [hb, toPM, pm]
      · simp [hb, toPM, pm]
  | inr j =>
      by_cases hb : c (Sref j)
      · simp [hb, toPM, pm]
      · simp [hb, toPM, pm]

/-- `pm` of the decision of `x = 1` recovers `x` when `x ∈ {±1}`. -/
theorem pm_decide_pm1 {x : ℝ} (hx : x ∈ ({(-1 : ℝ), 1} : Set ℝ)) : pm (decide (x = 1)) = x := by
  by_cases h1 : x = 1
  · have hb : decide (x = 1) = true := by
      simp [h1, decide_eq_true]
    rw [hb, pm]
    exact h1.symm
  · obtain (h | h') : x = -1 ∨ x = 1 := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
    · have hb : decide (x = 1) = false := by
        simp [h1, decide_eq_false]
      rw [hb, pm]
      exact h.symm
    · contradiction

/-- The set of all sample vectors with every coordinate in `{±1}` is finite. -/
theorem pm1_cube_finite {n m : ℕ} :
    {v : SampleVec n m | ∀ i, v i ∈ ({(-1 : ℝ), 1} : Set ℝ)}.Finite := by
  have hsub : {v : SampleVec n m | ∀ i, v i ∈ ({(-1 : ℝ), 1} : Set ℝ)} ⊆
      Set.range (fun e : (Fin n ⊕ Fin m) → Bool => WithLp.toLp 2 (fun i => pm (e i))) := by
    rintro v hv
    rw [Set.mem_range]
    refine ⟨fun i => (v i = 1), ?_⟩
    · ext i
      simpa using pm_decide_pm1 (hv i)
  exact (Set.finite_range (fun (e : (Fin n ⊕ Fin m) → Bool) => WithLp.toLp 2 (fun i => pm (e i)))).subset hsub

/-- The image of the class under `evalVec` is finite (a subset of the finite `{±1}` cube). -/
theorem feasibleImage_finite {X : Type*} {n m : ℕ} (C : Set (X → Bool))
    (Sinp : Fin n → X × Bool) (Sref : Fin m → X) :
    ((fun c => evalVec (toPM c) Sinp Sref) '' C).Finite := by
  refine pm1_cube_finite.subset fun v hv => by
    obtain ⟨c, _, rfl⟩ := hv
    exact fun i => evalVec_in_pm1 c Sinp Sref i

namespace P2MHole03_30db78a1
universe u_1
theorem solution {X : Type u_1} {n m : ℕ} (c : X → Bool) (Sinp : Fin n → X × Bool) (Sref : Fin m → X) :
  ‖evalVec (toPM c) Sinp Sref‖ ≤ √(↑n + ↑m) := by
  have hsq : ‖evalVec (toPM c) Sinp Sref‖ ^ 2 ≤ (n + m : ℝ) := by
    set f : (Fin n ⊕ Fin m) → ℝ :=
      Sum.elim (fun i => if c (Sinp i).1 then 1 else -1) (fun j => if c (Sref j) then 1 else -1) with hf
    show ‖WithLp.toLp 2 f‖ ^ 2 ≤ (n + m : ℝ)
    rw [EuclideanSpace.real_norm_sq_eq]
    dsimp only [WithLp.toLp]
    have hsq2 : ∀ i : Fin n ⊕ Fin m, f i ^ 2 = 1 := by
      intro i
      rcases i with (i | j)
      · cases c (Sinp i).1 <;> simp [f]
      · cases c (Sref j) <;> simp [f]
    rw [Finset.sum_congr rfl (fun x _ => hsq2 x)]
    have hsum : (∑ i : Fin n ⊕ Fin m, (1 : ℝ)) = (n + m : ℝ) := by
      simp [Fintype.card_sum]
    rw [hsum]
  have hfin : (‖evalVec (toPM c) Sinp Sref‖ : ℝ) ≤ √(↑n + ↑m) := by
    exact Real.le_sqrt_of_sq_le hsq
  exact hfin
end P2MHole03_30db78a1

/-- Each evaluation vector has L2-norm at most `√(n + m)` (sum of squared `±1` coordinates). -/
-- riskiest
theorem evalVec_norm_le {X : Type*} {n m : ℕ} (c : X → Bool) (Sinp : Fin n → X × Bool)
    (Sref : Fin m → X) :
    ‖evalVec (toPM c) Sinp Sref‖ ≤ Real.sqrt ((n : ℝ) + m) := by
  (first | exact P2MHole03_30db78a1.solution c Sinp Sref | (apply P2MHole03_30db78a1.solution <;> assumption))

/-- The sublevel sets of the norm are convex (triangle inequality). -/
theorem norm_sublevel_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {R : ℝ} :
    Convex ℝ {v : E | ‖v‖ ≤ R} := by
  refine fun (v : E) hv (w : E) hw (a b : ℝ) ha hb hab => by
    calc ‖a • v + b • w‖ ≤ ‖a • v‖ + ‖b • w‖ := norm_add_le (a • v) (b • w)
      _ ≤ ‖a‖ * ‖v‖ + ‖b‖ * ‖w‖ :=
        add_le_add (norm_smul_le a v) (norm_smul_le b w)
      _ = |a| * ‖v‖ + |b| * ‖w‖ := by
        have ha' : ‖a‖ = |a| := by norm_num
        have hb' : ‖b‖ = |b| := by norm_num
        rw [ha', hb']
      _ = a * ‖v‖ + b * ‖w‖ := by
        rw [abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * R + b * R :=
        add_le_add (mul_le_mul_of_nonneg_left hv ha) (mul_le_mul_of_nonneg_left hw hb)
      _ = (a + b) * R := by ring
      _ = R := by simpa [hab]

/-- The feasible set is contained in the closed ball of radius `√(n + m)`. -/
theorem feasibleSet_in_ball {X : Type*} {n m : ℕ} (C : Set (X → Bool))
    (Sinp : Fin n → X × Bool) (Sref : Fin m → X) :
    ∀ v ∈ feasibleSet C Sinp Sref, ‖v‖ ≤ Real.sqrt ((n : ℝ) + m) := by
  intro v hv
  have hsub : (fun c => evalVec (toPM c) Sinp Sref) '' C ⊆
      {v : SampleVec n m | ‖v‖ ≤ Real.sqrt ((n : ℝ) + m)} := by
    rintro _ ⟨c, hc, rfl⟩
    exact evalVec_norm_le c Sinp Sref
  have hconv : Convex ℝ {v : SampleVec n m | ‖v‖ ≤ Real.sqrt ((n : ℝ) + m)} :=
    norm_sublevel_convex
  exact convexHull_min hsub hconv hv

namespace P2MHole05_34103c8a
universe u_1
theorem solution {E : Type u_1} [inst : SeminormedAddCommGroup E] {R : ℝ} (s : Set E)
  (h : ∀ v ∈ s, ‖v‖ ≤ R) (hR : (0 : ℝ) ≤ R) : Metric.diam s ≤ (2 : ℝ) * R := by
  have h2 : 0 ≤ (2 : ℝ) * R := by nlinarith
  rw [Metric.diam]
  calc (Metric.ediam s).toReal
      _ ≤ (ENNReal.ofReal ((2 : ℝ) * R)).toReal := by
        have hd : Metric.ediam s ≤ ENNReal.ofReal ((2 : ℝ) * R) := by
          apply Metric.ediam_le
          intro x hx y hy
          have hxy : dist x y ≤ (2 : ℝ) * R := by
            rw [dist_eq_norm']
            calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le y x
              _ ≤ R + R := add_le_add (h y hy) (h x hx)
              _ = 2 * R := by ring
          rw [edist_le_ofReal h2]
          exact hxy
        have htop : ENNReal.ofReal ((2 : ℝ) * R) ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
        exact ENNReal.toNNReal_mono htop hd
      _ = (2 : ℝ) * R := by rw [ENNReal.toReal_ofReal h2]
end P2MHole05_34103c8a

/-- Any set contained in the closed ball of radius `R` has diameter at most `2 R`
    (needs `0 ≤ R`: with `R < 0` and `s = ∅` the claim would demand `0 ≤ 2 R`). -/
theorem diam_of_in_ball {E : Type*} [SeminormedAddCommGroup E] {R : ℝ}
    (s : Set E) (h : ∀ v ∈ s, ‖v‖ ≤ R) (hR : 0 ≤ R) :
    Metric.diam s ≤ 2 * R := by
  (first | exact P2MHole05_34103c8a.solution s h hR | (apply P2MHole05_34103c8a.solution <;> assumption))

/-- Lemma 3.5 (Feasible-set geometry), p.15 (arXiv:2609.17655, held version, sha256 312a0857…): `K = conv{c[S] : c ∈ C}` is convex and compact, with diameter at most
`2 √(|S̄inp| + |Sref|)`.

**Formalization Note.** `K` is compact, so `Metric.diam K` is the genuine diameter, not the junk value of an unbounded set. -/
theorem solution {X : Type*} {n m : ℕ} (C : Set (X → Bool)) (Sinp : Fin n → X × Bool)
    (Sref : Fin m → X) :
    Convex ℝ (feasibleSet C Sinp Sref) ∧ IsCompact (feasibleSet C Sinp Sref) ∧
      Metric.diam (feasibleSet C Sinp Sref) ≤ 2 * Real.sqrt ((n : ℝ) + m) := by
  refine ⟨?_, ?_, ?_⟩
  · exact convex_convexHull ℝ ((fun c => evalVec (toPM c) Sinp Sref) '' C)
  · exact Set.Finite.isCompact_convexHull ℝ (feasibleImage_finite C Sinp Sref)
  · exact diam_of_in_ball (feasibleSet C Sinp Sref) (feasibleSet_in_ball C Sinp Sref)
      (Real.sqrt_nonneg ((n : ℝ) + m))
