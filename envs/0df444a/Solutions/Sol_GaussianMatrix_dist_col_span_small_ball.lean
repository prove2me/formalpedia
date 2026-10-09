-- Prove2me | solution 1 for GaussianMatrix.dist_col_span_small_ball
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:52:20.518091+00:00
-- url     : https://prove2.me/submissions/7917ae33-f518-4f73-a5eb-a072b40d8cbc

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_gaussian_dist_colspace_small_ball

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

/-- Resampling one coordinate of a standard Gaussian vector: `(a, g) ↦ update a j g`
pushes `γⁿ ⊗ γ` forward to `γⁿ`. -/
theorem measurePreserving_update_coord {n : ℕ} (j : Fin n) :
    MeasurePreserving (fun p : (Fin n → ℝ) × ℝ => Function.update p.1 j p.2)
      ((Measure.pi fun _ : Fin n => gaussianReal 0 1).prod (gaussianReal 0 1))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  have hmeas : Measurable (fun p : (Fin n → ℝ) × ℝ => Function.update p.1 j p.2) := by
    fun_prop
  refine ⟨hmeas, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (Fin n → ℝ) × ℝ => Function.update p.1 j p.2) ⁻¹' Set.univ.pi s
      = Set.univ.pi (Function.update s j Set.univ) ×ˢ s j := by
    ext ⟨a, g⟩
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun l => ?_, by simpa using h j⟩
      by_cases hl : l = j
      · subst hl; simp
      · have := h l
        rw [Function.update_of_ne hl] at this
        rw [Function.update_of_ne hl]; exact this
    · rintro ⟨h1, h2⟩ l
      by_cases hl : l = j
      · subst hl; simpa using h2
      · have := h1 l
        rw [Function.update_of_ne hl] at this
        rw [Function.update_of_ne hl]; exact this
  rw [hpre, Measure.prod_prod, Measure.pi_pi,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun i => gaussianReal 0 1 (s i)) (Finset.mem_univ j),
    Function.update_self, measure_univ, one_mul, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]

/-- Resampling column `j` of a standard Gaussian matrix by an independent standard Gaussian
vector leaves its law unchanged. -/
theorem measurePreserving_updateCol (N n : ℕ) (j : Fin n) :
    MeasurePreserving
      (fun p : (Fin N → Fin n → ℝ) × (Fin N → ℝ) => fun i => Function.update (p.1 i) j (p.2 i))
      ((gaussianMatrix N n).prod (Measure.pi fun _ : Fin N => gaussianReal 0 1))
      (gaussianMatrix N n) := by
  have h1 := MeasurePreserving.symm _ (measurePreserving_arrowProdEquivProdArrow (Fin n → ℝ) ℝ
    (Fin N) (fun _ => Measure.pi fun _ : Fin n => gaussianReal 0 1) (fun _ => gaussianReal 0 1))
  have h2 := measurePreserving_pi
    (fun _ : Fin N => (Measure.pi fun _ : Fin n => gaussianReal 0 1).prod (gaussianReal 0 1))
    (fun _ => Measure.pi fun _ : Fin n => gaussianReal 0 1)
    (fun _ => measurePreserving_update_coord j)
  exact h2.comp h1

/-- The distance from column `j` to the span of the other columns is measurable
(it is an infimum of continuous functions, hence upper semicontinuous). -/
theorem measurable_colDist {N n : ℕ} (j : Fin n) :
    Measurable (fun A : Fin N → Fin n → ℝ => ⨅ x : {x : Fin n → ℝ // x j = 1},
        Real.sqrt ((Matrix.of A *ᵥ x.1) ⬝ᵥ (Matrix.of A *ᵥ x.1))) := by
  refine UpperSemicontinuous.measurable ?_
  refine upperSemicontinuous_ciInf (fun A => ⟨0, ?_⟩) fun x => ?_
  · rintro _ ⟨y, rfl⟩; exact Real.sqrt_nonneg _
  · refine Continuous.upperSemicontinuous ?_
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    fun_prop

/-- Zeroing one column leaves rank at most `n - 1`. -/
theorem rank_update_col_zero_le {N n : ℕ} (A : Fin N → Fin n → ℝ) (j : Fin n) :
    (Matrix.of fun i l => Function.update (A i) j 0 l).rank ≤ n - 1 := by
  let B' : Matrix (Fin N) {l : Fin n // l ≠ j} ℝ := Matrix.of fun i l => A i l.1
  let E : Matrix {l : Fin n // l ≠ j} (Fin n) ℝ := Matrix.of fun l k => if k = l.1 then 1 else 0
  have hBE : (Matrix.of fun i l => Function.update (A i) j 0 l) = B' * E := by
    ext i k
    simp only [B', E, Matrix.of_apply, Matrix.mul_apply, mul_ite, mul_one, mul_zero]
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self]
      symm
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [if_neg]; intro h; exact l.2 h.symm
    · rw [Function.update_of_ne hk, Finset.sum_eq_single ⟨k, hk⟩]
      · simp
      · intro b _ hb; rw [if_neg]; intro h; apply hb; exact Subtype.ext h.symm
      · simp
  rw [hBE]
  calc (B' * E).rank ≤ B'.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card {l : Fin n // l ≠ j} := Matrix.rank_le_card_width _
    _ = n - 1 := by simp [Fintype.card_subtype_compl]

/-- With `x j = 1`, `A' x = g + B x` where `A'` is `A` with column `j` replaced by `g` and
`B` is `A` with column `j` zeroed. -/
theorem updateCol_mulVec {N n : ℕ} (A : Fin N → Fin n → ℝ) (g : Fin N → ℝ) (j : Fin n)
    (x : Fin n → ℝ) (hx : x j = 1) :
    Matrix.of (fun i => Function.update (A i) j (g i)) *ᵥ x
      = g - (Matrix.of fun i l => Function.update (A i) j 0 l) *ᵥ (-x) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.sub_apply, Pi.neg_apply,
    mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
  have h : ∀ l, Function.update (A i) j (g i) l * x l
      = Function.update (A i) j 0 l * x l + (if l = j then g i * x l else 0) := by
    intro l
    by_cases hl : l = j
    · subst hl; simp
    · simp [hl]
  rw [Finset.sum_congr rfl fun l _ => h l, Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _), hx, mul_one, add_comm]

end GaussianMatrix

open GaussianMatrix

theorem solution {N n : ℕ} (hnN : n ≤ N) (j : Fin n) (u : ℝ) (hu : 0 ≤ u)
    (hud : u ≤ (N : ℝ) - n + 1) :
    (gaussianMatrix N n) {A | (⨅ x : {x : Fin n → ℝ // x j = 1},
        Real.sqrt ((Matrix.of A *ᵥ x.1) ⬝ᵥ (Matrix.of A *ᵥ x.1))) ^ 2 ≤ u}
      ≤ ENNReal.ofReal ((Real.exp 1 * u / ((N : ℝ) - n + 1)) ^ (((N : ℝ) - n + 1) / 2)) := by
  have hS : MeasurableSet {A : Fin N → Fin n → ℝ | (⨅ x : {x : Fin n → ℝ // x j = 1},
      Real.sqrt ((Matrix.of A *ᵥ x.1) ⬝ᵥ (Matrix.of A *ᵥ x.1))) ^ 2 ≤ u} :=
    measurableSet_le ((measurable_colDist j).pow_const 2) measurable_const
  have hΦ := measurePreserving_updateCol N n j
  rw [← hΦ.measure_preimage hS.nullMeasurableSet, Measure.prod_apply (hΦ.measurable hS)]
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (fun h => by subst h; exact j.elim0)
  have hd : ((N - n + 1 : ℕ) : ℝ) = (N : ℝ) - n + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hnN, Nat.cast_one]
  set bound := ENNReal.ofReal ((Real.exp 1 * u / ((N : ℝ) - n + 1)) ^ (((N : ℝ) - n + 1) / 2))
  calc ∫⁻ A, (Measure.pi fun _ : Fin N => gaussianReal 0 1) _ ∂(gaussianMatrix N n)
      ≤ ∫⁻ _, bound ∂(gaussianMatrix N n) := lintegral_mono fun A => ?_
    _ = bound := by rw [lintegral_const, measure_univ, mul_one]
  set B : Matrix (Fin N) (Fin n) ℝ := Matrix.of fun i l => Function.update (A i) j 0 l with hB
  have hrank : B.rank + (N - n + 1) ≤ N := by
    have : B.rank ≤ n - 1 := rank_update_col_zero_le A j
    omega
  have key := gaussian_dist_colspace_small_ball B (d := N - n + 1) (by omega) hrank u hu
    (by rw [hd]; exact hud)
  rw [hd] at key
  refine le_trans (measure_mono ?_) key
  intro g hg
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hg ⊢
  refine le_trans (pow_le_pow_left₀ (Real.iInf_nonneg fun _ => Real.sqrt_nonneg _) ?_ 2) hg
  have hne : Nonempty {x : Fin n → ℝ // x j = 1} := ⟨⟨Pi.single j 1, by simp⟩⟩
  refine le_ciInf fun x => ?_
  have hbdd : BddBelow (Set.range fun c : Fin n → ℝ =>
      Real.sqrt ((g - B *ᵥ c) ⬝ᵥ (g - B *ᵥ c))) :=
    ⟨0, by rintro _ ⟨c, rfl⟩; exact Real.sqrt_nonneg _⟩
  refine (ciInf_le hbdd (-x.1)).trans (le_of_eq ?_)
  rw [hB, ← updateCol_mulVec A g j x.1 x.2]
