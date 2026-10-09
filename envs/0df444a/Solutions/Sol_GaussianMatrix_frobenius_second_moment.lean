-- Prove2me | solution 1 for GaussianMatrix.frobenius_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:08:47.123317+00:00
-- url     : https://prove2.me/submissions/bb4508dd-09be-4841-9a90-46b3f5ce083e

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

open GaussianMatrix

namespace GaussianMatrix

lemma measurePreserving_coord {p m : ℕ} (a : Fin p) (b : Fin m) :
    MeasurePreserving (fun G : Fin p → Fin m → ℝ => G a b) (gaussianMatrix p m)
      (gaussianReal 0 1) :=
  (measurePreserving_eval (fun _ : Fin m => gaussianReal 0 1) b).comp
    (measurePreserving_eval (fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal 0 1) a)

lemma memLp_coord {p m : ℕ} (a : Fin p) (b : Fin m) (q : ENNReal) (hq : q ≠ ⊤) :
    MemLp (fun G : Fin p → Fin m → ℝ => G a b) q (gaussianMatrix p m) :=
  (memLp_id_gaussianReal' q hq).comp_measurePreserving (measurePreserving_coord a b)

lemma integral_comp_coord {p m : ℕ} (a : Fin p) (b : Fin m) (f : ℝ → ℝ)
    (hf : Measurable f) :
    ∫ G, f (G a b) ∂(gaussianMatrix p m) = ∫ x, f x ∂(gaussianReal 0 1) := by
  rw [← (measurePreserving_coord a b).map_eq, integral_map]
  · exact (measurePreserving_coord a b).measurable.aemeasurable
  · exact hf.aestronglyMeasurable

lemma integral_coord {p m : ℕ} (a : Fin p) (b : Fin m) :
    ∫ G, G a b ∂(gaussianMatrix p m) = 0 := by
  have := integral_comp_coord a b (fun x => x) measurable_id
  simpa [integral_id_gaussianReal] using this

lemma integral_coord_sq {p m : ℕ} (a : Fin p) (b : Fin m) :
    ∫ G, G a b ^ 2 ∂(gaussianMatrix p m) = 1 := by
  rw [integral_comp_coord a b (fun x => x ^ 2) (by fun_prop)]
  have h := variance_eq_sub (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp))
  rw [variance_id_gaussianReal] at h
  simp [integral_id_gaussianReal] at h
  exact h.symm

lemma integral_coord_mul {p m : ℕ} (a c : Fin p) (b d : Fin m) :
    ∫ G, G a b * G c d ∂(gaussianMatrix p m) = if a = c ∧ b = d then 1 else 0 := by
  by_cases hac : a = c
  · subst hac
    by_cases hbd : b = d
    · subst hbd
      simpa [← pow_two] using integral_coord_sq a b
    · simp only [hbd, and_false, if_false]
      have hrow := measurePreserving_eval
        (fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) a
      have h1 : ∫ G, G a b * G a d ∂(gaussianMatrix p m)
          = ∫ x, x b * x d ∂(Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) := by
        have := integral_map (μ := gaussianMatrix p m) hrow.measurable.aemeasurable
          (f := fun x : Fin m → ℝ => x b * x d) (by fun_prop)
        unfold gaussianMatrix at this ⊢
        rw [hrow.map_eq] at this
        exact this.symm
      rw [h1]
      have hind : iIndepFun (fun (i : Fin m) (ω : Fin m → ℝ) => ω i)
          (Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) :=
        iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id)
      rw [(hind.indepFun hbd).integral_fun_mul_eq_mul_integral
        (measurable_pi_apply b).aestronglyMeasurable (measurable_pi_apply d).aestronglyMeasurable]
      have h0 : ∫ x, x b ∂(Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) = 0 := by
        have hb := measurePreserving_eval (fun _ : Fin m => gaussianReal (0 : ℝ) 1) b
        have := integral_map (μ := Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1)
          hb.measurable.aemeasurable (f := fun x : ℝ => x) (by fun_prop)
        rw [hb.map_eq, integral_id_gaussianReal] at this
        exact this.symm
      simp [h0]
  · simp only [hac, false_and, if_false]
    have hind : iIndepFun (fun (i : Fin p) (ω : Fin p → Fin m → ℝ) => ω i)
        (gaussianMatrix p m) :=
      iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id)
    have h2 := (hind.indepFun hac).comp (measurable_pi_apply b) (measurable_pi_apply d)
    have := h2.integral_fun_mul_eq_mul_integral
      (by
        have : Measurable (fun ω : Fin p → Fin m → ℝ => ω a b) := by fun_prop
        exact this.aestronglyMeasurable)
      (by
        have : Measurable (fun ω : Fin p → Fin m → ℝ => ω c d) := by fun_prop
        exact this.aestronglyMeasurable)
    simp only [Function.comp_def] at this
    rw [this, integral_coord]
    simp

lemma integrable_coord_mul {p m : ℕ} (a c : Fin p) (b d : Fin m) (k : ℝ) :
    Integrable (fun G : Fin p → Fin m → ℝ => k * (G a b * G c d)) (gaussianMatrix p m) :=
  ((memLp_coord a b 2 (by simp)).integrable_mul (memLp_coord c d 2 (by simp))).const_mul k

lemma frobSq_expand {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin n) ℝ) (G : Fin p → Fin m → ℝ) :
    frobSq (S * Matrix.of G * T) = ∑ i, ∑ j, ∑ k, ∑ c, ∑ b, ∑ d,
      (S i k * T b j * S i c * T d j) * (G k b * G c d) := by
  unfold frobSq
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : (S * Matrix.of G * T) i j = ∑ k, ∑ b, S i k * G k b * T b j := by
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [h, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
  ring

lemma integral_quadratic {ι κ : Type*} [Fintype ι] [Fintype κ] {p m : ℕ}
    (w : ι → κ → Fin p → Fin p → Fin m → Fin m → ℝ) :
    ∫ G, (∑ i, ∑ j, ∑ k, ∑ c, ∑ b, ∑ d, w i j k c b d * (G k b * G c d)) ∂(gaussianMatrix p m)
      = ∑ i, ∑ j, ∑ k, ∑ b, w i j k k b b := by
  have hI : ∀ (k c : Fin p) (b : Fin m) (f : Fin m → ℝ),
      Integrable (fun G : Fin p → Fin m → ℝ => ∑ d, f d * (G k b * G c d))
        (gaussianMatrix p m) :=
    fun k c b f => integrable_finsetSum _ fun d _ => integrable_coord_mul k c b d _
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun c _ =>
    integrable_finsetSum _ fun b _ => hI k c b _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun c _ =>
    integrable_finsetSum _ fun b _ => hI k c b _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun c _ =>
    integrable_finsetSum _ fun b _ => hI k c b _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun b _ => hI k c b _]
  rw [Finset.sum_eq_single k]
  · rw [integral_finsetSum _ fun b _ => hI k k b _]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_finsetSum _ fun d _ => integrable_coord_mul k k b d _]
    simp [integral_const_mul, integral_coord_mul]
  · intro c _ hck
    rw [integral_finsetSum _ fun b _ => hI k c b _]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [integral_finsetSum _ fun d _ => integrable_coord_mul k c b d _]
    refine Finset.sum_eq_zero fun d _ => ?_
    simp [integral_const_mul, integral_coord_mul, Ne.symm hck]
  · simp

end GaussianMatrix

theorem solution {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin n) ℝ) :
    ∫ G, frobSq (S * Matrix.of G * T) ∂(gaussianMatrix p m) = frobSq S * frobSq T := by
  simp_rw [GaussianMatrix.frobSq_expand]
  rw [GaussianMatrix.integral_quadratic (fun i j k c b d => S i k * T b j * S i c * T d j)]
  unfold frobSq
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring