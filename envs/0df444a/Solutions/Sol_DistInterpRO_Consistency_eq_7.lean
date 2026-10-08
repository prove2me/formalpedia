-- Prove2me | solution 1 for DistInterpRO.Consistency.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T19:20:44.026393+00:00
-- url     : https://prove2.me/submissions/f372b057-6aca-42bd-9d05-cbb755322923

import Mathlib
import Definitions.Def_DistInterpRO_Consistency_Model

open MeasureTheory Filter Topology ProbabilityTheory

set_option autoImplicit false

namespace DistInterpRO.Consistency

lemma kernel_term_eq {m n : ℕ} {ε : ℝ} (hε : 0 < ε) (xi x : Fin m → ℝ) :
    ((n : ℝ) * ε ^ m)⁻¹ * kernel (ε⁻¹ • (x - xi)) =
      (Metric.closedBall xi ε).indicator
        (fun _ => ((n : ℝ) * ε ^ m)⁻¹ * (1 / (2 : ℝ) ^ m)) x := by
  have hiff : ‖ε⁻¹ • (x - xi)‖ ≤ 1 ↔ x ∈ Metric.closedBall xi ε := by
    rw [norm_smul, Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hε), inv_mul_le_iff₀ hε, mul_one]
  unfold kernel
  by_cases hx : x ∈ Metric.closedBall xi ε
  · rw [Set.indicator_of_mem hx, if_pos (hiff.mpr hx)]
  · rw [Set.indicator_of_notMem hx, if_neg (fun h => hx (hiff.mp h)), mul_zero]

lemma kernel_term_integrable {m n : ℕ} {ε : ℝ} (xi : Fin m → ℝ) :
    Integrable ((Metric.closedBall xi ε).indicator
        (fun _ => ((n : ℝ) * ε ^ m)⁻¹ * (1 / (2 : ℝ) ^ m))) := by
  rw [integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
  exact integrableOn_const (isCompact_closedBall xi ε).measure_lt_top.ne

lemma kernel_term_integral {m n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (xi : Fin m → ℝ) :
    ∫ x, (Metric.closedBall xi ε).indicator
        (fun _ => ((n : ℝ) * ε ^ m)⁻¹ * (1 / (2 : ℝ) ^ m)) x = 1 / (n : ℝ) := by
  rw [integral_indicator_const _ Metric.isClosed_closedBall.measurableSet]
  rw [measureReal_def, Real.volume_pi_closedBall xi hε.le, Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [smul_eq_mul, mul_pow]
  field_simp

lemma modulus_ge {V : Type*} {m : ℕ} (f : V → (Fin m → ℝ) → ℝ) (C : ℝ)
    (hfC : ∀ v x, |f v x| ≤ C) {r : ℝ} (hr : 0 ≤ r) (v : V) (x δ : Fin m → ℝ)
    (hδ : ‖δ‖ ≤ r) : |f v x - f v (x + δ)| ≤ modulus f r := by
  have hne : Nonempty {δ : Fin m → ℝ // ‖δ‖ ≤ r} := ⟨⟨0, by simpa using hr⟩⟩
  have hb : ∀ v x (δ : {δ : Fin m → ℝ // ‖δ‖ ≤ r}), |f v x - f v (x + δ.1)| ≤ 2 * C := by
    intro v x δ
    have h1 := hfC v x
    have h2 := hfC v (x + δ.1)
    calc |f v x - f v (x + δ.1)| ≤ |f v x| + |f v (x + δ.1)| := abs_sub _ _
      _ ≤ 2 * C := by linarith
  have hB3 : ∀ v x, BddAbove (Set.range fun δ : {δ : Fin m → ℝ // ‖δ‖ ≤ r} =>
      |f v x - f v (x + δ.1)|) := by
    intro v x
    exact ⟨2 * C, by rintro _ ⟨δ, rfl⟩; exact hb v x δ⟩
  have hB2 : ∀ v, BddAbove (Set.range fun x : Fin m → ℝ =>
      ⨆ δ : {δ : Fin m → ℝ // ‖δ‖ ≤ r}, |f v x - f v (x + δ.1)|) := by
    intro v
    refine ⟨2 * C, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact ciSup_le (fun δ => hb v x δ)
  have hB1 : BddAbove (Set.range fun v : V => ⨆ x : Fin m → ℝ,
      ⨆ δ : {δ : Fin m → ℝ // ‖δ‖ ≤ r}, |f v x - f v (x + δ.1)|) := by
    refine ⟨2 * C, ?_⟩
    rintro _ ⟨v, rfl⟩
    exact ciSup_le (fun x => ciSup_le (fun δ => hb v x δ))
  unfold modulus
  refine le_trans ?_ (le_ciSup hB1 v)
  refine le_trans ?_ (le_ciSup (hB2 v) x)
  exact le_ciSup (hB3 v x) ⟨δ, hδ⟩

lemma inf_le_of_mem {V : Type*} {m : ℕ} (f : V → (Fin m → ℝ) → ℝ) (C : ℝ)
    (hfC : ∀ v x, |f v x| ≤ C) {ε : ℝ} (v : V) (xi x : Fin m → ℝ)
    (hx : x ∈ Metric.closedBall xi ε) :
    (⨅ δ : {δ : Fin m → ℝ // ‖δ‖ ≤ ε}, f v (xi + δ.1)) ≤ f v x := by
  have hbb : BddBelow (Set.range fun δ : {δ : Fin m → ℝ // ‖δ‖ ≤ ε} => f v (xi + δ.1)) :=
    ⟨-C, by rintro _ ⟨δ, rfl⟩; exact (abs_le.mp (hfC _ _)).1⟩
  have hδ : ‖x - xi‖ ≤ ε := by rwa [Metric.mem_closedBall, dist_eq_norm] at hx
  have := ciInf_le hbb ⟨x - xi, hδ⟩
  simpa using this

lemma le_inf_add_of_mem {V : Type*} {m : ℕ} (f : V → (Fin m → ℝ) → ℝ) (C : ℝ)
    (hfC : ∀ v x, |f v x| ≤ C) {ε : ℝ} (hε : 0 < ε) (v : V) (xi x : Fin m → ℝ)
    (hx : x ∈ Metric.closedBall xi ε) :
    f v x ≤ (⨅ δ : {δ : Fin m → ℝ // ‖δ‖ ≤ ε}, f v (xi + δ.1)) + modulus f (2 * ε) := by
  have hne : Nonempty {δ : Fin m → ℝ // ‖δ‖ ≤ ε} := ⟨⟨0, by simpa using hε.le⟩⟩
  have hx' : ‖x - xi‖ ≤ ε := by rwa [Metric.mem_closedBall, dist_eq_norm] at hx
  have key : f v x - modulus f (2 * ε) ≤ ⨅ δ : {δ : Fin m → ℝ // ‖δ‖ ≤ ε}, f v (xi + δ.1) := by
    refine le_ciInf (fun δ => ?_)
    have hn : ‖x - xi - δ.1‖ ≤ 2 * ε := by
      calc ‖x - xi - δ.1‖ ≤ ‖x - xi‖ + ‖δ.1‖ := norm_sub_le _ _
        _ ≤ 2 * ε := by linarith [δ.2]
    have hm := modulus_ge f C hfC (by linarith) v (xi + δ.1) (x - xi - δ.1) hn
    have heq : xi + δ.1 + (x - xi - δ.1) = x := by abel
    rw [heq] at hm
    have := (abs_le.mp hm).1
    linarith
  linarith

end DistInterpRO.Consistency

open MeasureTheory Filter Topology ProbabilityTheory DistInterpRO.Consistency in
theorem solution {V : Type*} {m n : ℕ} (f : V → (Fin m → ℝ) → ℝ)
    (hfm : ∀ v, Measurable (f v)) (C : ℝ) (hfC : ∀ v x, |f v x| ≤ C)
    (hstar : (Fin m → ℝ) → ℝ) (hstar_nonneg : ∀ x, 0 ≤ hstar x)
    (hstar_int : Integrable hstar) (hstar_one : ∫ x, hstar x = 1)
    (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (xs : Fin n → Fin m → ℝ) (v : V) :
    roObjective f ε xs v - C * (∫ x, |kde ε xs x - hstar x|) ≤ (∫ x, f v x * hstar x) ∧
      (∫ x, f v x * hstar x) ≤
        roObjective f ε xs v + C * (∫ x, |kde ε xs x - hstar x|) +
          modulus f (2 * ε) := by
  -- the kernel pieces
  set c : ℝ := ((n : ℝ) * ε ^ m)⁻¹ * (1 / (2 : ℝ) ^ m) with hc
  set K : Fin n → (Fin m → ℝ) → ℝ := fun i =>
    (Metric.closedBall (xs i) ε).indicator (fun _ => c) with hK
  set I : Fin n → ℝ := fun i => ⨅ δ : {δ : Fin m → ℝ // ‖δ‖ ≤ ε}, f v (xs i + δ.1) with hI
  set d : ℝ := modulus f (2 * ε) with hd
  have hc0 : 0 ≤ c := by positivity
  have hKint : ∀ i, Integrable (K i) := fun i => kernel_term_integrable (n := n) (xs i)
  have hKintg : ∀ i, ∫ x, K i x = 1 / (n : ℝ) := fun i => kernel_term_integral hn hε (xs i)
  have hkde : ∀ x, kde ε xs x = ∑ i, K i x := by
    intro x
    unfold kde
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact kernel_term_eq hε (xs i) x
  have hkde_fun : kde ε xs = fun x => ∑ i, K i x := funext hkde
  have hkde_int : Integrable (kde ε xs) := by
    rw [hkde_fun]
    exact integrable_finset_sum _ (fun i _ => hKint i)
  have hfmeas : AEStronglyMeasurable (f v) := (hfm v).aestronglyMeasurable
  have hfb : ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), ‖f v x‖ ≤ C :=
    Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hfC v x)
  have hfh : Integrable (fun x => f v x * hstar x) := hstar_int.bdd_mul hfmeas hfb
  have hfk : Integrable (fun x => f v x * kde ε xs x) := hkde_int.bdd_mul hfmeas hfb
  -- step 1: |∫ f kde - ∫ f h*| ≤ C * L1
  have hdiff : |(∫ x, f v x * kde ε xs x) - ∫ x, f v x * hstar x| ≤
      C * ∫ x, |kde ε xs x - hstar x| := by
    rw [← integral_sub hfk hfh, ← integral_const_mul]
    have hg : Integrable (fun x => C * |kde ε xs x - hstar x|) :=
      ((hkde_int.sub hstar_int).abs).const_mul C
    have := norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall (fun x => by
      show ‖f v x * kde ε xs x - f v x * hstar x‖ ≤ C * |kde ε xs x - hstar x|
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_right (hfC v x) (abs_nonneg _)))
    simpa [Real.norm_eq_abs] using this
  have hd1 := (abs_le.mp hdiff).1
  have hd2 := (abs_le.mp hdiff).2
  -- step 2: bounds on ∫ f kde
  have hro : roObjective f ε xs v = ∑ i, I i * ∫ x, K i x := by
    unfold roObjective
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hKintg i]
    ring
  have hsumK : ∑ i : Fin n, ∫ x, K i x = 1 := by
    simp only [hKintg]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp
  have hlow : roObjective f ε xs v ≤ ∫ x, f v x * kde ε xs x := by
    have hint : Integrable (fun x => ∑ i, I i * K i x) :=
      integrable_finset_sum _ (fun i _ => (hKint i).const_mul (I i))
    have h1 : ∫ x, ∑ i, I i * K i x = roObjective f ε xs v := by
      rw [integral_finset_sum _ (fun i _ => (hKint i).const_mul (I i)), hro]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_const_mul]
    rw [← h1]
    refine integral_mono hint hfk (fun x => ?_)
    show ∑ i, I i * K i x ≤ f v x * kde ε xs x
    rw [hkde x, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    by_cases hx : x ∈ Metric.closedBall (xs i) ε
    · simp only [hK, Set.indicator_of_mem hx]
      exact mul_le_mul_of_nonneg_right (inf_le_of_mem f C hfC v (xs i) x hx) hc0
    · simp [hK, Set.indicator_of_notMem hx]
  have hup : ∫ x, f v x * kde ε xs x ≤ roObjective f ε xs v + d := by
    have hint : Integrable (fun x => ∑ i, (I i + d) * K i x) :=
      integrable_finset_sum _ (fun i _ => (hKint i).const_mul (I i + d))
    have h1 : ∫ x, ∑ i, (I i + d) * K i x = roObjective f ε xs v + d := by
      rw [integral_finset_sum _ (fun i _ => (hKint i).const_mul (I i + d)), hro]
      have : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          ∫ x, (I i + d) * K i x = I i * (∫ x, K i x) + d * (∫ x, K i x) := by
        intro i _
        rw [integral_const_mul]
        ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, hsumK, mul_one]
    rw [← h1]
    refine integral_mono hfk hint (fun x => ?_)
    show f v x * kde ε xs x ≤ ∑ i, (I i + d) * K i x
    rw [hkde x, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    by_cases hx : x ∈ Metric.closedBall (xs i) ε
    · simp only [hK, Set.indicator_of_mem hx]
      exact mul_le_mul_of_nonneg_right (le_inf_add_of_mem f C hfC hε v (xs i) x hx) hc0
    · simp [hK, Set.indicator_of_notMem hx]
  constructor
  · linarith
  · linarith
