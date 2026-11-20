-- Prove2me | solution 1 for EuclideanLineAvgDist.Embedding.gaussian_transition_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:41:07.347303+00:00
-- url     : https://prove2.me/submissions/fd14646d-34e7-46a1-a9d9-804ba8befe0a

import Mathlib
import Definitions.Def_EuclideanLineAvgDist_Embedding_Basic
import Definitions.Def_EuclideanLineAvgDist_Embedding_Markov
import Theorems.Thm_EuclideanLineAvgDist_Embedding_reversible_squared_displacement
universe u

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.Gaussian1

open EuclideanLineAvgDist.Embedding

/-- The law of `⟨γ, v⟩` for `γ ∼ N(0, I)` is `N(0, ‖v‖²)`. -/
lemma map_inner_stdGaussian (k : ℕ) (v : Eucl k) :
    (stdGaussian (Eucl k)).map (fun g => inner ℝ g v) = gaussianReal 0 (‖v‖₊ ^ 2) := by
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian (Eucl k)) (innerSL ℝ v)
  have e1 : ((innerSL ℝ v : Eucl k → ℝ)) = fun g => inner ℝ g v := by
    funext g; simp [real_inner_comm]
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian] at h
  simp only [innerSL_apply_norm] at h
  have : (‖v‖ ^ 2).toNNReal = ‖v‖₊ ^ 2 := by
    rw [← NNReal.coe_inj]; simp
  rw [this] at h
  rw [← h, e1]

lemma lintegral_comp_inner {k : ℕ} (v : Eucl k) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ g, F (inner ℝ g v) ∂(stdGaussian (Eucl k)) = ∫⁻ x, F x ∂(gaussianReal 0 (‖v‖₊ ^ 2)) := by
  rw [← map_inner_stdGaussian k v, lintegral_map hF (by fun_prop)]

/-- `E exp(c ⟨γ,v⟩) = exp(c² ‖v‖² / 2)`. -/
lemma lintegral_exp_inner {k : ℕ} (v : Eucl k) (c : ℝ) :
    ∫⁻ g, ENNReal.ofReal (Real.exp (c * inner ℝ g v)) ∂(stdGaussian (Eucl k))
      = ENNReal.ofReal (Real.exp (c ^ 2 * ‖v‖ ^ 2 / 2)) := by
  rw [lintegral_comp_inner v (fun x => ENNReal.ofReal (Real.exp (c * x))) (by fun_prop)]
  have hint := integrable_exp_mul_gaussianReal (μ := 0) (v := ‖v‖₊ ^ 2) c
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))]
  congr 1
  have := mgf_id_gaussianReal (μ := 0) (v := ‖v‖₊ ^ 2)
  have h2 := congrFun this c
  simp only [mgf, id] at h2
  rw [h2]
  congr 1
  simp; ring

/-- `E ⟨γ,v⟩² = ‖v‖²`. -/
lemma lintegral_inner_sq {k : ℕ} (v : Eucl k) :
    ∫⁻ g, ENNReal.ofReal ((inner ℝ g v) ^ 2) ∂(stdGaussian (Eucl k)) = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [lintegral_comp_inner v (fun x => ENNReal.ofReal (x ^ 2)) (by fun_prop)]
  have hm := memLp_id_gaussianReal (μ := (0:ℝ)) (v := ‖v‖₊ ^ 2) 2
  have hint : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 (‖v‖₊ ^ 2)) := by
    have := hm.integrable_sq
    simpa using this
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (fun x => sq_nonneg x))]
  congr 1
  have h := variance_id_gaussianReal (μ := (0:ℝ)) (v := ‖v‖₊ ^ 2)
  rw [variance_eq_integral (by fun_prop)] at h
  simp only [id, integral_id_gaussianReal, sub_zero] at h
  rw [show (fun x : ℝ => x ^ 2) = (fun x : ℝ => (x) ^ 2) from rfl, h]
  simp

/-- The mixture density: `m_c(g, v) = cosh(c⟨g,v⟩) exp(-c²‖v‖²/2)`. -/
noncomputable def mix {k : ℕ} (c : ℝ) (v : Eucl k) (g : Eucl k) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.exp (c * inner ℝ g v) + Real.exp (-(c * inner ℝ g v))) / 2 *
    Real.exp (-(c ^ 2 * ‖v‖ ^ 2 / 2)))

lemma lintegral_mix {k : ℕ} (v : Eucl k) (c : ℝ) :
    ∫⁻ g, mix c v g ∂(stdGaussian (Eucl k)) = 1 := by
  have key : ∀ g : Eucl k, mix c v g =
      ENNReal.ofReal (Real.exp (-(c ^ 2 * ‖v‖ ^ 2 / 2))) / 2 *
        (ENNReal.ofReal (Real.exp (c * inner ℝ g v)) + ENNReal.ofReal (Real.exp ((-c) * inner ℝ g v))) := by
    intro g
    unfold mix
    have h1 : (Real.exp (c * inner ℝ g v) + Real.exp (-(c * inner ℝ g v))) / 2 *
        Real.exp (-(c ^ 2 * ‖v‖ ^ 2 / 2)) =
        Real.exp (-(c ^ 2 * ‖v‖ ^ 2 / 2)) / 2 * (Real.exp (c * inner ℝ g v) + Real.exp ((-c) * inner ℝ g v)) := by
      rw [neg_mul]; ring
    rw [h1, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  simp_rw [key]
  rw [lintegral_const_mul' _ _ (by
      refine ENNReal.mul_ne_top ?_ ?_ <;> simp)]
  rw [lintegral_add_left (by fun_prop), lintegral_exp_inner, lintegral_exp_inner]
  have : (-c) ^ 2 = c ^ 2 := by ring
  rw [this, ← two_mul, ← mul_assoc, ENNReal.div_mul_cancel (by norm_num) (by norm_num),
    ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add]
  simp

end EuclideanLineAvgDist.Dev.Gaussian1
end

section
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.PathCalc

variable {G S : Type u} [MeasurableSpace G] [Fintype S] [MeasurableSpace S]
  (ν : Measure G) (W : G → S → S → ℝ≥0∞)

/-- Expectation over `r` steps of the chain started at `a`: a step draws `g ∼ ν`, then `z` with
weight `W g a z`.  The functional `F` is evaluated on the path `((g₁,z₁),…,(g_r,z_r))`. -/
noncomputable def pathE : (r : ℕ) → S → ((Fin r → G × S) → ℝ≥0∞) → ℝ≥0∞
  | 0, _, F => F (fun i => Fin.elim0 i)
  | r + 1, a, F => ∫⁻ g, ∑ z, W g a z *
      pathE r z (fun p => F (Fin.cons (g, z) p : Fin (r + 1) → G × S)) ∂ν

section basic

lemma pathE_mono [IsProbabilityMeasure ν] : ∀ (r : ℕ) (a : S) (F F' : (Fin r → G × S) → ℝ≥0∞),
    (∀ p, F p ≤ F' p) → pathE ν W r a F ≤ pathE ν W r a F'
  | 0, a, F, F', h => by simpa [pathE] using h _
  | r + 1, a, F, F', h => by
      simp only [pathE]
      refine lintegral_mono fun g => Finset.sum_le_sum fun z _ => ?_
      gcongr
      exact pathE_mono r z _ _ fun p => h _

lemma pathE_const (hW : ∀ g a, ∑ z, W g a z = 1) [IsProbabilityMeasure ν] :
    ∀ (r : ℕ) (a : S) (c : ℝ≥0∞), pathE ν W r a (fun _ => c) = c
  | 0, a, c => by simp [pathE]
  | r + 1, a, c => by
      simp only [pathE]
      simp_rw [pathE_const hW r, ← Finset.sum_mul, hW]
      simp

lemma pathE_const_mul [IsProbabilityMeasure ν] :
    ∀ (r : ℕ) (a : S) (c : ℝ≥0∞) (F : (Fin r → G × S) → ℝ≥0∞), c ≠ ∞ →
      pathE ν W r a (fun p => c * F p) = c * pathE ν W r a F
  | 0, a, c, F, _ => by simp [pathE]
  | r + 1, a, c, F, hc => by
      simp only [pathE]
      simp_rw [pathE_const_mul r _ c _ hc, mul_left_comm _ c, ← Finset.mul_sum]
      rw [lintegral_const_mul' _ _ hc]

variable [MeasurableSingletonClass S]

lemma measurable_cons (z : S) (r : ℕ) :
    Measurable (fun x : G × (Fin r → G × S) => (Fin.cons (x.1, z) x.2 : Fin (r + 1) → G × S)) := by
  refine measurable_pi_iff.mpr fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; fun_prop
  · simp only [Fin.cons_succ]; fun_prop

lemma pathE_meas [IsProbabilityMeasure ν] (hW : ∀ a z, Measurable (fun g => W g a z)) :
    ∀ (r : ℕ) (β : Type u) [MeasurableSpace β] (a : S) (F : β → (Fin r → G × S) → ℝ≥0∞),
      Measurable (fun x : β × (Fin r → G × S) => F x.1 x.2) →
        Measurable (fun b => pathE ν W r a (F b))
  | 0, β, _, a, F, hF => by
      simp only [pathE]
      exact hF.comp (measurable_id.prodMk measurable_const)
  | r + 1, β, _, a, F, hF => by
      simp only [pathE]
      refine Measurable.lintegral_prod_right' (f := fun bg : β × G => ∑ z, W bg.2 a z *
        pathE ν W r z (fun p => F bg.1 (Fin.cons (bg.2, z) p : Fin (r + 1) → G × S))) ?_
      refine Finset.measurable_sum _ fun z _ => ?_
      refine ((hW a z).comp measurable_snd).mul ?_
      refine pathE_meas hW r (β × G) z (fun bg p => F bg.1 (Fin.cons (bg.2, z) p)) ?_
      exact hF.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_cons z r).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))

lemma pathE_add [IsProbabilityMeasure ν] (hW : ∀ a z, Measurable (fun g => W g a z)) :
    ∀ (r : ℕ) (a : S) (F F' : (Fin r → G × S) → ℝ≥0∞), Measurable F → Measurable F' →
      pathE ν W r a (fun p => F p + F' p) = pathE ν W r a F + pathE ν W r a F'
  | 0, a, F, F', _, _ => by simp [pathE]
  | r + 1, a, F, F', hF, hF' => by
      have hc : ∀ z : S, ∀ (H : (Fin (r+1) → G × S) → ℝ≥0∞), Measurable H →
          Measurable (fun g => pathE ν W r z (fun p => H (Fin.cons (g, z) p : Fin (r + 1) → G × S))) := by
        intro z H hH
        refine pathE_meas ν W hW r G z (fun g p => H (Fin.cons (g, z) p)) ?_
        exact hH.comp ((measurable_cons z r))
      have hm : ∀ H : (Fin (r+1) → G × S) → ℝ≥0∞, Measurable H →
          Measurable (fun g => ∑ z, W g a z *
            pathE ν W r z (fun p => H (Fin.cons (g, z) p : Fin (r + 1) → G × S))) := fun H hH =>
        Finset.measurable_sum _ fun z _ => (hW a z).mul (hc z H hH)
      have e : ∀ (g : G) (z : S), pathE ν W r z (fun p => F (Fin.cons (g, z) p : Fin (r + 1) → G × S) +
          F' (Fin.cons (g, z) p : Fin (r + 1) → G × S)) =
          pathE ν W r z (fun p => F (Fin.cons (g, z) p : Fin (r + 1) → G × S)) +
          pathE ν W r z (fun p => F' (Fin.cons (g, z) p : Fin (r + 1) → G × S)) := fun g z =>
        pathE_add hW r z _ _ (hF.comp ((measurable_cons z r).comp (measurable_const.prodMk measurable_id)))
          (hF'.comp ((measurable_cons z r).comp (measurable_const.prodMk measurable_id)))
      simp only [pathE]
      simp_rw [e, mul_add, Finset.sum_add_distrib]
      rw [lintegral_add_left (hm F hF)]

end basic

end EuclideanLineAvgDist.Dev.PathCalc
end

section
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.PathCalc

variable {G S : Type u} [MeasurableSpace G] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S] [DecidableEq S] (ν : Measure G) [IsProbabilityMeasure ν]
  (W : G → S → S → ℝ≥0∞)

/-- One-step averaged transition weights. -/
noncomputable def Pm (w z : S) : ℝ≥0∞ := ∫⁻ g, W g w z ∂ν

/-- `i`-step transition weights (left recursion). -/
noncomputable def Pk : ℕ → S → S → ℝ≥0∞
  | 0, w, u => if w = u then 1 else 0
  | i + 1, w, u => ∑ z, Pm ν W w z * Pk i z u

/-- Additive functional: the sum over steps `i` of `h i g_i w_i z_i`, where `w_i` is the previous state. -/
noncomputable def sumT (h : ℕ → G → S → S → ℝ≥0∞) : (r : ℕ) → S → (Fin r → G × S) → ℝ≥0∞
  | 0, _, _ => 0
  | r + 1, w, p => h 0 (p 0).1 w (p 0).2 + sumT (fun i => h (i + 1)) r (p 0).2 (Fin.tail p)

/-- Multiplicative functional. -/
noncomputable def Fp (m : ℕ → G → S → ℝ≥0∞) : (r : ℕ) → (Fin r → G × S) → ℝ≥0∞
  | 0, _ => 1
  | r + 1, p => m 0 (p 0).1 (p 0).2 * Fp (fun i => m (i + 1)) r (Fin.tail p)

lemma sumT_meas : ∀ (r : ℕ) (h : ℕ → G → S → S → ℝ≥0∞),
    (∀ i w, Measurable (fun x : G × S => h i x.1 w x.2)) → ∀ w, Measurable (sumT h r w)
  | 0, h, _, w => by simp [sumT]
  | r + 1, h, hh, w => by
      show Measurable (fun p : Fin (r + 1) → G × S => h 0 (p 0).1 w (p 0).2 +
        sumT (fun i => h (i + 1)) r (p 0).2 (Fin.tail p))
      refine Measurable.add ?_ ?_
      · exact (hh 0 w).comp ((measurable_pi_apply 0))
      · have := sumT_meas r (fun i => h (i + 1)) (fun i w => hh (i + 1) w)
        have h2 : Measurable (fun q : S × (Fin r → G × S) => sumT (fun i => h (i + 1)) r q.1 q.2) :=
          measurable_from_prod_countable_right (fun s => this s)
        exact h2.comp (((measurable_snd.comp (measurable_pi_apply 0))).prodMk
          (measurable_pi_iff.mpr fun i => measurable_pi_apply i.succ))

lemma Fp_meas : ∀ (r : ℕ) (m : ℕ → G → S → ℝ≥0∞),
    (∀ i, Measurable (fun x : G × S => m i x.1 x.2)) → Measurable (Fp m r)
  | 0, m, _ => by simp [Fp]
  | r + 1, m, hm => by
      show Measurable (fun p : Fin (r + 1) → G × S => m 0 (p 0).1 (p 0).2 *
        Fp (fun i => m (i + 1)) r (Fin.tail p))
      refine Measurable.mul ?_ ?_
      · exact (hm 0).comp (measurable_pi_apply 0)
      · exact (Fp_meas r _ (fun i => hm (i + 1))).comp (measurable_pi_iff.mpr fun i => measurable_pi_apply i.succ)


variable {ν W}

lemma pathE_sumT (hW : ∀ a z, Measurable (fun g => W g a z)) (hs : ∀ g a, ∑ z, W g a z = 1) :
    ∀ (r : ℕ) (h : ℕ → G → S → S → ℝ≥0∞),
    (∀ i w, Measurable (fun x : G × S => h i x.1 w x.2)) → ∀ w,
    pathE ν W r w (sumT h r w) = ∑ i ∈ Finset.range r, ∑ u,
      Pk ν W i w u * ∫⁻ g, ∑ z, W g u z * h i g u z ∂ν
  | 0, h, _, w => by simp [pathE, sumT]
  | r + 1, h, hh, w => by
      have hE := pathE_sumT hW hs r (fun i => h (i + 1)) (fun i w => hh (i + 1) w)
      have hsm := sumT_meas r (fun i => h (i + 1)) (fun i w => hh (i + 1) w)
      have e : ∀ (g : G) (z : S), pathE ν W r z
          (fun p => sumT h (r + 1) w (Fin.cons (g, z) p : Fin (r + 1) → G × S)) =
          h 0 g w z + pathE ν W r z (sumT (fun i => h (i + 1)) r z) := by
        intro g z
        have := pathE_add ν W hW r z (fun _ => h 0 g w z) (sumT (fun i => h (i + 1)) r z)
          measurable_const (hsm z)
        rw [pathE_const ν W hs] at this
        simpa [sumT, Fin.tail_cons] using this
      simp only [pathE]
      simp_rw [e, mul_add, Finset.sum_add_distrib]
      have m1 : Measurable (fun g => ∑ z, W g w z * h 0 g w z) :=
        Finset.measurable_sum _ fun z _ => (hW w z).mul ((hh 0 w).comp (measurable_id.prodMk measurable_const))
      rw [lintegral_add_left m1, Finset.sum_range_succ', add_comm]
      congr 1
      · have m2 : ∀ z, Measurable (fun g => W g w z *
            pathE ν W r z (sumT (fun i => h (i + 1)) r z)) := fun z => (hW w z).mul measurable_const
        rw [lintegral_finsetSum _ (fun z _ => m2 z)]
        simp_rw [lintegral_mul_const _ (hW w _), hE]
        simp_rw [Finset.mul_sum, Pk]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Pm, mul_assoc]
      · simp [Pk]

lemma pathE_Fp_sum (hW : ∀ a z, Measurable (fun g => W g a z)) (hs : ∀ g a, ∑ z, W g a z = 1)
    (hsymm : ∀ g a z, W g a z = W g z a) :
    ∀ (r : ℕ) (m : ℕ → G → S → ℝ≥0∞), (∀ i, Measurable (fun x : G × S => m i x.1 x.2)) →
      (∀ i z, ∫⁻ g, m i g z ∂ν = 1) → (∀ i g z, m i g z ≠ ∞) →
      ∑ y, pathE ν W r y (Fp m r) = (Fintype.card S : ℝ≥0∞)
  | 0, m, _, _, _ => by simp [pathE, Fp]
  | r + 1, m, hm, hm1, hmf => by
      have hE := pathE_Fp_sum hW hs hsymm r (fun i => m (i + 1)) (fun i => hm (i + 1))
        (fun i z => hm1 (i + 1) z) (fun i g z => hmf (i + 1) g z)
      have e : ∀ (g : G) (z : S), pathE ν W r z
          (fun p => Fp m (r + 1) (Fin.cons (g, z) p : Fin (r + 1) → G × S)) =
          m 0 g z * pathE ν W r z (Fp (fun i => m (i + 1)) r) := by
        intro g z
        rw [← pathE_const_mul ν W r z _ _ (hmf 0 g z)]
        simp [Fp, Fin.tail_cons]
      simp only [pathE]
      simp_rw [e]
      have m2 : ∀ y z : S, Measurable (fun g => W g y z *
          (m 0 g z * pathE ν W r z (Fp (fun i => m (i + 1)) r))) := fun y z =>
        (hW y z).mul (((hm 0).comp (measurable_id.prodMk measurable_const)).mul measurable_const)
      have m3 : ∀ y : S, Measurable (fun g => ∑ z, W g y z *
          (m 0 g z * pathE ν W r z (Fp (fun i => m (i + 1)) r))) := fun y =>
        Finset.measurable_sum _ fun z _ => m2 y z
      rw [← lintegral_finsetSum _ (fun y _ => m3 y)]
      have : ∀ g : G, ∑ y, ∑ z, W g y z * (m 0 g z * pathE ν W r z (Fp (fun i => m (i + 1)) r)) =
          ∑ z, m 0 g z * pathE ν W r z (Fp (fun i => m (i + 1)) r) := by
        intro g
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [← Finset.sum_mul]
        have : ∑ y, W g y z = 1 := by simp_rw [hsymm g _ z]; exact hs g z
        rw [this, one_mul]
      simp_rw [this]
      have m4 : ∀ z : S, Measurable (fun g => m 0 g z * pathE ν W r z (Fp (fun i => m (i + 1)) r)) :=
        fun z => ((hm 0).comp (measurable_id.prodMk measurable_const)).mul measurable_const
      rw [lintegral_finsetSum _ (fun z _ => m4 z)]
      have hmz : ∀ z : S, Measurable (fun g => m 0 g z) :=
        fun z => (hm 0).comp (measurable_id.prodMk measurable_const)
      have e2 : ∀ z : S, ∫⁻ g, m 0 g z * pathE ν W r z (Fp (fun i => m (i + 1)) r) ∂ν =
          pathE ν W r z (Fp (fun i => m (i + 1)) r) := fun z => by
        rw [lintegral_mul_const _ (hmz z), hm1, one_mul]
      simp_rw [e2]
      exact hE

section Pk

variable (ν W)

lemma Pk_row (hP : ∀ w, ∑ z, Pm ν W w z = 1) : ∀ (i : ℕ) (w : S), ∑ u, Pk ν W i w u = 1
  | 0, w => by simp [Pk]
  | i + 1, w => by
      simp only [Pk]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, Pk_row hP i, mul_one]
      exact hP w

lemma Pk_col (hP : ∀ w, ∑ z, Pm ν W w z = 1) (hsy : ∀ w z, Pm ν W w z = Pm ν W z w) :
    ∀ (i : ℕ) (u : S), ∑ w, Pk ν W i w u = 1
  | 0, u => by simp [Pk]
  | i + 1, u => by
      simp only [Pk]
      rw [Finset.sum_comm]
      have : ∀ z, ∑ w, Pm ν W w z * Pk ν W i z u = Pk ν W i z u := fun z => by
        rw [← Finset.sum_mul]
        have : ∑ w, Pm ν W w z = 1 := by simp_rw [hsy _ z]; exact hP z
        rw [this, one_mul]
      simp_rw [this]
      exact Pk_col hP hsy i u

lemma Pk_add : ∀ (i j : ℕ) (a z : S), Pk ν W (i + j) a z = ∑ u, Pk ν W i a u * Pk ν W j u z
  | 0, j, a, z => by simp [Pk]
  | i + 1, j, a, z => by
      rw [show i + 1 + j = (i + j) + 1 by omega]
      simp only [Pk]
      simp_rw [Pk_add i j, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc]

lemma Pk_succ_right (i : ℕ) (a z : S) :
    Pk ν W (i + 1) a z = ∑ u, Pk ν W i a u * Pm ν W u z := by
  rw [Pk_add]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp [Pk]

end Pk

end EuclideanLineAvgDist.Dev.PathCalc
end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.Bridge

open EuclideanLineAvgDist.Embedding EuclideanLineAvgDist.Dev.PathCalc

variable {S : Type u} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The Markov kernel on the finite set `S` with transition weights `M`. -/
noncomputable def Pker (M : S → S → ℝ≥0∞) : Kernel S S :=
  Kernel.ofFunOfCountable (fun a => ∑ z, M a z • Measure.dirac z)

lemma Pker_apply_singleton (M : S → S → ℝ≥0∞) (a u : S) : Pker M a {u} = M a u := by
  simp [Pker, Kernel.ofFunOfCountable, Finset.sum_apply,
    Measure.dirac_apply', Set.indicator, eq_comm]

lemma Pker_markov (M : S → S → ℝ≥0∞) (hrow : ∀ a, ∑ z, M a z = 1) : IsMarkovKernel (Pker M) := by
  refine ⟨fun a => ⟨?_⟩⟩
  have : (Pker M a) Set.univ = ∑ u, Pker M a {u} := by
    rw [MeasureTheory.sum_measure_singleton]; simp
  rw [this]
  simp_rw [Pker_apply_singleton]
  exact hrow a

/-- The uniform probability measure on `S`. -/
noncomputable def unif (S : Type u) [Fintype S] [MeasurableSpace S] : Measure S :=
  (Fintype.card S : ℝ≥0∞)⁻¹ • ∑ a : S, Measure.dirac a

lemma unif_prob (hn : 0 < Fintype.card S) : IsProbabilityMeasure (unif S) := by
  refine ⟨?_⟩
  simp [unif, Finset.sum_apply]
  rw [ENNReal.inv_mul_cancel] <;> simp
  omega

lemma lintegral_unif (F : S → ℝ≥0∞) :
    ∫⁻ a, F a ∂(unif S) = (Fintype.card S : ℝ≥0∞)⁻¹ * ∑ a, F a := by
  simp [unif, lintegral_smul_measure, lintegral_finsetSum_measure]

lemma compProd_singleton (κ : Kernel S S) [IsMarkovKernel κ] (x y : S) :
    (unif S ⊗ₘ κ) {(x, y)} = (Fintype.card S : ℝ≥0∞)⁻¹ * κ x {y} := by
  rw [Measure.compProd_apply (measurableSet_singleton _), lintegral_unif]
  congr 1
  rw [Finset.sum_eq_single x]
  · congr 1; ext z; simp
  · intro b _ hb
    have : Prod.mk b ⁻¹' {(x, y)} = ∅ := by ext z; simp [hb]
    simp [this]
  · simp

lemma Pker_reversible (M : S → S → ℝ≥0∞) (hrow : ∀ a, ∑ z, M a z = 1)
    (hsy : ∀ a z, M a z = M z a) : IsReversible (unif S) (Pker M) := by
  haveI := Pker_markov M hrow
  unfold IsReversible
  refine Measure.ext_of_singleton fun p => ?_
  obtain ⟨x, y⟩ := p
  rw [Measure.map_apply measurable_swap (measurableSet_singleton _)]
  have : Prod.swap ⁻¹' {(x, y)} = {(y, x)} := by ext z; simp [Prod.ext_iff, and_comm, eq_comm]
  rw [this, compProd_singleton, compProd_singleton, Pker_apply_singleton, Pker_apply_singleton, hsy]

section withW

variable {G : Type u} [MeasurableSpace G] (ν : Measure G) [IsProbabilityMeasure ν] (W : G → S → S → ℝ≥0∞)

lemma kernelIter_singleton (hrow : ∀ a, ∑ z, Pm ν W a z = 1) :
    ∀ (i : ℕ) (a u : S), kernelIter (Pker (Pm ν W)) i a {u} = Pk ν W i a u := by
  haveI := Pker_markov (Pm ν W) hrow
  intro i
  induction i with
  | zero =>
      intro a u
      simp [kernelIter, Pk, Kernel.id_apply, Measure.dirac_apply' _ (measurableSet_singleton _),
        Set.indicator, eq_comm]
  | succ i ih =>
      intro a u
      rw [Pk_succ_right, kernelIter, Kernel.comp_apply,
        Measure.bind_apply (measurableSet_singleton _) (Kernel.aemeasurable _), lintegral_fintype]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Pker_apply_singleton, ih, mul_comm]

lemma sqDisp_formula {k : ℕ} (hrow : ∀ a, ∑ z, Pm ν W a z = 1) (φ : S → Eucl k) (i : ℕ) :
    sqDisplacement φ (unif S ⊗ₘ kernelIter (Pker (Pm ν W)) i) =
      (Fintype.card S : ℝ≥0∞)⁻¹ * ∑ a, ∑ u, Pk ν W i a u * ENNReal.ofReal (‖φ u - φ a‖ ^ 2) := by
  haveI := Pker_markov (Pm ν W) hrow
  haveI : IsMarkovKernel (kernelIter (Pker (Pm ν W)) i) := by
    induction i with
    | zero => simp only [kernelIter]; infer_instance
    | succ i ih => simp only [kernelIter]; infer_instance
  unfold sqDisplacement
  rw [lintegral_fintype, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [compProd_singleton, kernelIter_singleton ν W hrow]
  ring

theorem sq_bridge {k : ℕ} (hn : 0 < Fintype.card S) (hrow : ∀ a, ∑ z, Pm ν W a z = 1)
    (hsy : ∀ a z, Pm ν W a z = Pm ν W z a) (φ : S → Eucl k) (i : ℕ) (hi : 1 ≤ i) :
    (Fintype.card S : ℝ≥0∞)⁻¹ * ∑ a, ∑ u, Pk ν W i a u * ENNReal.ofReal (‖φ u - φ a‖ ^ 2) ≤
      (i : ℝ≥0∞) * ((Fintype.card S : ℝ≥0∞)⁻¹ *
        ∑ a, ∑ u, Pm ν W a u * ENNReal.ofReal (‖φ u - φ a‖ ^ 2)) := by
  haveI := Pker_markov (Pm ν W) hrow
  haveI := unif_prob (S := S) hn
  have h := reversible_squared_displacement φ (measurable_of_finite φ) (Pker (Pm ν W)) (unif S)
    (Pker_reversible (Pm ν W) hrow hsy) i hi
  rw [sqDisp_formula ν W hrow φ i] at h
  have h1 : kernelIter (Pker (Pm ν W)) 1 = Pker (Pm ν W) := by
    simp only [kernelIter]
    ext a s hs
    simp [Kernel.comp_apply, Kernel.id_apply, Measure.bind_apply hs (Kernel.aemeasurable _)]
  rw [← h1, sqDisp_formula ν W hrow φ 1] at h
  have : ∀ a u, Pk ν W 1 a u = Pm ν W a u := fun a u => by simp [Pk]
  simpa [this] using h

end withW

end EuclideanLineAvgDist.Dev.Bridge
end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.Pathwise

open EuclideanLineAvgDist.Embedding EuclideanLineAvgDist.Dev.PathCalc EuclideanLineAvgDist.Dev.Gaussian1


section generic

variable {G S : Type u} [MeasurableSpace G] [Fintype S] [MeasurableSpace S]

/-- Real-valued version of `sumT`. -/
noncomputable def sumTR (h : ℕ → G → S → S → ℝ) : (r : ℕ) → S → (Fin r → G × S) → ℝ
  | 0, _, _ => 0
  | r + 1, w, p => h 0 (p 0).1 w (p 0).2 + sumTR (fun i => h (i + 1)) r (p 0).2 (Fin.tail p)

lemma sumTR_nonneg : ∀ (r : ℕ) (h : ℕ → G → S → S → ℝ), (∀ i g w z, 0 ≤ h i g w z) →
    ∀ w p, 0 ≤ sumTR h r w p
  | 0, h, _, w, p => by simp [sumTR]
  | r + 1, h, hh, w, p => by
      simp only [sumTR]
      exact add_nonneg (hh _ _ _ _) (sumTR_nonneg r _ (fun i g w z => hh _ _ _ _) _ _)

lemma sumT_ofReal : ∀ (r : ℕ) (h : ℕ → G → S → S → ℝ), (∀ i g w z, 0 ≤ h i g w z) →
    ∀ w p, sumT (fun i g w z => ENNReal.ofReal (h i g w z)) r w p = ENNReal.ofReal (sumTR h r w p)
  | 0, h, _, w, p => by simp [sumT, sumTR]
  | r + 1, h, hh, w, p => by
      simp only [sumT, sumTR]
      rw [sumT_ofReal r (fun i => h (i + 1)) (fun i g w z => hh _ _ _ _),
        ENNReal.ofReal_add (hh _ _ _ _) (sumTR_nonneg r _ (fun i g w z => hh _ _ _ _) _ _)]

lemma sumTR_lin : ∀ (r : ℕ) (h1 h2 : ℕ → G → S → S → ℝ) (b : ℝ) (w : S) (p : Fin r → G × S),
    sumTR (fun i g w z => h1 i g w z - h2 i g w z - b) r w p =
      sumTR h1 r w p - sumTR h2 r w p - r * b
  | 0, h1, h2, b, w, p => by simp [sumTR]
  | r + 1, h1, h2, b, w, p => by
      simp only [sumTR]
      rw [sumTR_lin r (fun i => h1 (i + 1)) (fun i => h2 (i + 1))]
      push_cast; ring

end generic

section gauss

variable {k : ℕ} {S : Type} [Fintype S] [MeasurableSpace S] (val : S → Eucl k)

lemma step_exp {c : ℝ} (hc : 0 ≤ c) (g v : Eucl k) :
    ENNReal.ofReal (Real.exp (c * |inner ℝ g v| - c ^ 2 * ‖v‖ ^ 2 / 2 - Real.log 2)) ≤ mix c v g := by
  unfold mix
  apply ENNReal.ofReal_le_ofReal
  have h2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  have hu : Real.exp (c * |inner ℝ g v|) ≤ Real.exp (c * inner ℝ g v) + Real.exp (-(c * inner ℝ g v)) := by
    rcases abs_cases (inner ℝ g v) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
      have := Real.exp_pos (-(c * inner ℝ g v))
      linarith
    · rw [h, mul_neg]
      have := Real.exp_pos (c * inner ℝ g v)
      linarith
  have e1 : Real.exp (c * |inner ℝ g v| - c ^ 2 * ‖v‖ ^ 2 / 2 - Real.log 2) =
      Real.exp (c * |inner ℝ g v|) / 2 * Real.exp (-(c ^ 2 * ‖v‖ ^ 2 / 2)) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_neg (Real.log 2), h2]
    ring
  rw [e1]
  gcongr

variable (a0 : Eucl k) {c : ℕ → ℝ}

lemma path_exp : ∀ (r : ℕ) (c : ℕ → ℝ), (∀ i, 0 ≤ c i) → ∀ (w : S) (p : Fin r → Eucl k × S),
    ENNReal.ofReal (Real.exp (sumTR (fun i (g : Eucl k) (_ : S) (z : S) =>
      c i * |inner ℝ g (val z - a0)| - c i ^ 2 * ‖val z - a0‖ ^ 2 / 2 - Real.log 2) r w p)) ≤
      Fp (fun i (g : Eucl k) (z : S) => mix (c i) (val z - a0) g) r p
  | 0, c, _, w, p => by simp [sumTR, Fp]
  | r + 1, c, hc, w, p => by
      simp only [sumTR, Fp]
      rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact mul_le_mul' (step_exp (hc 0) _ _) (path_exp r (fun i => c (i + 1)) (fun i => hc _) _ _)

lemma pointwise_ineq (hc : ∀ i, 0 ≤ c i) (n : ℕ) (hn : 1 ≤ n) (r : ℕ) (w : S) (p : Fin r → Eucl k × S) :
    ENNReal.ofReal (sumTR (fun i (g : Eucl k) (_ : S) (z : S) =>
        c i * |inner ℝ g (val z - a0)|) r w p) + 1 ≤
      ENNReal.ofReal (sumTR (fun i (g : Eucl k) (_ : S) (z : S) =>
        c i ^ 2 * ‖val z - a0‖ ^ 2 / 2) r w p) + ENNReal.ofReal (r * Real.log 2 + Real.log n) +
      ENNReal.ofReal (1 / (n : ℝ)) * Fp (fun i (g : Eucl k) (z : S) => mix (c i) (val z - a0) g) r p := by
  set L := sumTR (fun i (g : Eucl k) (_ : S) (z : S) => c i * |inner ℝ g (val z - a0)|) r w p with hL
  set Q := sumTR (fun i (g : Eucl k) (_ : S) (z : S) => c i ^ 2 * ‖val z - a0‖ ^ 2 / 2) r w p with hQ
  have hL0 : 0 ≤ L := sumTR_nonneg _ _ (fun i g w z => by have := hc i; positivity) _ _
  have hQ0 : 0 ≤ Q := sumTR_nonneg _ _ (fun i g w z => by positivity) _ _
  have hE := path_exp val a0 r c hc w p
  have hlin := sumTR_lin r (fun i (g : Eucl k) (_ : S) (z : S) => c i * |inner ℝ g (val z - a0)|)
    (fun i (g : Eucl k) (_ : S) (z : S) => c i ^ 2 * ‖val z - a0‖ ^ 2 / 2) (Real.log 2) w p
  rw [← hL, ← hQ] at hlin
  rw [hlin] at hE
  set F := Fp (fun i (g : Eucl k) (z : S) => mix (c i) (val z - a0) g) r p
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  set E := L - Q - r * Real.log 2 with hEdef
  have h1 : L + 1 ≤ Q + (r * Real.log 2 + Real.log n) + Real.exp E * (1 / n) := by
    have := Real.add_one_le_exp (E - Real.log n)
    rw [Real.exp_sub, Real.exp_log hnpos] at this
    have e2 : Real.exp E * (1 / n) = Real.exp E / n := by ring
    rw [e2]
    linarith
  calc ENNReal.ofReal L + 1 = ENNReal.ofReal (L + 1) := by
        rw [ENNReal.ofReal_add hL0 zero_le_one]; simp
    _ ≤ ENNReal.ofReal (Q + (r * Real.log 2 + Real.log n) + Real.exp E * (1 / n)) :=
        ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal Q + ENNReal.ofReal (r * Real.log 2 + Real.log n) +
          ENNReal.ofReal (Real.exp E) * ENNReal.ofReal (1 / n) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add hQ0 (by positivity), ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ _ := by
        rw [mul_comm (ENNReal.ofReal (1 / n)) F]
        gcongr

end gauss

section chain

variable {k : ℕ} {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [DecidableEq S]
  (val : S → Eucl k) (a0 : Eucl k) {c : ℕ → ℝ} (W : Eucl k → S → S → ℝ≥0∞)

theorem per_a (hW : ∀ a z, Measurable (fun g => W g a z)) (hs : ∀ g a, ∑ z, W g a z = 1)
    (hsy : ∀ g a z, W g a z = W g z a) (hc : ∀ i, 0 ≤ c i) (hn : 1 ≤ Fintype.card S) (r : ℕ) (a : S)
    (ha : val a = a0) :
    ∑ i ∈ Finset.range r, ∑ u, Pk (stdGaussian (Eucl k)) W i a u *
        ∫⁻ g, ∑ z, W g u z * ENNReal.ofReal (c i * |inner ℝ g (val z - a0)|) ∂(stdGaussian (Eucl k)) ≤
      ∑ i ∈ Finset.range r, ∑ u, Pk (stdGaussian (Eucl k)) W i a u *
        ∫⁻ g, ∑ z, W g u z * ENNReal.ofReal (c i ^ 2 * ‖val z - a0‖ ^ 2 / 2) ∂(stdGaussian (Eucl k)) +
      ENNReal.ofReal (r * Real.log 2 + Real.log (Fintype.card S)) := by
  subst ha
  haveI : Nonempty S := ⟨a⟩
  set ν := stdGaussian (Eucl k) with hν
  set n := Fintype.card S with hn_def
  have hval : Measurable val := measurable_of_finite val
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hΛ : 0 ≤ (r : ℝ) * Real.log 2 + Real.log n := by positivity
  -- the functionals
  set hL : ℕ → Eucl k → S → S → ℝ := fun i g _ z => c i * |inner ℝ g (val z - val a)| with hLdef
  set hQ : ℕ → Eucl k → S → S → ℝ := fun i g _ z => c i ^ 2 * ‖val z - val a‖ ^ 2 / 2 with hQdef
  have hL0 : ∀ i g w z, 0 ≤ hL i g w z := fun i g w z => by have := hc i; simp only [hLdef]; positivity
  have hQ0 : ∀ i g w z, 0 ≤ hQ i g w z := fun i g w z => by simp only [hQdef]; positivity
  have hmL : ∀ i w, Measurable (fun x : Eucl k × S => ENNReal.ofReal (hL i x.1 w x.2)) := by
    intro i w; simp only [hLdef]; fun_prop
  have hmQ : ∀ i w, Measurable (fun x : Eucl k × S => ENNReal.ofReal (hQ i x.1 w x.2)) := by
    intro i w; simp only [hQdef]; fun_prop
  have EL := pathE_sumT (ν := ν) hW hs r (fun i g w z => ENNReal.ofReal (hL i g w z)) hmL a
  have EQ := pathE_sumT (ν := ν) hW hs r (fun i g w z => ENNReal.ofReal (hQ i g w z)) hmQ a
  have hsL := sumT_meas r (fun i g w z => ENNReal.ofReal (hL i g w z)) hmL a
  have hsQ := sumT_meas r (fun i g w z => ENNReal.ofReal (hQ i g w z)) hmQ a
  let mm : ℕ → Eucl k → S → ℝ≥0∞ := fun i g z => mix (c i) (val z - val a) g
  have hmm : ∀ i, Measurable (fun x : Eucl k × S => mm i x.1 x.2) := by
    intro i; simp only [mm, mix]; fun_prop
  have hFm := Fp_meas r mm hmm
  have hP : ∀ w, ∑ z, Pm ν W w z = 1 := fun w => by
    simp only [Pm]
    rw [← lintegral_finsetSum _ (fun z _ => hW w z)]
    simp [hs]
  have hmass := pathE_Fp_sum (ν := ν) (W := W) hW hs hsy r mm hmm (fun i z => lintegral_mix _ _)
    (fun i g z => ENNReal.ofReal_ne_top)
  have hFa : pathE ν W r a (Fp mm r) ≤ n := by
    rw [← hmass]
    exact Finset.single_le_sum (f := fun y => pathE ν W r y (Fp mm r)) (fun _ _ => zero_le) (Finset.mem_univ a)
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnt : (n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top n
  have hinv : ENNReal.ofReal (1 / (n : ℝ)) * (n : ℝ≥0∞) = 1 := by
    rw [one_div, ENNReal.ofReal_inv_of_pos hnR, ENNReal.ofReal_natCast]
    exact ENNReal.inv_mul_cancel hn0 hnt
  have key : pathE ν W r a (fun p => sumT (fun i g w z => ENNReal.ofReal (hL i g w z)) r a p + 1) ≤
      pathE ν W r a (fun p => (sumT (fun i g w z => ENNReal.ofReal (hQ i g w z)) r a p +
        ENNReal.ofReal ((r : ℝ) * Real.log 2 + Real.log n)) +
        ENNReal.ofReal (1 / (n : ℝ)) * Fp mm r p) := by
    refine pathE_mono ν W r a _ _ fun p => ?_
    rw [sumT_ofReal r hL hL0, sumT_ofReal r hQ hQ0]
    exact pointwise_ineq val (val a) hc n hn r a p
  set sQ := sumT (fun i g w z => ENNReal.ofReal (hQ i g w z)) r a with hsQdef
  set Λ' := ENNReal.ofReal ((r : ℝ) * Real.log 2 + Real.log n) with hΛ'
  have A1 : pathE ν W r a (fun p => (sQ p + Λ') + ENNReal.ofReal (1 / (n : ℝ)) * Fp mm r p) =
      pathE ν W r a (fun p => sQ p + Λ') + pathE ν W r a (fun p => ENNReal.ofReal (1 / (n : ℝ)) * Fp mm r p) :=
    pathE_add ν W hW r a (fun p => sQ p + Λ') (fun p => ENNReal.ofReal (1 / (n : ℝ)) * Fp mm r p)
      (hsQ.add measurable_const) (hFm.const_mul _)
  have A2 : pathE ν W r a (fun p => sQ p + Λ') = pathE ν W r a sQ + pathE ν W r a (fun _ => Λ') :=
    pathE_add ν W hW r a sQ (fun _ => Λ') hsQ measurable_const
  have A3 : pathE ν W r a (fun p => sumT (fun i g w z => ENNReal.ofReal (hL i g w z)) r a p + 1) =
      pathE ν W r a (sumT (fun i g w z => ENNReal.ofReal (hL i g w z)) r a) + pathE ν W r a (fun _ => 1) :=
    pathE_add ν W hW r a _ (fun _ => 1) hsL measurable_const
  rw [A1, A2, A3, pathE_const ν W hs, pathE_const ν W hs,
    pathE_const_mul ν W r a _ _ ENNReal.ofReal_ne_top] at key
  rw [EL, EQ] at key
  have key2 : (∑ i ∈ Finset.range r, ∑ u, Pk ν W i a u * ∫⁻ g, ∑ z, W g u z *
        ENNReal.ofReal (hL i g a z) ∂ν) + 1 ≤
      (∑ i ∈ Finset.range r, ∑ u, Pk ν W i a u * ∫⁻ g, ∑ z, W g u z *
        ENNReal.ofReal (hQ i g a z) ∂ν + ENNReal.ofReal ((r : ℝ) * Real.log 2 + Real.log n)) + 1 := by
    refine key.trans ?_
    gcongr
    calc ENNReal.ofReal (1 / (n : ℝ)) * pathE ν W r a (Fp mm r) ≤ ENNReal.ofReal (1 / (n : ℝ)) * n := by gcongr
      _ = 1 := hinv
  exact (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).mp key2

end chain

end EuclideanLineAvgDist.Dev.Pathwise
end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.Average

open EuclideanLineAvgDist.Embedding EuclideanLineAvgDist.Dev.PathCalc EuclideanLineAvgDist.Dev.Gaussian1
  EuclideanLineAvgDist.Dev.Pathwise EuclideanLineAvgDist.Dev.Bridge

lemma am_gm_lint {k : ℕ} (v : Eucl k) {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) :
    ∫⁻ g, ENNReal.ofReal (c * |inner ℝ g v|) ∂(stdGaussian (Eucl k)) ≤
      ENNReal.ofReal (c * ε / 2) * ENNReal.ofReal (‖v‖ ^ 2) + ENNReal.ofReal (c / (2 * ε)) := by
  have hpt : ∀ g : Eucl k, ENNReal.ofReal (c * |inner ℝ g v|) ≤
      ENNReal.ofReal (c * ε / 2) * ENNReal.ofReal ((inner ℝ g v) ^ 2) + ENNReal.ofReal (c / (2 * ε)) := by
    intro g
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    set x := inner ℝ g v
    have : c * |x| ≤ c * ε / 2 * x ^ 2 + c / (2 * ε) := by
      have h1 : 0 ≤ (ε * |x| - 1) ^ 2 := sq_nonneg _
      have h2 : |x| ^ 2 = x ^ 2 := sq_abs x
      have h3 : |x| ≤ ε / 2 * x ^ 2 + 1 / (2 * ε) := by
        rw [← h2]
        have : ε / 2 * |x| ^ 2 + 1 / (2 * ε) - |x| = (ε * |x| - 1) ^ 2 / (2 * ε) := by
          field_simp; ring
        have : 0 ≤ (ε * |x| - 1) ^ 2 / (2 * ε) := by positivity
        linarith
      calc c * |x| ≤ c * (ε / 2 * x ^ 2 + 1 / (2 * ε)) := by gcongr
        _ = _ := by ring
    exact this
  calc ∫⁻ g, ENNReal.ofReal (c * |inner ℝ g v|) ∂(stdGaussian (Eucl k))
      ≤ ∫⁻ g, (ENNReal.ofReal (c * ε / 2) * ENNReal.ofReal ((inner ℝ g v) ^ 2) +
          ENNReal.ofReal (c / (2 * ε))) ∂(stdGaussian (Eucl k)) := lintegral_mono hpt
    _ = _ := by
        rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop), lintegral_inner_sq]
        simp

section tri

variable {k : ℕ} {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  (val : S → Eucl k) (W : Eucl k → S → S → ℝ≥0∞)

lemma tri_step (hW : ∀ a z, Measurable (fun g => W g a z)) (hs : ∀ g a, ∑ z, W g a z = 1)
    (u a : S) {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) :
    ENNReal.ofReal c * ∫⁻ g, ∑ z, W g u z * ENNReal.ofReal |inner ℝ g (val z - val u)|
        ∂(stdGaussian (Eucl k)) ≤
      ∫⁻ g, ∑ z, W g u z * ENNReal.ofReal (c * |inner ℝ g (val z - val a)|) ∂(stdGaussian (Eucl k)) +
        ENNReal.ofReal (c * ε / 2) * ENNReal.ofReal (‖val u - val a‖ ^ 2) +
        ENNReal.ofReal (c / (2 * ε)) := by
  have hval : Measurable val := measurable_of_finite val
  have m1 : Measurable (fun g : Eucl k => ∑ z, W g u z *
      ENNReal.ofReal (c * |inner ℝ g (val z - val a)|)) :=
    Finset.measurable_sum _ fun z _ => (hW u z).mul (by fun_prop)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ∫⁻ g, ENNReal.ofReal c * ∑ z, W g u z * ENNReal.ofReal |inner ℝ g (val z - val u)|
          ∂(stdGaussian (Eucl k))
      ≤ ∫⁻ g, (∑ z, W g u z * ENNReal.ofReal (c * |inner ℝ g (val z - val a)|) +
          ENNReal.ofReal (c * |inner ℝ g (val u - val a)|)) ∂(stdGaussian (Eucl k)) := by
        refine lintegral_mono fun g => ?_
        calc ENNReal.ofReal c * ∑ z, W g u z * ENNReal.ofReal |inner ℝ g (val z - val u)|
            = ∑ z, W g u z * ENNReal.ofReal (c * |inner ℝ g (val z - val u)|) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun z _ => ?_
              rw [ENNReal.ofReal_mul hc]; ring
          _ ≤ ∑ z, W g u z * (ENNReal.ofReal (c * |inner ℝ g (val z - val a)|) +
                ENNReal.ofReal (c * |inner ℝ g (val u - val a)|)) := by
              refine Finset.sum_le_sum fun z _ => ?_
              gcongr
              rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
              apply ENNReal.ofReal_le_ofReal
              have : inner ℝ g (val z - val u) = inner ℝ g (val z - val a) - inner ℝ g (val u - val a) := by
                rw [← inner_sub_right]; congr 1; abel
              rw [this, ← mul_add]
              gcongr
              exact abs_sub _ _
          _ = _ := by
              simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul]
    _ = ∫⁻ g, ∑ z, W g u z * ENNReal.ofReal (c * |inner ℝ g (val z - val a)|) ∂(stdGaussian (Eucl k)) +
          ∫⁻ g, ENNReal.ofReal (c * |inner ℝ g (val u - val a)|) ∂(stdGaussian (Eucl k)) :=
        lintegral_add_left m1 _
    _ ≤ _ := by
        rw [add_assoc]
        gcongr
        exact am_gm_lint _ hc hε

end tri

section avg

variable {k : ℕ} {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [DecidableEq S]
  (val : S → Eucl k) (W : Eucl k → S → S → ℝ≥0∞)

/-- `E |⟨γ, x₁ - x₀⟩|` in extended nonnegative form. -/
noncomputable def tE : ℝ≥0∞ :=
  (Fintype.card S : ℝ≥0∞)⁻¹ * ∑ u, ∫⁻ g, ∑ z, W g u z *
    ENNReal.ofReal |inner ℝ g (val z - val u)| ∂(stdGaussian (Eucl k))

/-- `E ‖x₁ - x₀‖²` in extended nonnegative form. -/
noncomputable def sE : ℝ≥0∞ :=
  (Fintype.card S : ℝ≥0∞)⁻¹ * ∑ a, ∑ u, Pm (stdGaussian (Eucl k)) W a u *
    ENNReal.ofReal (‖val u - val a‖ ^ 2)

/-- `E ‖x_j - x_0‖²`. -/
noncomputable def Bj (j : ℕ) : ℝ≥0∞ :=
  (Fintype.card S : ℝ≥0∞)⁻¹ * ∑ a, ∑ u, Pk (stdGaussian (Eucl k)) W j a u *
    ENNReal.ofReal (‖val u - val a‖ ^ 2)

lemma hq_simp (hW : ∀ a z, Measurable (fun g => W g a z)) (i : ℕ) (a : S) {cc : ℝ} (hcc : 0 ≤ cc) :
    ∑ u, Pk (stdGaussian (Eucl k)) W i a u * ∫⁻ g, ∑ z, W g u z *
        ENNReal.ofReal (cc * ‖val z - val a‖ ^ 2 / 2) ∂(stdGaussian (Eucl k)) =
      ENNReal.ofReal (cc / 2) * ∑ z, Pk (stdGaussian (Eucl k)) W (i + 1) a z *
        ENNReal.ofReal (‖val z - val a‖ ^ 2) := by
  have h1 : ∀ u, ∫⁻ g, ∑ z, W g u z * ENNReal.ofReal (cc * ‖val z - val a‖ ^ 2 / 2)
        ∂(stdGaussian (Eucl k)) =
      ∑ z, Pm (stdGaussian (Eucl k)) W u z * ENNReal.ofReal (cc * ‖val z - val a‖ ^ 2 / 2) := by
    intro u
    have m : ∀ z, Measurable (fun g => W g u z *
        ENNReal.ofReal (cc * ‖val z - val a‖ ^ 2 / 2)) := fun z => (hW u z).mul measurable_const
    rw [lintegral_finsetSum _ (fun z _ => m z)]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [lintegral_mul_const _ (hW u z)]; rfl
  simp_rw [h1]
  simp_rw [Pk_succ_right, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [show cc * ‖val z - val a‖ ^ 2 / 2 = cc / 2 * ‖val z - val a‖ ^ 2 by ring,
    ENNReal.ofReal_mul (by positivity)]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

lemma Pm_row (hW : ∀ a z, Measurable (fun g => W g a z)) (hs : ∀ g a, ∑ z, W g a z = 1) (a : S) :
    ∑ z, Pm (stdGaussian (Eucl k)) W a z = 1 := by
  simp only [Pm]
  have m : ∀ z, Measurable (fun g => W g a z) := fun z => hW a z
  rw [← lintegral_finsetSum _ (fun z _ => m z)]
  simp [hs]

lemma Pm_sym (hsy : ∀ g a z, W g a z = W g z a) (a z : S) :
    Pm (stdGaussian (Eucl k)) W a z = Pm (stdGaussian (Eucl k)) W z a := by
  simp only [Pm, hsy]

lemma Bj_le (hW : ∀ a z, Measurable (fun g => W g a z)) (hs : ∀ g a, ∑ z, W g a z = 1)
    (hsy : ∀ g a z, W g a z = W g z a) (hn : 0 < Fintype.card S) (j : ℕ) :
    Bj val W j ≤ (j : ℝ≥0∞) * sE val W := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [Bj, Pk]
  · exact sq_bridge (stdGaussian (Eucl k)) W hn (Pm_row W hW hs) (Pm_sym W hsy) val j hj

lemma step_one (hW : ∀ a z, Measurable (fun g => W g a z)) (hs : ∀ g a, ∑ z, W g a z = 1)
    (hsy : ∀ g a z, W g a z = W g z a) (hn : 0 < Fintype.card S) {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    (i : ℕ) :
    ENNReal.ofReal c * tE val W ≤
      (Fintype.card S : ℝ≥0∞)⁻¹ * ∑ a, ∑ u, Pk (stdGaussian (Eucl k)) W i a u *
        (∫⁻ g, ∑ z, W g u z * ENNReal.ofReal (c * |inner ℝ g (val z - val a)|) ∂(stdGaussian (Eucl k))) +
      ENNReal.ofReal (c * ε / 2) * Bj val W i + ENNReal.ofReal (c / (2 * ε)) := by
  set ν := stdGaussian (Eucl k) with hν
  set n := Fintype.card S with hn_def
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  have hnt : (n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top n
  have hcol := Pk_col ν W (Pm_row W hW hs) (Pm_sym W hsy) i
  have hrow := Pk_row ν W (Pm_row W hW hs) i
  set Ht : S → ℝ≥0∞ := fun u => ∫⁻ g, ∑ z, W g u z * ENNReal.ofReal |inner ℝ g (val z - val u)| ∂ν with hHt
  have e1 : ENNReal.ofReal c * tE val W =
      (n : ℝ≥0∞)⁻¹ * ∑ a, ∑ u, Pk ν W i a u * (ENNReal.ofReal c * Ht u) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hcol, one_mul]
    simp only [tE, hHt, Finset.mul_sum]
    rw [Finset.sum_congr rfl]
    intro u _
    ring
  have e2 : ∀ a u, Pk ν W i a u * (ENNReal.ofReal c * Ht u) ≤ Pk ν W i a u *
      ((∫⁻ g, ∑ z, W g u z * ENNReal.ofReal (c * |inner ℝ g (val z - val a)|) ∂ν) +
        ENNReal.ofReal (c * ε / 2) * ENNReal.ofReal (‖val u - val a‖ ^ 2) +
        ENNReal.ofReal (c / (2 * ε))) := fun a u => by
    gcongr
    exact tri_step val W hW hs u a hc hε
  rw [e1]
  calc (n : ℝ≥0∞)⁻¹ * ∑ a, ∑ u, Pk ν W i a u * (ENNReal.ofReal c * Ht u)
      ≤ (n : ℝ≥0∞)⁻¹ * ∑ a, ∑ u, Pk ν W i a u *
      ((∫⁻ g, ∑ z, W g u z * ENNReal.ofReal (c * |inner ℝ g (val z - val a)|) ∂ν) +
        ENNReal.ofReal (c * ε / 2) * ENNReal.ofReal (‖val u - val a‖ ^ 2) +
        ENNReal.ofReal (c / (2 * ε))) := by
        gcongr with a _ u _
        exact tri_step val W hW hs u a hc hε
    _ = _ := by
        simp_rw [mul_add, Finset.sum_add_distrib, mul_add]
        have mid : (n : ℝ≥0∞)⁻¹ * ∑ x, ∑ x_1, Pk ν W i x x_1 *
            (ENNReal.ofReal (c * ε / 2) * ENNReal.ofReal (‖val x_1 - val x‖ ^ 2)) =
            ENNReal.ofReal (c * ε / 2) * Bj val W i := by
          simp only [Bj, hν, hn_def]
          rw [mul_left_comm]
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          ring
        have last : (n : ℝ≥0∞)⁻¹ * ∑ x : S, ∑ x_1, Pk ν W i x x_1 * ENNReal.ofReal (c / (2 * ε)) =
            ENNReal.ofReal (c / (2 * ε)) := by
          simp_rw [← Finset.sum_mul, hrow]
          simp only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hh : (n : ℝ≥0∞)⁻¹ * (Fintype.card S : ℝ≥0∞) = 1 := ENNReal.inv_mul_cancel hn0 hnt
          calc _ = ((n : ℝ≥0∞)⁻¹ * (Fintype.card S : ℝ≥0∞)) * ENNReal.ofReal (c / (2 * ε)) := by ring
            _ = _ := by rw [hh, one_mul]
        rw [mid, last]

lemma avg_per_a (hW : ∀ a z, Measurable (fun g => W g a z)) (hs : ∀ g a, ∑ z, W g a z = 1)
    (hsy : ∀ g a z, W g a z = W g z a) (hn : 0 < Fintype.card S) {c : ℕ → ℝ} (hc : ∀ i, 0 ≤ c i)
    (r : ℕ) :
    ∑ i ∈ Finset.range r, (Fintype.card S : ℝ≥0∞)⁻¹ * ∑ a, ∑ u, Pk (stdGaussian (Eucl k)) W i a u *
        (∫⁻ g, ∑ z, W g u z * ENNReal.ofReal (c i * |inner ℝ g (val z - val a)|)
          ∂(stdGaussian (Eucl k))) ≤
      ∑ i ∈ Finset.range r, ENNReal.ofReal (c i ^ 2 / 2) * Bj val W (i + 1) +
        ENNReal.ofReal (r * Real.log 2 + Real.log (Fintype.card S)) := by
  set ν := stdGaussian (Eucl k) with hν
  set n := Fintype.card S with hn_def
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  have hnt : (n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top n
  set Λ := ENNReal.ofReal (r * Real.log 2 + Real.log n) with hΛ
  have h1 : ∀ a : S, ∑ i ∈ Finset.range r, ∑ u, Pk ν W i a u *
        (∫⁻ g, ∑ z, W g u z * ENNReal.ofReal (c i * |inner ℝ g (val z - val a)|) ∂ν) ≤
      ∑ i ∈ Finset.range r, ENNReal.ofReal (c i ^ 2 / 2) * ∑ z, Pk ν W (i + 1) a z *
        ENNReal.ofReal (‖val z - val a‖ ^ 2) + Λ := by
    intro a
    refine (per_a val (val a) W hW hs hsy hc hn r a rfl).trans ?_
    gcongr
    exact (hq_simp val W hW _ a (sq_nonneg (c _))).le
  calc ∑ i ∈ Finset.range r, (n : ℝ≥0∞)⁻¹ * ∑ a, ∑ u, Pk ν W i a u *
        (∫⁻ g, ∑ z, W g u z * ENNReal.ofReal (c i * |inner ℝ g (val z - val a)|) ∂ν)
      = (n : ℝ≥0∞)⁻¹ * ∑ a, ∑ i ∈ Finset.range r, ∑ u, Pk ν W i a u *
        (∫⁻ g, ∑ z, W g u z * ENNReal.ofReal (c i * |inner ℝ g (val z - val a)|) ∂ν) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (n : ℝ≥0∞)⁻¹ * ∑ a : S, (∑ i ∈ Finset.range r, ENNReal.ofReal (c i ^ 2 / 2) * ∑ z, Pk ν W (i + 1) a z *
        ENNReal.ofReal (‖val z - val a‖ ^ 2) + Λ) := by
        gcongr with a _
        exact h1 a
    _ = _ := by
        rw [Finset.sum_add_distrib, mul_add, Finset.sum_comm]
        congr 1
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Bj, hn_def, ← Finset.mul_sum]
          ring
        · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hh : (n : ℝ≥0∞)⁻¹ * (Fintype.card S : ℝ≥0∞) = 1 := ENNReal.inv_mul_cancel hn0 hnt
          calc _ = ((n : ℝ≥0∞)⁻¹ * (Fintype.card S : ℝ≥0∞)) * Λ := by ring
            _ = _ := by rw [hh, one_mul]

theorem main_enn (hW : ∀ a z, Measurable (fun g => W g a z)) (hs : ∀ g a, ∑ z, W g a z = 1)
    (hsy : ∀ g a z, W g a z = W g z a) (hn : 0 < Fintype.card S) {c ε : ℕ → ℝ}
    (hc : ∀ i, 0 ≤ c i) (hε : ∀ i, 0 < ε i) (r : ℕ) :
    ∑ i ∈ Finset.range r, ENNReal.ofReal (c i) * tE val W ≤
      ∑ i ∈ Finset.range r, (ENNReal.ofReal (c i ^ 2 / 2) * (((i + 1 : ℕ) : ℝ≥0∞) * sE val W) +
        ENNReal.ofReal (c i * ε i / 2) * ((i : ℝ≥0∞) * sE val W) + ENNReal.ofReal (c i / (2 * ε i))) +
      ENNReal.ofReal (r * Real.log 2 + Real.log (Fintype.card S)) := by
  have h1 := Finset.sum_le_sum (s := Finset.range r) (fun i _ => step_one val W hW hs hsy hn (hc i) (hε i) i)
  have h2 := avg_per_a val W hW hs hsy hn hc r
  calc ∑ i ∈ Finset.range r, ENNReal.ofReal (c i) * tE val W
      ≤ ∑ i ∈ Finset.range r, ((Fintype.card S : ℝ≥0∞)⁻¹ * ∑ a, ∑ u, Pk (stdGaussian (Eucl k)) W i a u *
        (∫⁻ g, ∑ z, W g u z * ENNReal.ofReal (c i * |inner ℝ g (val z - val a)|)
          ∂(stdGaussian (Eucl k))) + ENNReal.ofReal (c i * ε i / 2) * Bj val W i +
          ENNReal.ofReal (c i / (2 * ε i))) := h1
    _ = (∑ i ∈ Finset.range r, (Fintype.card S : ℝ≥0∞)⁻¹ * ∑ a, ∑ u, Pk (stdGaussian (Eucl k)) W i a u *
        (∫⁻ g, ∑ z, W g u z * ENNReal.ofReal (c i * |inner ℝ g (val z - val a)|)
          ∂(stdGaussian (Eucl k)))) + ∑ i ∈ Finset.range r, ENNReal.ofReal (c i * ε i / 2) * Bj val W i +
          ∑ i ∈ Finset.range r, ENNReal.ofReal (c i / (2 * ε i)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ (∑ i ∈ Finset.range r, ENNReal.ofReal (c i ^ 2 / 2) * (((i + 1 : ℕ) : ℝ≥0∞) * sE val W) +
        ENNReal.ofReal (r * Real.log 2 + Real.log (Fintype.card S))) +
        ∑ i ∈ Finset.range r, ENNReal.ofReal (c i * ε i / 2) * ((i : ℝ≥0∞) * sE val W) +
        ∑ i ∈ Finset.range r, ENNReal.ofReal (c i / (2 * ε i)) := by
        refine add_le_add (add_le_add (h2.trans (add_le_add_left (Finset.sum_le_sum fun i _ => ?_) _) |>.trans le_rfl)
          (Finset.sum_le_sum fun i _ => ?_)) le_rfl
        · gcongr
          exact Bj_le val W hW hs hsy hn (i + 1)
        · gcongr
          exact Bj_le val W hW hs hsy hn i
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        ring

end avg

end EuclideanLineAvgDist.Dev.Average
end

section
open scoped BigOperators
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.RealCore

/-- Per-term lower bound. -/
lemma term_lb {t s : ℝ} (ht : 0 ≤ t) (hs : 0 < s) (i : ℕ) :
    t ^ 2 / (4 * ((i + 1) * s)) - 1 ≤
      (t / ((i + 1) * s)) * t -
        ((t / ((i + 1) * s)) ^ 2 / 2 * (((i + 1 : ℕ) : ℝ) * s) +
          (t / ((i + 1) * s)) * (1 / Real.sqrt ((i + 1) * s)) / 2 * ((i : ℝ) * s) +
          (t / ((i + 1) * s)) / (2 * (1 / Real.sqrt ((i + 1) * s)))) := by
  have hj : (0 : ℝ) < (i + 1) * s := by positivity
  set q := Real.sqrt ((i + 1) * s) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr hj
  have hq2 : q ^ 2 = (i + 1) * s := Real.sq_sqrt hj.le
  have his : (i : ℝ) * s ≤ q ^ 2 := by rw [hq2]; nlinarith
  push_cast
  have e1 : t / ((i + 1) * s) = t / q ^ 2 := by rw [hq2]
  rw [e1]
  have h1 : t / q ^ 2 * (1 / q) / 2 * (i * s) ≤ t / q ^ 2 * (1 / q) / 2 * q ^ 2 := by
    gcongr
  have h2 : t / q ^ 2 * (1 / q) / 2 * q ^ 2 = t / (2 * q) := by field_simp
  have h3 : t / q ^ 2 / (2 * (1 / q)) = t / (2 * q) := by field_simp
  have h4 : (t / q ^ 2) ^ 2 / 2 * ((i + 1) * s) = t ^ 2 / (2 * q ^ 2) := by
    rw [← hq2]; field_simp
  have h5 : t / q ^ 2 * t = t ^ 2 / q ^ 2 := by ring
  have h6 : t ^ 2 / (4 * ((i + 1) * s)) = t ^ 2 / (4 * q ^ 2) := by rw [hq2]
  rw [h4, h3, h5, h6]
  have h7 : 0 ≤ (t / (2 * q) - 1) ^ 2 := sq_nonneg _
  have h8 : (t / (2 * q) - 1) ^ 2 = t ^ 2 / (4 * q ^ 2) - t / q + 1 := by field_simp; ring
  have h9 : t / q = t / (2 * q) + t / (2 * q) := by field_simp; ring
  have h10 : t ^ 2 / q ^ 2 = 4 * (t ^ 2 / (4 * q ^ 2)) := by field_simp
  have h11 : t ^ 2 / (2 * q ^ 2) = 2 * (t ^ 2 / (4 * q ^ 2)) := by field_simp; ring
  linarith [h1, h2]

lemma real_core {t s Λ : ℝ} (ht : 0 ≤ t) (hs : 0 < s) (r : ℕ)
    (H : ∑ i ∈ Finset.range r, (t / ((i + 1) * s)) * t ≤
      ∑ i ∈ Finset.range r, ((t / ((i + 1) * s)) ^ 2 / 2 * (((i + 1 : ℕ) : ℝ) * s) +
          (t / ((i + 1) * s)) * (1 / Real.sqrt ((i + 1) * s)) / 2 * ((i : ℝ) * s) +
          (t / ((i + 1) * s)) / (2 * (1 / Real.sqrt ((i + 1) * s)))) + Λ) :
    t ^ 2 / s * ∑ i ∈ Finset.range r, (1 / ((i : ℝ) + 1)) ≤ 4 * (Λ + r) := by
  have h1 := Finset.sum_le_sum (s := Finset.range r) (fun i _ => term_lb ht hs i)
  rw [Finset.sum_sub_distrib] at h1
  have h2 : ∑ i ∈ Finset.range r, (t ^ 2 / (4 * (((i : ℝ) + 1) * s))) =
      t ^ 2 / (4 * s) * ∑ i ∈ Finset.range r, (1 / ((i : ℝ) + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    field_simp
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h1
  have h3 : ∑ i ∈ Finset.range r, ((t / ((i + 1) * s)) * t -
        ((t / ((i + 1) * s)) ^ 2 / 2 * (((i + 1 : ℕ) : ℝ) * s) +
          (t / ((i + 1) * s)) * (1 / Real.sqrt ((i + 1) * s)) / 2 * ((i : ℝ) * s) +
          (t / ((i + 1) * s)) / (2 * (1 / Real.sqrt ((i + 1) * s))))) ≤ Λ := by
    rw [Finset.sum_sub_distrib]; linarith
  have h4 := Finset.sum_le_sum (s := Finset.range r) (fun i _ => term_lb ht hs i)
  have h5 : ∑ i ∈ Finset.range r, (t ^ 2 / (4 * (((i : ℝ) + 1) * s)) - 1) ≤ Λ :=
    h4.trans h3
  rw [Finset.sum_sub_distrib, h2] at h5
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h5
  have : t ^ 2 / s = 4 * (t ^ 2 / (4 * s)) := by field_simp
  rw [this]
  nlinarith

lemma harm_lb (r : ℕ) : Real.log ((r : ℝ) + 1) ≤ ∑ i ∈ Finset.range r, (1 / ((i : ℝ) + 1)) := by
  have := log_add_one_le_harmonic r
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at this
  push_cast at this
  simpa [one_div] using this

lemma final_bound {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) (hn : 1 ≤ n)
    (h : τ * ∑ i ∈ Finset.range ⌈Real.log (max 3 (n : ℝ))⌉₊, (1 / ((i : ℝ) + 1)) ≤
      4 * ((⌈Real.log (max 3 (n : ℝ))⌉₊ * Real.log 2 + Real.log n) + ⌈Real.log (max 3 (n : ℝ))⌉₊)) :
    τ ≤ 20 * (Real.log (max 3 (n : ℝ)) / Real.log (Real.log (max 3 (n : ℝ)))) := by
  set N : ℝ := max 3 (n : ℝ) with hN
  set L := Real.log N with hL
  set r := ⌈L⌉₊ with hr
  have hN3 : (3 : ℝ) ≤ N := le_max_left _ _
  have hnN : (n : ℝ) ≤ N := le_max_right _ _
  have hL1 : 1 < L := by
    have h3 : Real.log 3 ≤ L := Real.log_le_log (by norm_num) hN3
    have : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    linarith
  have hLL : 0 < Real.log L := Real.log_pos hL1
  have hrL : L ≤ r := Nat.le_ceil L
  have hrL2 : (r : ℝ) < L + 1 := Nat.ceil_lt_add_one (by linarith)
  have hlogn : Real.log n ≤ L := Real.log_le_log (by exact_mod_cast hn) hnN
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have hlog20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hH : Real.log L ≤ ∑ i ∈ Finset.range r, (1 / ((i : ℝ) + 1)) := by
    refine le_trans ?_ (harm_lb r)
    exact Real.log_le_log (by linarith) (by linarith)
  have hrpos : (0 : ℝ) ≤ r := by positivity
  have h1 : τ * Real.log L ≤ 4 * ((r * Real.log 2 + Real.log n) + r) := by
    refine le_trans ?_ h
    exact mul_le_mul_of_nonneg_left hH hτ
  have h2 : 4 * ((r * Real.log 2 + Real.log n) + r) ≤ 20 * L := by
    have : (r : ℝ) * Real.log 2 ≤ r := by nlinarith
    nlinarith
  rw [← mul_div_assoc, le_div_iff₀ hLL]
  nlinarith

end EuclideanLineAvgDist.Dev.RealCore
end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.Final

open EuclideanLineAvgDist.Embedding EuclideanLineAvgDist.Dev.PathCalc EuclideanLineAvgDist.Dev.Gaussian1
  EuclideanLineAvgDist.Dev.Pathwise EuclideanLineAvgDist.Dev.Bridge EuclideanLineAvgDist.Dev.Average
  EuclideanLineAvgDist.Dev.RealCore

section conv

variable {k : ℕ} {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [DecidableEq S]
  (val : S → Eucl k) (W : Eucl k → S → S → ℝ≥0∞)

/-- Real form of `main_enn`. -/
theorem main_real (hW : ∀ a z, Measurable (fun g => W g a z)) (hs : ∀ g a, ∑ z, W g a z = 1)
    (hsy : ∀ g a z, W g a z = W g z a) (hn : 0 < Fintype.card S) {t s : ℝ} (ht : 0 ≤ t) (hs0 : 0 ≤ s)
    (htE : tE val W = ENNReal.ofReal t) (hsE : sE val W = ENNReal.ofReal s) {c ε : ℕ → ℝ}
    (hc : ∀ i, 0 ≤ c i) (hε : ∀ i, 0 < ε i) (r : ℕ) :
    ∑ i ∈ Finset.range r, c i * t ≤
      ∑ i ∈ Finset.range r, (c i ^ 2 / 2 * (((i + 1 : ℕ) : ℝ) * s) + c i * ε i / 2 * ((i : ℝ) * s) +
        c i / (2 * ε i)) + (r * Real.log 2 + Real.log (Fintype.card S)) := by
  have h := main_enn val W hW hs hsy hn hc hε r
  rw [htE, hsE] at h
  have hn1 : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (Fintype.card S) := Real.log_nonneg hn1
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hnn : ∀ i, 0 ≤ c i / (2 * ε i) := fun i => by have := hc i; have := hε i; positivity
  have e1 : ∑ i ∈ Finset.range r, ENNReal.ofReal (c i) * ENNReal.ofReal t =
      ENNReal.ofReal (∑ i ∈ Finset.range r, c i * t) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hc i) ht)]
    exact Finset.sum_congr rfl fun i _ => (ENNReal.ofReal_mul (hc i)).symm
  have e2 : ∀ i, ENNReal.ofReal (c i ^ 2 / 2) * (((i + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal s) +
        ENNReal.ofReal (c i * ε i / 2) * ((i : ℝ≥0∞) * ENNReal.ofReal s) + ENNReal.ofReal (c i / (2 * ε i)) =
      ENNReal.ofReal (c i ^ 2 / 2 * (((i + 1 : ℕ) : ℝ) * s) + c i * ε i / 2 * ((i : ℝ) * s) +
        c i / (2 * ε i)) := by
    intro i
    have := hc i; have := hε i
    rw [ENNReal.ofReal_add (by positivity) (hnn i), ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  simp_rw [e2] at h
  rw [e1, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by have := hc i; have := hε i; positivity),
    ← ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => by have := hc i; have := hε i; positivity)
      (by positivity)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by
    have := Finset.sum_nonneg (s := Finset.range r) (fun i _ => (by have := hc i; have := hε i; positivity : 0 ≤
      c i ^ 2 / 2 * (((i + 1 : ℕ) : ℝ) * s) + c i * ε i / 2 * ((i : ℝ) * s) + c i / (2 * ε i)))
    positivity)).mp h

end conv

lemma lint_abs_fin {k : ℕ} (v : Eucl k) :
    ∫⁻ g, ENNReal.ofReal |inner ℝ g v| ∂(stdGaussian (Eucl k)) ≠ ⊤ := by
  have h := am_gm_lint v (c := 1) (ε := 1) zero_le_one one_pos
  simp only [one_mul] at h
  refine ne_top_of_le_ne_top ?_ h
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.ofReal_ne_top⟩

section XK

variable {k : ℕ} (X : Finset (Eucl k)) (K : Eucl k → X → X → ℝ)

/-- The weights `ofReal (K g a z)`. -/
noncomputable def Wk : Eucl k → X → X → ℝ≥0∞ := fun g a z => ENNReal.ofReal (K g a z)

variable {X K}

lemma Wk_meas (hK : IsGaussianTransitionFamily X K) (a z : X) : Measurable (fun g => Wk X K g a z) :=
  (hK.2.2.2 a z).ennreal_ofReal

lemma Wk_sum (hK : IsGaussianTransitionFamily X K) (g : Eucl k) (a : X) : ∑ z, Wk X K g a z = 1 := by
  simp only [Wk]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hK.2.1 g a z), hK.2.2.1 g a]
  simp

lemma Wk_symm (hK : IsGaussianTransitionFamily X K) (g : Eucl k) (a z : X) :
    Wk X K g a z = Wk X K g z a := by
  simp only [Wk, hK.1 g a z]

lemma Wk_le_one (hK : IsGaussianTransitionFamily X K) (g : Eucl k) (a z : X) : Wk X K g a z ≤ 1 := by
  rw [← Wk_sum hK g a]
  exact Finset.single_le_sum (f := fun z => Wk X K g a z) (fun _ _ => zero_le) (Finset.mem_univ z)

lemma t_bridge (hK : IsGaussianTransitionFamily X K) (hn : 1 ≤ X.card) :
    ENNReal.ofReal (projectionMean X K) = tE (Subtype.val : X → Eucl k) (Wk X K) ∧
      tE (Subtype.val : X → Eucl k) (Wk X K) ≠ ⊤ := by
  have hnR : (0 : ℝ) < X.card := by exact_mod_cast hn
  set f : Eucl k → ℝ := fun g => (1 / (X.card : ℝ)) * ∑ x : X, ∑ y : X,
      K g x y * |inner ℝ g ((y : Eucl k) - (x : Eucl k))| with hf
  have hf0 : ∀ g, 0 ≤ f g := fun g => by
    simp only [hf]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (hK.2.1 g x y) (abs_nonneg _))
  have hfm : Measurable f := by
    simp only [hf]
    refine measurable_const.mul (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ => ?_)
    exact (hK.2.2.2 x y).mul (by fun_prop)
  have pw : ∀ g, ENNReal.ofReal (f g) = (Fintype.card X : ℝ≥0∞)⁻¹ * ∑ x : X, ∑ y : X,
      Wk X K g x y * ENNReal.ofReal |inner ℝ g ((y : Eucl k) - (x : Eucl k))| := by
    intro g
    simp only [hf]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun x _ =>
      Finset.sum_nonneg fun y _ => mul_nonneg (hK.2.1 g x y) (abs_nonneg _))]
    congr 1
    · rw [one_div, ENNReal.ofReal_inv_of_pos hnR, Fintype.card_coe]
      simp
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg (fun y _ => mul_nonneg (hK.2.1 g x y) (abs_nonneg _))]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [ENNReal.ofReal_mul (hK.2.1 g x y)]
      rfl
  have hmeasy : ∀ x : X, Measurable (fun g : Eucl k => ∑ y : X, Wk X K g x y *
      ENNReal.ofReal |inner ℝ g ((y : Eucl k) - (x : Eucl k))|) := fun x =>
    Finset.measurable_sum _ fun y _ => (Wk_meas hK x y).mul (by fun_prop)
  have hlint : ∫⁻ g, ENNReal.ofReal (f g) ∂(stdGaussian (Eucl k)) =
      tE (Subtype.val : X → Eucl k) (Wk X K) := by
    simp_rw [pw]
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun x _ => hmeasy x),
      lintegral_finsetSum _ (fun x _ => hmeasy x)]
    simp only [tE, Fintype.card_coe]
  have hfin : tE (Subtype.val : X → Eucl k) (Wk X K) ≠ ⊤ := by
    unfold tE
    refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (by rw [Fintype.card_coe]; omega))) (ENNReal.sum_ne_top.mpr fun u _ => ?_)
    refine ne_top_of_le_ne_top (b := ∑ z : X, ∫⁻ g, ENNReal.ofReal |inner ℝ g ((z : Eucl k) - (u : Eucl k))|
      ∂(stdGaussian (Eucl k))) (ENNReal.sum_ne_top.mpr fun z _ => lint_abs_fin _) ?_
    rw [← lintegral_finsetSum _ (fun z _ => by fun_prop)]
    refine lintegral_mono fun g => Finset.sum_le_sum fun z _ => ?_
    calc Wk X K g u z * ENNReal.ofReal |inner ℝ g ((z : Eucl k) - (u : Eucl k))|
        ≤ 1 * ENNReal.ofReal |inner ℝ g ((z : Eucl k) - (u : Eucl k))| := by
          gcongr; exact Wk_le_one hK g u z
      _ = _ := one_mul _
  refine ⟨?_, hfin⟩
  have : projectionMean X K = ∫ g, f g ∂(stdGaussian (Eucl k)) := rfl
  rw [this, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm.aestronglyMeasurable,
    ENNReal.ofReal_toReal (by rw [hlint]; exact hfin), hlint]

lemma s_bridge (hK : IsGaussianTransitionFamily X K) (hn : 1 ≤ X.card) :
    ENNReal.ofReal (squaredStepMean X K) = sE (Subtype.val : X → Eucl k) (Wk X K) ∧
      sE (Subtype.val : X → Eucl k) (Wk X K) ≠ ⊤ := by
  have hnR : (0 : ℝ) < X.card := by exact_mod_cast hn
  set f : Eucl k → ℝ := fun g => (1 / (X.card : ℝ)) * ∑ x : X, ∑ y : X,
      K g x y * ‖(y : Eucl k) - (x : Eucl k)‖ ^ 2 with hf
  have hf0 : ∀ g, 0 ≤ f g := fun g => by
    simp only [hf]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (hK.2.1 g x y) (by positivity))
  have hfm : Measurable f := by
    simp only [hf]
    refine measurable_const.mul (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ => ?_)
    exact (hK.2.2.2 x y).mul (by fun_prop)
  have pw : ∀ g, ENNReal.ofReal (f g) = (Fintype.card X : ℝ≥0∞)⁻¹ * ∑ x : X, ∑ y : X,
      Wk X K g x y * ENNReal.ofReal (‖(y : Eucl k) - (x : Eucl k)‖ ^ 2) := by
    intro g
    simp only [hf]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun x _ =>
      Finset.sum_nonneg fun y _ => mul_nonneg (hK.2.1 g x y) (by positivity))]
    congr 1
    · rw [one_div, ENNReal.ofReal_inv_of_pos hnR, Fintype.card_coe]
      simp
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg (fun y _ => mul_nonneg (hK.2.1 g x y) (by positivity))]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [ENNReal.ofReal_mul (hK.2.1 g x y)]
      rfl
  have hlint : ∫⁻ g, ENNReal.ofReal (f g) ∂(stdGaussian (Eucl k)) =
      sE (Subtype.val : X → Eucl k) (Wk X K) := by
    simp_rw [pw]
    have hm : ∀ x : X, Measurable (fun g : Eucl k => ∑ y : X, Wk X K g x y *
        ENNReal.ofReal (‖(y : Eucl k) - (x : Eucl k)‖ ^ 2)) := fun x =>
      Finset.measurable_sum _ fun y _ => (Wk_meas hK x y).mul measurable_const
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun x _ => hm x),
      lintegral_finsetSum _ (fun x _ => hm x)]
    simp only [sE, Fintype.card_coe]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    have hm2 : ∀ y : X, Measurable (fun g : Eucl k => Wk X K g x y *
        ENNReal.ofReal (‖(y : Eucl k) - (x : Eucl k)‖ ^ 2)) := fun y =>
      (Wk_meas hK x y).mul measurable_const
    rw [lintegral_finsetSum _ (fun y _ => hm2 y)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [lintegral_mul_const _ (Wk_meas hK x y)]
    rfl
  have hfin : sE (Subtype.val : X → Eucl k) (Wk X K) ≠ ⊤ := by
    unfold sE
    refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (by rw [Fintype.card_coe]; omega)))
      (ENNReal.sum_ne_top.mpr fun a _ => ENNReal.sum_ne_top.mpr fun u _ => ?_)
    refine ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top
    refine ne_top_of_le_ne_top (b := 1) ENNReal.one_ne_top ?_
    calc Pm (stdGaussian (Eucl k)) (Wk X K) a u = ∫⁻ g, Wk X K g a u ∂(stdGaussian (Eucl k)) := rfl
      _ ≤ ∫⁻ g, 1 ∂(stdGaussian (Eucl k)) := lintegral_mono fun g => Wk_le_one hK g a u
      _ = 1 := by simp
  refine ⟨?_, hfin⟩
  have : squaredStepMean X K = ∫ g, f g ∂(stdGaussian (Eucl k)) := rfl
  rw [this, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm.aestronglyMeasurable,
    ENNReal.ofReal_toReal (by rw [hlint]; exact hfin), hlint]

end XK

end EuclideanLineAvgDist.Dev.Final
end

section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.Final

open EuclideanLineAvgDist.Embedding EuclideanLineAvgDist.Dev.Average EuclideanLineAvgDist.Dev.RealCore

lemma proj_nonneg {k : ℕ} (X : Finset (Eucl k)) (K : Eucl k → X → X → ℝ)
    (hK : IsGaussianTransitionFamily X K) : 0 ≤ projectionMean X K := by
  unfold projectionMean
  refine integral_nonneg fun g => ?_
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (hK.2.1 g x y) (abs_nonneg _))

lemma sq_nonneg' {k : ℕ} (X : Finset (Eucl k)) (K : Eucl k → X → X → ℝ)
    (hK : IsGaussianTransitionFamily X K) : 0 ≤ squaredStepMean X K := by
  unfold squaredStepMean
  refine integral_nonneg fun g => ?_
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (hK.2.1 g x y) (by positivity))

theorem main_theorem {k : ℕ} (X : Finset (Eucl k)) (K : Eucl k → X → X → ℝ)
    (hK : IsGaussianTransitionFamily X K) :
    projectionMean X K ^ 2 ≤ 20 * squaredStepMean X K * logRate X.card := by
  classical
  by_cases hn0 : X.card = 0
  · have hX : X = ∅ := Finset.card_eq_zero.mp hn0
    subst hX
    simp [projectionMean, squaredStepMean]
  have hn : 1 ≤ X.card := Nat.one_le_iff_ne_zero.mpr hn0
  have hnpos : 0 < Fintype.card X := by rw [Fintype.card_coe]; omega
  obtain ⟨htE, -⟩ := t_bridge hK hn
  obtain ⟨hsE, -⟩ := s_bridge hK hn
  have ht := proj_nonneg X K hK
  have hs0 := sq_nonneg' X K hK
  set t := projectionMean X K with ht_def
  set s := squaredStepMean X K with hs_def
  have hW := Wk_meas hK
  have hs1 := Wk_sum hK
  have hsy := Wk_symm hK
  have hlog : 0 ≤ Real.log (X.card : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rcases hs0.eq_or_lt with hs00 | hspos
  · -- `s = 0` forces `t = 0`
    have ht0 : t ≤ 0 := by
      by_contra hpos
      replace hpos : 0 < t := lt_of_not_ge hpos
      set M : ℝ := 1 / 2 + Real.log 2 + Real.log (X.card : ℝ) with hM
      have hM0 : 0 ≤ M := by positivity
      set c0 : ℝ := (M + 1) / t with hc0
      have hc0pos : 0 < c0 := by positivity
      have := main_real (Subtype.val : X → Eucl k) (Wk X K) hW hs1 hsy hnpos ht hs0 htE.symm
        hsE.symm (c := fun _ => c0) (ε := fun _ => c0) (fun _ => hc0pos.le)
        (fun _ => hc0pos) 1
      simp only [Finset.sum_range_one, Fintype.card_coe] at this
      rw [← hs00] at this
      have e : c0 / (2 * c0) = 1 / 2 := by field_simp
      simp at this
      have h2 : c0 * t = M + 1 := by rw [hc0]; field_simp
      rw [e] at this
      linarith
    have : t = 0 := le_antisymm ht0 ht
    rw [this, ← hs00]
    simp
  · have hr := main_real (Subtype.val : X → Eucl k) (Wk X K) hW hs1 hsy hnpos ht hs0 htE.symm hsE.symm
      (c := fun i => t / (((i : ℝ) + 1) * s)) (ε := fun i => 1 / Real.sqrt (((i : ℝ) + 1) * s))
      (fun i => by positivity)
      (fun i => by have : (0 : ℝ) < ((i : ℝ) + 1) * s := by positivity
                   exact one_div_pos.mpr (Real.sqrt_pos.mpr this))
      ⌈Real.log (max 3 (X.card : ℝ))⌉₊
    rw [Fintype.card_coe] at hr
    have hcore := real_core ht hspos _ hr
    have hfin := final_bound (τ := t ^ 2 / s) (by positivity) X.card hn hcore
    unfold logRate
    rw [div_le_iff₀ hspos] at hfin
    nlinarith

end EuclideanLineAvgDist.Dev.Final

open scoped BigOperators
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist

open EuclideanLineAvgDist.Embedding in
theorem chk_gaussian_transition_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (X : Finset (Eucl k)) (K : Eucl k → X → X → ℝ),
      IsGaussianTransitionFamily X K →
        projectionMean X K ^ 2 ≤ C * squaredStepMean X K * logRate X.card :=
  ⟨20, by norm_num, fun _ _ _ hK => EuclideanLineAvgDist.Dev.Final.main_theorem _ _ hK⟩

end EuclideanLineAvgDist

end

theorem solution : type_of% @EuclideanLineAvgDist.chk_gaussian_transition_bound := @EuclideanLineAvgDist.chk_gaussian_transition_bound
