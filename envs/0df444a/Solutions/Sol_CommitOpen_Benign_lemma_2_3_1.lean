-- Prove2me | solution 1 for CommitOpen.Benign.lemma_2_3_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:03:52.578266+00:00
-- url     : https://prove2.me/submissions/d7bb45d8-fae4-4d10-8b92-005878d6bf68

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace X5CO

open CommitOpen.Benign

variable {ι I W E : Type} [Fintype ι] [Fintype I] [Fintype W] [Fintype E]

theorem norm_sq_comb (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ ι)) (J : Finset I) (c : I → ℂ) :
    ‖∑ i ∈ J, c i • b i‖ ^ 2 = ∑ i ∈ J, ‖c i‖ ^ 2 := by
  have h := b.orthonormal.inner_sum c c J
  rw [inner_self_eq_norm_sq_to_K] at h
  have h3 : ∑ i ∈ J, (starRingEnd ℂ) (c i) * c i = ((∑ i ∈ J, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => Complex.conj_mul' (c i)
  have h4 := h.trans h3
  have h5 : ((‖∑ i ∈ J, c i • b i‖ ^ 2 : ℝ) : ℂ) = ((∑ i ∈ J, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h4]; push_cast; rfl
  exact Complex.ofReal_injective h5

theorem amp_eq (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ ι)) (J : Finset I) (α : I → ℂ)
    (φE : I → EuclideanSpace ℂ E) (u : EuclideanSpace ℂ ι) (e : E) :
    ampAlong u (superposition b J α φE) e = ∑ i ∈ J, (α i * inner ℂ u (b i)) * φE i e := by
  simp only [ampAlong, superposition, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.star_apply]; ring

theorem col_eq (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ ι)) (J : Finset I) (α : I → ℂ)
    (φE : I → EuclideanSpace ℂ E) (e : E) :
    (WithLp.toLp 2 fun a => superposition b J α φE (a, e) : EuclideanSpace ℂ ι) =
      ∑ i ∈ J, (α i * φE i e) • b i := by
  ext a
  simp only [superposition, PiLp.toLp_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem total_meas (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ ι))
    (w : OrthonormalBasis W ℂ (EuclideanSpace ℂ ι)) (J : Finset I) (α : I → ℂ)
    (φE : I → EuclideanSpace ℂ E) (hφE : ∀ i ∈ J, ‖φE i‖ = 1)
    (hα : ∑ i ∈ J, ‖α i‖ ^ 2 = 1) :
    ∑ v, measProb (w v) (superposition b J α φE) = 1 := by
  set φ := superposition b J α φE
  have h1 : ∀ v e, ampAlong (w v) φ e = inner ℂ (w v) (WithLp.toLp 2 fun a => φ (a, e) :
      EuclideanSpace ℂ ι) := by
    intro v e
    simp only [ampAlong, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  unfold measProb
  rw [Finset.sum_comm]
  have h2 : ∀ e, ∑ v, ‖ampAlong (w v) φ e‖ ^ 2 =
      ‖(WithLp.toLp 2 fun a => φ (a, e) : EuclideanSpace ℂ ι)‖ ^ 2 := by
    intro e
    rw [← w.sum_sq_norm_inner_right]
    exact Finset.sum_congr rfl fun v _ => by rw [h1]
  rw [Finset.sum_congr rfl fun e _ => h2 e]
  rw [Finset.sum_congr rfl fun e _ => by rw [col_eq, norm_sq_comb]]
  simp_rw [norm_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_pow, ← Finset.mul_sum]
  rw [← hα]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := hφE i hi
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at this
  rw [this, mul_one]

theorem meas_le (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ ι)) (J : Finset I) (α : I → ℂ)
    (φE : I → EuclideanSpace ℂ E) (hφE : ∀ i ∈ J, ‖φE i‖ = 1) (u : EuclideanSpace ℂ ι) :
    measProb u (superposition b J α φE) ≤ J.card * mixtureProb b J α u := by
  set V : EuclideanSpace ℂ E := ∑ i ∈ J, (α i * inner ℂ u (b i)) • φE i
  have hV : measProb u (superposition b J α φE) = ‖V‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    unfold measProb
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [amp_eq]
    congr 2
    simp [V, WithLp.ofLp_sum, Finset.sum_apply]
  have hn : ‖V‖ ≤ ∑ i ∈ J, ‖α i * inner ℂ u (b i)‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i hi => ?_))
    rw [norm_smul, hφE i hi, mul_one]
  rw [hV]
  calc ‖V‖ ^ 2 ≤ (∑ i ∈ J, ‖α i * inner ℂ u (b i)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ ≤ J.card * ∑ i ∈ J, ‖α i * inner ℂ u (b i)‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    _ = _ := by
      unfold mixtureProb; congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_mul, mul_pow]

theorem l231 [Nonempty W] (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ ι))
    (w : OrthonormalBasis W ℂ (EuclideanSpace ℂ ι)) (J : Finset I) (α : I → ℂ)
    (φE : I → EuclideanSpace ℂ E) (hφE : ∀ i ∈ J, ‖φE i‖ = 1)
    (hα : ∑ i ∈ J, ‖α i‖ ^ 2 = 1) :
    minEntropy (fun v => mixtureProb b J α (w v)) - Real.logb 2 (J.card : ℝ) ≤
      minEntropy (fun v => measProb (w v) (superposition b J α φE)) := by
  set P := fun v => measProb (w v) (superposition b J α φE)
  set Q := fun v => mixtureProb b J α (w v)
  set p := Finset.univ.sup' Finset.univ_nonempty P
  set q := Finset.univ.sup' Finset.univ_nonempty Q
  have hpq : p ≤ J.card * q := by
    refine Finset.sup'_le _ _ fun v _ => (meas_le b J α φE hφE (w v)).trans ?_
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' Q (Finset.mem_univ v)) (by positivity)
  have hp : 0 < p := by
    by_contra h
    push Not at h
    have : ∑ v, P v ≤ 0 := Finset.sum_nonpos fun v _ =>
      (Finset.le_sup' P (Finset.mem_univ v)).trans h
    rw [total_meas b w J α φE hφE hα] at this
    linarith
  have hJq : 0 < (J.card : ℝ) * q := hp.trans_le hpq
  have hJ : 0 < (J.card : ℝ) := by
    rcases (Nat.cast_nonneg J.card : (0:ℝ) ≤ J.card).eq_or_lt with h | h
    · rw [← h, zero_mul] at hJq; exact absurd hJq (lt_irrefl 0)
    · exact h
  have hq : 0 < q := pos_of_mul_pos_right hJq hJ.le
  unfold minEntropy
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hp hpq
  rw [Real.logb_mul hJ.ne' hq.ne'] at this
  change -Real.logb 2 q - Real.logb 2 J.card ≤ -Real.logb 2 p
  linarith

end X5CO

open CommitOpen.Benign in
theorem solution {ι I W E : Type} [Fintype ι] [Fintype I] [Fintype W] [Nonempty W]
    [Fintype E] (b : OrthonormalBasis I ℂ (EuclideanSpace ℂ ι))
    (w : OrthonormalBasis W ℂ (EuclideanSpace ℂ ι)) (J : Finset I) (α : I → ℂ)
    (φE : I → EuclideanSpace ℂ E) (hφE : ∀ i ∈ J, ‖φE i‖ = 1)
    (hα : ∑ i ∈ J, ‖α i‖ ^ 2 = 1) :
    minEntropy (fun v => mixtureProb b J α (w v)) - Real.logb 2 (J.card : ℝ) ≤
      minEntropy (fun v => measProb (w v) (superposition b J α φE)) :=
  X5CO.l231 b w J α φE hφE hα
