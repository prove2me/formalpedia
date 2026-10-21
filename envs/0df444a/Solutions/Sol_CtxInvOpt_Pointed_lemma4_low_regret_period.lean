-- Prove2me | solution 1 for CtxInvOpt.Pointed.lemma4_low_regret_period
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:54:03.793455+00:00
-- url     : https://prove2.me/submissions/28265924-220e-4067-84a8-fdb8f8be8e90

import Mathlib
import Definitions.Def_CtxInvOpt_Greedy_Online
import Definitions.Def_CtxInvOpt_Pointed_EllCone

set_option autoImplicit false
open Matrix CtxInvOpt.Pointed

namespace CIP4

lemma inner_eq_sum {k : ℕ} (x y : EuclideanSpace ℝ (Fin k)) :
    inner ℝ x y = ∑ i, x i * y i := by
  simp [PiLp.inner_apply, mul_comm]

lemma parseval {m : ℕ} (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ) (a b : Fin (m + 1) → ℝ) :
    (Uᵀ *ᵥ a) ⬝ᵥ (Uᵀ *ᵥ b) = a ⬝ᵥ b := by
  have h : U * Uᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 hU
  rw [Matrix.mulVec_transpose U a, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h,
    Matrix.one_mulVec]

lemma rot_inner {m : ℕ} (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ) (x y : EuclideanSpace ℝ (Fin (m + 1))) :
    ∑ i, rotCoord U x i * rotCoord U y i = inner ℝ x y := by
  rw [inner_eq_sum]
  have := parseval U hU (WithLp.ofLp x) (WithLp.ofLp y)
  simpa [rotCoord, dotProduct] using this

lemma rot_zero {m : ℕ} (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (x : EuclideanSpace ℝ (Fin (m + 1))) :
    rotCoord U x 0 = inner ℝ x (axisVec U) := by
  rw [inner_eq_sum]
  simp [rotCoord, axisVec, Matrix.mulVec, dotProduct, mul_comm]

lemma rot_smul {m : ℕ} (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin (m + 1))) (i : Fin (m + 1)) :
    rotCoord U (c • x) i = c * rotCoord U x i := by
  simp [rotCoord, Matrix.mulVec_smul]

end CIP4

open CIP4 in
theorem solution {n m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (C0 : Set (EuclideanSpace ℝ (Fin (m + 1)))) (hC0 : C0 ⊆ CtxInvOpt.Offline.unitSphere (m + 1))
    (cstar : EuclideanSpace ℝ (Fin (m + 1))) (hcstar : cstar ∈ C0)
    (X : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (m + 1)))
    (xstar : ℕ → EuclideanSpace ℝ (Fin n))
    (hxstar : ∀ s, xstar s ∈ CtxInvOpt.Offline.argminSet cstar (X s) (f s))
    (t : ℕ) (hX : CtxInvOpt.Offline.IsActionSet (X t)) (hf : CtxInvOpt.Offline.IsContext (f t))
    (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ)
    (hK : CtxInvOpt.Greedy.knowledgeSet C0 X f xstar t ⊆ ellCone w U)
    (xpi : EuclideanSpace ℝ (Fin n)) (hxpi : xpi ∈ CtxInvOpt.Offline.argminSet (axisVec U) (X t) (f t))
    (h12 : tailQuad w (rotCoord U (effDiff (f t xpi - f t (xstar t)))) ≤ ε ^ 2) :
    inner ℝ (f t xpi - f t (xstar t)) cstar ≤ ε := by
  have hcK : cstar ∈ CtxInvOpt.Greedy.knowledgeSet C0 X f xstar t :=
    ⟨hcstar, fun s _ x hx => (hxstar s).2 x hx⟩
  obtain ⟨hc0, hcq⟩ := hK hcK
  set u := f t xpi - f t (xstar t) with hu
  by_cases hu0 : u = 0
  · rw [hu0, inner_zero_left]; exact hε.le
  have hupos : 0 < ‖u‖ := norm_pos_iff.2 hu0
  have hxs : xstar t ∈ X t := (hxstar t).1
  have hnu : ‖u‖ ≤ 1 := by
    rw [hu, ← dist_eq_norm]
    calc dist (f t xpi) (f t (xstar t)) ≤ 1 * dist xpi (xstar t) := by
          have := hf.dist_le_mul xpi (xstar t)
          simpa using this
      _ ≤ 1 := by
          rw [one_mul]
          exact (Metric.dist_le_diam_of_mem hX.2.1.isBounded hxpi.1 hxs).trans hX.2.2
  have hua : inner ℝ u (axisVec U) ≤ 0 := by
    rw [hu, inner_sub_left]
    have := hxpi.2 (xstar t) hxs
    linarith
  have hu0' : rotCoord U u 0 ≤ 0 := by rw [rot_zero]; exact hua
  have hcn : ‖cstar‖ = 1 := by simpa [CtxInvOpt.Offline.unitSphere] using hC0 hcstar
  have hc1 : ∑ i, rotCoord U cstar i ^ 2 = 1 := by
    have := rot_inner U hU cstar cstar
    rw [real_inner_self_eq_norm_sq, hcn] at this
    simpa [sq] using this
  have hc0le : rotCoord U cstar 0 ≤ 1 := by
    have h1 : rotCoord U cstar 0 ^ 2 ≤ ∑ i, rotCoord U cstar i ^ 2 :=
      Finset.single_le_sum (f := fun i => rotCoord U cstar i ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ 0)
    rw [hc1] at h1
    nlinarith
  have hdec : inner ℝ u cstar = rotCoord U u 0 * rotCoord U cstar 0 +
      ∑ i : Fin m, rotCoord U u i.succ * rotCoord U cstar i.succ := by
    rw [← rot_inner U hU, Fin.sum_univ_succ]
  -- the test (12)
  have hA : ∑ i : Fin m, w i * rotCoord U u i.succ ^ 2 ≤ ε ^ 2 * ‖u‖ ^ 2 := by
    have e : effDiff u = ‖u‖⁻¹ • u := by unfold effDiff; rw [if_neg hu0]
    rw [e] at h12
    unfold tailQuad at h12
    have h2 : ∀ i : Fin m, w i * rotCoord U (‖u‖⁻¹ • u) i.succ ^ 2 =
        (‖u‖⁻¹) ^ 2 * (w i * rotCoord U u i.succ ^ 2) := by
      intro i; rw [rot_smul]; ring
    simp_rw [h2] at h12
    rw [← Finset.mul_sum] at h12
    have h3 : (‖u‖⁻¹) ^ 2 * ∑ i : Fin m, w i * rotCoord U u i.succ ^ 2 ≤ ε ^ 2 := h12
    have hpos2 : 0 < ‖u‖ ^ 2 := by positivity
    have : ∑ i : Fin m, w i * rotCoord U u i.succ ^ 2 =
        ‖u‖ ^ 2 * ((‖u‖⁻¹) ^ 2 * ∑ i : Fin m, w i * rotCoord U u i.succ ^ 2) := by
      field_simp
    rw [this]
    nlinarith
  -- Cauchy–Schwarz
  have hB : ∑ i : Fin m, rotCoord U cstar i.succ ^ 2 / w i ≤ rotCoord U cstar 0 ^ 2 := hcq
  have hCS : (∑ i : Fin m, rotCoord U u i.succ * rotCoord U cstar i.succ) ^ 2 ≤
      (∑ i : Fin m, w i * rotCoord U u i.succ ^ 2) *
        (∑ i : Fin m, rotCoord U cstar i.succ ^ 2 / w i) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin m => Real.sqrt (w i) * rotCoord U u i.succ)
      (fun i : Fin m => rotCoord U cstar i.succ / Real.sqrt (w i))
    have e1 : ∀ i : Fin m, Real.sqrt (w i) * rotCoord U u i.succ *
        (rotCoord U cstar i.succ / Real.sqrt (w i)) =
        rotCoord U u i.succ * rotCoord U cstar i.succ := by
      intro i
      have : Real.sqrt (w i) ≠ 0 := (Real.sqrt_pos.2 (hw i)).ne'
      field_simp
    have e2 : ∀ i : Fin m, (Real.sqrt (w i) * rotCoord U u i.succ) ^ 2 =
        w i * rotCoord U u i.succ ^ 2 := by
      intro i; rw [mul_pow, Real.sq_sqrt (hw i).le]
    have e3 : ∀ i : Fin m, (rotCoord U cstar i.succ / Real.sqrt (w i)) ^ 2 =
        rotCoord U cstar i.succ ^ 2 / w i := by
      intro i; rw [div_pow, Real.sq_sqrt (hw i).le]
    simp only [e1, e2, e3] at this
    exact this
  set S := ∑ i : Fin m, rotCoord U u i.succ * rotCoord U cstar i.succ with hS
  set R := ε * ‖u‖ * rotCoord U cstar 0 with hR
  have hR0 : 0 ≤ R := by positivity
  have hS2 : S ^ 2 ≤ R ^ 2 := by
    have hAB : (∑ i : Fin m, w i * rotCoord U u i.succ ^ 2) *
        (∑ i : Fin m, rotCoord U cstar i.succ ^ 2 / w i) ≤
        (ε ^ 2 * ‖u‖ ^ 2) * rotCoord U cstar 0 ^ 2 := by
      apply mul_le_mul hA hB
      · exact Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (hw i).le)
      · positivity
    calc S ^ 2 ≤ _ := hCS
      _ ≤ _ := hAB
      _ = R ^ 2 := by rw [hR]; ring
  have hSR : S ≤ R := by
    by_contra hcon
    replace hcon := not_le.1 hcon
    nlinarith
  rw [hdec]
  have h1 : rotCoord U u 0 * rotCoord U cstar 0 ≤ 0 := by nlinarith
  have h2 : R ≤ ε := by
    rw [hR]
    calc ε * ‖u‖ * rotCoord U cstar 0 = ε * (‖u‖ * rotCoord U cstar 0) := by ring
      _ ≤ ε * (1 * 1) := by
          apply mul_le_mul_of_nonneg_left _ hε.le
          exact mul_le_mul hnu hc0le hc0 zero_le_one
      _ = ε := by ring
  linarith
