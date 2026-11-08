-- Prove2me | solution 1 for DynTargetMV.existence_uniqueness_QP
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:51:11.531363+00:00
-- url     : https://prove2.me/submissions/6ca280f3-79fc-4dad-ba33-edae95221cc0

import Mathlib
import Definitions.Def_DynTargetMV_Market_Assumption1
import Definitions.Def_DynTargetMV_Market_Assumption2
import Definitions.Def_DynTargetMV_Market_IsQPSol

open Set Matrix

namespace Aux_DTMV

theorem cont_dot {m : ℕ} (a : Fin m → ℝ) : Continuous (fun w : Fin m → ℝ => a ⬝ᵥ w) := by
  simp only [dotProduct]
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))

theorem cont_mulVec {n m : ℕ} (Q : Matrix (Fin n) (Fin m) ℝ) :
    Continuous (fun w : Fin m → ℝ => Q *ᵥ w) := by
  apply continuous_pi
  intro i
  simp only [Matrix.mulVec]
  exact cont_dot (Q i)

theorem cont_q {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (fun w : Fin m → ℝ => w ⬝ᵥ (S *ᵥ w)) := by
  simp only [dotProduct]
  apply continuous_finsetSum _ (fun i _ => ?_)
  exact (continuous_apply i).mul ((continuous_apply i).comp (cont_mulVec S))

end Aux_DTMV

open DynTargetMV Aux_DTMV in
theorem solution {m d n : ℕ} (M : Market m d n) (hA1 : M.Assumption1)
    (hA2 : M.Assumption2) (ψ : ℝ → ℝ) :
    ∀ t ∈ Ico 0 M.T, ∃! v : Fin m → ℝ, M.IsQPSol ψ t v := by
  intro t ht
  obtain ⟨δ, hδ, hpsd⟩ := hA1.nondeg
  set S := M.σ t * (M.σ t)ᵀ with hS
  have hSsymm : Sᵀ = S := by rw [hS, transpose_mul, transpose_transpose]
  have hcross : ∀ u w : Fin m → ℝ, u ⬝ᵥ (S *ᵥ w) = w ⬝ᵥ (S *ᵥ u) := by
    intro u w
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hSsymm, dotProduct_comm]
  have hq : ∀ w : Fin m → ℝ, δ * (w ⬝ᵥ w) ≤ w ⬝ᵥ (S *ᵥ w) := by
    intro w
    have h := (hpsd t ht.1).dotProduct_mulVec_nonneg w
    simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul] at h
    linarith
  set F : Set (Fin m → ℝ) := {w | ψ t ≤ M.b t ⬝ᵥ w ∧ 0 ≤ M.Q *ᵥ w} with hF
  set f := halfQuad S with hf
  have hfq : ∀ w, f w = (1 / 2) * (w ⬝ᵥ (S *ᵥ w)) := fun w => rfl
  have hfcont : Continuous f := by
    have : f = fun w => (1 / 2 : ℝ) * (w ⬝ᵥ (S *ᵥ w)) := rfl
    rw [this]; exact continuous_const.mul (cont_q S)
  have hFclosed : IsClosed F := by
    apply IsClosed.inter
    · exact isClosed_le continuous_const (cont_dot _)
    · exact isClosed_le continuous_const (cont_mulVec _)
  have hFconv : ∀ u ∈ F, ∀ w ∈ F, (1 / 2 : ℝ) • (u + w) ∈ F := by
    rintro u ⟨hu1, hu2⟩ w ⟨hw1, hw2⟩
    refine ⟨?_, ?_⟩
    · rw [dotProduct_smul, dotProduct_add, smul_eq_mul]; linarith
    · rw [mulVec_smul, mulVec_add]
      intro i
      have h1 := hu2 i
      have h2 := hw2 i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.zero_apply] at h1 h2 ⊢
      linarith
  -- feasibility
  obtain ⟨y, hy1, hy2⟩ := hA2 t ht
  set c := max 0 (ψ t / (M.b t ⬝ᵥ y)) with hc
  have hc0 : 0 ≤ c := le_max_left _ _
  have hw0 : c • y ∈ F := by
    refine ⟨?_, ?_⟩
    · rw [dotProduct_smul, smul_eq_mul]
      have : ψ t / (M.b t ⬝ᵥ y) ≤ c := le_max_right _ _
      rw [div_le_iff₀ hy1] at this
      linarith
    · rw [mulVec_smul]
      intro i
      have := hy2 i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
      exact mul_nonneg hc0 this
  set w0 := c • y
  -- compact sublevel set
  set K := F ∩ {w | f w ≤ f w0} with hK
  have hKc : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact hFclosed.inter (isClosed_le hfcont continuous_const)
    · set R := Real.sqrt (2 * f w0 / δ) with hR
      apply (Metric.isBounded_closedBall (x := (0 : Fin m → ℝ)) (r := R)).subset
      rintro w ⟨_, hwf⟩
      simp only [Set.mem_setOf_eq] at hwf
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
      intro i
      rw [Real.norm_eq_abs]
      apply Real.abs_le_sqrt
      have h1 := hq w
      have h2 : w i ^ 2 ≤ w ⬝ᵥ w := by
        simp only [dotProduct]
        have := Finset.single_le_sum (f := fun j => w j * w j)
          (fun j _ => mul_self_nonneg (w j)) (Finset.mem_univ i)
        nlinarith
      rw [hfq] at hwf
      rw [le_div_iff₀ hδ]
      nlinarith
  obtain ⟨v, hvK, hvmin⟩ := hKc.exists_isMinOn ⟨w0, hw0, show f w0 ≤ f w0 from le_refl _⟩ hfcont.continuousOn
  have hvF : v ∈ F := hvK.1
  have hvopt : ∀ w ∈ F, f v ≤ f w := by
    intro w hw
    by_cases hwf : f w ≤ f w0
    · exact isMinOn_iff.mp hvmin w ⟨hw, hwf⟩
    · have := isMinOn_iff.mp hvmin w0 ⟨hw0, show f w0 ≤ f w0 from le_refl _⟩
      push_neg at hwf
      linarith
  refine ⟨v, ⟨hvF, fun w hw => hvopt w hw⟩, ?_⟩
  rintro u ⟨huF, humin⟩
  have h1 : f u ≤ f v := humin hvF
  have h2 : f v ≤ f u := hvopt u huF
  have hmid := hvopt _ (hFconv u huF v hvF)
  have hmid' := humin (hFconv u huF v hvF)
  -- f(mid) = (f u + f v)/2 - (1/8) (u - v) S (u - v)
  have hexp : f ((1 / 2 : ℝ) • (u + v)) =
      (f u + f v) / 2 - (1 / 8) * ((u - v) ⬝ᵥ (S *ᵥ (u - v))) := by
    rw [hfq, hfq, hfq]
    simp only [mulVec_smul, mulVec_add, mulVec_sub, dotProduct_smul, smul_dotProduct,
      dotProduct_add, add_dotProduct, dotProduct_sub, sub_dotProduct, smul_eq_mul]
    rw [hcross v u]
    ring
  have hle : (u - v) ⬝ᵥ (S *ᵥ (u - v)) ≤ 0 := by
    simp only at hmid'
    linarith
  have hzero : (u - v) ⬝ᵥ (u - v) = 0 := by
    have := hq (u - v)
    have h0 : 0 ≤ (u - v) ⬝ᵥ (u - v) := by
      simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    nlinarith
  have := dotProduct_self_eq_zero.mp hzero
  exact (sub_eq_zero.mp this)
