-- Prove2me | solution 1 for FuzzyGames.Values.diag_axioms
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T03:19:48.440205+00:00
-- url     : https://prove2.me/submissions/14a060ea-bf24-4634-bfe3-9e4f027fdb4d

import Mathlib
import Definitions.Def_FuzzyGames_Values_Basic

open FuzzyGames.Values

namespace FuzzyDiagAux

lemma lin_coord {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℝ) (x : Fin n → ℝ) :
    L x = ∑ i, x i * L (Pi.single i 1) := by
  have := L.toLinearMap.pi_apply_eq_sum_univ x
  refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [smul_eq_mul]
  have hs : (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
    funext j; simp [Pi.single_apply, eq_comm]
  rw [hs]; rfl

lemma cont_integrand {n : ℕ} {v : (Fin n → ℝ) → ℝ} (hv : ContDiff ℝ 1 v) (y : Fin n → ℝ) :
    Continuous fun t : ℝ => fderiv ℝ v (t • (1 : Fin n → ℝ)) y :=
  ((hv.continuous_fderiv one_ne_zero).comp (continuous_id.smul continuous_const)).clm_apply
    continuous_const

lemma integrable_integrand {n : ℕ} {v : (Fin n → ℝ) → ℝ} (hv : ContDiff ℝ 1 v)
    (y : Fin n → ℝ) :
    IntervalIntegrable (fun t : ℝ => fderiv ℝ v (t • (1 : Fin n → ℝ)) y) MeasureTheory.volume
      0 1 :=
  (cont_integrand hv y).intervalIntegrable 0 1

/-- The diagonal formula commutes with linear changes of players fixing `τ^N`. -/
lemma diag_comp {n m : ℕ} (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (hA : A 1 = 1)
    {v : (Fin n → ℝ) → ℝ} (hv : ContDiff ℝ 1 v) {w : (Fin m → ℝ) → ℝ}
    (hw : ∀ σ, w σ = v (A σ)) (j : Fin m) :
    diagValue w j = ∑ i, A (Pi.single j 1) i * diagValue v i := by
  let Ac : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ) := LinearMap.toContinuousLinearMap A
  have hwc : w = v ∘ Ac := by funext σ; exact hw σ
  have hdv : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hfd : ∀ x, fderiv ℝ w x = (fderiv ℝ v (Ac x)).comp Ac := by
    intro x
    rw [hwc]
    exact fderiv_comp x (hdv _) Ac.differentiableAt |>.trans (by rw [Ac.fderiv])
  unfold diagValue
  have hint : ∀ t : ℝ, fderiv ℝ w (t • (1 : Fin m → ℝ)) (Pi.single j 1) =
      ∑ i, A (Pi.single j 1) i * fderiv ℝ v (t • (1 : Fin n → ℝ)) (Pi.single i 1) := by
    intro t
    rw [hfd, ContinuousLinearMap.comp_apply]
    have h1 : Ac (t • (1 : Fin m → ℝ)) = t • (1 : Fin n → ℝ) := by
      simp [Ac, map_smul, hA]
    rw [h1, lin_coord]
    rfl
  simp_rw [hint]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact intervalIntegral.integral_const_mul _ _
  · intro i _
    exact (integrable_integrand hv _).const_mul _

lemma diag_pareto {n : ℕ} {v : (Fin n → ℝ) → ℝ} (hv : ContDiff ℝ 1 v) (h0 : v 0 = 0) :
    ∑ i, diagValue v i = v 1 := by
  unfold diagValue
  rw [← intervalIntegral.integral_finsetSum (fun i _ => integrable_integrand hv _)]
  have hdv : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hsum : ∀ t : ℝ, ∑ i, fderiv ℝ v (t • (1 : Fin n → ℝ)) (Pi.single i 1) =
      fderiv ℝ v (t • (1 : Fin n → ℝ)) 1 := by
    intro t; rw [lin_coord (fderiv ℝ v (t • (1 : Fin n → ℝ))) 1]; simp
  simp_rw [hsum]
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => v (s • (1 : Fin n → ℝ))) (fderiv ℝ v (t • (1 : Fin n → ℝ)) 1) t := by
    intro t _
    have hid : HasDerivAt (fun s : ℝ => s • (1 : Fin n → ℝ)) (1 : Fin n → ℝ) t := by
      simpa using (hasDerivAt_id t).smul_const (1 : Fin n → ℝ)
    exact (hdv _).hasFDerivAt.comp_hasDerivAt t hid
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (integrable_integrand hv 1)]
  simp [h0]

lemma diag_bound {n : ℕ} {v : (Fin n → ℝ) → ℝ} (hv : ContDiff ℝ 1 v) :
    ‖diagValue v‖ ≤ c1seminorm v := by
  have hcont : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hcont.norm.continuousOn)
  have hbdd : BddAbove (Set.range fun τ : FuzzyGames.NTUCore.cube n => ‖fderiv ℝ v τ‖) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨τ, rfl⟩
    have := hB τ τ.2
    simpa using this
  set S := ⨆ τ : FuzzyGames.NTUCore.cube n, ‖fderiv ℝ v τ‖ with hS
  have hS0 : 0 ≤ S := Real.iSup_nonneg fun _ => norm_nonneg _
  have hS1 : 0 ≤ ⨆ τ : FuzzyGames.NTUCore.cube n, |v τ| := Real.iSup_nonneg fun _ => abs_nonneg _
  have hSc : S ≤ c1seminorm v := by unfold c1seminorm; linarith
  refine le_trans ?_ hSc
  refine (pi_norm_le_iff_of_nonneg hS0).2 fun i => ?_
  unfold diagValue
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := S) (f := fun t : ℝ => fderiv ℝ v (t • (1 : Fin n → ℝ)) (Pi.single i 1)) ?_
  · simpa using this
  · intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hmem : t • (1 : Fin n → ℝ) ∈ FuzzyGames.NTUCore.cube n := by
      constructor
      · intro j; simp [ht.1.le]
      · intro j; simp [ht.2]
    calc ‖fderiv ℝ v (t • (1 : Fin n → ℝ)) (Pi.single i 1)‖
        ≤ ‖fderiv ℝ v (t • (1 : Fin n → ℝ))‖ * ‖(Pi.single i (1 : ℝ) : Fin n → ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ v (t • (1 : Fin n → ℝ))‖ * 1 := by
          gcongr; simp [Pi.norm_single]
      _ ≤ S := by
          rw [mul_one]
          exact le_ciSup hbdd (⟨_, hmem⟩ : FuzzyGames.NTUCore.cube n)

lemma diag_add {n : ℕ} {v w : (Fin n → ℝ) → ℝ} (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w) :
    diagValue (v + w) = diagValue v + diagValue w := by
  funext i
  unfold diagValue
  have : ∀ t : ℝ, fderiv ℝ (v + w) (t • (1 : Fin n → ℝ)) (Pi.single i 1) =
      fderiv ℝ v (t • (1 : Fin n → ℝ)) (Pi.single i 1) +
        fderiv ℝ w (t • (1 : Fin n → ℝ)) (Pi.single i 1) := by
    intro t
    rw [fderiv_add ((hv.differentiable (by norm_num)) _) ((hw.differentiable (by norm_num)) _)]
    rfl
  simp_rw [this]
  rw [Pi.add_apply, intervalIntegral.integral_add (integrable_integrand hv _)
    (integrable_integrand hw _)]

lemma diag_smul {n : ℕ} (c : ℝ) {v : (Fin n → ℝ) → ℝ} :
    diagValue (c • v) = c • diagValue v := by
  funext i
  unfold diagValue
  have : ∀ t : ℝ, fderiv ℝ (c • v) (t • (1 : Fin n → ℝ)) (Pi.single i 1) =
      c * fderiv ℝ v (t • (1 : Fin n → ℝ)) (Pi.single i 1) := by
    intro t
    rw [fderiv_const_smul_field]
    rfl
  simp_rw [this]
  rw [Pi.smul_apply, intervalIntegral.integral_const_mul, smul_eq_mul]

end FuzzyDiagAux

open FuzzyDiagAux in
theorem solution :
    IsParetoOptimal (fun n (v : Vn n) => diagValue v.1) ∧
      IsSymmetric (fun n (v : Vn n) => diagValue v.1) ∧
      IsAtomic (fun n (v : Vn n) => diagValue v.1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n _ v
    exact diag_pareto v.2.1 v.2.2
  · intro n _ θ v w hw i
    have h := diag_comp (LinearMap.funLeft ℝ ℝ θ.symm) (by ext; simp) v.2.1 (w := w.1)
      (fun σ => by rw [hw σ]; rfl) i
    simp only at h ⊢
    rw [h, Finset.sum_eq_single (θ i)]
    · simp [LinearMap.funLeft_apply]
    · intro j _ hj
      have : θ.symm j ≠ i := by
        intro h'; apply hj; rw [← h']; simp
      simp [LinearMap.funLeft_apply, Pi.single_apply, this]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · intro n _ m P _ v w hw j
    have h := diag_comp (LinearMap.funLeft ℝ ℝ P) (by ext; simp) v.2.1 (w := w.1)
      (fun σ => by rw [hw σ]; rfl) j
    simp only at h ⊢
    rw [h, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : P i = j <;> simp [LinearMap.funLeft_apply, Pi.single_apply, hi]
