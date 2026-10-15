-- Prove2me | solution 1 for CauchyRiemannIndex.exists_periodic_solution_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-14T21:09:49.469391+00:00
-- url     : https://prove2.me/submissions/cfe66905-3f3d-433b-88b7-97fb07a0a454

import Definitions.Def_CauchyRiemannIndex_Setting
import Theorems.Thm_AsymptoticOperator_linearODE_existsUnique
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory Matrix Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace CauchyRiemannIndex

/-- Matrices acting on `ℝ²ⁿ` as continuous linear maps. -/
noncomputable abbrev crE {n : ℕ} (A : Mat n) : Vec n →L[ℝ] Vec n :=
  Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ) A

lemma crPerB_clm_cont {n : ℕ} : Continuous (fun A : Mat n => crE A) :=
  LinearMap.continuous_of_finiteDimensional
    (Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearMap

lemma crE_mul {n : ℕ} (A B : Mat n) (v : Vec n) : crE (A * B) v = crE A (crE B v) := by
  simp [crE, map_mul]

lemma crE_one {n : ℕ} (v : Vec n) : crE (1 : Mat n) v = v := by
  simp [crE, map_one]

lemma crE_JJ {n : ℕ} (v : Vec n) : crE (J₀ n) (crE (J₀ n) v) = -v := by
  rw [← crE_mul, show J₀ n * J₀ n = -1 from Matrix.J_squared _ _]
  simp [crE, map_neg, map_one]

lemma crPerB_exists_fund {n : ℕ} (S : ℝ → Mat n) (hS : Continuous S) :
    ∃ Ψ : ℝ → Mat n, IsFundamentalSolution S Ψ ∧ Continuous Ψ := by
  letI : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Mat n) := Matrix.normedSpace
  let A : ℝ → Mat n := fun t => J₀ n * S t
  have hA : Continuous A := continuous_const.mul hS
  let B : ℝ → Mat n →L[ℝ] Mat n :=
    fun t => LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (A t))
  have hB : Continuous B := by
    refine continuous_clm_apply.2 fun y => ?_
    exact hA.mul continuous_const
  obtain ⟨Ψ, ⟨hΨ0, hΨ⟩, -⟩ := AsymptoticOperator.linearODE_existsUnique B hB 1
  exact ⟨Ψ, ⟨hΨ0, hΨ⟩, continuous_iff_continuousAt.2 fun t => (hΨ t).continuousAt⟩

/-- Existence of the fundamental solution together with its symplectic inverse. -/
lemma crPerB_fund {n : ℕ} (S : ℝ → Mat n) (hS : IsSymLoop S) :
    ∃ Ψ : ℝ → Mat n, IsFundamentalSolution S Ψ ∧ Continuous Ψ ∧
      ∀ t, -(J₀ n * (Ψ t)ᵀ * J₀ n) * Ψ t = 1 := by
  obtain ⟨Ψ, ⟨hΨ0, hd⟩, hΨc⟩ := crPerB_exists_fund S hS.1
  refine ⟨Ψ, ⟨hΨ0, hd⟩, hΨc, fun t => ?_⟩
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  let T : Mat n →L[ℝ] Mat n :=
    LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv (Fin n ⊕ Fin n)
      (Fin n ⊕ Fin n) ℝ ℝ).toLinearMap
  have hT : ∀ s : ℝ, HasDerivAt (fun s => (Ψ s)ᵀ) ((J₀ n * S s * Ψ s)ᵀ) s :=
    fun s => T.hasFDerivAt.comp_hasDerivAt s (hd s)
  have hJ : ∀ X : Mat n, J₀ n * (J₀ n * X) = -X := by
    intro X
    rw [← mul_assoc, show J₀ n * J₀ n = -1 from Matrix.J_squared _ _, neg_one_mul]
  have hf : ∀ s : ℝ, HasDerivAt (fun s => (Ψ s)ᵀ * J₀ n * Ψ s) 0 s := by
    intro s
    have h := ((hT s).mul_const (J₀ n)).mul (hd s)
    have hsym : (S s)ᵀ = S s := hS.2.2 s
    have key : (J₀ n * S s * Ψ s)ᵀ * J₀ n * Ψ s +
        (Ψ s)ᵀ * J₀ n * (J₀ n * S s * Ψ s) = 0 := by
      rw [transpose_mul, transpose_mul, hsym, show (J₀ n)ᵀ = -J₀ n from Matrix.J_transpose _ _]
      simp only [mul_assoc, neg_mul, mul_neg, hJ]
      simp
    rw [key] at h
    exact h
  have hc : (Ψ t)ᵀ * J₀ n * Ψ t = J₀ n := by
    have := is_const_of_deriv_eq_zero (f := fun s => (Ψ s)ᵀ * J₀ n * Ψ s)
      (fun x => (hf x).differentiableAt) (fun x => (hf x).deriv) t 0
    rw [this]
    simp [hΨ0]
  calc -(J₀ n * (Ψ t)ᵀ * J₀ n) * Ψ t = -(J₀ n * ((Ψ t)ᵀ * J₀ n * Ψ t)) := by
        simp only [mul_assoc, neg_mul]
    _ = 1 := by rw [hc, show J₀ n * J₀ n = -1 from Matrix.J_squared _ _, neg_neg]

/-- Product rule for a matrix path applied to a vector path. -/
lemma crPerB_hasDerivAt_apply {n : ℕ} {Ψ : ℝ → Mat n} {Ψ' : Mat n} {v : ℝ → Vec n} {v' : Vec n}
    {t : ℝ} (hΨ : HasDerivAt Ψ Ψ' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => crE (Ψ s) (v s)) (crE Ψ' (v t) + crE (Ψ t) v') t := by
  letI : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Mat n) := Matrix.normedSpace
  let L : Mat n →L[ℝ] (Vec n →L[ℝ] Vec n) := LinearMap.toContinuousLinearMap
    (Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearMap
  have hL : HasDerivAt (fun s => L (Ψ s)) (L Ψ') t := L.hasFDerivAt.comp_hasDerivAt t hΨ
  exact hL.clm_apply hv

/-- Uniqueness for `d' = J₀ S d`, `d 0 = 0`. -/
lemma crPerB_unique {n : ℕ} (S : ℝ → Mat n) (hS : Continuous S) (d : ℝ → Vec n)
    (hd : ∀ t, HasDerivAt d (crE (J₀ n * S t) (d t)) t) (h0 : d 0 = 0) : d = 0 := by
  let B : ℝ → Vec n →L[ℝ] Vec n := fun t => crE (J₀ n * S t)
  have hB : Continuous B := crPerB_clm_cont.comp (continuous_const.mul hS)
  obtain ⟨z, -, hz⟩ := AsymptoticOperator.linearODE_existsUnique B hB 0
  have e1 := hz d ⟨h0, hd⟩
  have e2 := hz 0 ⟨rfl, fun t => by simpa [B] using hasDerivAt_const t (0 : Vec n)⟩
  rw [e1, e2]

theorem solution_aux (n : ℕ) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf)
    (hnd : IsNondegenerate Sinf) :
    ∃ C : ℝ, ∀ g : ℝ → Vec n, Continuous g → Function.Periodic g 1 →
      ∃ ψ : ℝ → Vec n, ContDiff ℝ 1 ψ ∧ Function.Periodic ψ 1 ∧
        (∀ t, Matrix.toEuclideanLin (J₀ n) (deriv ψ t) +
          Matrix.toEuclideanLin (Sinf t) (ψ t) = g t) ∧
        ∀ t, ‖ψ t‖ ≤ C * ∫ τ in Set.Ico (0 : ℝ) 1, ‖g τ‖ := by
  obtain ⟨Ψ, hΨ, hΨc, hinv⟩ := crPerB_fund Sinf hS
  let Φ : ℝ → Mat n := fun t => -(J₀ n * (Ψ t)ᵀ * J₀ n)
  have hΦc : Continuous Φ :=
    ((continuous_const.mul hΨc.matrix_transpose).mul continuous_const).neg
  have hright : ∀ t, Ψ t * Φ t = 1 := fun t => mul_eq_one_comm.1 (hinv t)
  have hEc : Continuous (fun A : Mat n => crE A) := crPerB_clm_cont
  obtain ⟨MΨ, hMΨ⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    (hEc.comp hΨc).continuousOn
  obtain ⟨MΦ, hMΦ⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    (hEc.comp hΦc).continuousOn
  set MJ := ‖crE (J₀ n)‖ with hMJ
  set P1 := Ψ 1 with hP1
  set R : Mat n := (1 - P1)⁻¹ * P1 with hR
  set K := ‖crE R‖ with hK
  have hdet : (1 - P1).det ≠ 0 := hnd Ψ hΨ
  have hRinv : (1 - P1) * (1 - P1)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)
  set MΨ' := max MΨ 0
  set Mw := max MΦ 0 * MJ
  refine ⟨MΨ' * (K + 1) * Mw, fun g hg hgp => ?_⟩
  let w : ℝ → Vec n := fun τ => crE (Φ τ) (-(crE (J₀ n) (g τ)))
  have hwc : Continuous w :=
    (hEc.comp hΦc).clm_apply ((crE (J₀ n)).continuous.comp hg).neg
  set I : Vec n := ∫ τ in (0 : ℝ)..1, w τ with hI
  set c : Vec n := crE R I with hc
  let ψ₀ : ℝ → Vec n := fun t => c + ∫ τ in (0 : ℝ)..t, w τ
  let ψ : ℝ → Vec n := fun t => crE (Ψ t) (ψ₀ t)
  have hψ₀d : ∀ t, HasDerivAt ψ₀ (w t) t := fun t =>
    (intervalIntegral.integral_hasDerivAt_right (hwc.intervalIntegrable _ _)
      (hwc.stronglyMeasurableAtFilter _ _) hwc.continuousAt).const_add c
  have hψd : ∀ t, HasDerivAt ψ (crE (J₀ n * Sinf t) (ψ t) - crE (J₀ n) (g t)) t := by
    intro t
    have h := crPerB_hasDerivAt_apply (hΨ.2 t) (hψ₀d t)
    convert h using 1
    simp only [ψ, w]
    rw [← crE_mul (Ψ t) (Φ t), hright, crE_one, crE_mul (J₀ n * Sinf t) (Ψ t)]
    abel
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun t => (hψd t).continuousAt
  have hderiv : deriv ψ = fun t => crE (J₀ n * Sinf t) (ψ t) - crE (J₀ n) (g t) :=
    funext fun t => (hψd t).deriv
  -- periodicity
  have hψ0 : ψ 0 = c := by simp [ψ, ψ₀, hΨ.1, crE_one]
  have hψ1 : ψ 1 = c := by
    show crE P1 (c + I) = c
    have h1 : c - crE P1 c = crE P1 I := by
      have : crE (1 - P1) c = crE P1 I := by
        rw [hc, hR, ← crE_mul, ← mul_assoc, hRinv, one_mul]
      have e : crE (1 - P1) c = c - crE P1 c := by simp [crE, map_sub]
      rw [← e, this]
    rw [map_add]
    rw [← h1]; abel
  have hper : Function.Periodic ψ 1 := by
    have hd0 := crPerB_unique Sinf hS.1 (fun t => ψ (t + 1) - ψ t) (fun t => by
      have h1 := (hψd (t + 1)).comp_add_const t 1
      have h2 := (h1.sub (hψd t))
      have e : (crE (J₀ n * Sinf (t + 1)) (ψ (t + 1)) - crE (J₀ n) (g (t + 1))) -
          (crE (J₀ n * Sinf t) (ψ t) - crE (J₀ n) (g t)) =
          crE (J₀ n * Sinf t) (ψ (t + 1) - ψ t) := by
        rw [hS.2.1 t, hgp t, ContinuousLinearMap.map_sub]; abel
      exact e ▸ h2) (by simp [hψ0, hψ1])
    intro t
    have := congrFun hd0 t
    simpa [sub_eq_zero] using this
  have hcd : ContDiff ℝ 1 ψ := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun t => (hψd t).differentiableAt, ?_⟩
    rw [hderiv]
    exact ((hEc.comp (continuous_const.mul hS.1)).clm_apply hψc).sub
      ((crE (J₀ n)).continuous.comp hg)
  refine ⟨ψ, hcd, hper, fun t => ?_, ?_⟩
  · show crE (J₀ n) (deriv ψ t) + crE (Sinf t) (ψ t) = g t
    rw [hderiv, map_sub, crE_mul, crE_JJ, crE_JJ]
    abel
  -- the bound
  have hMΦ0 : 0 ≤ max MΦ 0 := le_max_right _ _
  have hMw0 : 0 ≤ Mw := mul_nonneg hMΦ0 (norm_nonneg _)
  have hwb : ∀ τ ∈ Icc (0 : ℝ) 1, ‖w τ‖ ≤ Mw * ‖g τ‖ := by
    intro τ hτ
    calc ‖w τ‖ ≤ ‖crE (Φ τ)‖ * ‖-(crE (J₀ n) (g τ))‖ := (crE (Φ τ)).le_opNorm _
      _ ≤ max MΦ 0 * (MJ * ‖g τ‖) := by
          rw [norm_neg]
          exact mul_le_mul ((hMΦ τ hτ).trans (le_max_left _ _)) ((crE (J₀ n)).le_opNorm _)
            (norm_nonneg _) hMΦ0
      _ = Mw * ‖g τ‖ := by ring
  set W := ∫ τ in (0 : ℝ)..1, ‖w τ‖ with hW
  have hWb : W ≤ Mw * ∫ τ in Set.Ico (0 : ℝ) 1, ‖g τ‖ := by
    rw [hW, intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul,
      integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo]
    refine setIntegral_mono_on (hwc.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      ((hg.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self).const_mul _) measurableSet_Ioc
      fun τ hτ => hwb τ (Ioc_subset_Icc_self hτ)
  have hW0 : 0 ≤ W := intervalIntegral.integral_nonneg zero_le_one fun _ _ => norm_nonneg _
  have hcb : ‖c‖ ≤ K * W := by
    calc ‖c‖ ≤ K * ‖I‖ := (crE R).le_opNorm _
      _ ≤ K * W := mul_le_mul_of_nonneg_left
          (intervalIntegral.norm_integral_le_integral_norm zero_le_one) (norm_nonneg _)
  intro t
  obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico₀ one_pos t
  rw [hty]
  have hpart : ‖∫ τ in (0 : ℝ)..y, w τ‖ ≤ W := by
    refine (intervalIntegral.norm_integral_le_integral_norm hy.1).trans ?_
    exact intervalIntegral.integral_mono_interval le_rfl hy.1 hy.2.le
      (Eventually.of_forall fun _ => norm_nonneg _) (hwc.norm.intervalIntegrable _ _)
  have hMΨy : ‖crE (Ψ y)‖ ≤ MΨ' := (hMΨ y (Ico_subset_Icc_self hy)).trans (le_max_left _ _)
  have hMΨ'0 : 0 ≤ MΨ' := le_max_right _ _
  calc ‖ψ y‖ ≤ ‖crE (Ψ y)‖ * ‖ψ₀ y‖ := (crE (Ψ y)).le_opNorm _
    _ ≤ MΨ' * (K * W + W) := by
        refine mul_le_mul hMΨy ((norm_add_le _ _).trans (add_le_add hcb hpart))
          (norm_nonneg _) hMΨ'0
    _ = MΨ' * (K + 1) * W := by ring
    _ ≤ MΨ' * (K + 1) * (Mw * ∫ τ in Set.Ico (0 : ℝ) 1, ‖g τ‖) :=
        mul_le_mul_of_nonneg_left hWb (mul_nonneg hMΨ'0 (by positivity))
    _ = MΨ' * (K + 1) * Mw * ∫ τ in Set.Ico (0 : ℝ) 1, ‖g τ‖ := by ring

end CauchyRiemannIndex

open CauchyRiemannIndex in
theorem solution (n : ℕ) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf)
    (hnd : IsNondegenerate Sinf) :
    ∃ C : ℝ, ∀ g : ℝ → Vec n, Continuous g → Function.Periodic g 1 →
      ∃ ψ : ℝ → Vec n, ContDiff ℝ 1 ψ ∧ Function.Periodic ψ 1 ∧
        (∀ t, Matrix.toEuclideanLin (J₀ n) (deriv ψ t) +
          Matrix.toEuclideanLin (Sinf t) (ψ t) = g t) ∧
        ∀ t, ‖ψ t‖ ≤ C * ∫ τ in Set.Ico (0 : ℝ) 1, ‖g τ‖ :=
  solution_aux n Sinf hS hnd
