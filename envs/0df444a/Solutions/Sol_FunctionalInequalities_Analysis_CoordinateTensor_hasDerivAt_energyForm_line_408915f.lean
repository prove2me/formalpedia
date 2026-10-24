-- Prove2me | solution 1 for FunctionalInequalities.Analysis.CoordinateTensor.hasDerivAt_energyForm_line_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:56:53.058124+00:00
-- url     : https://prove2.me/submissions/3af3cc22-94cf-41b5-86e5-2122266b548f

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_EnergyForm
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
import Mathlib
import Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_slot_derivative_sum_408915f

noncomputable section
open Matrix
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.CoordinateTensor
end FunctionalInequalities.Analysis.CoordinateTensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.CoordinateTensor
variable {n r : ℕ}
private lemma FunctionalInequalities.Analysis.CoordinateTensor.delta_product (J K : Fin r → Fin n) :
    (∏ s, if J s = K s then (1 : ℝ) else 0) =
      if J = K then 1 else 0 := by
  classical
  by_cases h : J = K
  · subst K
    simp
  · rw [if_neg h]
    have hex : ∃ s, J s ≠ K s := by
      by_contra hnone
      apply h
      funext s
      by_contra hs
      exact hnone ⟨s, hs⟩
    obtain ⟨s, hs⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ s) (if_neg hs)
end
end
end
section S3Bf2EnergyFormFirstOrder
open Matrix
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.CoordinateTensor
end FunctionalInequalities.Analysis.CoordinateTensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.CoordinateTensor
variable {n r : ℕ}
private lemma FunctionalInequalities.Analysis.CoordinateTensor.inverse_line {R : Type*} [NormedRing R]
    [NormedAlgebra ℝ R] [HasSummableGeomSeries R] (H : R) :
    HasDerivAt (fun t : ℝ => Ring.inverse (1 + t • H)) (-H) 0 := by
  have hl : HasDerivAt (fun t : ℝ => (1 : R) + t • H) H 0 := by
    simpa only [id_eq, one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const H).const_add (1 : R))
  have hi :
      HasFDerivAt Ring.inverse
        (-((ContinuousLinearMap.mulLeftRight ℝ R) (1 : R)) (1 : R))
        ((1 : R) + (0 : ℝ) • H) := by
    simpa only [zero_smul, add_zero, inv_one, Units.val_one] using
      (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : Rˣ))
  have hc := hi.comp_hasDerivAt 0 hl
  have heq :
      (-((ContinuousLinearMap.mulLeftRight ℝ R) (1 : R)) (1 : R)) H = -H := by
    change -((1 : R) * H * 1) = -H
    rw [one_mul, mul_one]
  simpa only [Function.comp_def] using hc.congr_deriv heq
/-- The entries of `(1 + εH)⁻¹` have derivative `−⟪e_i, H e_k⟫` at `ε = 0`. -/
theorem FunctionalInequalities.Analysis.CoordinateTensor.hasDerivAt_inner_ringInverse_one_add (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (i k : Fin n) :
    HasDerivAt (fun ε : ℝ => ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
        Ring.inverse (1 + ε • H) (EuclideanSpace.basisFun (Fin n) ℝ k)⟫)
      (-⟪EuclideanSpace.basisFun (Fin n) ℝ i, H (EuclideanSpace.basisFun (Fin n) ℝ k)⟫) 0 := by
  have hi :
      HasDerivAt (fun t : ℝ => Ring.inverse (1 + t • H)) (-H) 0 := by
    convert inverse_line H using 1
  have hv := hi.clm_apply
    (hasDerivAt_const (0 : ℝ) (EuclideanSpace.basisFun (Fin n) ℝ k))
  have h := (hasDerivAt_const (0 : ℝ)
    (EuclideanSpace.basisFun (Fin n) ℝ i)).inner ℝ hv
  simpa using h
private lemma FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_mul {f g : ℝ → ℝ} {df dg x : ℝ}
    (hf : HasDerivAt f df x) (hg : HasDerivAt g dg x) :
    HasDerivAt (fun t => f t * g t) (df * g x + f x * dg) x := by
  convert hf.mul hg using 1 <;> rfl
private lemma FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℝ) (df : ι → ℝ) (x : ℝ)
    (hf : ∀ i ∈ s, HasDerivAt (f i) (df i) x) :
    HasDerivAt (fun t => ∑ i ∈ s, f i t) (∑ i ∈ s, df i) x := by
  have h := HasDerivAt.sum hf
  have he : (∑ i ∈ s, f i) = (fun t => ∑ i ∈ s, f i t) := by
    funext t
    simp
  rw [he] at h
  convert h using 1
private lemma FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ → ℝ) (df : ι → ℝ) (x : ℝ)
    (hf : ∀ i ∈ s, HasDerivAt (f i) (df i) x) :
    HasDerivAt (fun t => ∏ i ∈ s, f i t)
      (∑ i ∈ s, (∏ j ∈ s.erase i, f j x) * df i) x := by
  have h := HasDerivAt.finsetProd hf
  have he : (∏ i ∈ s, f i) = (fun t => ∏ i ∈ s, f i t) := by
    funext t
    simp
  rw [he] at h
  simp only [smul_eq_mul] at h
  convert h using 1
namespace FunctionalInequalities.Analysis.CoordinateTensor
end FunctionalInequalities.Analysis.CoordinateTensor
open FunctionalInequalities.Analysis.CoordinateTensor in
set_option maxHeartbeats 800000 in
/-- **BKL (88), first order, along the line**: `d/dε F(1 + εH, T + εX)|₀ = 2⟨T, X⟩ − ⟨T, Σ_H T⟩`. -/
theorem solution (T : (Fin r → Fin n) → ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (X : (Fin r → Fin n) → ℝ) :
    HasDerivAt (fun ε : ℝ => FunctionalInequalities.Analysis.CoordinateTensor.energyForm (1 + ε • H) (T + ε • X))
      (2 * FunctionalInequalities.Analysis.CoordinateTensor.inner T X - FunctionalInequalities.Analysis.CoordinateTensor.inner T (FunctionalInequalities.Analysis.CoordinateTensor.actSum (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) T)) 0 := by
  classical
  let a (i k : Fin n) (t : ℝ) : ℝ :=
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
      Ring.inverse (1 + t • H) (EuclideanSpace.basisFun (Fin n) ℝ k)⟫
  let P (J K : Fin r → Fin n) : ℝ :=
    ∏ s, if J s = K s then (1 : ℝ) else 0
  let Q (J K : Fin r → Fin n) : ℝ :=
    ∑ s, (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
      (-FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H (J s) (K s))
  have a0 (i k : Fin n) : a i k 0 = if i = k then 1 else 0 := by
    have hz :
        (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) +
          (0 : ℝ) • H = 1 := by
      apply ContinuousLinearMap.ext
      intro v
      change v + (0 : ℝ) • H v = v
      simp
    unfold a
    rw [hz, Ring.inverse_one]
    exact (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite i k
  have ha (i k : Fin n) :
      HasDerivAt (a i k) (-FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H i k) 0 :=
    FunctionalInequalities.Analysis.CoordinateTensor.hasDerivAt_inner_ringInverse_one_add H i k
  have hp (J K : Fin r → Fin n) :
      HasDerivAt (fun t => ∏ s, a (J s) (K s) t) (Q J K) 0 := by
    have h := real_deriv_prod Finset.univ
      (fun s t => a (J s) (K s) t)
      (fun s => -FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H (J s) (K s)) 0
      (fun s _ => ha (J s) (K s))
    apply h.congr_deriv
    simp only [a0, Q]
  have hp0 (J K : Fin r → Fin n) :
      (∏ s, a (J s) (K s) 0) = P J K := by
    simp only [a0, P]
  have ht (J : Fin r → Fin n) :
      HasDerivAt (fun t : ℝ => T J + t * X J) (X J) 0 := by
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id (0 : ℝ)).mul_const (X J)).const_add (T J))
  let d (J K : Fin r → Fin n) : ℝ :=
    (X J * T K + T J * X K) * P J K + T J * T K * Q J K
  have hterm (J K : Fin r → Fin n) :
      HasDerivAt
        (fun t : ℝ => (T J + t * X J) * (T K + t * X K) *
          (∏ s, a (J s) (K s) t))
        (d J K) 0 := by
    have h := real_deriv_mul (real_deriv_mul (ht J) (ht K)) (hp J K)
    apply h.congr_deriv
    simp only [zero_mul, add_zero, hp0, d]
  have hraw :
      HasDerivAt
        (fun t : ℝ => ∑ J, ∑ K,
          (T J + t * X J) * (T K + t * X K) *
            (∏ s, a (J s) (K s) t))
        (∑ J, ∑ K, d J K) 0 := by
    apply real_deriv_sum
    intro J _
    apply real_deriv_sum
    intro K _
    exact hterm J K
  have hfirst :
      (∑ J, ∑ K, (X J * T K + T J * X K) * P J K) =
        2 * FunctionalInequalities.Analysis.CoordinateTensor.inner T X := by
    calc
      (∑ J, ∑ K, (X J * T K + T J * X K) * P J K) =
          ∑ J, (X J * T J + T J * X J) := by
        apply Finset.sum_congr rfl
        intro J _
        simp [P, delta_product, mul_ite]
      _ = ∑ J, 2 * (T J * X J) := by
        apply Finset.sum_congr rfl
        intro J _
        ring
      _ = 2 * FunctionalInequalities.Analysis.CoordinateTensor.inner T X := by
        rw [← Finset.mul_sum]
        rfl
  have hsecond :
      (∑ J, ∑ K, T J * T K * Q J K) =
        -FunctionalInequalities.Analysis.CoordinateTensor.inner T (FunctionalInequalities.Analysis.CoordinateTensor.actSum (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) T) :=
    FunctionalInequalities.Analysis.CoordinateTensor.slot_derivative_sum_408915f T (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H)
  have hd :
      (∑ J, ∑ K, d J K) =
        2 * FunctionalInequalities.Analysis.CoordinateTensor.inner T X - FunctionalInequalities.Analysis.CoordinateTensor.inner T (FunctionalInequalities.Analysis.CoordinateTensor.actSum (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) T) := by
    simp only [d, Finset.sum_add_distrib]
    rw [hfirst, hsecond]
    rfl
  have h := hraw.congr_deriv hd
  convert h using 1 <;> rfl
