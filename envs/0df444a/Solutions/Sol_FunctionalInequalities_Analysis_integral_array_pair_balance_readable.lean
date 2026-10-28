-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_array_pair_balance_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:39:35.861293+00:00
-- url     : https://prove2.me/submissions/111ed766-e63e-45c4-884b-392982edbf38

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution

noncomputable section
section ArrayPairBalance
open MeasureTheory
set_option maxHeartbeats 1200000 in
/-- Finite integral balance of paired integrable arrays; one-use support of the flux identity. -/
 theorem solution {n : ℕ}
    (A B C D : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hA : ∀ a b, Integrable (A a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hB : ∀ a b, Integrable (B a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hC : ∀ a b, Integrable (C a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hD : ∀ a b, Integrable (D a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hF : Integrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hPair : ∀ a b,
      (∫ x, A a b x + B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, C a b x + D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hTrace : (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :
    (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
    -(∫ x, F x - (∑ a : Fin n, ∑ b : Fin n, C a b x) +
      ∑ a : Fin n, ∑ b : Fin n, A a b x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  have hA_inner :
      ∀ a : Fin n,
        Integrable (fun x => ∑ b : Fin n, A a b x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro a
    apply integrable_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      Finset.univ
    intro b _
    exact hA a b
  have hB_inner :
      ∀ a : Fin n,
        Integrable (fun x => ∑ b : Fin n, B a b x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro a
    apply integrable_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      Finset.univ
    intro b _
    exact hB a b
  have hC_inner :
      ∀ a : Fin n,
        Integrable (fun x => ∑ b : Fin n, C a b x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro a
    apply integrable_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      Finset.univ
    intro b _
    exact hC a b
  have hD_inner :
      ∀ a : Fin n,
        Integrable (fun x => ∑ b : Fin n, D a b x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro a
    apply integrable_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      Finset.univ
    intro b _
    exact hD a b
  have hA_total :
      Integrable (fun x => ∑ a : Fin n, ∑ b : Fin n, A a b x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integrable_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      Finset.univ
    intro a _
    exact hA_inner a
  have hC_total :
      Integrable (fun x => ∑ a : Fin n, ∑ b : Fin n, C a b x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integrable_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      Finset.univ
    intro a _
    exact hC_inner a
  have hIA :
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, A a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    calc
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∑ a : Fin n, ∫ x, ∑ b : Fin n, A a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun a _ => hA_inner a)
      _ = ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, A a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply Finset.sum_congr rfl
        intro a _
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun b _ => hA a b)
  have hIB :
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    calc
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∑ a : Fin n, ∫ x, ∑ b : Fin n, B a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun a _ => hB_inner a)
      _ = ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply Finset.sum_congr rfl
        intro a _
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun b _ => hB a b)
  have hIC :
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, C a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    calc
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∑ a : Fin n, ∫ x, ∑ b : Fin n, C a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun a _ => hC_inner a)
      _ = ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, C a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply Finset.sum_congr rfl
        intro a _
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun b _ => hC a b)
  have hID :
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    calc
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∑ a : Fin n, ∫ x, ∑ b : Fin n, D a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun a _ => hD_inner a)
      _ = ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply Finset.sum_congr rfl
        intro a _
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun b _ => hD a b)
  have hPairSum :
      (∑ a : Fin n, ∑ b : Fin n,
        ((∫ x, A a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))) =
      (∑ a : Fin n, ∑ b : Fin n,
        ((∫ x, C a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    have h := hPair a b
    rw [integral_add (hA a b) (hB a b),
      integral_add (hC a b) (hD a b)] at h
    exact h
  have hSums :
      (∑ a : Fin n, ∑ b : Fin n,
        (∫ x, A a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) +
        (∑ a : Fin n, ∑ b : Fin n,
          (∫ x, B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) =
      (∑ a : Fin n, ∑ b : Fin n,
        (∫ x, C a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) +
        (∑ a : Fin n, ∑ b : Fin n,
          (∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) := by
    simpa only [Finset.sum_add_distrib] using hPairSum
  have hBalance :
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
        (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
        (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    calc
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          (∑ a : Fin n, ∑ b : Fin n,
            ∫ x, A a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∑ a : Fin n, ∑ b : Fin n,
            ∫ x, B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        rw [hIA, hIB]
      _ =
          (∑ a : Fin n, ∑ b : Fin n,
            ∫ x, C a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∑ a : Fin n, ∑ b : Fin n,
            ∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := hSums
      _ =
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        rw [← hIC, ← hID]
  have hDTrace :
      (∑ a : Fin n, ∑ b : Fin n,
          ∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    calc
      (∑ a : Fin n, ∑ b : Fin n,
          ∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hID.symm
      _ = -(∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := hTrace
  have hExpand :
      (∫ x, F x - (∑ a : Fin n, ∑ b : Fin n, C a b x) +
          ∑ a : Fin n, ∑ b : Fin n, A a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        (∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) -
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    calc
      (∫ x, F x - (∑ a : Fin n, ∑ b : Fin n, C a b x) +
          ∑ a : Fin n, ∑ b : Fin n, A a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          (∫ x, F x - (∑ a : Fin n, ∑ b : Fin n, C a b x)
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
            (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        exact integral_add (hF.sub hC_total) hA_total
      _ =
          (∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) -
            (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
            (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        rw [integral_sub hF hC_total]
  rw [hExpand]
  linarith [hBalance, hDTrace]
