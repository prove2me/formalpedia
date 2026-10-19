-- Prove2me | solution 1 for Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.tendsto_of_dense_eventually_equiLipschitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/8265566d-5615-42cf-89fe-cb3c1f6c3fcd

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics BergmanMonomials LatticeAsymptotics LaurentJetSeparatedness
open GlobalBergmanKernelBound MomentMinimizer MomentOptimizer MomentTargetGeodesic
open MomentFirstVariation MomentRegularity BergmanJetBasis MomentWeakGlobalKernel
open BergmanJetPointwiseLogKernel
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
theorem _root_.solution
    {X : Type*} [PseudoMetricSpace X]
    (f : ℕ → X → ℝ) (g : X → ℝ)
    (C : ℝ≥0)
    (hf : ∀ᶠ k : ℕ in atTop, LipschitzWith C (f k))
    (hg : LipschitzWith C g)
    {S : Set X} (hS : Dense S)
    (hconv : ∀ y ∈ S,
      Tendsto (fun k : ℕ => f k y) atTop (𝓝 (g y)))
    (x : X) :
    Tendsto (fun k : ℕ => f k x) atTop (𝓝 (g x)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ : ℝ := ε / (4 * ((C : ℝ) + 1))
  have hC : 0 ≤ (C : ℝ) := C.coe_nonneg
  have hC1 : 0 < (C : ℝ) + 1 := by linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨y, hy, hxy⟩ := hS.exists_dist_lt x hδ
  have hsmall : (C : ℝ) * dist x y < ε / 4 := by
    calc
      (C : ℝ) * dist x y ≤
          ((C : ℝ) + 1) * dist x y := by
        exact mul_le_mul_of_nonneg_right (by linarith)
          (dist_nonneg : 0 ≤ dist x y)
      _ < ((C : ℝ) + 1) * δ :=
        mul_lt_mul_of_pos_left hxy hC1
      _ = ε / 4 := by
        dsimp [δ]
        field_simp [hC1.ne']
  have hmiddle :
      ∀ᶠ k : ℕ in atTop, dist (f k y) (g y) < ε / 2 := by
    have h := (hconv y hy)
      (Metric.ball_mem_nhds (g y) (half_pos hε))
    change
      ∀ᶠ k : ℕ in atTop, f k y ∈ Metric.ball (g y) (ε / 2)
      at h
    filter_upwards [h] with k hk
    exact Metric.mem_ball.mp hk
  have hnear :
      ∀ᶠ k : ℕ in atTop, dist (f k x) (g x) < ε := by
    filter_upwards [hf, hmiddle] with k hfk hmid
    have hfirst := hfk.dist_le_mul x y
    have hlast : dist (g y) (g x) ≤
        (C : ℝ) * dist x y := by
      calc
        dist (g y) (g x) = dist (g x) (g y) := dist_comm _ _
        _ ≤ (C : ℝ) * dist x y := hg.dist_le_mul x y
    calc
      dist (f k x) (g x) ≤
          dist (f k x) (f k y) + dist (f k y) (g x) :=
        dist_triangle _ _ _
      _ ≤ dist (f k x) (f k y) +
          (dist (f k y) (g y) + dist (g y) (g x)) :=
        by
          simpa [add_comm] using
            (add_le_add_left
              (dist_triangle (f k y) (g y) (g x))
              (dist (f k x) (f k y)))
      _ < ε := by linarith
  exact Filter.eventually_atTop.mp hnear
end Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
