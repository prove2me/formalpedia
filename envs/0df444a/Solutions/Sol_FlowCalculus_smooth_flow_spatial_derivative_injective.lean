-- Prove2me | solution 1 for FlowCalculus.smooth_flow_spatial_derivative_injective
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T22:00:58.491591+00:00
-- url     : https://prove2.me/submissions/3b82243e-2c9d-4fde-919c-4ed6903e2cbe

import Theorems.Thm_FlowCalculus_spatial_differential_hasDerivAt
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith

open Set Function
open scoped ContDiff Topology NNReal
set_option autoImplicit false

theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (X ψ : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y)
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t) :
    ∀ t y, Injective (fderiv ℝ (ψ t) y) := by
  intro t y
  have hDX : ContDiff ℝ ∞ (fun p : ℝ × V => fderiv ℝ (X p.1) p.2) := by
    have hh : ContDiff ℝ ∞ (fun p : (ℝ × V) × V => X p.1.1 p.2) :=
      hX.comp (contDiff_fst.fst.prodMk contDiff_snd)
    exact hh.fderiv contDiff_snd (by simp)
  let A : ℝ → V →L[ℝ] V := fun s => fderiv ℝ (X s) (ψ s y)
  have hAc : Continuous A := hDX.continuous.comp
    (continuous_id.prodMk (hψ.continuous.comp (continuous_id.prodMk continuous_const)))
  let R := |t| + 1
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image (hAc.norm.continuousOn :
    ContinuousOn (fun s => ‖A s‖) (Icc (-R) R))
  let K : ℝ≥0 := ⟨max 0 B, le_max_left _ _⟩
  have hLip : ∀ s ∈ Ioo (-R) R, LipschitzOnWith K (A s) univ := by
    intro s hs
    have hnorm : ‖A s‖ ≤ (K : ℝ) :=
      (hB (mem_image_of_mem _ (Ioo_subset_Icc_self hs))).trans (le_max_right _ _)
    exact ((A s).lipschitz.weaken (by exact_mod_cast hnorm)).lipschitzOnWith
  have ht : t ∈ Ioo (-R) R := by
    constructor <;> dsimp [R] <;> linarith [le_abs_self t, neg_abs_le t]
  have hz : (0 : ℝ) ∈ Ioo (-R) R := by constructor <;> dsimp [R] <;> linarith [abs_nonneg t]
  have hkernel : ∀ v, fderiv ℝ (ψ t) y v = 0 → v = 0 := by
    intro v hv
    let β : ℝ → V := fun s => fderiv ℝ (ψ s) y v
    have hβ : ∀ s, HasDerivAt β (A s (β s)) s := fun s =>
      FlowCalculus.spatial_differential_hasDerivAt X hX ψ hψ hd s y v
    have heq : EqOn β (fun _ => (0 : V)) (Ioo (-R) R) :=
      ODE_solution_unique_of_mem_Ioo hLip ht
        (fun s _ => ⟨hβ s, mem_univ _⟩)
        (fun s _ => ⟨by simpa using hasDerivAt_const s (0 : V), mem_univ _⟩) hv
    have hinit : ψ 0 = id := funext h0
    have hβ0 := heq hz
    simpa [β, hinit] using hβ0
  intro v w he
  have he0 : fderiv ℝ (ψ t) y (v - w) = 0 := by simp [map_sub, he]
  exact sub_eq_zero.mp (hkernel (v - w) he0)
