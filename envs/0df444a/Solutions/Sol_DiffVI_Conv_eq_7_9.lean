-- Prove2me | solution 1 for DiffVI.Conv.eq_7_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:35:12.86675+00:00
-- url     : https://prove2.me/submissions/3e080746-822e-40fb-8dcb-8d7bb065c8a0

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Conv_Setting
open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace Aux_DiffVI79

lemma int_inner {m : ℕ} {μ : Measure ℝ} {f g : ℝ → EuclideanSpace ℝ (Fin m)}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : Integrable (fun t => ⟪f t, g t⟫_ℝ) μ := by
  have := L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)
  refine this.congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with t h1 h2
  rw [h1, h2]

end Aux_DiffVI79

open SolodovSvaiterVI.Alg21 DiffVI.Conv in
theorem solution {m : ℕ} (D : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hD : DiffVI.Exist.IsPSD D) (T : ℝ)
    (g : ℕ → ℝ → EuclideanSpace ℝ (Fin m)) (ul : ℝ → EuclideanSpace ℝ (Fin m))
    (hgL2 : ∀ k, MemLp (g k) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hw : WeakL2Tendsto T g ul) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      (∫ t in Set.Icc (0 : ℝ) T, ⟪ul t, D (ul t)⟫_ℝ) - ε ≤
        ∫ t in Set.Icc (0 : ℝ) T, ⟪g k t, D (g k t)⟫_ℝ := by
  intro ε hε
  obtain ⟨-, hu, hlim⟩ := hw
  set A := ContinuousLinearMap.adjoint D with hA
  set ψ : ℝ → EuclideanSpace ℝ (Fin m) := fun t => A (ul t) + D (ul t) with hψ
  have hψL2 : MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    (ContinuousLinearMap.comp_memLp' A hu).add (ContinuousLinearMap.comp_memLp' D hu)
  have hT := hlim ψ hψL2
  set I := ∫ t in Set.Icc (0 : ℝ) T, ⟪ul t, D (ul t)⟫_ℝ with hI
  have hIint : Integrable (fun t => ⟪ul t, D (ul t)⟫_ℝ) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    Aux_DiffVI79.int_inner hu (ContinuousLinearMap.comp_memLp' D hu)
  have hψu : ∫ t in Set.Icc (0 : ℝ) T, ⟪ψ t, ul t⟫_ℝ = 2 * I := by
    rw [hI, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
    simp only [hψ, inner_add_left, hA, ContinuousLinearMap.adjoint_inner_left]
    rw [real_inner_comm (D (ul t)) (ul t)]
    ring
  rw [hψu] at hT
  have hev : ∀ᶠ k in atTop, 2 * I - ε < ∫ t in Set.Icc (0 : ℝ) T, ⟪ψ t, g k t⟫_ℝ :=
    hT.eventually (lt_mem_nhds (by linarith))
  filter_upwards [hev] with k hk
  have hgk := hgL2 k
  have i1 : Integrable (fun t => ⟪g k t, D (g k t)⟫_ℝ) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    Aux_DiffVI79.int_inner hgk (ContinuousLinearMap.comp_memLp' D hgk)
  have i2 : Integrable (fun t => ⟪ψ t, g k t⟫_ℝ) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    Aux_DiffVI79.int_inner hψL2 hgk
  have hpt : ∀ t, ⟪ψ t, g k t⟫_ℝ - ⟪ul t, D (ul t)⟫_ℝ ≤ ⟪g k t, D (g k t)⟫_ℝ := by
    intro t
    have h0 := hD (g k t - ul t)
    simp only [map_sub, inner_sub_left, inner_sub_right] at h0
    simp only [hψ, inner_add_left, hA, ContinuousLinearMap.adjoint_inner_left]
    rw [real_inner_comm (D (ul t)) (g k t)] at h0
    linarith
  have hmono : ∫ t in Set.Icc (0 : ℝ) T, (⟪ψ t, g k t⟫_ℝ - ⟪ul t, D (ul t)⟫_ℝ) ≤
      ∫ t in Set.Icc (0 : ℝ) T, ⟪g k t, D (g k t)⟫_ℝ :=
    integral_mono (i2.sub hIint) i1 hpt
  rw [integral_sub i2 hIint] at hmono
  linarith
