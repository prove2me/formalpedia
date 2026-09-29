-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_neighbour_transverse_direction
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T16:49:25.662619+00:00
-- url     : https://prove2.me/submissions/5da8b00c-7f47-41c5-91db-0b0514d0f3df

import Definitions.Def_PartialMonitoringGame
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set

namespace BanditAlgorithm

theorem partial_monitoring_neighbour_transverse_direction
    {k d : ℕ} {𝕊 : Type*}
    (G : PartialMonitoringGame k d 𝕊) (a b : Fin k)
    (hab : NeighbouringActions G a b) :
    ∃ q : Fin d → ℝ,
      (∑ i, q i) = 0 ∧
      (∑ i, (G.L a i - G.L b i) * q i) = 1 := by
  classical
  let V := EuclideanSpace ℝ (Fin d)
  let T : ℝ →ₗ[ℝ] V :=
    { toFun := fun r ↦ WithLp.toLp 2 (fun _ ↦ r)
      map_add' := by
        intro r s
        apply WithLp.ofLp_injective
        ext i
        change r + s = r + s
        rfl
      map_smul' := by
        intro r s
        apply WithLp.ofLp_injective
        ext i
        change r * s = r * s
        rfl }
  let v : V := WithLp.toLp 2 (fun i ↦ G.L a i - G.L b i)
  have hv_not : v ∉ LinearMap.range T := by
    rintro ⟨r, hr⟩
    have hvconst : ∀ i : Fin d, G.L a i - G.L b i = r := by
      intro i
      have hi := congrArg (fun z : V ↦ z i) hr
      exact hi.symm
    obtain ⟨u, hua, hub⟩ := hab.2.2.1
    have hsum : ∑ i, u i = 1 := hua.1.2
    have hab0 : ∑ i, (G.L a i - G.L b i) * u i = 0 := by
      have hle := hua.2 b
      have hge0 : 0 ≤ ∑ i, (G.L a i - G.L b i) * u i := by
        have hb := hub.2 a
        have hneg : (∑ i, (G.L b i - G.L a i) * u i) =
            -(∑ i, (G.L a i - G.L b i) * u i) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [hneg] at hb
        linarith
      linarith
    have hr0 : r = 0 := by
      have : (∑ i, (G.L a i - G.L b i) * u i) = r := by
        calc
          _ = ∑ i, r * u i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hvconst i]
          _ = r := by rw [← Finset.mul_sum, hsum, mul_one]
      linarith
    have hL : ∀ i : Fin d, G.L a i = G.L b i := by
      intro i
      linarith [hvconst i]
    have hcell : pmCell G a = pmCell G b := by
      ext x
      simp only [pmCell, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hx, ha⟩
        refine ⟨hx, ?_⟩
        intro c
        simpa only [hL] using ha c
      · rintro ⟨hx, hb⟩
        refine ⟨hx, ?_⟩
        intro c
        simpa only [hL] using hb c
    have hinter : pmCell G a ∩ pmCell G b = pmCell G a := by
      rw [← hcell, inter_self]
    have hdim1 := hab.1.2
    have hdim2 := hab.2.2.2
    rw [hinter] at hdim2
    omega
  let U : Submodule ℝ V := LinearMap.range T
  obtain ⟨z, hzU, w, hwU, hvzw⟩ := U.exists_add_mem_mem_orthogonal v
  have hw_ne : w ≠ 0 := by
    intro hw
    apply hv_not
    change v ∈ U
    rw [hvzw, hw, add_zero]
    exact hzU
  have hvw : inner ℝ v w = ‖w‖ ^ 2 := by
    rw [hvzw, inner_add_left]
    have hzw : inner ℝ z w = 0 := (U.mem_orthogonal w).mp hwU z hzU
    rw [hzw, zero_add, real_inner_self_eq_norm_sq]
  have hvw_pos : 0 < inner ℝ v w := by rw [hvw]; positivity
  let qE : V := (inner ℝ v w)⁻¹ • w
  let q : Fin d → ℝ := fun i ↦ qE i
  refine ⟨q, ?_, ?_⟩
  · have honeU : WithLp.toLp 2 (fun _ : Fin d ↦ (1 : ℝ)) ∈ U := by
      refine ⟨1, ?_⟩
      apply WithLp.ofLp_injective
      ext i
      simp [T]
    have how : inner ℝ (WithLp.toLp 2 (fun _ : Fin d ↦ (1 : ℝ))) w = 0 :=
      (U.mem_orthogonal w).mp hwU _ honeU
    have : inner ℝ (WithLp.toLp 2 (fun _ : Fin d ↦ (1 : ℝ))) qE = 0 := by
      simp [qE, inner_smul_right, how]
    simpa [q, PiLp.inner_apply, mul_comm] using this
  · have : inner ℝ v qE = 1 := by
      simp [qE, inner_smul_right, hvw_pos.ne']
    change (∑ i, qE i * (G.L a i - G.L b i)) = 1 at this
    simpa [q, mul_comm] using this

end BanditAlgorithm

theorem solution
    {k d : ℕ} {𝕊 : Type*}
    (G : BanditAlgorithm.PartialMonitoringGame k d 𝕊) (a b : Fin k)
    (hab : BanditAlgorithm.NeighbouringActions G a b) :
    ∃ q : Fin d → ℝ,
      (∑ i, q i) = 0 ∧
      (∑ i, (G.L a i - G.L b i) * q i) = 1 :=
  BanditAlgorithm.partial_monitoring_neighbour_transverse_direction G a b hab
