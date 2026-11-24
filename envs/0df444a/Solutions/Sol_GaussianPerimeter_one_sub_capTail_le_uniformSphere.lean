-- Prove2me | solution 1 for GaussianPerimeter.one_sub_capTail_le_uniformSphere
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:26:54.349733+00:00
-- url     : https://prove2.me/submissions/62cf2e89-6387-42a0-8a7d-a16590e3b648

module
public import Definitions.Def_GaussianPerimeter_SphereSections
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Definitions.Def_GaussianPerimeter_SphereCap
public import Theorems.Thm_GaussianPerimeter_uniformSphere_cap_le_capTail

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n)
    {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : ‖v‖ = 1) {ρ R : ℝ}
    (hρ : 0 < ρ) (hR : ρ < R) :
    1 - ENNReal.ofReal (capTail n (ρ / R)) ≤
      uniformSphere (EuclideanSpace ℝ (Fin (n + 1)))
        {u | ⟪R • v, (u : EuclideanSpace ℝ (Fin (n + 1)))⟫ < ρ} := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let S : Set (Metric.sphere (0 : E) 1) := {u | ρ / R ≤ ⟪v, (u : E)⟫}
  have hR0 := hρ.trans hR
  have hset : {u : Metric.sphere (0 : E) 1 | ⟪R • v, (u : E)⟫ < ρ} = Sᶜ := by
    ext u
    simp only [S, mem_compl_iff, mem_ofPred_eq, not_le, real_inner_smul_left]
    rw [lt_div_iff₀ hR0, mul_comm]
  have hs : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  change _ ≤ uniformSphere E _
  rw [hset, measure_compl hs (measure_ne_top _ _), measure_univ]
  exact tsub_le_tsub_left
    (uniformSphere_cap_le_capTail n hn hv (div_pos hρ hR0) ((div_lt_one hR0).2 hR)) _
end GaussianPerimeter
