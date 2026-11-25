-- Prove2me | solution 1 for ContrastiveInverts.sphere_dot_product_map_is_scaled_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T17:48:14.264218+00:00
-- url     : https://prove2.me/submissions/22bbf52b-7ff2-4bb5-b894-01a7219e0d9d

import Mathlib
import Definitions.Def_ContrastiveInverts_Basic

open MeasureTheory Filter Topology

open ContrastiveInverts in
theorem solution {N : ℕ} (hN : 0 < N) (r : ℝ) (hr : 0 < r)
    (h : Vec N → Vec N) (hmap : ∀ x, h x ∈ Metric.sphere (0 : Vec N) r)
    (hdiff : ∃ U : Set (Vec N), IsOpen U ∧ Metric.sphere (0 : Vec N) 1 ⊆ U ∧
      DifferentiableOn ℝ h U)
    (hdot : ∀ z ∈ Metric.sphere (0 : Vec N) 1, ∀ z' ∈ Metric.sphere (0 : Vec N) 1,
      r ^ 2 * inner ℝ z z' = inner ℝ (h z) (h z')) :
    ∃ U : Vec N ≃ₗᵢ[ℝ] Vec N, ∀ z ∈ Metric.sphere (0 : Vec N) 1, h z = r • U z := by
  set e := EuclideanSpace.basisFun (Fin N) ℝ with he
  have hes : ∀ i, e i ∈ Metric.sphere (0 : Vec N) 1 := fun i => by
    simp [e.orthonormal.1 i]
  set u : Fin N → Vec N := fun i => r⁻¹ • h (e i) with hu
  have hr0 : r ≠ 0 := hr.ne'
  have huinner : ∀ i (z : Vec N), z ∈ Metric.sphere (0 : Vec N) 1 →
      inner ℝ (u i) (r⁻¹ • h z) = inner ℝ (e i) z := by
    intro i z hz
    simp only [hu, real_inner_smul_left, real_inner_smul_right]
    rw [← hdot _ (hes i) _ hz]
    field_simp
  have hon : Orthonormal ℝ u := by
    rw [orthonormal_iff_ite]
    intro i j
    have := huinner i (e j) (hes j)
    simp only [hu] at this ⊢
    rw [this]
    exact (orthonormal_iff_ite.mp e.orthonormal) i j
  have hcard : Fintype.card (Fin N) = Module.finrank ℝ (Vec N) := by simp
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  set b' := basisOfOrthonormalOfCardEqFinrank hon hcard with hb'
  have hb'eq : ⇑b' = u := coe_basisOfOrthonormalOfCardEqFinrank hon hcard
  set ob := OrthonormalBasis.mk hon (by rw [← hb'eq, b'.span_eq]) with hob
  have hobu : ∀ i, ob i = u i := fun i => by simp [hob]
  refine ⟨e.repr.trans ob.repr.symm, fun z hz => ?_⟩
  have key : r⁻¹ • h z = (e.repr.trans ob.repr.symm) z := by
    rw [LinearIsometryEquiv.trans_apply, ← ob.sum_repr' (r⁻¹ • h z), ← ob.sum_repr_symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hobu, huinner i z hz, OrthonormalBasis.repr_apply_apply]
  rw [← key, smul_smul, mul_inv_cancel₀ hr0, one_smul]
