-- Prove2me | solution 1 for ConnesGreen.sourceLift_dense
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T03:03:33.062841+00:00
-- url     : https://prove2.me/submissions/9b7866ec-7103-496e-8f09-927daa5988d8

import Definitions.Def_ConnesGreen_canonical_model
import Theorems.Thm_ConnesGreen_energyGraph_no_derivative_only

set_option autoImplicit false
open Complex MeasureTheory
open scoped BigOperators InnerProductSpace lp ENNReal Classical
noncomputable section
namespace ConnesGreen

/-- The original source loading, now with its linear and continuity facts. -/
def sourceLoadCLM (t : ℝ) : WindowL2 t →L[ℂ] Ambient t where
  toFun := sourceLoad t
  map_add' f g := by
    ext i
    simp [sourceLoad, smul_add]
    split_ifs <;> simp
  map_smul' c f := by
    ext i
    simp [sourceLoad, smul_smul, mul_comm]
  cont := by
    unfold sourceLoad
    apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => WindowL2 t)).symm.continuous.comp
    apply continuous_pi
    intro i
    by_cases hi : i = 0
    · simp only [hi, if_pos rfl]
      exact continuous_const
    · simp only [if_neg hi]
      fun_prop

def sourceLiftCLM (t : ℝ) : WindowL2 t →L[ℂ] Physical t :=
  (energySubspace t).orthogonalProjectionOnto.comp (sourceLoadCLM t)

theorem sourceLiftCLM_apply (t : ℝ) (f : WindowL2 t) :
    sourceLiftCLM t f = sourceLift t f := rfl

/-- The projected source detects exactly the second L2 coordinate. -/
theorem sourceLift_inner (t : ℝ) (f : WindowL2 t) (h : Physical t) :
    ⟪sourceLift t f, h⟫_ℂ = (2 : ℂ) * ⟪f, (h : Ambient t) 1⟫_ℂ := by
  rw [sourceLift, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  simp [sourceLoad, PiLp.inner_apply, Fin.sum_univ_two, inner_smul_left,
    map_ofNat]

theorem sourceLift_annihilator_iff (t : ℝ) (h : Physical t) :
    (∀ f : WindowL2 t, ⟪sourceLift t f, h⟫_ℂ = 0) ↔
      (h : Ambient t) 1 = 0 := by
  simp only [sourceLift_inner, mul_eq_zero, (by norm_num : (2 : ℂ) ≠ 0), false_or]
  constructor
  · intro hh
    exact inner_self_eq_zero.mp (hh ((h : Ambient t) 1))
  · intro hh f
    simp [hh]

/-- RG-1 is exactly the closability obstruction: the completed admissible
energy graph has no nonzero derivative-only vector. Neither implication
assumes density, a weak-derivative theorem, or a surrogate carrier. -/
theorem sourceLift_dense_iff_no_derivative_only (t : ℝ) :
    DenseRange (sourceLift t) ↔
      ∀ h : Physical t, (h : Ambient t) 1 = 0 → h = 0 := by
  have hd : DenseRange (sourceLift t) ↔
      (sourceLiftCLM t).range.topologicalClosure = ⊤ := by
    change Dense (Set.range (sourceLift t)) ↔ _
    rw [dense_iff_closure_eq]
    change closure (Set.range (sourceLift t)) = Set.univ ↔ _
    change closure (↑(sourceLiftCLM t).range : Set (Physical t)) = Set.univ ↔ _
    rw [← Submodule.topologicalClosure_coe]
    exact SetLike.coe_set_eq (p := (sourceLiftCLM t).range.topologicalClosure)
      (q := (⊤ : Submodule ℂ (Physical t)))
  rw [hd, Submodule.topologicalClosure_eq_top_iff]
  constructor
  · intro hh h hc
    have hm : h ∈ (sourceLiftCLM t).rangeᗮ := by
      rw [Submodule.mem_orthogonal]
      rintro _ ⟨f, rfl⟩
      exact (sourceLift_annihilator_iff t h).mpr hc f
    simpa [hh] using hm
  · intro hh
    apply eq_bot_iff.mpr
    intro h hm
    apply hh h
    apply (sourceLift_annihilator_iff t h).mp
    intro f
    exact ((sourceLiftCLM t).range.mem_orthogonal h).mp hm _ ⟨f, rfl⟩

end ConnesGreen

theorem solution (t : ℝ) (ht : 0 < t) : DenseRange (ConnesGreen.sourceLift t) :=
  (ConnesGreen.sourceLift_dense_iff_no_derivative_only t).mpr
    (ConnesGreen.energyGraph_no_derivative_only t ht)
