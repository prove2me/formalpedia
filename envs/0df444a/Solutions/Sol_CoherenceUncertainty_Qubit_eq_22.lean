-- Prove2me | solution 1 for CoherenceUncertainty.Qubit.eq_22
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T23:16:02.559225+00:00
-- url     : https://prove2.me/submissions/163becb4-d15e-46f5-a766-4c355f4a75d2

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_CoherenceUncertainty_Qubit_Model

private theorem binEnt_eq (q : ℝ) :
    WildeQIT.binaryEntropy q = (Real.log 2)⁻¹ • Real.binEntropy q := by
  unfold WildeQIT.binaryEntropy
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog, Real.logb, smul_eq_mul]
  ring

theorem solution (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ConcaveOn ℝ (Set.Icc 0 1) (CoherenceUncertainty.Qubit.fp p) ∧
      ∀ x : ℝ, CoherenceUncertainty.Qubit.fp p x = CoherenceUncertainty.Qubit.fp p (1 - x) := by
  constructor
  · let g : ℝ →ᵃ[ℝ] ℝ :=
      ⟨fun x => x * p + (1 - x) * (1 - p), (2 * p - 1) • LinearMap.id,
        by intro x v; simp [smul_eq_mul]; ring⟩
    have h1 : ConcaveOn ℝ (Set.Icc (0:ℝ) 1) (fun y => (Real.log 2)⁻¹ • Real.binEntropy y) :=
      Real.strictConcave_binEntropy.concaveOn.smul
        (inv_nonneg.2 (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)))
    have h2 := h1.comp_affineMap g
    have hfp : CoherenceUncertainty.Qubit.fp p =
        (fun y => (Real.log 2)⁻¹ • Real.binEntropy y) ∘ ⇑g := by
      funext x
      simp only [CoherenceUncertainty.Qubit.fp, binEnt_eq, Function.comp]
      rfl
    rw [hfp]
    refine (h2.subset ?_ (convex_Icc 0 1))
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    show 0 ≤ x * p + (1 - x) * (1 - p) ∧ x * p + (1 - x) * (1 - p) ≤ 1
    constructor <;> nlinarith [mul_nonneg hx0 hp0, mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hp1),
      mul_nonneg hx0 (sub_nonneg.2 hp1), mul_nonneg (sub_nonneg.2 hx1) hp0]
  · intro x
    have : (1 - x) * p + (1 - (1 - x)) * (1 - p) = 1 - (x * p + (1 - x) * (1 - p)) := by ring
    unfold CoherenceUncertainty.Qubit.fp
    rw [this, binEnt_eq, binEnt_eq, Real.binEntropy_one_sub]
