-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.exists_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:39.838779+00:00
-- url     : https://prove2.me/submissions/e59750f1-7af4-4da4-bd98-77f7566db8ff

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryFin
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_cj_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_exists_refl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
open Matrix
variable {k : Type*} [Field k]
namespace Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
theorem _root_.solution {m : ℕ} (σ : k ≃+* k) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x)
    (x : Fin (m + 1) → k) (hx : ∑ i, σ (x i) * x i = 1) :
    ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) k, cj σ g * g = 1 ∧ ∀ i, g i 0 = x i := by
  have he : ∑ i, σ ((Pi.single 0 1 : Fin (m + 1) → k) i) * (Pi.single 0 1 : Fin (m + 1) → k) i = 1 := by
    rw [Finset.sum_eq_single 0] <;> simp +contextual
  have hs : ∀ y : Fin (m + 1) → k, ∑ i, σ (y i) * (Pi.single 0 1 : Fin (m + 1) → k) i = σ (y 0) := by
    intro y
    rw [Finset.sum_eq_single 0] <;> simp +contextual
  by_cases h1 : σ (x 0) = 1
  · obtain ⟨t, ht⟩ := hne
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp at ht
    have hst0 : σ t ≠ 0 := by simpa using ht0
    set ζ : k := σ t / t with hζ
    have hζ0 : ζ ≠ 0 := div_ne_zero hst0 ht0
    have hsζ : σ ζ = t / σ t := by simp [hζ, hσ]
    have hN : σ ζ * ζ = 1 := by
      rw [hsζ, hζ]; field_simp
    have hsζ1 : σ ζ ≠ 1 := by
      rw [hsζ]
      intro h
      rw [div_eq_one_iff_eq hst0] at h
      exact ht h.symm
    obtain ⟨g, hg, hgx⟩ := exists_refl σ hσ (Pi.single 0 1) (fun i => ζ * x i) he
      (by
        have : ∀ i, σ (ζ * x i) * (ζ * x i) = (σ ζ * ζ) * (σ (x i) * x i) := by
          intro i; rw [map_mul]; ring
        simp only [this, ← Finset.mul_sum, hx, hN, mul_one])
      (by rw [hs, map_mul, h1, mul_one]; exact hsζ1)
    refine ⟨ζ⁻¹ • g, ?_, ?_⟩
    · have hc : cj σ (ζ⁻¹ • g) = (σ ζ)⁻¹ • cj σ g := by
        ext i j
        simp [cj_apply]
      rw [hc, smul_mul_smul_comm, hg, ← mul_inv, hN, inv_one, one_smul]
    · intro i
      have := congrFun hgx i
      rw [Matrix.mulVec_single_one] at this
      simp only [Matrix.col_apply] at this
      simp [this, hζ0]
  · obtain ⟨g, hg, hgx⟩ := exists_refl σ hσ (Pi.single 0 1) x he hx (by rw [hs]; exact h1)
    refine ⟨g, hg, fun i => ?_⟩
    have := congrFun hgx i
    rw [Matrix.mulVec_single_one] at this
    simpa using this
end Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
