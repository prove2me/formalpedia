-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.isInt_of_latOf_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:05.714798+00:00
-- url     : https://prove2.me/submissions/afed8500-bbf0-490d-9ebe-e8958e87b632

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_mem_latOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution (g h : GL (Fin n) K) (hle : latOf R h ≤ latOf R g) :
    IsInt R (((g⁻¹ * h : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by
  intro i j
  have hmem : (h : Matrix (Fin n) (Fin n) K) *ᵥ (fun k => ((Pi.single j (1 : R) : Fin n → R) k : K))
      ∈ latOf R h := (mem_latOf R h _).2 ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := (mem_latOf R g _).1 (hle hmem)
  have hcoe : (fun k => ((Pi.single j (1 : R) : Fin n → R) k : K)) = Pi.single j (1 : K) := by
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  rw [hcoe] at hv
  have key : (((g⁻¹ * h : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single j (1 : K) =
      fun k => (v k : K) := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hv, Matrix.mulVec_mulVec, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have := congrFun key i
  rw [Matrix.mulVec_single_one] at this
  simp only [Matrix.col_apply] at this
  rw [this]
  exact (v i).2
end Formalism.DoubleCosetMeasures.P
