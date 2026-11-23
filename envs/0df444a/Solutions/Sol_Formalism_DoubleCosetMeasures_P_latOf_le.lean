-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.latOf_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:28.530775+00:00
-- url     : https://prove2.me/submissions/0569f755-08c5-4d07-9706-56762396d5a0

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
theorem _root_.solution (g h : GL (Fin n) K)
    (hM : IsInt R (((g⁻¹ * h : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)) :
    latOf R h ≤ latOf R g := by
  intro w hw
  obtain ⟨v, rfl⟩ := (mem_latOf R h w).1 hw
  rw [mem_latOf]
  set M : Matrix (Fin n) (Fin n) K := ((g⁻¹ * h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hMdef
  refine ⟨fun i => ⟨(M *ᵥ (fun j => (v j : K))) i, ?_⟩, ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact R.sum_mem fun k _ => R.mul_mem (hM i k) (v k).2
  · have hgM : (g : Matrix (Fin n) (Fin n) K) * M = h := by
      rw [hMdef, Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.one_mul]
    change (g : Matrix (Fin n) (Fin n) K) *ᵥ (M *ᵥ (fun j => (v j : K))) = _
    rw [Matrix.mulVec_mulVec, hgM]
end Formalism.DoubleCosetMeasures.P
