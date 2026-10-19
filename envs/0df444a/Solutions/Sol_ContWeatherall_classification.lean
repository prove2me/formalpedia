-- Prove2me | solution 1 for ContWeatherall.classification
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:56:23.353246+00:00
-- url     : https://prove2.me/submissions/ded1ca61-055e-46b6-a17e-5b524d7801b7

import Theorems.Thm_ContWeatherall_h1Vanishes
import Theorems.Thm_ContWeatherall_h2Vanishes
import Theorems.Thm_ContWeatherall_full_iff
import Theorems.Thm_ContWeatherall_faithful_iff
import Theorems.Thm_ContWeatherall_essSurj_iff

open CategoryTheory ContinuousAlternatingMap ContWeatherall
open scoped ContDiff

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (P : (E → E [⋀^Fin 2]→L[ℝ] F) → Prop) [Nonempty (Pot P)] :
    (fieldStrength P).Full ∧ (fieldStrength P).EssSurj ∧
      ((fieldStrength P).Faithful ↔ Subsingleton F) ∧
      H1Vanishes E F ∧ H2Vanishes P ∧ (H0Vanishes E F ↔ Subsingleton F) := by
  have h0 : H0Vanishes E F ↔ Subsingleton F := by
    constructor
    · intro h
      have hc (c : F) : c = 0 := by
        have hg : grad (fun _ : E => c) = 0 := by
          funext x
          simp [grad_apply]
          exact (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (0 : Fin 1)).map_zero
        exact congrFun (h (fun _ => c) contDiff_const hg) (0 : E)
      exact ⟨fun a b => (hc a).trans (hc b).symm⟩
    · intro h
      let := h
      intro χ _ _
      exact Subsingleton.elim _ _
  exact ⟨(full_iff P).mpr (h1Vanishes E F), (essSurj_iff P).mpr (h2Vanishes P),
    (faithful_iff P).trans h0, h1Vanishes E F, h2Vanishes P, h0⟩
