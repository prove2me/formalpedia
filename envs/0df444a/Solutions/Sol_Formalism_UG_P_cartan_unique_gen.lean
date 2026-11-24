-- Prove2me | solution 1 for Formalism.UG.P.cartan_unique_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:04:51.482836+00:00
-- url     : https://prove2.me/submissions/d214a703-c90d-456d-b151-481841268279

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Theorems.Thm_Formalism_UG_P_cartan_entries_of_mem
import Theorems.Thm_Formalism_UG_P_cartan_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] (O : Subring L) {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
namespace Formalism.UG.P
theorem _root_.solution (val : Valuation L Γ) (hO : ∀ x, x ∈ O ↔ val x ≤ 1) (ϖ : L)
    (hϖ0 : ϖ ≠ 0) (hϖ : val ϖ < 1) {m : ℕ} (a a' : Fin m → ℤ) (ha : Antitone a)
    (ha' : Antitone a') (k₁ : GL (Fin m) L) (hk₁ : k₁ ∈ GLint (Fin m) O)
    (k₂ : GL (Fin m) L) (hk₂ : k₂ ∈ GLint (Fin m) O)
    (h : (k₁ : Matrix (Fin m) (Fin m) L) * Matrix.diagonal (fun i => ϖ ^ a i) *
      (k₂ : Matrix (Fin m) (Fin m) L) = Matrix.diagonal (fun i => ϖ ^ a' i)) : a = a' := by
  have hk₁i : k₁⁻¹ ∈ GLint (Fin m) O := inv_mem hk₁
  have hk₂i : k₂⁻¹ ∈ GLint (Fin m) O := inv_mem hk₂
  have e1 : Matrix.diagonal (fun i => ϖ ^ a i) * (k₂ : Matrix (Fin m) (Fin m) L) =
      ((k₁⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) * Matrix.diagonal (fun i => ϖ ^ a' i) := by
    rw [← h, ← mul_assoc, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have e2 : Matrix.diagonal (fun i => ϖ ^ a' i) * ((k₂⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) =
      (k₁ : Matrix (Fin m) (Fin m) L) * Matrix.diagonal (fun i => ϖ ^ a i) := by
    rw [← h, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  funext i
  apply le_antisymm
  · by_contra hlt
    push_neg at hlt
    exact cartan_core O val hO ϖ hϖ0 hϖ a' a ha' ha k₂⁻¹ hk₂i _
      (cartan_entries_of_mem O k₁ hk₁) e2 i hlt
  · by_contra hlt
    push_neg at hlt
    exact cartan_core O val hO ϖ hϖ0 hϖ a a' ha ha' k₂ hk₂ _
      (cartan_entries_of_mem O k₁⁻¹ hk₁i) e1 i hlt
end Formalism.UG.P
