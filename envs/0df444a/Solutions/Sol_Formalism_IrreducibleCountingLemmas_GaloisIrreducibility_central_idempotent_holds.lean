-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.central_idempotent_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:11:50.396847+00:00
-- url     : https://prove2.me/submissions/dca7a7c9-bdd1-4151-a7b9-ea0b64b107c1

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdempotent
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_isIrreducible_of
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_centralIdem_mul
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_centralIdem_comm_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : CentralIdempotent := by
  intro G V _ _ _ _ _ _ ρ h
  constructor
  · obtain ⟨μ, h1, h2⟩ := centralIdem_mul ρ ρ h
    have hirr : ρ.IsIrreducible := isIrreducible_of ρ h
    have hc0 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have : Invertible (Nat.card G : ℂ) :=
      invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
    have horth := Representation.char_orthonormal ρ ρ
    rw [if_pos ⟨Representation.Equiv.refl ρ⟩, Nat.card_eq_fintype_card] at horth
    have h3 : ∑ g, ρ.character g⁻¹ * ρ.character g = (Fintype.card G : ℂ) := by
      have : ∑ g, ρ.character g⁻¹ * ρ.character g = ∑ g, ρ.character g * ρ.character g⁻¹ :=
        Finset.sum_congr rfl fun g _ => mul_comm _ _
      rw [this]
      field_simp at horth
      simpa using horth
    rw [h2]
    have h4 : (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * μ = 1 := by
      rw [h3] at h1
      field_simp
      rw [mul_comm]; exact h1
    rw [h4, one_smul]
  · intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [mul_add, add_mul, ha, hb]
    | single g c =>
      have : MonoidAlgebra.single g c = c • MonoidAlgebra.of ℂ G g := by
        simp [MonoidAlgebra.of_apply]
      rw [this, mul_smul_comm, smul_mul_assoc, centralIdem_comm_of]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
