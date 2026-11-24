-- Prove2me | solution 1 for Formalism.L2.Col.lenW_eq_length
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:21:18.306545+00:00
-- url     : https://prove2.me/submissions/fa3f4c4a-020c-4022-adf2-f6405db55a40

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff
import Theorems.Thm_Formalism_L2_Col_atW_restrictScalars
import Theorems.Thm_Formalism_L2_Col_length_restrict_ow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.Col
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    lenW w A B = Module.length (𝓞 K) (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A ⧸
      (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype) := by
  unfold lenW
  rw [← length_restrict_ow w]
  have hA : ∀ x : V, x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A ↔ x ∈ atW w A := fun x => by
    rw [← atW_restrictScalars]; rfl
  have hB : ∀ x : V, x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B ↔ x ∈ atW w B := fun x => by
    rw [← atW_restrictScalars]; rfl
  let e : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A ≃ₗ[𝓞 K] atW w A :=
    { toFun := fun x => ⟨x.1, (hA _).1 x.2⟩
      invFun := fun x => ⟨x.1, (hA _).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine LinearEquiv.length_eq (((Submodule.Quotient.equiv _
    (((atW w B).comap (atW w A).subtype).restrictScalars (𝓞 K)) e ?_).trans
    (Submodule.Quotient.restrictScalarsEquiv (𝓞 K) _)).symm)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hB _).1 hy
  · intro hx
    exact ⟨e.symm x, (hB _).2 hx, e.apply_symm_apply x⟩
end Formalism.L2.Col
