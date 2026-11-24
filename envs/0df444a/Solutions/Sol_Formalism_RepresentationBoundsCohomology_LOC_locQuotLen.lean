-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.locQuotLen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:45:21.457911+00:00
-- url     : https://prove2.me/submissions/25d52c7d-0680-433c-a2e4-99b3fb34a95f

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_RowCol
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_SubmoduleLengthBoundStatement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_QuotLen
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_mem_mulSub
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_length_quot_le_add
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_length_quot_of_KO
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_rowColength


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO annih)
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
open Module
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution : StatLocQuotLen.{u} := by
  intro O M _ _ _ _ _ _ d N δ hδ ℓ e
  let Q := Submodule.torsion O M
  have hA := length_quot_le_add ((ℓ : O) ^ e) Q

  have hT0 : finrank O Q = 0 := by
    rw [Module.finrank_eq_zero_iff]
    intro x
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (x : M)).mp x.2
    refine ⟨a, nonZeroDivisors.coe_ne_zero a, ?_⟩
    apply Subtype.ext
    rw [Submodule.coe_smul, Submodule.coe_zero]
    exact ha
  have hrank : finrank O (M ⧸ Q) = finrank O M := by
    have h := Submodule.finrank_quotient_add_finrank Q
    rw [hT0, add_zero] at h
    exact h
  have hB := Formalism.RepresentationBoundsCohomology.rowColength O (M ⧸ Q) (mulSub ((ℓ : O) ^ e) (M ⧸ Q)) ℓ e
    (fun m => (mem_mulSub _).2 ⟨m, rfl⟩)
  have htors : Module.length O (Submodule.torsion O (M ⧸ Q)) = 0 := by
    rw [Submodule.QuotientTorsion.torsion_eq_bot]
    exact Module.length_eq_zero
  rw [htors, add_zero, hrank] at hB

  let N' : Submodule O N := Q.comap δ
  let δ' : N' →ₗ[O] Q := δ.restrict (fun x hx => hx)
  have hδ' : Function.Surjective δ' := by
    intro x
    obtain ⟨n, hn⟩ := hδ x.2
    exact ⟨⟨n, by show δ n ∈ Q; rw [hn]; exact x.2⟩, Subtype.ext hn⟩
  have hC := length_quot_of_KO (N.subtype ∘ₗ N'.subtype)
    (N.injective_subtype.comp N'.injective_subtype) δ' hδ' ℓ e
  refine hA.trans ((add_le_add hC hB).trans (le_of_eq ?_))
  rw [eO, Nat.cast_add, add_mul, add_comm]
end Formalism.RepresentationBoundsCohomology.LOC
