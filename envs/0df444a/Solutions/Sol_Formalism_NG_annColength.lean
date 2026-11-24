-- Prove2me | solution 1 for Formalism.NG.annColength
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:24:36.417508+00:00
-- url     : https://prove2.me/submissions/54a44b1b-9424-42e7-b98a-a16d83869f8a

import Definitions.Def_Formalism_CharacterColumnKernels_StatementRho
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_mem_annih
import Theorems.Thm_Formalism_NG_matlis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution : StatAnnColength := by
  intro O Cw Cs _ _ _ _ _ _ _ pr Fs Im hle
  let I' : Submodule O Fs := Im.comap Fs.subtype
  let Φ : annih pr Im →ₗ[O] ((Fs ⧸ I') →ₗ[O] KO O) :=
    { toFun := fun c => I'.liftQ (pr c.1 ∘ₗ Fs.subtype) (fun x hx => by
        simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply]
        exact (IdempotentNormalFormsRhoFacts.mem_annih pr Im c.1).1 c.2 x.1 hx)
      map_add' := fun a b => by ext x; simp
      map_smul' := fun r a => by ext x; simp }
  have hker : LinearMap.ker Φ ≤ (annih pr Fs).comap (annih pr Im).subtype := by
    intro c hc
    rw [Submodule.mem_comap, Submodule.subtype_apply, IdempotentNormalFormsRhoFacts.mem_annih]
    intro x hx
    have := LinearMap.congr_fun (LinearMap.mem_ker.mp hc) (Submodule.Quotient.mk ⟨x, hx⟩)
    simpa [Φ] using this
  have hle' : (annih pr Fs).comap (annih pr Im).subtype ≤ LinearMap.ker Φ := by
    intro c hc
    rw [Submodule.mem_comap, Submodule.subtype_apply, IdempotentNormalFormsRhoFacts.mem_annih] at hc
    rw [LinearMap.mem_ker]
    ext x
    simp [Φ, hc x.1 x.2]
  have hinj := LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ Φ hle' hker)
  by_cases hfinQ : IsFiniteLength O (Fs ⧸ I')
  swap
  · rw [← Module.length_ne_top_iff, ne_eq, not_not] at hfinQ
    exact hfinQ ▸ le_top
  calc _ ≤ Module.length O ((Fs ⧸ I') →ₗ[O] KO O) := Module.length_le_of_injective _ hinj
    _ = _ := matlis O (Fs ⧸ I') hfinQ
end Formalism.NG
