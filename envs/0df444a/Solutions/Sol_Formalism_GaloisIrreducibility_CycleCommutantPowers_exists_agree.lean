-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.CycleCommutantPowers.exists_agree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:19.841348+00:00
-- url     : https://prove2.me/submissions/a422852b-4e1b-4331-bc5f-d39b63d95023

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_JordanPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Equiv Equiv.Perm MulAction
open Formalism.GaloisIrreducibility.CycleCommutantPowers
variable {α : Type} [Fintype α] [DecidableEq α]
namespace Formalism.GaloisIrreducibility.CycleCommutantPowers
theorem _root_.solution (G : Subgroup (Perm α)) (Γ : Finset α)
    (hG : IsMultiplyPretransitive G α Γ.card) (π : Perm α) :
    ∃ x ∈ G, ∀ γ ∈ Γ, x γ = π γ := by
  classical
  let e : Fin Γ.card ↪ α :=
    ⟨fun i => ((Γ.equivFin.symm i : Γ) : α), fun i j h => Γ.equivFin.symm.injective (Subtype.ext h)⟩
  let e' : Fin Γ.card ↪ α := e.trans π.toEmbedding
  have hpt : IsPretransitive G (Fin Γ.card ↪ α) := hG
  obtain ⟨g, hg⟩ := hpt.exists_smul_eq e e'
  refine ⟨g, g.2, fun γ hγ => ?_⟩
  have h := congrArg (fun f : Fin Γ.card ↪ α => f (Γ.equivFin ⟨γ, hγ⟩)) hg
  have h2 : e (Γ.equivFin ⟨γ, hγ⟩) = γ := by
    show ((Γ.equivFin.symm (Γ.equivFin ⟨γ, hγ⟩) : Γ) : α) = γ
    rw [Equiv.symm_apply_apply]
  have h3 : (g : Perm α) (e (Γ.equivFin ⟨γ, hγ⟩)) = π (e (Γ.equivFin ⟨γ, hγ⟩)) := by
    first
      | exact h
      | (simp only [Function.Embedding.smul_apply, Subgroup.smul_def, Perm.smul_def] at h; exact h)
  rwa [h2] at h3
end Formalism.GaloisIrreducibility.CycleCommutantPowers
