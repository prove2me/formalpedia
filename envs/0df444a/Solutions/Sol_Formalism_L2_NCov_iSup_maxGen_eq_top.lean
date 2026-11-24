-- Prove2me | solution 1 for Formalism.L2.NCov.iSup_maxGen_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:28:40.630564+00:00
-- url     : https://prove2.me/submissions/98655f3c-beb4-4c3f-8e23-39070f120464

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
import Theorems.Thm_Formalism_L2_NCov_mem_maxGen_add
import Theorems.Thm_Formalism_L2_NCov_mem_maxGen_mul
import Theorems.Thm_Formalism_L2_NCov_maxGen_smul_one
import Theorems.Thm_Formalism_L2_NCov_algebraMap_end_eq
import Theorems.Thm_Formalism_L2_NCov_commute_adjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.NCov
open Module Module.End
variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
variable [IsLocalRing O]
variable {S : Set (End K V)}
namespace Formalism.L2.NCov
theorem _root_.solution [FiniteDimensional K V] (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b)
    (hsplit : ∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤) (t : Algebra.adjoin O S) :
    ⨆ μ, (t : End K V).maxGenEigenspace μ = ⊤ := by
  have hgen := iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (fun a : S => (a : End K V)) (fun a b _ => hS a a.2 b b.2) (fun a => hsplit a a.2)
  have key : ∀ χ : S → K, ∀ x (hx : x ∈ Algebra.adjoin O S), ∃ μ,
      (⨅ a : S, (a : End K V).maxGenEigenspace (χ a)) ≤ x.maxGenEigenspace μ := by
    intro χ x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact ⟨χ ⟨x, hx⟩, iInf_le (fun a : S => (a : End K V).maxGenEigenspace (χ a)) ⟨x, hx⟩⟩
    | algebraMap r =>
      exact ⟨algebraMap O K r, by rw [algebraMap_end_eq, maxGen_smul_one]; exact le_top⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a + b, fun v hv => mem_maxGen_add (commute_adjoin hS hx hy) (ha hv) (hb hv)⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a * b, fun v hv => mem_maxGen_mul (commute_adjoin hS hx hy) (ha hv) (hb hv)⟩
  rw [eq_top_iff, ← hgen]
  refine iSup_le fun χ => ?_
  obtain ⟨μ, hμ⟩ := key χ t t.2
  exact hμ.trans (le_iSup (fun μ => (t : End K V).maxGenEigenspace μ) μ)
end Formalism.L2.NCov
