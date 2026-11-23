-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PermutationFixedPoints.card_stab_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:39.430282+00:00
-- url     : https://prove2.me/submissions/e01a704a-412b-41af-914e-486f72ede9af

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_TwoMulNumDerangementsLeFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.PermutationFixedPoints
namespace Formalism.CyclotomicNorms.PermutationFixedPoints
theorem _root_.solution (N : ℕ) (S : Finset (Fin N)) :
    (univ.filter (fun σ : Equiv.Perm (Fin N) => ∀ x, σ x ∈ S ↔ x ∈ S)).card ≤
      S.card.factorial * (N - S.card).factorial := by
  have hsub : univ.filter (fun σ : Equiv.Perm (Fin N) => ∀ x, σ x ∈ S ↔ x ∈ S) ⊆
      (univ : Finset (Equiv.Perm {x // x ∈ S} × Equiv.Perm {x // x ∉ S})).image
        (Equiv.Perm.subtypeCongrHom (fun x => x ∈ S)) := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨(σ.subtypePerm (p := fun x => x ∈ S) (fun x => hσ x),
      σ.subtypePerm (p := fun x => x ∉ S) (fun x => not_congr (hσ x))), ?_⟩
    ext z
    rw [Equiv.Perm.subtypeCongrHom_apply]
    by_cases hz : z ∈ S
    · rw [Equiv.Perm.subtypeCongr.left_apply _ _ hz]
      rfl
    · rw [Equiv.Perm.subtypeCongr.right_apply _ _ hz]
      rfl
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le
    _ = _ := by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_perm, Fintype.card_perm,
        Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
end Formalism.CyclotomicNorms.PermutationFixedPoints
