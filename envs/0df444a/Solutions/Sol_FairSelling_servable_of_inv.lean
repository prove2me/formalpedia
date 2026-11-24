-- Prove2me | solution 1 for FairSelling.servable_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:22:43.006805+00:00
-- url     : https://prove2.me/submissions/b209e804-0908-424e-8fa2-0ee5d381230c

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsLemma9
import Definitions.Def_RequestProject_TwoThirds
import Theorems.Thm_FairSelling_servable_empty
import Theorems.Thm_FairSelling_Canonical_cash_sum_le
import Theorems.Thm_FairSelling_canonical_of_inv
import Theorems.Thm_FairSelling_losses_of_round
import Theorems.Thm_FairSelling_servable_of_round


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) :
    ∀ (m : ℕ) (T : Finset (Fin n)) (R : Finset G) (D : ℝ), T.card = m → Inv v p T R D →
      Servable v p (thr v p) T R D := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro T R D hcard hInv
    obtain ⟨hD, hL, hsmall⟩ := hInv
    rcases Finset.eq_empty_or_nonempty T with rfl | hT
    · exact servable_empty v p _ R hD
    · obtain ⟨i, hiT, hmax⟩ := Finset.exists_max_image T (fun a => MMS n (v a) p) hT
      have hm : 0 < m := by
        rw [← hcard]; exact Finset.card_pos.mpr hT
      haveI : NeZero m := ⟨by omega⟩
      obtain ⟨C⟩ := canonical_of_inv v p hv hp ⟨hD, hL, hsmall⟩ hiT hmax hcard
      refine servable_of_round v p (thr v p) hiT hcard C ?_
      intro Kset part hiK hKT hinj hloss hspecial hzero
      set J : Finset (Fin m) := Kset.image part with hJ
      have hDnew : 0 ≤ D + (∑ g ∈ C.sold J, p g) - ∑ j ∈ J, C.cash j := by
        have := C.cash_sum_le J
        linarith
      have hcardnew : (T \ Kset).card < m := by
        have h1 : (T \ Kset).card ≤ (T.erase i).card := by
          refine Finset.card_le_card ?_
          intro a ha
          rcases Finset.mem_sdiff.mp ha with ⟨haT, haK⟩
          exact Finset.mem_erase.mpr ⟨fun h => haK (h ▸ hiK), haT⟩
        have h2 : (T.erase i).card = m - 1 := by
          rw [Finset.card_erase_of_mem hiT, hcard]
        omega
      refine IH _ hcardnew (T \ Kset) _ _ rfl ⟨hDnew, ?_, ?_⟩
      · exact losses_of_round v p ⟨hD, hL, hsmall⟩ hmax C Kset part hKT hinj hloss hspecial hzero
      · intro a ha g hg
        exact hsmall a (Finset.mem_sdiff.mp ha).1 g (Finset.mem_sdiff.mp hg).1
end FairSelling
