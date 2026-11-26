-- Prove2me | solution 1 for BKAR.Forest.boundarySupportOrderTreeContribution_eq_sum_supportOrderPairs_treeFiber_of_activeEdges_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:51:09.840992+00:00
-- url     : https://prove2.me/submissions/31921a87-1f7f-4601-9574-dee3771aa3cc

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_def
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_zero_of_activeEdges_eq_empty
import Theorems.Thm_BKAR_Forest_localBoundarySupportOrderSum_eq_sum_supportOrderPairs
import Theorems.Thm_BKAR_Forest_ActiveExtension_activeEdges_card_lt
import Theorems.Thm_BKAR_Forest_EdgeExtension_activeEdges_card_lt
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeContribution_def
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeContribution_eq_zero_of_activeEdges_eq_empty


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      boundarySupportOrderTreeFiberIntegrable choices n
        F pref prefixTs top ρ →
      boundarySupportOrderTreeContribution choices F pref prefixTs top ρ =
        Finset.sum (supportOrderPairs V)
          (fun x =>
            boundarySupportOrderTreeFiber choices F pref prefixTs top
              x.1 x.2 ρ)
  | 0, F, pref, prefixTs, top, ρ, hle, _hfiber => by
      have hcard : F.activeEdges.card = 0 :=
        Nat.eq_zero_of_le_zero hle
      have hF : F.activeEdges = ∅ :=
        Finset.card_eq_zero.mp hcard
      rw [boundarySupportOrderTreeContribution_eq_zero_of_activeEdges_eq_empty
        choices F pref prefixTs top ρ hF]
      apply Eq.symm
      apply Finset.sum_eq_zero
      intro x _
      rw [boundarySupportOrderTreeFiber_eq_zero_of_activeEdges_eq_empty
        choices F pref prefixTs top x.1 x.2 ρ hF]
  | n + 1, F, pref, prefixTs, top, ρ, hle, hfiber => by
      rcases hfiber with ⟨hInt, hchildFiber⟩
      rw [boundarySupportOrderTreeContribution_def]
      rw [localBoundarySupportOrderSum_eq_sum_supportOrderPairs]
      rw [show
          Finset.sum (supportOrderPairs V)
              (fun x =>
                boundarySupportOrderTreeFiber choices F pref prefixTs top
                  x.1 x.2 ρ) =
            Finset.sum (supportOrderPairs V)
              (fun x =>
                localBoundarySupportOrderContribution choices F pref prefixTs
                    top x.1 x.2 ρ +
                  Finset.sum F.activeEdges.attach
                    (fun e => ∫ t in 0..top,
                      boundarySupportOrderTreeFiber choices
                        (choices F e).forest (pref ++ [e.val])
                        (prefixTs ++ [t]) t x.1 x.2 ρ)) by
        apply Finset.sum_congr rfl
        intro x _
        rw [boundarySupportOrderTreeFiber_def]]
      rw [Finset.sum_add_distrib]
      apply congrArg
        (fun r =>
          Finset.sum (supportOrderPairs V)
              (fun x =>
                localBoundarySupportOrderContribution choices F pref prefixTs
                  top x.1 x.2 ρ) + r)
      calc
        Finset.sum F.activeEdges.attach
            (fun e => ∫ t in 0..top,
              boundarySupportOrderTreeContribution choices
                (choices F e).forest (pref ++ [e.val])
                (prefixTs ++ [t]) t ρ) =
          Finset.sum F.activeEdges.attach
            (fun e => ∫ t in 0..top,
              Finset.sum (supportOrderPairs V)
                (fun x =>
                  boundarySupportOrderTreeFiber choices
                    (choices F e).forest (pref ++ [e.val])
                    (prefixTs ++ [t]) t x.1 x.2 ρ)) := by
            apply Finset.sum_congr rfl
            intro e _
            apply intervalIntegral.integral_congr
            intro t ht
            have hchild_le :
                (choices F e).forest.activeEdges.card ≤ n := by
              have hlt :
                  (choices F e).forest.activeEdges.card <
                    F.activeEdges.card :=
                (choices F e).activeEdges_card_lt
              exact Nat.lt_succ_iff.mp (hlt.trans_le hle)
            exact
              solution
                choices n (choices F e).forest (pref ++ [e.val])
                (prefixTs ++ [t]) t ρ hchild_le (hchildFiber e t ht)
        _ =
          Finset.sum F.activeEdges.attach
            (fun e =>
              Finset.sum (supportOrderPairs V)
                (fun x => ∫ t in 0..top,
                  boundarySupportOrderTreeFiber choices
                    (choices F e).forest (pref ++ [e.val])
                    (prefixTs ++ [t]) t x.1 x.2 ρ)) := by
            apply Finset.sum_congr rfl
            intro e _
            rw [intervalIntegral.integral_finsetSum (hInt e)]
        _ =
          Finset.sum (supportOrderPairs V)
            (fun x =>
              Finset.sum F.activeEdges.attach
                (fun e => ∫ t in 0..top,
                  boundarySupportOrderTreeFiber choices
                    (choices F e).forest (pref ++ [e.val])
                    (prefixTs ++ [t]) t x.1 x.2 ρ)) := by
            rw [Finset.sum_comm]
end BKAR.Forest
