-- Prove2me | solution 1 for Formalism.CountingSumsFrames.peel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:25.549938+00:00
-- url     : https://prove2.me/submissions/a4c047cf-d6bc-48af-89bd-adf165497e4c

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_nil
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_cons
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_keep
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι]
namespace Formalism.CountingSumsFrames
theorem _root_.solution (B : V → V → K) (φ Ts π : ι → V →ₗ[K] V) (c : ι → K) (C : ι → Set V) (Y : Set V)
    (hYC : ∀ i, Y ⊆ C i) (hTY : ∀ i, ∀ y ∈ Y, Ts i y ∈ Y)
    (hkeep : ∀ i j, i < j → ∀ u ∈ C i, φ j u ∈ C i)
    (hcomm : ∀ i j, i < j → ∀ u ∈ C i, π i (φ j u) = φ j (π i u))
    (hadj : ∀ i, ∀ u ∈ C i, ∀ u' ∈ Y, B (φ i u) (Ts i u') = c i * B (π i u) u') :
    ∀ l : List ι, l.Pairwise (· < ·) → ∀ u ∈ Y, (∀ i ∈ l, π i u = u) → ∀ y ∈ Y,
      B (lcomp φ l u) (lcomp Ts l y) = (l.map c).prod * B u y
  | [], _, u, _, _, y, _ => by simp [lcomp_nil]
  | i :: l, hl, u, hu, hfix, y, hy => by
    rw [List.pairwise_cons] at hl
    rw [lcomp_cons, lcomp_cons, LinearMap.comp_apply, LinearMap.comp_apply]
    have hX : lcomp φ l u ∈ C i :=
      lcomp_keep φ (C i) l (fun j hj => hkeep i j (hl.1 j hj)) u (hYC i hu)
    have hZ : lcomp Ts l y ∈ Y := lcomp_keep Ts Y l (fun j _ => hTY j) y hy
    rw [hadj i _ hX _ hZ]
    rw [lcomp_comm φ (π i) (C i) l (fun j hj => hkeep i j (hl.1 j hj)) (fun j hj => hcomm i j (hl.1 j hj)) u
      (hYC i hu)]
    rw [hfix i List.mem_cons_self]
    rw [solution B φ Ts π c C Y hYC hTY hkeep hcomm hadj l hl.2 u hu (fun j hj => hfix j (List.mem_cons_of_mem _ hj))
      y hy]
    simp [mul_assoc]
end Formalism.CountingSumsFrames
