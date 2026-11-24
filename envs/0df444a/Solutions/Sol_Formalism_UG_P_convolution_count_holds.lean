-- Prove2me | solution 1 for Formalism.UG.P.convolution_count_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:09:27.684606+00:00
-- url     : https://prove2.me/submissions/135fe4dd-4384-4b48-a7d7-3817696a5c40

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FiniteCosetsInDoset
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds
import Theorems.Thm_Formalism_UG_P_finite_cosets_in_doset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G]
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.ConvCount := by
  classical
  intro G _ K k _ hK a b g
  set S : Set (G ⧸ K) := {x : G ⧸ K | x.out ∈ DoubleCoset.doubleCoset a (K : Set G) K ∧
    x.out⁻¹ * g ∈ DoubleCoset.doubleCoset b (K : Set G) K} with hSdef
  have hfin : S.Finite := by
    refine (finite_cosets_in_doset hK a).subset fun x hx => ?_
    obtain ⟨h, hh, c, hc, e⟩ := DoubleCoset.mem_doubleCoset.1 hx.1
    exact ⟨⟨h, hh⟩, ⟨c, hc⟩, e⟩
  have hterm : ∀ x : G ⧸ K, dosetInd k K a x.out * dosetInd k K b (x.out⁻¹ * g) =
      if x ∈ S then 1 else 0 := by
    intro x
    simp only [dosetInd, Set.indicator_apply, Pi.one_apply, hSdef, Set.mem_setOf_eq]
    split_ifs <;> simp_all
  show ∑ᶠ x : G ⧸ K, dosetInd k K a x.out * dosetInd k K b (x.out⁻¹ * g) = _
  rw [finsum_congr hterm, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_]
  · rw [Finset.sum_congr rfl (fun x hx => if_pos (hfin.mem_toFinset.1 hx))]
    simp [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  · intro x hx
    rw [Function.mem_support] at hx
    rw [Set.Finite.coe_toFinset]
    by_contra h
    exact hx (if_neg h)
end Formalism.UG.P
