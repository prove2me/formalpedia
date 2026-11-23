-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.exists_index
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:47.339536+00:00
-- url     : https://prove2.me/submissions/b5544931-5e74-4f33-875b-b35cce2af204

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_rootsBar_nodup
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_rootsBar_card
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_pow_mem
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]
variable {N : ℕ} {f : (ZMod g)[X]}
namespace Formalism.CyclotomicNorms.CycleTypeFiniteOrder
theorem _root_.solution (hf : GoodPoly N f) : ∃ (r : Fin N → Fbar g) (σ : Equiv.Perm (Fin N)),
    Function.Injective r ∧ Finset.univ.val.map r = rootsBar f ∧ (∀ i, r (σ i) = r i ^ g) := by
  classical
  set Rt := (rootsBar f).toFinset
  have hc : Fintype.card Rt = N := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup (rootsBar_nodup hf), rootsBar_card hf]
  set e := (Fintype.equivFinOfCardEq hc).symm
  set r : Fin N → Fbar g := fun i => (e i : Fbar g) with hrdef
  have hr : Function.Injective r := fun i j h => e.injective (Subtype.ext h)
  have hmem : ∀ i, r i ∈ rootsBar f := fun i => Multiset.mem_toFinset.mp (e i).2
  have hsurj : ∀ x ∈ rootsBar f, ∃ i, r i = x := fun x hx =>
    ⟨e.symm ⟨x, Multiset.mem_toFinset.mpr hx⟩, by simp [r]⟩
  choose s hs using fun i => hsurj _ (pow_mem hf (hmem i))
  have hsinj : Function.Injective s := fun i j h => hr (frobenius_inj (Fbar g) g (by
    simp only [frobenius_def]; rw [← hs i, ← hs j, h]))
  refine ⟨r, Equiv.ofBijective s (Finite.injective_iff_bijective.mp hsinj), hr, ?_,
    fun i => (hs i)⟩
  refine (Multiset.Nodup.ext (Multiset.Nodup.map hr Finset.univ.nodup) (rootsBar_nodup hf)).mpr ?_
  intro x; constructor
  · intro h; obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp h; exact hmem i
  · intro h; obtain ⟨i, rfl⟩ := hsurj x h; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
