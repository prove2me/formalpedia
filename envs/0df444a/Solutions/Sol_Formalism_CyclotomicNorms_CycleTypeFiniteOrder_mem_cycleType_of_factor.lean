-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.mem_cycleType_of_factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:47.571797+00:00
-- url     : https://prove2.me/submissions/1060a8b1-9956-4d70-99bc-f534aba0159f

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_mem_rootsBar
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_iter_eq
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_exists_dvd
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_eval_pow_iter
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
variable {g : ℕ} [hg : Fact g.Prime] {N : ℕ} {f : (ZMod g)[X]}
variable {r : Fin N → Fbar g} {σ : Equiv.Perm (Fin N)}
namespace Formalism.CyclotomicNorms.CycleTypeFiniteOrder
theorem _root_.solution (hf : GoodPoly N f) (hr : Function.Injective r)
    (hrf : Finset.univ.val.map r = rootsBar f) (hσ : ∀ i, r (σ i) = r i ^ g)
    (q : (ZMod g)[X]) (hq : Irreducible q) (hqf : q ∣ f) (hp : q.natDegree.Prime) :
    q.natDegree ∈ σ.cycleType := by
  classical
  set alg := algebraMap (ZMod g) (Fbar g)
  have hqdeg : (q.map alg).degree ≠ 0 := by
    rw [degree_map]; intro h
    have := natDegree_eq_of_degree_eq_some h
    exact hp.ne_zero this
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (q.map alg) hqdeg
  have hαf : α ∈ rootsBar f := by
    rw [mem_rootsBar hf]
    obtain ⟨c, hc⟩ := hqf
    rw [hc, Polynomial.map_mul, eval_mul, hα.eq_zero, zero_mul]
  obtain ⟨i0, -, hi0⟩ := Multiset.mem_map.mp (hrf ▸ hαf : α ∈ Finset.univ.val.map r)
  set O := Finset.univ.filter (fun j => σ.SameCycle i0 j) with hO
  have hOs : ∀ j ∈ O, σ j ∈ O := by
    intro j hj
    simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact Equiv.Perm.sameCycle_apply_right.mpr hj
  have hi0O : i0 ∈ O := by
    rw [hO, Finset.mem_filter]; exact ⟨Finset.mem_univ _, Equiv.Perm.SameCycle.refl _ _⟩
  obtain ⟨Q, hQm, hQf, hQd, hQr⟩ := exists_dvd hf hrf hσ O hOs

  have hqQ : q ∣ Q := by
    by_contra hnd
    obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hq).mpr hnd
    have := congrArg (fun p => (p.map alg).eval α) hab
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, eval_add, eval_mul,
      eval_one] at this
    rw [hα.eq_zero, ← hi0, hQr i0 hi0O] at this
    simp at this
  have hle1 : q.natDegree ≤ O.card := hQd ▸ natDegree_le_of_dvd hqQ hQm.ne_zero
  have hle2 : O.card ≤ q.natDegree := by
    have hq0 : q.map alg ≠ 0 := (Polynomial.map_ne_zero_iff alg.injective).mpr hq.ne_zero
    have hsub : O.image r ⊆ (q.map alg).roots.toFinset := by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨n, hn⟩ := hj.exists_nat_pow_eq
      rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot, ← hn, iter_eq hσ, hi0]
      exact eval_pow_iter q α hα.eq_zero n
    calc O.card = (O.image r).card := (Finset.card_image_of_injective O hr).symm
      _ ≤ (q.map alg).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ (q.map alg).roots.card := Multiset.toFinset_card_le _
      _ ≤ (q.map alg).natDegree := card_roots' _
      _ = q.natDegree := natDegree_map _
  have hcard : O.card = q.natDegree := le_antisymm hle2 hle1
  have hmove : σ i0 ≠ i0 := by
    intro hfix
    have : O = {i0} := by
      ext j
      simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; exact (h.eq_of_left hfix).symm
      · rintro rfl; exact Equiv.Perm.SameCycle.refl _ _
    rw [this, Finset.card_singleton] at hcard
    exact hp.one_lt.ne hcard
  have hsupp : (σ.cycleOf i0).support = O := by
    ext j
    rw [Equiv.Perm.mem_support_cycleOf_iff]
    simp [hO, Equiv.Perm.mem_support, hmove]
  rw [Equiv.Perm.cycleType_def, Multiset.mem_map]
  refine ⟨σ.cycleOf i0, ?_, ?_⟩
  · exact Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr hmove)
  · simp [hsupp, hcard]
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
