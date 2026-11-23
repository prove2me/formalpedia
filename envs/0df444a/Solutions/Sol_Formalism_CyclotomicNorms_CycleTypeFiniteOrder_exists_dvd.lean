-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.exists_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:01:39.311615+00:00
-- url     : https://prove2.me/submissions/b3d600da-04d7-4724-ac30-1c69910e39c5

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_mem_range_of_pow_eq
import Theorems.Thm_P2M_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_map_ne_zero__0cc604524e09
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
variable {r : Fin N → Fbar g} {σ : Equiv.Perm (Fin N)}
namespace Formalism.CyclotomicNorms.CycleTypeFiniteOrder
theorem _root_.solution (hf : GoodPoly N f) (hrf : Finset.univ.val.map r = rootsBar f)
    (hσ : ∀ i, r (σ i) = r i ^ g) (S : Finset (Fin N)) (hS : ∀ i ∈ S, σ i ∈ S) :
    ∃ Q : (ZMod g)[X], Q.Monic ∧ Q ∣ f ∧ Q.natDegree = S.card ∧
      ∀ i ∈ S, (Q.map (algebraMap (ZMod g) (Fbar g))).eval (r i) = 0 := by
  classical
  set P : (Fbar g)[X] := ((S.val.map r).map fun a => X - C a).prod with hPdef
  have hPm : P.Monic := monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  have hSσ : S.map σ.toEmbedding = S :=
    Finset.eq_of_subset_of_card_le (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy; exact hS x hx) (by rw [Finset.card_map])
  have hfrob : P.map (frobenius (Fbar g) g) = P := by
    rw [hPdef, Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    conv_rhs => rw [← hSσ]
    rw [Finset.map_val, Multiset.map_map, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro i _
    simp [frobenius_def, hσ]
  have hlift : P ∈ lifts (algebraMap (ZMod g) (Fbar g)) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    apply mem_range_of_pow_eq
    have := congrArg (fun p => p.coeff n) hfrob
    simpa [coeff_map, frobenius_def] using this
  obtain ⟨Q, hQP, hQd, hQm⟩ := lifts_and_natDegree_eq_and_monic hlift hPm
  have hPdvd : P ∣ f.map (algebraMap (ZMod g) (Fbar g)) := by
    rw [hPdef, Multiset.prod_X_sub_C_dvd_iff_le_roots (map_ne_zero' hf)]
    change S.val.map r ≤ rootsBar f
    rw [← hrf]
    exact Multiset.map_le_map (Finset.val_le_iff.mpr (Finset.subset_univ S))
  refine ⟨Q, hQm, ?_, ?_, ?_⟩
  · rw [← map_dvd_map (algebraMap (ZMod g) (Fbar g)) (algebraMap (ZMod g) (Fbar g)).injective hQm, hQP]
    exact hPdvd
  · rw [hQd, hPdef, natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map, Finset.card_val]
  · intro i hi
    rw [hQP]
    have : r i ∈ P.roots := by
      rw [hPdef, roots_multiset_prod_X_sub_C]; exact Multiset.mem_map_of_mem _ hi
    exact (mem_roots hPm.ne_zero).mp this
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
