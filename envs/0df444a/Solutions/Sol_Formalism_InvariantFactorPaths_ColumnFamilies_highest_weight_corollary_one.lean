-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.highest_weight_corollary_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:17:46.486645+00:00
-- url     : https://prove2.me/submissions/c0a42cf7-df53-49b9-a063-9743f31dda36

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhCountAll
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_InducedSectionsSpanStatement
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_reduce
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_span_transfer
import Theorems.Thm_Formalism_GradedWeylDivisibility_colSums
import Theorems.Thm_Formalism_GradedWeylDivisibility_leadInterlaced
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_standardMonomialSpanDomain
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_bidet_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_brk_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_le_last
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_span_le
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_zero_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
private theorem antitone_of_step_lemma {n : ℕ} (g : Fin n → ℤ) (h : ∀ l j : Fin n, (j : ℕ) = l + 1 → g j ≤ g l) :
    Antitone g := by
  intro a b hab
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [Fin.mk_le_mk] at hab
  revert hb
  induction b, hab using Nat.le_induction with
  | base => intro hb; exact le_rfl
  | succ b hab ih =>
    intro hb
    exact (h ⟨b, by omega⟩ ⟨b + 1, hb⟩ rfl).trans (ih (by omega))
end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : InducedSectionsSpanStatement := by
  intro n _ mu R _ _ _
  constructor
  · intro hmu
    apply Set.Subset.antisymm
    · intro f hf
      obtain ⟨k, Q, hk, hfQ, hQ⟩ := qh_reduce mu f hf
      rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain R n n] at hQ
      rw [SetLike.mem_coe, hfQ]
      refine qh_span_transfer (Submodule.span R (Set.range fun I : TIdx mu => mapCoord R (brk mu I))) _ _ ?_ Q hQ
      rintro x ⟨K, sz, hsz, I, hsh, rfl⟩
      exact qh_bidet_mem hmu k (hk _) sz hsz I (fun t => by rw [hsh]; exact Int.toNat_of_nonneg (hk t))
    · exact qh_span_le (by rintro _ ⟨I, rfl⟩; exact qh_brk_mem hmu I)
  · intro hmu
    ext f
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hf
      obtain ⟨k, Q, hk, hfQ, hQ⟩ := qh_reduce mu f hf
      by_contra hf0
      have hQ0 : Q ≠ 0 := by
        rintro rfl
        apply hf0
        rw [hfQ]
        simp
      apply hmu
      have hInt := Formalism.GradedWeylDivisibility.leadInterlaced R n n _ Q hQ hQ0
      have hcol := Formalism.GradedWeylDivisibility.colSums R n n _ Q hQ _ (MonomialOrder.degree_mem_support (m := Formalism.GradedWeylDivisibility.colLex n n) hQ0)
      set m := (Formalism.GradedWeylDivisibility.colLex n n).degree Q
      apply antitone_of_step_lemma mu
      intro l j hlj
      have hI : Formalism.GradedWeylDivisibility.InterlacedAt 0 l j m := hInt l j hlj
      have hI2 := hI (lastIdx n)
      have e1 : (∑ b : Fin n with b ≤ lastIdx n, m (b, j)) = ∑ b, m (b, j) := by
        rw [Finset.filter_true_of_mem (fun b _ => qh_le_last b)]
      have e2 : (∑ b : Fin n with b < lastIdx n, m (b, l)) ≤ ∑ b, m (b, l) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      have cj := hcol j
      have cl := hcol l
      have tj := Int.toNat_of_nonneg (hk j)
      have tl := Int.toNat_of_nonneg (hk l)
      omega
    · rintro rfl
      exact qh_zero_mem mu
end Formalism.InvariantFactorPaths.ColumnFamilies
