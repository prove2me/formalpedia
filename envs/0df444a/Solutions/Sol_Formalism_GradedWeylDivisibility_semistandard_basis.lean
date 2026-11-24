-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.semistandard_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:32.851422+00:00
-- url     : https://prove2.me/submissions/aef925b3-1313-444c-bb62-bbc3203b8509

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SSBasis
import Theorems.Thm_Formalism_GradedWeylDivisibility_bidetMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_colSums
import Theorems.Thm_Formalism_GradedWeylDivisibility_column_lex_bideterminant
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcassem_sub_lt
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldbasis_bidet_rowHom
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldbasis_linearIndependent
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldbasis_rowWt_bidetExp
import Theorems.Thm_Formalism_GradedWeylDivisibility_leadInterlaced
import Theorems.Thm_Formalism_GradedWeylDivisibility_sSYTExists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.GradedWeylDivisibility
open scoped MonomialOrder
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : SSBasis := by
  intro R _ _ k n ν
  have hex : ∀ m : ssIdx k n ν, ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ i, sz i ≤ n)
      (I : ∀ i, Fin (sz i) → Fin k),
      shapeDeg sz = ν ∧ (∀ i, StrictMono (I i)) ∧ bidetExp sz hsz I = m.1 := fun m =>
    sSYTExists k n ν m.1 m.2.2 m.2.1
  choose K sz hsz I hshape hmono hexp using hex
  set b : ssIdx k n ν → MvPolynomial (Fin k × Fin n) R := fun m => bideterminant R (sz m) (hsz m) (I m) with hb
  have hdeg : ∀ m, (colLex k n).degree (b m) = m.1 := fun m =>
    (column_lex_bideterminant R k n (K m) (sz m) (hsz m) (I m) (hmono m)).1.trans (hexp m)
  have hlc : ∀ m, (colLex k n).leadingCoeff (b m) = 1 := fun m =>
    (column_lex_bideterminant R k n (K m) (sz m) (hsz m) (I m) (hmono m)).2
  have hmem : ∀ m, b m ∈ dualWeyl R k n ν := fun m => by
    have := bidetMem R k n (K m) (sz m) (hsz m) (I m)
    rw [hshape m] at this
    exact this
  refine ⟨b, ⟨?_, ?_, ?_⟩, fun m => ⟨hdeg m, hlc m, K m, sz m, hsz m, I m, hshape m, hmono m, rfl⟩⟩
  ·
    refine ldbasis_linearIndependent (colLex k n) b ?_ hlc
    intro m m' h
    exact Subtype.ext ((hdeg m).symm.trans (h.trans (hdeg m')))
  ·
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      exact hmem m
    · suffices key : ∀ d : (colLex k n).syn, ∀ f ∈ dualWeyl R k n ν,
          (colLex k n).toSyn ((colLex k n).degree f) = d → f ∈ Submodule.span R (Set.range b) by
        intro f hf
        exact key _ f hf rfl
      intro d
      induction d using WellFoundedLT.induction with
      | _ d ih =>
        intro f hf hd
        by_cases hf0 : f = 0
        · rw [hf0]; exact Submodule.zero_mem _
        set m := (colLex k n).degree f with hm
        have hint : Interlaced m := leadInterlaced R k n ν f hf hf0
        have hcol : ∀ t : Fin n, ∑ a : Fin k, m (a, t) = ν t :=
          colSums R k n ν f hf m (((colLex k n).degree_mem_support_iff f).mpr hf0)
        set mi : ssIdx k n ν := ⟨m, hint, hcol⟩ with hmi
        have hbS : b mi ∈ Submodule.span R (Set.range b) := Submodule.subset_span ⟨mi, rfl⟩
        set f' := f - (colLex k n).leadingCoeff f • b mi with hf'
        have hf'mem : f' ∈ dualWeyl R k n ν :=
          Submodule.sub_mem _ hf (Submodule.smul_mem _ _ (hmem mi))
        have hdecomp : f = f' + (colLex k n).leadingCoeff f • b mi := by
          rw [hf']; abel
        rw [hdecomp]
        refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hbS)
        by_cases h0 : f' = 0
        · rw [h0]; exact Submodule.zero_mem _
        have hlt := lcassem_sub_lt (colLex k n) (f := f) (g := b mi) (hdeg mi) (hlc mi) h0
        exact ih _ (hd ▸ hlt) f' hf'mem rfl
  ·
    intro m
    show IsWeightedHomogeneous (rowW k n) (bideterminant R (sz m) (hsz m) (I m)) (rowWt m.1)
    rw [← hexp m, ldbasis_rowWt_bidetExp]
    exact ldbasis_bidet_rowHom R (sz m) (hsz m) (I m)
end Formalism.GradedWeylDivisibility
