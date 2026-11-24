-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lower_triangular_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:44.706329+00:00
-- url     : https://prove2.me/submissions/0eb6bc9d-6f0a-4d36-966f-b9fdb7a0e5e6

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LowerTriangularIntegral
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lre_intQ_apply
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lre_lowerTri
import Theorems.Thm_Formalism_GradedWeylDivisibility_bidetMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_colSums
import Theorems.Thm_Formalism_GradedWeylDivisibility_column_lex_bideterminant
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcassem_sub_lt
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldlat_map_bidet
import Theorems.Thm_Formalism_GradedWeylDivisibility_leadInterlaced
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_sSYTExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
open scoped MonomialOrder
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution : LowerTriIntegral := by
  intro r n ν
  suffices key : ∀ d : (colLex r n).syn, ∀ Q ∈ dualWeyl ℚ r n ν,
      (∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, coeff e Q = z) →
      (colLex r n).toSyn ((colLex r n).degree Q) = d →
      ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, Q = intQ r n Q' by
    intro Q hQ hint
    exact key _ Q hQ hint rfl
  intro d
  induction d using WellFoundedLT.induction with
  | _ d ih =>
    intro f hf hz hd
    by_cases hf0 : f = 0
    · exact ⟨0, by rw [hf0, map_zero]⟩
    set m := (colLex r n).degree f with hm
    have hint : Interlaced m := leadInterlaced ℚ r n ν f hf hf0
    have hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t :=
      colSums ℚ r n ν f hf m (((colLex r n).degree_mem_support_iff f).mpr hf0)
    obtain ⟨K, sz, hsz, I, hshape, hmono, hexp⟩ := sSYTExists r n ν m hcol hint
    obtain ⟨hbdeg, hblc⟩ := column_lex_bideterminant ℚ r n K sz hsz I hmono
    have hbmap : bideterminant ℚ sz hsz I = intQ r n (bideterminant ℤ sz hsz I) := by
      rw [lre_intQ_apply, ldlat_map_bidet]
    have hbmem : bideterminant ℚ sz hsz I ∈ dualWeyl ℚ r n ν := by
      have := bidetMem ℚ r n K sz hsz I
      rw [hshape] at this
      exact this
    have hmL : LowerTri m := by
      rw [← hexp]
      exact lre_lowerTri sz hsz I hmono
    obtain ⟨c, hc⟩ := hz m hmL
    have hlc : (colLex r n).leadingCoeff f = (c : ℚ) := hc
    have hf'mem : f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I ∈ dualWeyl ℚ r n ν :=
      Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hbmem)
    have hf'z : ∀ e : Fin r × Fin n →₀ ℕ, LowerTri e →
        ∃ z : ℤ, coeff e (f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I) = z := by
      intro e he
      obtain ⟨z, hz'⟩ := hz e he
      refine ⟨z - c * coeff e (bideterminant ℤ sz hsz I), ?_⟩
      rw [coeff_sub, coeff_smul, hz', hlc, hbmap, lre_intQ_apply, coeff_map]
      simp
    have hfin : ∃ Q'' : MvPolynomial (Fin r × Fin n) ℤ,
        f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I = intQ r n Q'' := by
      by_cases h0 : f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I = 0
      · exact ⟨0, by rw [h0, map_zero]⟩
      · have hlt := lcassem_sub_lt (colLex r n) (f := f) (g := bideterminant ℚ sz hsz I) (hbdeg.trans hexp) hblc h0
        exact ih _ (hd ▸ hlt) _ hf'mem hf'z rfl
    obtain ⟨Q'', hQ''⟩ := hfin
    refine ⟨Q'' + c • bideterminant ℤ sz hsz I, ?_⟩
    rw [map_add, map_smul, ← hQ'', ← hbmap, hlc, Int.cast_smul_eq_zsmul]
    abel
end Formalism.CohomologicalDescent.LR
