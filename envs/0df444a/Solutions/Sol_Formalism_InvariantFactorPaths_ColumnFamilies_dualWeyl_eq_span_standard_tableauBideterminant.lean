-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.dualWeyl_eq_span_standard_tableauBideterminant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:28:08.688811+00:00
-- url     : https://prove2.me/submissions/48d2be30-1ffb-46ff-b25e-694e2f40d1db

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
import Theorems.Thm_Formalism_GradedWeylDivisibility_colSums
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcassem_sub_lt
import Theorems.Thm_Formalism_GradedWeylDivisibility_leadInterlaced
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_exp_surj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (B : Type) [CommRing B] [IsDomain B] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    dualWeyl B n n (qa_nu mu) =
      Submodule.span B (Set.range fun I : {I : TIdx mu // StdT I} => qa_P B I.1) := by
  apply le_antisymm
  · suffices key : ∀ d : (colLex n n).syn, ∀ f ∈ dualWeyl B n n (qa_nu mu),
        (colLex n n).toSyn ((colLex n n).degree f) = d →
          f ∈ Submodule.span B (Set.range fun I : {I : TIdx mu // StdT I} => qa_P B I.1) by
      intro f hf
      exact key _ f hf rfl
    intro d
    induction d using WellFoundedLT.induction with
    | _ d ih =>
      intro f hf hd
      by_cases hf0 : f = 0
      · rw [hf0]; exact Submodule.zero_mem _
      have hint : Interlaced ((colLex n n).degree f) := leadInterlaced B n n _ f hf hf0
      have hcol := colSums B n n _ f hf _ (((colLex n n).degree_mem_support_iff f).mpr hf0)
      obtain ⟨I, hI, he⟩ := qa_exp_surj hmu _ ⟨hint, hcol⟩
      have hbS : qa_P B I ∈ Submodule.span B (Set.range fun I : {I : TIdx mu // StdT I} => qa_P B I.1) :=
        Submodule.subset_span ⟨⟨I, hI⟩, rfl⟩
      have hdecomp : f = (f - (colLex n n).leadingCoeff f • qa_P B I) + (colLex n n).leadingCoeff f • qa_P B I := by
        abel
      rw [hdecomp]
      refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hbS)
      by_cases h0 : f - (colLex n n).leadingCoeff f • qa_P B I = 0
      · rw [h0]; exact Submodule.zero_mem _
      have hlt := lcassem_sub_lt (colLex n n) (f := f) (g := qa_P B I) ((tableauBideterminant_degree_leadingCoeff B I).1.trans he)
        (tableauBideterminant_degree_leadingCoeff B I).2 h0
      exact ih _ (hd ▸ hlt) _ (Submodule.sub_mem _ hf (Submodule.smul_mem _ _ (tableauBideterminant_mem_dualWeyl B hmu I))) rfl
  · rw [Submodule.span_le]
    rintro _ ⟨I, rfl⟩
    exact tableauBideterminant_mem_dualWeyl B hmu I.1
end Formalism.InvariantFactorPaths.ColumnFamilies
