-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.leadInterlaced_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:52.432025+00:00
-- url     : https://prove2.me/submissions/59312acf-ffd2-4c71-9200-95ea70681f3c

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LeadInterlaced
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclint_degreeOf_none_rename_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial
noncomputable section
namespace Formalism.GradedWeylDivisibility
private theorem colAddGen_eq_rename_some_of_mem_dualWeyl {B : Type*} [CommRing B] {r n : ℕ}
    {ν : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) B} (hf : f ∈ dualWeyl B r n ν)
    {l j : Fin n} (hlj : l < j) :
    colAddGen B l j f = rename some f := by
  unfold dualWeyl at hf
  rw [Submodule.mem_inf] at hf
  have h := hf.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply] at h
  exact sub_eq_zero.mp (h l j hlj)
end Formalism.GradedWeylDivisibility
end
end

set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (h1 : CompDeg) (h2 : LeadComp) (h3 : TwoColumn) : LeadInterlaced := by
  intro B _ _ r n ν f hf hf0
  intro l j hlj
  have hlt : l < j := Fin.lt_iff_val_lt_val.2 (by omega)
  have hdeg : (colLex r n).degree
      (weightedHomogeneousComponent (pairW (r := r) l j)
        (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f) =
      (colLex r n).degree f :=
    h2 B r n (Fin r × Fin n →₀ ℕ) (pairW (r := r) l j) f
  have hcoeff : coeff ((colLex r n).degree f)
      (weightedHomogeneousComponent (pairW (r := r) l j)
        (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f) =
      coeff ((colLex r n).degree f) f := by
    rw [coeff_weightedHomogeneousComponent, if_pos rfl]
  have hg0 : weightedHomogeneousComponent (pairW (r := r) l j)
      (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f ≠ 0 := by
    intro h
    have hne : coeff ((colLex r n).degree f) f ≠ 0 :=
      (colLex r n).coeff_degree_ne_zero_iff.mpr hf0
    apply hne
    rw [← hcoeff, h, coeff_zero]
  have hcol : degreeOf none (colAddGen B l j f) ≤ 0 := by
    rw [colAddGen_eq_rename_some_of_mem_dualWeyl hf hlt, lclint_degreeOf_none_rename_some]
  have hcomp := h1 B r n l j
    (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) 0 f hcol
  have hhom := weightedHomogeneousComponent_isWeightedHomogeneous
    (w := pairW (r := r) l j)
    (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f
  have key := h3 B r n l j hlt 0 0
    (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) _ hg0 hhom
    (fun b hb => absurd hb (Nat.not_lt_zero _)) hcomp
  rw [hdeg] at key
  exact key
end Formalism.GradedWeylDivisibility
