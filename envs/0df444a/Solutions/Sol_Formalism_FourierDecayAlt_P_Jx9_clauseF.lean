-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx9.clauseF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:56.232788+00:00
-- url     : https://prove2.me/submissions/ba555558-ef4f-411a-80ec-585cc00fd49b

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_psd_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_psd_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx9
variable {X K : Type} [CommRing K]
open Classical
namespace Formalism.FourierDecayAlt.P.Jx9
theorem _root_.solution (R : Subring K) (F' : Finset X) (Θ : K → X → X → ℂ) (Bk : X → X → ℂ)
    (hper : ∀ x, ∀ r ∈ R, Θ (x + r) = Θ x) (hpsd : ∀ x, A5.IsPSD F' (Θ x))
    (hfin : {x : K ⧸ R.toAddSubgroup | ∃ h ∈ F', ∃ h' ∈ F', Θ (Quotient.out x) h h' ≠ 0}.Finite)
    (hsum : A5.IsPSD F' (fun h h' => Bk h h' - ∑ᶠ x : K ⧸ R.toAddSubgroup, Θ (Quotient.out x) h h'))
    (T : Finset K) (hT : ∀ y ∈ T, ∀ y' ∈ T, y - y' ∈ R → y = y') :
    A5.IsPSD F' (fun h h' => Bk h h' - ∑ y ∈ T, Θ y h h') := by
  set cls : K → K ⧸ R.toAddSubgroup := fun y => (y : K ⧸ R.toAddSubgroup) with hcls
  have hout : ∀ y : K, Θ (Quotient.out (cls y)) = Θ y := by
    intro y
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add R.toAddSubgroup y
    rw [hcls]; simp only
    rw [hr]; exact hper y r r.2
  have hinj : Set.InjOn cls T := by
    intro y hy y' hy' e
    apply hT y hy y' hy'
    have := (QuotientAddGroup.eq (s := R.toAddSubgroup)).1 e
    have h2 : y - y' = -(-y + y') := by ring
    rw [h2]; exact R.toAddSubgroup.neg_mem this
  set Xf : Finset (K ⧸ R.toAddSubgroup) := hfin.toFinset ∪ T.image cls with hXf
  have h1 : ∀ h ∈ F', ∀ h' ∈ F', ∑ᶠ x : K ⧸ R.toAddSubgroup, Θ (Quotient.out x) h h' =
      ∑ x ∈ Xf, Θ (Quotient.out x) h h' := by
    intro h hh h' hh'
    apply finsum_eq_sum_of_support_subset
    intro x hx
    simp only [hXf, coe_union, Set.mem_union]
    left
    simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    exact ⟨h, hh, h', hh', hx⟩
  have h2 : ∀ h h', ∑ y ∈ T, Θ y h h' = ∑ x ∈ T.image cls, Θ (Quotient.out x) h h' := by
    intro h h'
    rw [sum_image hinj]
    exact sum_congr rfl fun y _ => by rw [hout]
  have h3 := psd_add hsum (psd_sum (Xf \ T.image cls) (fun x => Θ (Quotient.out x)) fun x _ => hpsd _)
  refine psd_congr h3 ?_
  intro h hh h' hh'
  rw [h1 h hh h' hh', h2, ← sum_sdiff (show T.image cls ⊆ Xf from subset_union_right)]
  ring
end Formalism.FourierDecayAlt.P.Jx9
