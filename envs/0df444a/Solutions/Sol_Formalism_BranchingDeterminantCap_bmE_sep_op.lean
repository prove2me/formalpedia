-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmE_sep_op
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:54.787478+00:00
-- url     : https://prove2.me/submissions/d0e806db-1ad0-42f7-b1f4-630eec2b7757

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmE_comm_apply
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmE_eq_zero_of_comp
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R σ B : Type*} [CommRing R] [AddCommMonoid B] (w : σ → B) (ω : B → ℤ)
    (C : ℤ → Module.End R (MvPolynomial σ R)) (W : Submodule R (MvPolynomial σ R)) (χ : B → ℤ → ℤ)
    (admitted : B → Prop) (hCC : ∀ u v, Commute (C u) (C v))
    (hCc : ∀ u β, Commute (weightedHomogeneousComponent w β : Module.End R (MvPolynomial σ R)) (C u))
    (hCW : ∀ u, ∀ G ∈ W, C u G ∈ W)
    (hEig : ∀ G ∈ W, ∀ β, weightedHomogeneousComponent w β G ≠ 0 →
      (∀ β', weightedHomogeneousComponent w β' G ≠ 0 → ω β' ≤ ω β) →
      admitted β ∧ ∀ u, C u (weightedHomogeneousComponent w β G) =
        ((χ β u : ℤ) : R) • weightedHomogeneousComponent w β G)
    (hSep : ∀ β β', admitted β → admitted β' → β ≠ β' → ∃ u, χ β u ≠ χ β' u) :
    ∀ (k : ℕ) (S : Finset B) (β0 : B), S.card ≤ k → admitted β0 → β0 ∉ S →
      ∃ (Q : Module.End R (MvPolynomial σ R)) (q : ℤ), q ≠ 0 ∧ (∀ u, Commute Q (C u)) ∧
        (∀ β, Commute (weightedHomogeneousComponent w β : Module.End R (MvPolynomial σ R)) Q) ∧
        (∀ G ∈ W, Q G ∈ W) ∧
        (∀ F, (∀ u, C u F = ((χ β0 u : ℤ) : R) • F) → Q F = ((q : ℤ) : R) • F) ∧
        (∀ G ∈ W, (∀ β, weightedHomogeneousComponent w β G ≠ 0 → β ∈ S) → Q G = 0) := by
  classical
  have hempty : ∀ β0 : B,
      ∃ (Q : Module.End R (MvPolynomial σ R)) (q : ℤ), q ≠ 0 ∧ (∀ u, Commute Q (C u)) ∧
        (∀ β, Commute (weightedHomogeneousComponent w β : Module.End R (MvPolynomial σ R)) Q) ∧
        (∀ G ∈ W, Q G ∈ W) ∧
        (∀ F, (∀ u, C u F = ((χ β0 u : ℤ) : R) • F) → Q F = ((q : ℤ) : R) • F) ∧
        (∀ G ∈ W, (∀ β, weightedHomogeneousComponent w β G ≠ 0 → β ∈ (∅ : Finset B)) → Q G = 0) := by
    intro β0
    refine ⟨1, 1, one_ne_zero, fun u => Commute.one_left _, fun β => Commute.one_right _,
      fun G hG => by simpa using hG, fun F _ => by simp, fun G _ hS => ?_⟩
    rw [bmE_eq_zero_of_comp w G (fun β => by_contra fun hne => absurd (hS β hne) (Finset.notMem_empty β))]
    simp
  intro k
  induction k with
  | zero =>
    intro S β0 hS _ _
    have hS0 : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hS)
    subst hS0
    exact hempty β0
  | succ k ih =>
    intro S β0 hS hA0 h0S
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact hempty β0
    obtain ⟨β1, hβ1, hmax⟩ := Finset.exists_max_image S ω hne
    have hcard : (S.erase β1).card ≤ k := by
      rw [Finset.card_erase_of_mem hβ1]; omega
    have h0S' : β0 ∉ S.erase β1 := fun h => h0S (Finset.mem_of_mem_erase h)
    obtain ⟨Q', q', hq', hQC, hQc, hQW, hQe, hQk⟩ := ih (S.erase β1) β0 hcard hA0 h0S'
    by_cases hA1 : admitted β1
    · have hne01 : β0 ≠ β1 := fun h => h0S (h ▸ hβ1)
      obtain ⟨u, hu⟩ := hSep β0 β1 hA0 hA1 hne01
      set T : Module.End R (MvPolynomial σ R) := C u - ((χ β1 u : ℤ) : R) • 1 with hT
      have hTa : ∀ G, T G = C u G - ((χ β1 u : ℤ) : R) • G := fun G => by simp [hT]
      refine ⟨Q' * T, q' * (χ β0 u - χ β1 u), mul_ne_zero hq' (sub_ne_zero.2 hu), ?_, ?_, ?_, ?_, ?_⟩
      · intro v
        exact (hQC v).mul_left ((hCC u v).sub_left ((Commute.one_left _).smul_left _))
      · intro β
        exact (hQc β).mul_right ((hCc u β).sub_right ((Commute.one_right _).smul_right _))
      · intro G hG
        rw [Module.End.mul_apply, hTa]
        exact hQW _ (W.sub_mem (hCW u G hG) (W.smul_mem _ hG))
      · intro F hF
        rw [Module.End.mul_apply, hTa, hF u, ← sub_smul, map_smul, hQe F hF, smul_smul]
        congr 1
        push_cast
        ring
      · intro G hG hS
        rw [Module.End.mul_apply]
        apply hQk (T G) (by rw [hTa]; exact W.sub_mem (hCW u G hG) (W.smul_mem _ hG))
        intro β hβ
        have hcomp : weightedHomogeneousComponent w β (T G) =
            T (weightedHomogeneousComponent w β G) := by
          rw [hTa, hTa, map_sub, map_smul, bmE_comm_apply (hCc u β)]
        rw [hcomp] at hβ
        have hβG : weightedHomogeneousComponent w β G ≠ 0 := fun h0 => hβ (by rw [h0, map_zero])
        refine Finset.mem_erase.2 ⟨?_, hS β hβG⟩
        rintro rfl
        apply hβ
        rw [hTa, (hEig G hG β hβG (fun β' hβ' => hmax β' (hS β' hβ'))).2 u, sub_self]
    · refine ⟨Q', q', hq', hQC, hQc, hQW, hQe, fun G hG hS => hQk G hG fun β hβ =>
        Finset.mem_erase.2 ⟨?_, hS β hβ⟩⟩
      rintro rfl
      exact hA1 (hEig G hG β hβ (fun β' hβ' => hmax β' (hS β' hβ'))).1
end Formalism.BranchingDeterminantCap
