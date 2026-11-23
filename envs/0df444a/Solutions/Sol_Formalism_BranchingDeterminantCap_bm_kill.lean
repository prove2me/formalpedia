-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_kill
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:31.695224+00:00
-- url     : https://prove2.me/submissions/acda156b-25ca-453e-89f1-1da18d6caf1a

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_list_eigen
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmE_comm_apply
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmE_comp_ne_iff
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmE_sep_op
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
theorem _root_.solution {R σ B : Type*} [CommRing R] [IsDomain R] [CharZero R] [AddCommMonoid B] (w : σ → B) (ω : B → ℤ)
    (C : ℤ → Module.End R (MvPolynomial σ R)) (W : Submodule R (MvPolynomial σ R)) (χ : B → ℤ → ℤ)
    (admitted : B → Prop) (hCC : ∀ u v, Commute (C u) (C v))
    (hCc : ∀ u β, Commute (weightedHomogeneousComponent w β : Module.End R (MvPolynomial σ R)) (C u))
    (hCW : ∀ u, ∀ G ∈ W, C u G ∈ W)
    (hEig : ∀ G ∈ W, ∀ β, weightedHomogeneousComponent w β G ≠ 0 →
      (∀ β', weightedHomogeneousComponent w β' G ≠ 0 → ω β' ≤ ω β) →
      admitted β ∧ ∀ u, C u (weightedHomogeneousComponent w β G) =
        ((χ β u : ℤ) : R) • weightedHomogeneousComponent w β G)
    (hSep : ∀ β β', admitted β → admitted β' → β ≠ β' → ∃ u, χ β u ≠ χ β' u)
    (ℓ : List ℤ) (b : B) (hℓ : ∀ β, admitted β → β ≠ b → ∃ u ∈ ℓ, χ β u = 0)
    (G : MvPolynomial σ R) (hG : G ∈ W) (hb : weightedHomogeneousComponent w b G = 0) :
    (ℓ.map C).prod G = 0 := by
  classical
  have main : ∀ (k : ℕ) (G : MvPolynomial σ R), G ∈ W →
      (G.support.image (Finsupp.weight w)).card ≤ k →
      weightedHomogeneousComponent w b G = 0 → (ℓ.map C).prod G = 0 := by
    intro k
    induction k with
    | zero =>
      intro G _ hc _
      have h1 := Finset.card_eq_zero.1 (Nat.le_zero.1 hc)
      rw [Finset.image_eq_empty] at h1
      rw [support_eq_empty.1 h1, map_zero]
    | succ k ih =>
      intro G hG hc hb
      rcases (G.support.image (Finsupp.weight w)).eq_empty_or_nonempty with h0 | hne
      · rw [Finset.image_eq_empty] at h0
        rw [support_eq_empty.1 h0, map_zero]
      obtain ⟨β0, hβ0, hmax⟩ := Finset.exists_max_image _ ω hne
      have hF0 : weightedHomogeneousComponent w β0 G ≠ 0 := (bmE_comp_ne_iff w G β0).2 hβ0
      obtain ⟨hA0, hE0⟩ := hEig G hG β0 hF0
        (fun β' hβ' => hmax β' ((bmE_comp_ne_iff w G β').1 hβ'))
      have hne0 : β0 ≠ b := fun h => hF0 (h ▸ hb)
      obtain ⟨Q, q, hq, hQC, hQc, hQW, hQe, hQk⟩ :=
        bmE_sep_op w ω C W χ admitted hCC hCc hCW hEig hSep _
          ((G.support.image (Finsupp.weight w)).erase β0) β0 le_rfl hA0 (Finset.notMem_erase _ _)
      have hQG : ∀ u, C u (Q G) = ((χ β0 u : ℤ) : R) • Q G := by
        intro u
        have h1 : Q (C u G - ((χ β0 u : ℤ) : R) • G) = 0 := by
          apply hQk _ (W.sub_mem (hCW u G hG) (W.smul_mem _ hG))
          intro β hβ
          rw [map_sub, map_smul, bmE_comm_apply (hCc u β)] at hβ
          refine Finset.mem_erase.2 ⟨?_, (bmE_comp_ne_iff w G β).1 (fun h0 => hβ (by rw [h0]; simp))⟩
          rintro rfl
          exact hβ (by rw [hE0 u, sub_self])
        rw [map_sub, map_smul, sub_eq_zero] at h1
        rw [← bmE_comm_apply (hQC u) G, h1]
      have hZ1 : (ℓ.map C).prod (Q G) = 0 := by
        rw [bm_list_eigen C (χ β0) (Q G) hQG ℓ]
        obtain ⟨u, hu, hχ⟩ := hℓ β0 hA0 hne0
        have h0 : (ℓ.map (χ β0)).prod = 0 := List.prod_eq_zero (List.mem_map.2 ⟨u, hu, hχ⟩)
        rw [h0]
        simp
      have hcomp : ∀ β, weightedHomogeneousComponent w β (((q : ℤ) : R) • G - Q G) =
          ((q : ℤ) : R) • weightedHomogeneousComponent w β G -
            Q (weightedHomogeneousComponent w β G) := by
        intro β
        rw [map_sub, map_smul, bmE_comm_apply (hQc β)]
      have hsub : ((((q : ℤ) : R) • G - Q G).support.image (Finsupp.weight w)) ⊆
          (G.support.image (Finsupp.weight w)).erase β0 := by
        intro β hβ
        have hβ' := (bmE_comp_ne_iff w _ β).2 hβ
        rw [hcomp] at hβ'
        refine Finset.mem_erase.2 ⟨?_, (bmE_comp_ne_iff w G β).1 (fun h0 => hβ' (by rw [h0]; simp))⟩
        rintro rfl
        exact hβ' (by rw [hQe _ hE0, sub_self])
      have hcard : ((((q : ℤ) : R) • G - Q G).support.image (Finsupp.weight w)).card ≤ k := by
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hβ0] at h1
        omega
      have h2 := ih (((q : ℤ) : R) • G - Q G) (W.sub_mem (W.smul_mem _ hG) (hQW G hG)) hcard
        (by rw [hcomp, hb]; simp)
      rw [map_sub, map_smul, hZ1, sub_zero] at h2
      exact (smul_eq_zero.1 h2).resolve_left (Int.cast_ne_zero.2 hq)
  exact main _ G hG le_rfl hb
end Formalism.BranchingDeterminantCap
