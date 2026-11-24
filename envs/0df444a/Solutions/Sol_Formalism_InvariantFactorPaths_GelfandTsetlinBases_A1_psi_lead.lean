-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.psi_lead
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:14:18.624635+00:00
-- url     : https://prove2.me/submissions/7356ae1d-f119-4a8a-9764-229fbfbe332c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_LeadAt_prod
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_weight_wt
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_col_lead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_isIndex_can
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_sum_Dc
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_isPath_trunc
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_path_finite
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_pathProductDegrees


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
theorem _root_.solution (R : Type) [CommRing R] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ (N + 1)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      LeadAt (wt n N (isVec N)) (rho n N (isVec N) (DD μ N))
        (psiPath R isVec μ (N + 1) (canIdx (μ (N + 1))))
        ((ε : MvPolynomial (ℕ × Fin n) R) * psiPath R isVec μ N (canIdx (μ N)) * monomial (DD μ N) 1) := by
  classical
  have hp0 := isPath_trunc hp
  obtain ⟨hfin1, -⟩ := Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathProductDegrees R n (N + 1) isVec B μ _ hp (isIndex_can _)
  obtain ⟨hfin0, -⟩ := Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathProductDegrees R n N isVec B μ _ hp0 (isIndex_can _)
  have hchg := Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.path_finite hp (Nat.lt_succ_self N)
  obtain ⟨S, hS1, hS0, hSc⟩ : ∃ S : Finset ℤ,
      Function.mulSupport (fun c : ℤ =>
        Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec μ c (XR R n) (N + 1) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ (N + 1)) c)) ⊆ ↑S ∧
      Function.mulSupport (fun c : ℤ =>
        Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec μ c (XR R n) N (Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ N) c)) ⊆ ↑S ∧
      ∀ c, Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (N + 1)) c ≠ Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ N) c → c ∈ S :=
    ⟨hfin1.toFinset ∪ hfin0.toFinset ∪ hchg.toFinset,
      fun c hc => Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_union_left _ (hfin1.mem_toFinset.mpr hc))),
      fun c hc => Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_union_right _ (hfin0.mem_toFinset.mpr hc))),
      fun c hc => Finset.mem_union_right _ (hchg.mem_toFinset.mpr hc)⟩
  choose a ha hL using fun c => col_lead R hp c
  have e1 : Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath R isVec μ (N + 1) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ (N + 1))) =
      ∏ c ∈ S, Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec μ c (XR R n) (N + 1) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ (N + 1)) c) :=
    finprod_eq_prod_of_mulSupport_subset _ hS1
  have e0 : Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath R isVec μ N (Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ N)) =
      ∏ c ∈ S, Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec μ c (XR R n) N (Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ N) c) :=
    finprod_eq_prod_of_mulSupport_subset _ hS0
  have hsum : ∑ c ∈ S, Dc μ N c = DD μ N := sum_Dc hp S hSc
  have hlev : ∑ c ∈ S, Finsupp.weight (wt n N (isVec N)) (Dc μ N c) =
      rho n N (isVec N) (DD μ N) := by
    rw [← map_sum, hsum, weight_wt]
  have hterm : ∏ c ∈ S, ((a c : MvPolynomial (ℕ × Fin n) R) *
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec μ c (XR R n) N (Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ N) c) * monomial (Dc μ N c) 1) =
      ((∏ c ∈ S, a c : ℤ) : MvPolynomial (ℕ × Fin n) R) * Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath R isVec μ N (Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ N)) *
        monomial (DD μ N) 1 := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Int.cast_prod, e0, ← hsum, monomial_sum_one]
  have hprod := Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.LeadAt.prod S (fun c => Finsupp.weight (wt n N (isVec N)) (Dc μ N c))
    (fun c => Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec μ c (XR R n) (N + 1) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ (N + 1)) c))
    (fun c => (a c : MvPolynomial (ℕ × Fin n) R) *
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec μ c (XR R n) N (Formalism.InvariantFactorPaths.GelfandTsetlinBases.canIdx (μ N) c) * monomial (Dc μ N c) 1)
    (fun c _ => hL c)
  rw [hlev, hterm, ← e1] at hprod
  refine ⟨∏ c ∈ S, a c, ?_, hprod⟩
  refine Finset.prod_induction _ (fun x : ℤ => x = 1 ∨ x = -1) ?_ (Or.inl rfl) (fun c _ => ha c)
  intro x y hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
