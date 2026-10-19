-- Prove2me | solution 1 for ConnesRigidity.exists_infinite_pairwise_nonisomorphic_propertyT_icc_groups_with_isomorphic_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/1da05a99-a310-43c5-a12f-272b90123266

import Mathlib
import Definitions.Def_ConnesRigidity
import Theorems.Thm_ConnesRigidity_groupFactorsIsomorphic_symm
import Theorems.Thm_ConnesRigidity_groupFactorsIsomorphic_trans
import Theorems.Thm_ConnesRigidity_gamma_pairwise_nonisomorphic
import Theorems.Thm_ConnesRigidity_PaperAnalyticInput_lambda_propertyT
import Theorems.Thm_ConnesRigidity_PaperAnalyticInput_gamma_propertyT
import Theorems.Thm_ConnesRigidity_PaperAnalyticInput_lambda_icc
import Theorems.Thm_ConnesRigidity_PaperAnalyticInput_gamma_icc

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open ConnesRigidity
noncomputable section
namespace ConnesRigidity
theorem _root_.solution :
    ∃ (Λ : ConnesRigidity.CountableDiscreteGroup.{0})
      (Γ : ℕ → ConnesRigidity.CountableDiscreteGroup.{0}),
      Group.FG Λ ∧
      (∀ n, Group.FG (Γ n)) ∧
      ConnesRigidity.IsICC Λ ∧
      (∀ n, ConnesRigidity.IsICC (Γ n)) ∧
      ConnesRigidity.HasKazhdanPropertyT Λ ∧
      (∀ n, ConnesRigidity.HasKazhdanPropertyT (Γ n)) ∧
      (∀ n, ConnesRigidity.TracialGroupFactorsIsomorphic (Γ n) Λ) ∧
      (∀ m n, ConnesRigidity.TracialGroupFactorsIsomorphic (Γ m) (Γ n)) ∧
      (∀ ⦃m n : ℕ⦄, m ≠ n →
        ¬ConnesRigidity.GroupsIsomorphic (Γ m) (Γ n)) ∧
      (∀ n, ¬ConnesRigidity.GroupsIsomorphic Λ (Γ n)) := by
  let F := manuscriptInfinitePropertyTFiber
  refine ⟨F.Lambda, F.Gamma, F.lambda_fg, F.gamma_fg,
    F.lambda_icc, F.gamma_icc, F.lambda_propertyT, F.gamma_propertyT,
    F.factors_isomorphic, ?_, ?_, F.lambda_not_isomorphic⟩
  · intro m n
    exact groupFactorsIsomorphic_trans (F.factors_isomorphic m)
      (groupFactorsIsomorphic_symm (F.factors_isomorphic n))
  · intro m n hmn
    exact F.gamma_pairwise_nonisomorphic hmn
end ConnesRigidity
