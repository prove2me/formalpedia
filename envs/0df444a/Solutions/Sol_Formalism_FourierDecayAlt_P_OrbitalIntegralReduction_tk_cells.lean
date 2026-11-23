-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.tk_cells
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:47.89222+00:00
-- url     : https://prove2.me/submissions/82c41e4e-f7fc-4357-81bf-3e4bc5c5f379

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_lat_finset_inf
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_S_refine
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_S_ind
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_ind_fin
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {V : Type} [AddCommGroup V]
variable [TopologicalSpace V] [IsTopologicalAddGroup V]
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution {V₀ : AddSubgroup V} (h0 : Lat V₀) {Q : Type} (c : Q → V) (N : Q → AddSubgroup V)
    (hN : ∀ q, Lat (N q)) (hpart : ∀ v, ∃! q, v - c q ∈ N q) (f : V → ℂ)
    (hf : ∀ q, ∀ w ∈ N q, f (c q + w) = f (c q)) (hfin : {q | f (c q) ≠ 0}.Finite)
    {M : AddSubgroup V} (hM : Lat M) (hinv : ∀ v, ∀ l ∈ M, f (v + l) = f v) :
    tk_S V₀ M f = ∑ᶠ q, (gi (N q) V₀ : ℂ) * f (c q) := by
  classical
  set S := hfin.toFinset with hS
  have hM' : Lat (M ⊓ S.inf N) := tk_lat_finset_inf hM N hN S
  have hle : ∀ q ∈ S, M ⊓ S.inf N ≤ N q := fun q hq => inf_le_right.trans (Finset.inf_le hq)
  have hdec : ∀ v, f v = ∑ q ∈ S, f (c q) * (if v - c q ∈ N q then (1 : ℂ) else 0) := by
    intro v
    obtain ⟨q₀, hq₀, huniq⟩ := hpart v
    have hv : f v = f (c q₀) := by
      have := hf q₀ _ hq₀
      rwa [add_sub_cancel] at this
    have hterm : ∀ q ∈ S, f (c q) * (if v - c q ∈ N q then (1 : ℂ) else 0) =
        if q = q₀ then f (c q₀) else 0 := by
      intro q _
      by_cases hq : q = q₀
      · subst hq; simp [hq₀]
      · rw [if_neg hq, if_neg (fun h => hq (huniq q h)), mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', hv]
    by_cases hq : q₀ ∈ S
    · rw [if_pos hq]
    · rw [if_neg hq]
      by_contra hne
      exact hq (by rw [hS, Set.Finite.mem_toFinset]; exact hne)
  rw [← tk_S_refine h0 hM hM' inf_le_left f hinv]
  have h1 : ∑ᶠ y : V ⧸ (M ⊓ S.inf N), f (Quotient.out y) =
      ∑ q ∈ S, f (c q) * ∑ᶠ y : V ⧸ (M ⊓ S.inf N),
        (if (Quotient.out y : V) - c q ∈ N q then (1 : ℂ) else 0) := by
    have hy : ∀ y : V ⧸ (M ⊓ S.inf N), f (Quotient.out y) =
        ∑ q ∈ S, f (c q) * (if (Quotient.out y : V) - c q ∈ N q then (1 : ℂ) else 0) :=
      fun y => hdec _
    rw [finsum_congr hy, finsum_sum_comm]
    · exact Finset.sum_congr rfl fun q _ => (mul_finsum _ _).symm
    · intro q hq
      refine (tk_ind_fin h0 (hN q) hM' (hle q hq) (c q)).subset ?_
      intro y hy
      simp only [Function.mem_support] at hy ⊢
      exact right_ne_zero_of_mul hy
  unfold tk_S
  rw [h1, Finset.mul_sum, finsum_eq_sum_of_support_subset (s := S)]
  · refine Finset.sum_congr rfl fun q hq => ?_
    have := tk_S_ind h0 (hN q) hM' (hle q hq) (c q)
    unfold tk_S at this
    rw [← this]
    ring
  · intro q hq
    simp only [Function.mem_support] at hq
    rw [hS, Set.Finite.coe_toFinset]
    exact right_ne_zero_of_mul hq
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
