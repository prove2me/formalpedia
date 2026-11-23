-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.integral_lattice_refinement_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:30.524485+00:00
-- url     : https://prove2.me/submissions/f63fc1b6-849d-4aac-8478-6589d3c79ac3

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_finsum_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_out_sub_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_lat_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_volL_refine
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_relIndex_ne_zero
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
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x3
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.IntLatRefine := by
  classical
  intro K _ _ _ R ψ hd Λ Λ' Om f hΛ hΛ' hle _ hOm hf
  have hR := lat_R hd.isOpen hd.isCompact
  set F : K → ℂ := fun z => if z ∈ Om then f z else 0 with hFdef
  have hF : ∀ z, ∀ l ∈ Λ, F (z + l) = F z := by
    intro z l hl
    by_cases hz : z ∈ Om
    · simp only [hFdef, hz, hOm z hz l hl, if_true]
      exact hf z hz l hl
    · have : z + l ∉ Om := by
        intro h
        apply hz
        have := hOm _ h (-l) (Λ.neg_mem hl)
        simpa using this
      simp only [hFdef, hz, this, if_false]
  have hne : Λ'.relIndex Λ ≠ 0 := relIndex_ne_zero hΛ'.1 hΛ.2
  have : Finite (Λ ⧸ Λ'.addSubgroupOf Λ) := Nat.finite_of_card_ne_zero hne
  have key : ∑ᶠ y : K ⧸ Λ', F (Quotient.out y) =
      (Λ'.relIndex Λ : ℂ) * ∑ᶠ y : K ⧸ Λ, F (Quotient.out y) := by
    rw [← show Nat.card (Λ ⧸ Λ'.addSubgroupOf Λ) = Λ'.relIndex Λ from rfl,
      ← finsum_fst (AddSubgroup.quotientEquivProdOfLE hle) (fun y : K ⧸ Λ => F (Quotient.out y))]
    refine finsum_congr fun y => ?_
    have := hF (Quotient.out y) _ (out_sub_mem hle y)
    rw [← this]
    congr 1
    ring
  have e1 : intLat R Λ' Om f = (volL R Λ' : ℂ) * ∑ᶠ y : K ⧸ Λ', F (Quotient.out y) := by
    unfold intLat
    congr 1
  have e2 : intLat R Λ Om f = (volL R Λ : ℂ) * ∑ᶠ y : K ⧸ Λ, F (Quotient.out y) := by
    unfold intLat
    congr 1
  rw [e1, e2, key, volL_refine hR (lat_iff.1 hΛ') (lat_iff.1 hΛ) hle]
  push_cast
  ring
end Formalism.FourierDecayAlt.P
