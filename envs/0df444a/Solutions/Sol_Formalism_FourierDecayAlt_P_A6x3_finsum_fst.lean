-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x3.finsum_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:10.757807+00:00
-- url     : https://prove2.me/submissions/9c8eca3c-a302-4c47-ab5c-3ef7991c4328

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
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
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x3
namespace Formalism.FourierDecayAlt.P.A6x3
theorem _root_.solution {X Y Z : Type} [Finite Z] [Nonempty Z] (e : X ≃ Y × Z) (G : Y → ℂ) :
    ∑ᶠ x, G (e x).1 = (Nat.card Z : ℂ) * ∑ᶠ y, G y := by
  rw [finsum_comp_equiv e (f := fun p => G p.1)]
  have hs : Function.support (fun p : Y × Z => G p.1) = Function.support G ×ˢ Set.univ := by
    ext p; simp
  by_cases hf : (Function.support G).Finite
  · rw [finsum_curry _ (by
      show (Function.support (fun p : Y × Z => G p.1)).Finite
      rw [hs]; exact hf.prod Set.finite_univ), mul_finsum]
    refine finsum_congr fun a => ?_
    have := Fintype.ofFinite Z
    rw [finsum_eq_sum_of_fintype]
    show ∑ _i : Z, G a = _
    rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul]
  · rw [finsum_of_infinite_support hf, finsum_of_infinite_support, mul_zero]
    rw [hs]
    intro h
    apply hf
    have := h.image Prod.fst
    refine this.subset ?_
    intro y hy
    obtain ⟨z⟩ := (inferInstance : Nonempty Z)
    exact ⟨(y, z), ⟨hy, Set.mem_univ _⟩, rfl⟩
end Formalism.FourierDecayAlt.P.A6x3
