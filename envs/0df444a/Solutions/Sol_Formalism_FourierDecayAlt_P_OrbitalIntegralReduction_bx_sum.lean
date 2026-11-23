-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.bx_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:01.58981+00:00
-- url     : https://prove2.me/submissions/c84dd5fc-c50b-4950-9cf2-60516f8f9196

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_fin_box

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (_hD : LocalDatum K R ψ) {ι κ : Type} [Fintype ι] [Fintype κ] {Λ L : AddSubgroup K}
    (hΛ : IsLat Λ) (hL : IsLat L) (f : (ι ⊕ κ → K) → ℂ) (hs : BSupp L f) :
    bx R Λ (ι ⊕ κ) f = bx R Λ ι (fun a => bx R Λ κ (fun b => f (Sum.elim a b))) := by
  unfold bx
  rw [← mul_finsum, Fintype.card_sum, pow_add, mul_assoc]
  congr 2
  rw [← finsum_comp_equiv (Equiv.sumArrowEquivProdArrow ι κ (K ⧸ Λ)).symm]
  have hfin : (Function.support (fun p : (ι → K ⧸ Λ) × (κ → K ⧸ Λ) =>
      f (fun i => Quotient.out ((Equiv.sumArrowEquivProdArrow ι κ (K ⧸ Λ)).symm p i)))).Finite := by
    refine ((tk_fin_box Λ hΛ.1 (fun _ : ι => (L : Set K)) (fun _ => hL.2)).prod
      (tk_fin_box Λ hΛ.1 (fun _ : κ => (L : Set K)) (fun _ => hL.2))).subset ?_
    intro p hp
    have := hs _ hp
    exact ⟨fun i => this (Sum.inl i), fun i => this (Sum.inr i)⟩
  rw [finsum_curry _ hfin]
  refine finsum_congr fun a => finsum_congr fun b => ?_
  congr 1
  funext i
  rcases i with i | i <;> rfl
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
