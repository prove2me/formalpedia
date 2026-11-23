-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Ind.fin_supp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:27.5218+00:00
-- url     : https://prove2.me/submissions/a221eae1-1512-469a-a321-7b0d2d0d0baf

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_gaussF_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.Ind
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {m : ℕ}
namespace Formalism.FourierDecayAlt.P.A6x7.Ind
theorem _root_.solution {Λ₀ L : AddSubgroup K} (hΛ₀ : IsLat Λ₀) (hL : IsLat L)
    (M : Matrix (Fin m) (Fin m) K) :
    (Function.support fun y : Fin m → K ⧸ Λ₀ =>
      gaussF ψ L M (fun i => Quotient.out (y i))).Finite := by
  have hq : {q : K ⧸ Λ₀ | (Quotient.out q : K) ∈ L}.Finite := by
    have : DiscreteTopology (K ⧸ Λ₀) := QuotientAddGroup.discreteTopology hΛ₀.1
    have hc : IsCompact ((QuotientAddGroup.mk : K → K ⧸ Λ₀) '' (L : Set K)) :=
      hL.2.image QuotientAddGroup.continuous_mk
    refine hc.finite_of_discrete.subset ?_
    intro q hq
    exact ⟨_, hq, QuotientAddGroup.out_eq' q⟩
  refine (Set.Finite.pi' (fun _ => hq)).subset ?_
  intro y hy i
  by_contra hcon
  apply hy
  exact gaussF_neg (fun h => hcon (h i))
end Formalism.FourierDecayAlt.P.A6x7.Ind
