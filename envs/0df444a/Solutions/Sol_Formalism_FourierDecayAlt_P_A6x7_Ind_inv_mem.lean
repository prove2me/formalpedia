-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Ind.inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:45.770811+00:00
-- url     : https://prove2.me/submissions/f5f5afa3-6993-404a-b89f-a553a499bf7e

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_qf_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_single_mem

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
variable {K : Type} [CommRing K] {m : ℕ}
variable {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x7.Ind
theorem _root_.solution (h2 : IsUnit (2 : K)) {M : Matrix (Fin m) (Fin m) K} (hM : M.IsSymm)
    {L : AddSubgroup K} (hperp : perp ψ (perp ψ L) = L) (hA : GaussAdm ψ L M) (y : Fin m → K)
    (hy : ∀ i, y i ∈ perp ψ L) (j : Fin m) : (M⁻¹ *ᵥ y) j ∈ L := by
  rw [← hperp]
  intro a ha
  have hs : (M⁻¹).IsSymm := hM.inv
  have e := qf_add h2 M⁻¹ hs (Pi.single j a) y
  have h1 := hA (Pi.single j a + y) (fun i => (perp ψ L).add_mem (single_mem ha j i) (hy i))
  have h2' := hA (Pi.single j a) (single_mem ha j)
  have h3 := hA y hy
  change ψ (qf M⁻¹ _) = 1 at h1 h2' h3
  rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h2', h3, one_mul, mul_one] at h1
  rwa [single_dotProduct, mul_comm] at h1
end Formalism.FourierDecayAlt.P.A6x7.Ind
