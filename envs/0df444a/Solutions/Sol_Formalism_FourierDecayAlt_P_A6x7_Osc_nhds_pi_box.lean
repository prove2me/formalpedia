-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Osc.nhds_pi_box
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:29.747826+00:00
-- url     : https://prove2.me/submissions/4acba9e4-2c8a-4110-bb13-28b7dc755fdc

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.Osc
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.A6x7.Osc
theorem _root_.solution [TopologicalSpace K] {m : ℕ} (V : Set (Fin m → K))
    (hV : V ∈ 𝓝 (0 : Fin m → K)) : ∃ W ∈ 𝓝 (0 : K), ∀ l : Fin m → K, (∀ k, l k ∈ W) → l ∈ V := by
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, -, t, ht, hI⟩ := hV
  exact ⟨⋂ k, t k, Filter.iInter_mem.2 ht, fun l hl => hI fun k _ => Set.mem_iInter.1 (hl k) k⟩
end Formalism.FourierDecayAlt.P.A6x7.Osc
