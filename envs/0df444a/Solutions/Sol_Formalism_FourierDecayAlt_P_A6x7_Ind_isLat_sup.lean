-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Ind.isLat_sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:29.652246+00:00
-- url     : https://prove2.me/submissions/b4a5123c-8312-4e2d-9965-fe35dc835807

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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.Ind
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {m : ℕ}
namespace Formalism.FourierDecayAlt.P.A6x7.Ind
theorem _root_.solution {L L' : AddSubgroup K} (h : IsLat L) (h' : IsLat L') : IsLat (L ⊔ L') := by
  refine ⟨AddSubgroup.isOpen_mono (le_sup_left : L ≤ L ⊔ L') h.1, ?_⟩
  have : ((L ⊔ L' : AddSubgroup K) : Set K) = (fun p : K × K => p.1 + p.2) '' ((L : Set K) ×ˢ (L' : Set K)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hx
      exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact AddSubgroup.mem_sup.2 ⟨a, ha, b, hb, rfl⟩
  rw [this]
  exact (h.2.prod h'.2).image (continuous_fst.add continuous_snd)
end Formalism.FourierDecayAlt.P.A6x7.Ind
