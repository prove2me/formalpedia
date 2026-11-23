-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite.finite_classes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:25.343565+00:00
-- url     : https://prove2.me/submissions/139db078-10d9-4df4-a0fe-cff2c5dc80e5

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanPositiveSemidefinite

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
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite
namespace Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite
theorem _root_.solution {K : Type} [AddCommGroup K] (R P : AddSubgroup K) (h : R.relIndex P ≠ 0) :
    {x : K ⧸ R | (Quotient.out x : K) ∈ P}.Finite := by
  have hfi : (R.addSubgroupOf P).FiniteIndex := ⟨h⟩
  have : Finite (P ⧸ R.addSubgroupOf P) := inferInstance
  refine (Set.finite_range
    (fun q : P ⧸ R.addSubgroupOf P => (((Quotient.out q : P) : K) : K ⧸ R))).subset ?_
  intro x hx
  refine ⟨((⟨Quotient.out x, hx⟩ : P) : P ⧸ R.addSubgroupOf P), ?_⟩
  have h1 : ((Quotient.out ((⟨Quotient.out x, hx⟩ : P) : P ⧸ R.addSubgroupOf P) : P) :
      P ⧸ R.addSubgroupOf P) = ((⟨Quotient.out x, hx⟩ : P) : P ⧸ R.addSubgroupOf P) :=
    QuotientAddGroup.out_eq' _
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
  have h2 : (((Quotient.out ((⟨Quotient.out x, hx⟩ : P) : P ⧸ R.addSubgroupOf P) : P) : K) :
      K ⧸ R) = ((Quotient.out x : K) : K ⧸ R) := by
    rw [QuotientAddGroup.eq]; simpa using h1
  exact h2.trans (QuotientAddGroup.out_eq' x)
end Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite
