-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.gi_comap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:36.488738+00:00
-- url     : https://prove2.me/submissions/a008e27c-7c30-4b5e-86b6-9d469051b610

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
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


section
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
namespace Formalism.FourierDecayAlt.P.A5x5
section Index
variable {V W : Type} [AddCommGroup V] [AddCommGroup W]
private theorem relIndex_eq_of_mem_iff {H H' K : AddSubgroup V} (h : ∀ v ∈ K, v ∈ H ↔ v ∈ H') :
    H.relIndex K = H'.relIndex K := by
  have e : H.addSubgroupOf K = H'.addSubgroupOf K := by
    ext x
    simp only [AddSubgroup.mem_addSubgroupOf]
    exact h x x.2
  unfold AddSubgroup.relIndex
  rw [e]
variable [TopologicalSpace V] [IsTopologicalAddGroup V]
end Index
section Mod
variable {K : Type} [CommRing K] {R : Subring K}
variable [TopologicalSpace K] [IsTopologicalRing K]
end Mod
section Mat
variable {K : Type} [CommRing K] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] {R : Subring K}
variable [TopologicalSpace K] [IsTopologicalRing K]
end Mat
section Block
variable {K : Type} [CommRing K] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] {R : Subring K}
end Block
section Elim
variable {K : Type} [CommRing K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {R : Subring K}
variable [TopologicalSpace K] [IsTopologicalRing K] {ψ : AddChar K ℂ}
end Elim
section Kern
variable {K : Type} [CommRing K] {R : Subring K}
variable [TopologicalSpace K] [IsTopologicalRing K] {ψ : AddChar K ℂ}
end Kern
end Formalism.FourierDecayAlt.P.A5x5
namespace Formalism.FourierDecayAlt.P
open A5x5
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x5
variable {V W : Type} [AddCommGroup V] [AddCommGroup W]
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution (f : V →+ W) (A L : AddSubgroup V) (A' L' : AddSubgroup W)
    (h1 : ∀ v ∈ L, v ∈ A ↔ f v ∈ A') (h2 : ∀ v ∈ A, v ∈ L ↔ f v ∈ L')
    (h3 : L.map f = L') (h4 : A.map f = A') : gi A L = gi A' L' := by
  subst h3 h4
  unfold gi
  rw [← AddSubgroup.relIndex_comap, ← AddSubgroup.relIndex_comap]
  have k1 : ((L.map f).comap f).relIndex A = L.relIndex A :=
    relIndex_eq_of_mem_iff fun v hv => by rw [AddSubgroup.mem_comap, h2 v hv]
  have k2 : ((A.map f).comap f).relIndex L = A.relIndex L :=
    relIndex_eq_of_mem_iff fun v hv => by rw [AddSubgroup.mem_comap, h1 v hv]
  rw [k1, k2]
end Formalism.FourierDecayAlt.P.A5x5
