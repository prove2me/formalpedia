-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x9.compact_principle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:41.732811+00:00
-- url     : https://prove2.me/submissions/ddf36f09-eb29-435e-9688-7087b09b2d75

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_iInter_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_lat_J
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_J_anti

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x9
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
variable (π : Kˣ)
namespace Formalism.FourierDecayAlt.P.A6x9
theorem _root_.solution (hd : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (hπ : (π : K) ∈ R) (hπ' : ∀ x : K, ∃ m : ℕ, (π : K) ^ m * x ∈ R)
    (F : K → K) (hF : Continuous F) (C : Set K) (hC : IsCompact C)
    (h : ∀ n : ℕ, ∃ u ∈ C, F u ∈ mulR R ((π : K) ^ n)) : ∃ u ∈ C, F u = 0 := by
  have := hd.t2
  have hne := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n : ℕ => C ∩ F ⁻¹' (mulR R ((π : K) ^ n) : Set K))
    (fun i => Set.inter_subset_inter_right _ (Set.preimage_mono (J_anti π hπ (Nat.le_succ i))))
    (fun i => by obtain ⟨u, hu, hu'⟩ := h i; exact ⟨u, hu, hu'⟩)
    (hC.inter_right (((lat_J π hd 0).cp.isClosed).preimage hF))
    (fun i => hC.isClosed.inter (((lat_J π hd i).cp.isClosed).preimage hF))
  obtain ⟨u, hu⟩ := hne
  rw [Set.mem_iInter] at hu
  exact ⟨u, (hu 0).1, iInter_zero π hd hn hπ' _ (fun n => (hu n).2)⟩
end Formalism.FourierDecayAlt.P.A6x9
