-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x9.nhds_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:00.359118+00:00
-- url     : https://prove2.me/submissions/a3e4ef69-0c22-4511-8bda-49abc9fdac34

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
    (hπ : (π : K) ∈ R) (hπ' : ∀ x : K, ∃ m : ℕ, (π : K) ^ m * x ∈ R) (V : Set K)
    (hV : V ∈ 𝓝 (0 : K)) : ∃ n : ℕ, (mulR R ((π : K) ^ n) : Set K) ⊆ V := by
  have := hd.t2
  by_contra hcon
  push Not at hcon
  have hne := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n : ℕ => (mulR R ((π : K) ^ n) : Set K) ∩ (interior V)ᶜ)
    (fun i => Set.inter_subset_inter_left _ (J_anti π hπ (Nat.le_succ i)))
    (fun i => by
      obtain ⟨u, hu, hu'⟩ := Set.not_subset.1 (hcon i)
      exact ⟨u, hu, fun h => hu' (interior_subset h)⟩)
    ((lat_J π hd 0).cp.inter_right isOpen_interior.isClosed_compl)
    (fun i => (lat_J π hd i).cp.isClosed.inter isOpen_interior.isClosed_compl)
  obtain ⟨u, hu⟩ := hne
  rw [Set.mem_iInter] at hu
  have h0 := iInter_zero π hd hn hπ' u (fun n => (hu n).1)
  apply (hu 0).2
  rw [h0]
  exact mem_interior_iff_mem_nhds.2 hV
end Formalism.FourierDecayAlt.P.A6x9
