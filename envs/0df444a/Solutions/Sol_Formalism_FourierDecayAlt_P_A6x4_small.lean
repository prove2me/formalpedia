-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x4.small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:40.485518+00:00
-- url     : https://prove2.me/submissions/12c79b17-f676-4935-bf54-cb38754309b6

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_inter_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_lat_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x4
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x4
theorem _root_.solution (hD : LocalDatum K R ψ) (hQ : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) {p q : K}
    (hpq : p * q = 1) (hp : p ∈ R) (hex : ∀ x : K, ∃ m : ℕ, p ^ m * x ∈ R) {V : Set K}
    (hV : V ∈ 𝓝 (0 : K)) : ∃ m : ℕ, ∀ x, q ^ m * x ∈ R → x ∈ V := by
  have := hD.t2
  by_contra hcon
  push Not at hcon
  let t : ℕ → Set K := fun m => (fun x => q ^ m * x) ⁻¹' (R : Set K) ∩ (interior V)ᶜ
  have hcl : ∀ m, IsClosed (t m) := fun m =>
    (hD.isCompact.isClosed.preimage (by fun_prop)).inter isOpen_interior.isClosed_compl
  have hne : (⋂ m, t m).Nonempty := by
    apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t
    · intro m x hx
      exact ⟨lat_mono hpq hp (Nat.le_succ m) hx.1, hx.2⟩
    · intro m
      obtain ⟨x, hx, hxV⟩ := hcon m
      exact ⟨x, hx, fun h => hxV (interior_subset h)⟩
    · apply hD.isCompact.of_isClosed_subset (hcl 0)
      intro x hx
      simpa using hx.1
    · exact hcl
  obtain ⟨x, hx⟩ := hne
  rw [Set.mem_iInter] at hx
  have hx0 : x = 0 := inter_zero hD hQ hpq hex fun m => (hx m).1
  apply (hx 0).2
  rw [hx0]
  exact mem_interior_iff_mem_nhds.2 hV
end Formalism.FourierDecayAlt.P.A6x4
