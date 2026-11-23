-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.pow_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:01.113943+00:00
-- url     : https://prove2.me/submissions/c8705c97-5e15-4a29-bc00-b04679e5fe38

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_I_compact
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_I_isOpen
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_sep
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_I_anti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
namespace Adic
theorem _root_.solution (h : Adic R ϖ) [IsReduced K] (s : ℕ) :
    ∃ n0 : ℕ, ∀ u ∈ R, u ^ s ∈ I R ((ϖ : K) ^ n0) → u ∈ I R (ϖ : K) := by
  have := h.t2
  by_contra hcon
  push Not at hcon
  let C : ℕ → Set K := fun n => (R : Set K) ∩ ((I R (ϖ : K))ᶜ ∩ (fun u => u ^ s) ⁻¹' I R ((ϖ : K) ^ n))
  have hcl : ∀ n, IsClosed (C n) := fun n =>
    h.isCompact.isClosed.inter ((I_isOpen h.isOpen ϖ).isClosed_compl.inter
      ((I_compact h.isCompact _).isClosed.preimage (continuous_pow s)))
  obtain ⟨u, hu⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    (fun n x hx => ⟨hx.1, hx.2.1, I_anti h.mem (Nat.le_succ n) hx.2.2⟩)
    (fun n => by
      obtain ⟨u, hu, h1, h2⟩ := hcon n
      exact ⟨u, hu, h2, h1⟩)
    (h.isCompact.of_isClosed_subset (hcl 0) Set.inter_subset_left) hcl
  have hu' := Set.mem_iInter.1 hu
  have h0 : u ^ s = 0 := h.sep _ fun n => (hu' n).2.2
  have : u = 0 := IsNilpotent.eq_zero ⟨s, h0⟩
  exact (hu' 0).2.1 ⟨0, R.zero_mem, by simp [this]⟩
end Adic
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
