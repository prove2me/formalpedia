-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x4.Kp_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:17.960803+00:00
-- url     : https://prove2.me/submissions/22b71dc0-2fd8-40a5-8124-ddd553cfb7c3

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
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



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x4
namespace Formalism.FourierDecayAlt.P.A5x4
theorem _root_.solution {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (w w' : Point K)
    (h : {q : Cos R w | IsInt R (orbZ w (rep R q))}.Finite)
    (h' : {q : Cos R w' | IsInt R (orbZ w' (rep R q))}.Finite) :
    Kp R ψ w w' = ∑ q ∈ h.toFinset, ∑ q' ∈ h'.toFinset,
      (Nat.card (isoZZ R (orbZ w (rep R q)) (orbZ w' (rep R q'))) : ℂ) * phase ψ (rep R q) *
        conj (phase ψ (rep R q')) := by
  unfold Kp
  rw [finsum_eq_sum_of_support_subset (s := h.toFinset ×ˢ h'.toFinset), Finset.sum_product]
  · refine Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun q' hq' => ?_
    have h1 : IsInt R (orbZ w (rep R q)) := by simpa using hq
    have h2 : IsInt R (orbZ w' (rep R q')) := by simpa using hq'
    simp only [pairTerm]
    rw [if_pos ⟨h1, h2⟩]
  · intro q hq
    simp only [Function.mem_support, pairTerm] at hq
    by_contra hcon
    apply hq
    rw [if_neg]
    · simp
    · intro hI
      apply hcon
      simp [hI.1, hI.2]
end Formalism.FourierDecayAlt.P.A5x4
