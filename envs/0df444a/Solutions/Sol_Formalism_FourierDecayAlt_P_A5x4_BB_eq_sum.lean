-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x4.BB_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:41.172994+00:00
-- url     : https://prove2.me/submissions/4fd55fa0-c9c3-4fed-aa32-75d01d476707

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Theorems.Thm_Formalism_DoubleCosetMeasures_Final_bbNorm
import Theorems.Thm_Formalism_DoubleCosetMeasures_Final_suppCompact
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_suppCompact
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
open Classical
namespace Formalism.FourierDecayAlt.P.A5x4
theorem _root_.solution {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (R : Subring K) (ψ : AddChar K ℂ) (hL : LocalDatum K R ψ) (w : Point K)
    (μ₁ : Measure (lowW K w.1 w.2)) (μ₂ : Measure (upUniG K w.1.sum))
    [μ₁.IsMulRightInvariant] [μ₂.IsMulLeftInvariant] [SFinite μ₁] [SFinite μ₂]
    (h1 : μ₁ (intSub R (lowW K w.1 w.2) : Set (lowW K w.1 w.2)) = 1)
    (h2 : μ₂ (intSub R (upUniG K w.1.sum) : Set (upUniG K w.1.sum)) = 1)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R)
    (h : {q : Cos R w | IsInt R (orbZ w (rep R q))}.Finite) :
    BB R w.1 w.2 ψ C e lam μ₁ μ₂ = ∑ q ∈ h.toFinset,
      (Nat.card (isoSet R (orbZ w (rep R q)) C e lam) : ℂ) * phase ψ (rep R q) := by
  have := hL.t2
  have hψ : ∀ r ∈ R, ψ r = 1 := by
    intro r hr
    have := (hL.selfDual 1).2 R.one_mem r hr
    simpa using this
  rw [Formalism.DoubleCosetMeasures.Final.bbNorm K R hL.isOpen w.1 w.2 ψ hψ μ₁ μ₂ h1 h2 C e lam
    (Formalism.DoubleCosetMeasures.Final.suppCompact K R hL.isOpen hL.isCompact w.1 w.2 ψ C e lam),
    finsum_eq_sum_of_support_subset (s := h.toFinset)]
  · refine Finset.sum_congr rfl fun q hq => ?_
    have h1 : IsInt R (orbZ w (rep R q)) := by simpa using hq
    have h3 : phi R w.1 w.2 ψ C e lam (q.1.out, q.2.out) =
      (if IsInt R (orbZ w (rep R q)) then
        (Nat.card (isoSet R (orbZ w (rep R q)) C e lam) : ℂ) else 0) * phase ψ (rep R q) := rfl
    rw [h3, if_pos h1]
  · intro q hq
    have h3 : phi R w.1 w.2 ψ C e lam (q.1.out, q.2.out) =
      (if IsInt R (orbZ w (rep R q)) then
        (Nat.card (isoSet R (orbZ w (rep R q)) C e lam) : ℂ) else 0) * phase ψ (rep R q) := rfl
    simp only [Function.mem_support] at hq
    rw [h3] at hq
    by_contra hcon
    apply hq
    rw [if_neg]
    · simp
    · intro hI
      apply hcon
      simpa using hI
end Formalism.FourierDecayAlt.P.A5x4
