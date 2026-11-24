-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gram_kernel_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:56.113437+00:00
-- url     : https://prove2.me/submissions/a95093e3-bf76-4683-a57d-d8bf52694db3

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_integral_points_finite
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_Kp_eq_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_BB_eq_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_isoCount
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A5.GramIdentity := by
  intro K _ _ _ R ψ hL w w' μ₁ μ₂ μ₁' μ₂' _ _ _ _ _ _ _ _ h1 h2 h1' h2' ι _ C _ _ e lam hne hex
  have hf := integral_points_finite K R ψ hL w
  have hf' := integral_points_finite K R ψ hL w'
  rw [Kp_eq_sum R ψ w w' hf hf']
  have hterm : ∀ a, BB R w.1 w.2 ψ (C a) (e a) (lam a) μ₁ μ₂ *
        conj (BB R w'.1 w'.2 ψ (C a) (e a) (lam a) μ₁' μ₂') /
        (Nat.card (autSet R (C a) (e a) (lam a)) : ℂ) =
      ∑ q ∈ hf.toFinset, ∑ q' ∈ hf'.toFinset,
        ((Nat.card (isoSet R (orbZ w (rep R q)) (C a) (e a) (lam a)) : ℂ) *
        (Nat.card (isoSet R (orbZ w' (rep R q')) (C a) (e a) (lam a)) : ℂ) /
        (Nat.card (autSet R (C a) (e a) (lam a)) : ℂ)) * phase ψ (rep R q) *
        conj (phase ψ (rep R q')) := by
    intro a
    rw [BB_eq_sum R ψ hL w μ₁ μ₂ h1 h2 (C a) (e a) (lam a) hf,
      BB_eq_sum R ψ hL w' μ₁' μ₂' h1' h2' (C a) (e a) (lam a) hf', map_sum,
      Finset.sum_mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun q' _ => ?_
    rw [map_mul, map_natCast]
    ring
  rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q' _ => ?_
  have hq1 : IsInt R (orbZ w (rep R q)) := by simpa using hq
  rw [← isoCount R (orbZ w (rep R q)) (orbZ w' (rep R q')) ι C e lam hne (hex _ hq1),
    Finset.sum_mul, Finset.sum_mul]
end Formalism.FourierDecayAlt.P
