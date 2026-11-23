-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.minor_monomial_exponent_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:28.615874+00:00
-- url     : https://prove2.me/submissions/be6b9aee-8853-414f-8057-1c972c676cea

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbitFamily
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OrbMul
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_OneLetterUnramifiedBound
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoShapeLow
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
theorem _root_.solution {K : Type} [Field K] {N0 N1 C : ℕ} (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) (κ : Fin N0 × Fin N1 →₀ ℕ)
    (hκ : κ ∈ (minorProd (fun (i : Fin N0) (b : Fin N1) =>
      (MvPolynomial.X (i, b) : MvPolynomial (Fin N0 × Fin N1) K)) p hp I).support)
    (y : Fin N0 × Fin N1) : κ y ≤ C := by
  classical
  have hrow : oldRowLow (N1 := N1) (fun i k : Fin N0 => if i = k then (1 : K) else 0) =
      fun (i : Fin N0) (b : Fin N1) =>
        (MvPolynomial.X (i, b) : MvPolynomial (Fin N0 × Fin N1) K) := by
    funext i b
    unfold oldRowLow
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h := (monoShapeLow.{0} K N0 N1 N0 C (fun i k : Fin N0 => if i = k then (1 : K) else 0)
    p hp I κ (by rw [hrow]; exact hκ)).2 y.1
  exact le_trans (Finset.single_le_sum (f := fun b : Fin N1 => κ (y.1, b))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ y.2)) h
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
