-- Prove2me | solution 1 for Formalism.L2.Th1.G.HurwitzJetIntegrality.jetsIn_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:42:49.852112+00:00
-- url     : https://prove2.me/submissions/4abf94b9-91ae-486c-80ef-6e0e18721602

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Theorems.Thm_Formalism_LT_TorsProof_one_mem


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
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral)
open Formalism.L2.Th1.G.HurwitzJetIntegrality
namespace Formalism.L2.Th1.G.HurwitzJetIntegrality
theorem _root_.solution (h1 : JetsRing) (h2 : JetsDivPow) {K : Type} [Field K] [CharZero K]
    (R : Subring K) {ι κ : Type} (f : MvPowerSeries ι K) (a : ι → MvPowerSeries κ K)
    (hf : JetsIn R f) (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (ha : ∀ i, JetsIn R (a i)) (d : ι →₀ ℕ) :
    JetsIn R (MvPowerSeries.C (MvPowerSeries.coeff d f) * d.prod fun s e => (a s) ^ e) := by
  obtain ⟨hC, -, -, -, hmul⟩ := h1 K R κ
  have e : MvPowerSeries.C (MvPowerSeries.coeff d f) * d.prod (fun s e => (a s) ^ e) =
      MvPowerSeries.C (((mfact d : ℕ) : K) * MvPowerSeries.coeff d f) *
        d.prod (fun s e => MvPowerSeries.C ((e.factorial : K)⁻¹) * (a s) ^ e) := by
    simp only [mfact, Finsupp.prod]
    rw [Finset.prod_mul_distrib, ← map_prod, ← mul_assoc, ← map_mul]
    congr 2
    push_cast
    rw [mul_comm (∏ x ∈ d.support, ((d x).factorial : K)) _, mul_assoc, ← Finset.prod_mul_distrib,
      Finset.prod_eq_one (fun x _ => mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))),
      mul_one]
  rw [e]
  refine hmul _ _ (hC _ (hf d)) ?_
  simp only [Finsupp.prod]
  exact Finset.prod_induction _ (JetsIn R) (fun x y hx hy => hmul x y hx hy)
    (by simpa using hC 1 R.one_mem) (fun s _ => h2 K R κ (a s) (ha0 s) (ha s) (d s))
end Formalism.L2.Th1.G.HurwitzJetIntegrality
