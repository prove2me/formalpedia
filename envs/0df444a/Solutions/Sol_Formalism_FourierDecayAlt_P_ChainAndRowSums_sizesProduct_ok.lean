-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChainAndRowSums.sizesProduct_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:22.664994+00:00
-- url     : https://prove2.me/submissions/581bf4b4-bfda-4ce3-937d-0ddacd50d320

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainAndRowSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ChainAndRowSums
open Formalism.FourierDecayAlt.crystallineComparison
namespace Formalism.FourierDecayAlt.P.ChainAndRowSums
theorem _root_.solution : SizesProduct := by
  intro f s Maa C₄ A B M vol hs hC hA0 hAC hB0 hBC hvol hMaa0 hMaaA hM
  have hC0 : 0 ≤ C₄ := by linarith
  have hprodv : 0 ≤ ∏ n ∈ Ico 1 s, vol n := Finset.prod_nonneg (fun n _ => hvol n)
  have h1 : ∏ n ∈ Ico 1 s, M n ≤ ∏ n ∈ Ico 1 s, (B ^ f * vol n) :=
    Finset.prod_le_prod (fun n hn => (hM n hn).1) (fun n hn => (hM n hn).2)
  have h2 : ∏ n ∈ Ico 1 s, (B ^ f * vol n) ≤ ∏ n ∈ Ico 1 s, (C₄ ^ f * vol n) :=
    Finset.prod_le_prod (fun n _ => mul_nonneg (pow_nonneg hB0 _) (hvol n))
      (fun n _ => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB0 hBC f) (hvol n))
  have h3 : A ^ f ≤ C₄ ^ f := pow_le_pow_left₀ hA0 hAC f
  have hMp : 0 ≤ ∏ n ∈ Ico 1 s, M n := Finset.prod_nonneg (fun n hn => (hM n hn).1)
  calc Maa * ∏ n ∈ Ico 1 s, M n ≤ C₄ ^ f * ∏ n ∈ Ico 1 s, (C₄ ^ f * vol n) := by
        apply mul_le_mul (hMaaA.trans h3) (h1.trans h2) hMp (pow_nonneg hC0 _)
    _ = C₄ ^ (f * s) * ∏ n ∈ Ico 1 s, vol n := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico, ← mul_assoc, ← pow_mul,
          ← pow_add]
        congr 2
        rcases s with _ | s
        · omega
        · simp [Nat.mul_succ]; ring
end Formalism.FourierDecayAlt.P.ChainAndRowSums
