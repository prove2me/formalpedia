-- Prove2me | solution 1 for Formalism.L2.Th1.F.EtaEis.tsum_int_telescope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:24:06.698963+00:00
-- url     : https://prove2.me/submissions/476789cf-e864-4929-b70e-88264639a9be

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_EtaEis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EtaEis
namespace Formalism.L2.Th1.F.EtaEis
theorem _root_.solution (a : ℤ → ℂ) (hs : Summable fun m : ℤ => a m - a (m + 1))
    (h1 : Tendsto (fun N : ℕ => a (N : ℤ)) atTop (𝓝 0))
    (h2 : Tendsto (fun N : ℕ => a (-(N : ℤ))) atTop (𝓝 0)) :
    ∑' m : ℤ, (a m - a (m + 1)) = 0 := by
  have hH : HasSum (fun N : ℕ => (a (N : ℤ) - a ((N : ℤ) + 1))
      + (a (-((N : ℤ) + 1)) - a (-((N : ℤ) + 1) + 1))) (∑' m : ℤ, (a m - a (m + 1))) := by
    exact hs.hasSum.nat_add_neg_add_one
  have hpart : ∀ N : ℕ, ∑ i ∈ Finset.range N, ((a (i : ℤ) - a ((i : ℤ) + 1))
      + (a (-((i : ℤ) + 1)) - a (-((i : ℤ) + 1) + 1))) = a (-(N : ℤ)) - a (N : ℤ) := by
    intro N
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have e1 : -((k : ℤ) + 1) + 1 = -(k : ℤ) := by ring
      rw [e1]
      push_cast
      ring
  have hlim := (h2.sub h1).congr (fun N => (hpart N).symm)
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique hH.tendsto_sum_nat hlim
end Formalism.L2.Th1.F.EtaEis
