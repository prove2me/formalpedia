-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcX.LT.GLP.pi_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:07:55.046552+00:00
-- url     : https://prove2.me/submissions/7b658548-651b-4fcc-8cb1-2b1daedd61a8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NcXGLP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcX Formalism.L2.SG.Pf.NcX.LT Formalism.L2.SG.Pf.NcX.LT.GLP
variable {K : Type*} [Field K]
namespace Formalism.L2.SG.Pf.NcX.LT.GLP
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module K V] {a : ℕ} (ψ : Fin a → Module.Dual K V)
    (hψ : LinearIndependent K ψ) : Function.Surjective (LinearMap.pi ψ) := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hf0
  have hsum : ∑ i, f (Pi.single i 1) • ψ i = 0 := by
    ext v
    have hv : f (LinearMap.pi ψ v) = 0 := hfk ⟨v, rfl⟩
    have hdec : LinearMap.pi ψ v = ∑ i, ψ i v • (Pi.single i 1 : Fin a → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hdec, map_sum] at hv
    simpa [smul_eq_mul, mul_comm] using hv
  have hc := Fintype.linearIndependent_iff.1 hψ _ hsum
  apply LinearMap.pi_ext'
  intro i
  ext
  simp [hc i]
end Formalism.L2.SG.Pf.NcX.LT.GLP
