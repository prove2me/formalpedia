-- Prove2me | solution 1 for Formalism.L2.Th1.F.quasiPeriodConstIsogeny_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:28:56.965784+00:00
-- url     : https://prove2.me/submissions/a0404ec4-1a9a-4aba-82b4-03a3173288bf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstIsogeny
import Theorems.Thm_Formalism_L2_Th1_F_S2IsogenyPsi_eta_rel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open S2IsogenyPsi
namespace Formalism.L2.Th1.F
theorem _root_.solution (hP : IsogenyP) (hd : ZetaHasDeriv) (hq : ZetaQuasi) (he : EtaSplit)
    (hc : KerRepsCard) : QuasiPeriodConstIsogeny := by
  intro L α S hα hst hS
  have hω₁ : L.ω₁ ∈ L.lattice := PeriodPair.mem_lattice.mpr ⟨1, 0, by simp⟩
  have hne : L.ω₁ ≠ 0 := by
    intro h0
    have hli := L.indep
    rw [LinearIndependent.pair_iff] at hli
    have h1 := (hli 1 0 (by rw [h0]; simp)).1
    exact one_ne_zero h1
  have hrel := eta_rel hP hd hq L α S hα hst hS L.ω₁ hω₁
  rw [he L (α * L.ω₁), he L L.ω₁] at hrel
  have hcard : ((S.card : ℂ) + 1) = (Complex.normSq α : ℂ) := by
    have h2 := hc L α S hα hst hS
    exact_mod_cast h2
  rw [hcard] at hrel
  rw [← Complex.mul_conj] at hrel ⊢
  apply mul_right_cancel₀ hne
  rw [map_mul] at hrel
  linear_combination hrel
end Formalism.L2.Th1.F
