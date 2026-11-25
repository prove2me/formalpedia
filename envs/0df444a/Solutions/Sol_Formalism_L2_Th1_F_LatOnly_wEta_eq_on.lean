-- Prove2me | solution 1 for Formalism.L2.Th1.F.LatOnly.wEta_eq_on
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:22:35.385096+00:00
-- url     : https://prove2.me/submissions/f40f3822-bcf4-4c82-8340-a272e8646bb4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
import Theorems.Thm_Formalism_L2_Th1_F_LatOnly_wZeta_eq
import Theorems.Thm_Formalism_L2_Th1_F_zetaQuasi


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
open Formalism.L2.Th1.F.LatOnly
variable {L L' : PeriodPair}
namespace Formalism.L2.Th1.F.LatOnly
theorem _root_.solution (h : L.lattice = L'.lattice) {ω : ℂ} (hω : ω ∈ L.lattice) :
    wEta L ω = wEta L' ω := by
  have hhalf : L.ω₁ / 2 ∉ L.lattice := by
    intro hx
    obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.mp hx
    have hli := L.indep
    rw [LinearIndependent.pair_iff] at hli
    obtain ⟨h1, h2⟩ := hli ((p : ℝ) - 1 / 2) (q : ℝ) (by
      simp only [Complex.real_smul]
      push_cast
      linear_combination hpq)
    have h3 : (2 : ℝ) * p = 1 := by linarith
    have h2p : (2 * p : ℤ) = 1 := by exact_mod_cast h3
    omega
  have hω' : ω ∈ L'.lattice := by rw [← h]; exact hω
  have hhalf' : L.ω₁ / 2 ∉ L'.lattice := by rw [← h]; exact hhalf
  have e1 := zetaQuasi L ω (L.ω₁ / 2) hω hhalf
  have e2 := zetaQuasi L' ω (L.ω₁ / 2) hω' hhalf'
  rw [wZeta_eq h] at e1
  linear_combination e2 - e1
end Formalism.L2.Th1.F.LatOnly
