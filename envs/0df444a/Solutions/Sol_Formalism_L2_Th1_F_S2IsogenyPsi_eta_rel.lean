-- Prove2me | solution 1 for Formalism.L2.Th1.F.S2IsogenyPsi.eta_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:09:43.304376+00:00
-- url     : https://prove2.me/submissions/2ae3f604-589c-4ffe-acb0-c6242d1a1739

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstIsogeny
import Theorems.Thm_Formalism_L2_Th1_F_S2IsogenyPsi_notMem_of_dom
import Theorems.Thm_Formalism_L2_Th1_F_S2IsogenyPsi_add_dom
import Theorems.Thm_Formalism_L2_Th1_F_S2IsogenyPsi_psi_const

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
open Formalism.L2.Th1.F.S2IsogenyPsi
namespace Formalism.L2.Th1.F.S2IsogenyPsi
theorem _root_.solution (hP : IsogenyP) (hd : ZetaHasDeriv) (hq : ZetaQuasi) (L : PeriodPair) (α : ℂ)
    (S : Finset ℂ) (hα : α ≠ 0) (hst : MulStable L α) (hS : IsKerReps L α S) (ω : ℂ)
    (hω : ω ∈ L.lattice) :
    α * wEta L (α * ω) - ((S.card : ℂ) + 1) * wEta L ω = (∑ P ∈ S, L.weierstrassP P) * ω := by
  have hhalf : L.ω₁ / 2 ∉ L.lattice := by
    intro h
    obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.mp h
    have hli := L.indep
    rw [LinearIndependent.pair_iff] at hli
    obtain ⟨h1, h2⟩ := hli ((p : ℝ) - 1 / 2) (q : ℝ) (by
      simp only [Complex.real_smul]
      push_cast
      linear_combination hpq)
    have h3 : (2 : ℝ) * p = 1 := by linarith
    have h2p : (2 * p : ℤ) = 1 := by exact_mod_cast h3
    omega
  have hax : α * (L.ω₁ / 2 / α) = L.ω₁ / 2 := by field_simp
  obtain ⟨x, hx⟩ : ∃ x, α * x ∉ L.lattice := ⟨L.ω₁ / 2 / α, by rw [hax]; exact hhalf⟩
  have hx0 : x ∉ L.lattice := notMem_of_dom hst hx
  have hαω : α * ω ∈ L.lattice := hst ω hω
  have hy : α * (x + ω) ∉ L.lattice := add_dom hαω hx
  have hc := psi_const hP hd L α S hα hst hS hy hx
  have hsum : ∑ P ∈ S, wZeta L (x + ω + P) = ∑ P ∈ S, (wZeta L (x + P) + wEta L ω) := by
    apply Finset.sum_congr rfl
    intro P hPS
    have hxP : x + P ∉ L.lattice := notMem_of_dom hst (add_dom (hS.1 P hPS).1 hx)
    rw [show x + ω + P = x + P + ω by ring, hq L ω (x + P) hω hxP]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  simp only [psi] at hc
  rw [show α * (x + ω) = α * x + α * ω by ring, hq L (α * ω) (α * x) hαω hx, hq L ω x hω hx0,
    hsum] at hc
  linear_combination hc
end Formalism.L2.Th1.F.S2IsogenyPsi
