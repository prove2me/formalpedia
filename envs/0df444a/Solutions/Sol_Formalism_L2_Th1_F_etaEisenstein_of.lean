-- Prove2me | solution 1 for Formalism.L2.Th1.F.etaEisenstein_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:51:08.164707+00:00
-- url     : https://prove2.me/submissions/ac8b17f9-a149-40aa-8cd3-8fca6cf23be2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_EtaEis
import Theorems.Thm_Formalism_L2_Th1_F_EtaEis_core

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
open EtaEis
namespace Formalism.L2.Th1.F
theorem _root_.solution (hs : ZetaSummable) (ho : ZetaOdd) : EtaEisenstein := by
  intro L
  have hu1 : L.ω₁ ≠ 0 := by
    intro h; exact L.ω₁_div_two_notMem_lattice (by rw [h]; simp)
  have hu2 : L.ω₂ ≠ 0 := by
    intro h; exact L.ω₂_div_two_notMem_lattice (by rw [h]; simp)

  have hS2 : ∀ x : ℂ, Summable fun p : ℤ × ℤ => tm ((p.2 : ℂ) * L.ω₂ + (p.1 : ℂ) * L.ω₁) x := by
    intro x
    refine ((L.latticeEquivProd.symm.toEquiv.summable_iff).mpr (hs L x)).congr fun p => ?_
    simp only [Function.comp, LinearEquiv.coe_toEquiv, L.latticeEquiv_symm_apply, tm, add_comm]
  have hZ2 : ∀ x : ℂ, wZeta L x = ∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * L.ω₂ + (p.1 : ℂ) * L.ω₁) x := by
    intro x
    rw [wZeta, ← L.latticeEquivProd.symm.toEquiv.tsum_eq]
    refine tsum_congr fun p => ?_
    simp only [LinearEquiv.coe_toEquiv, L.latticeEquiv_symm_apply, tm, add_comm]
  have hS1 : ∀ x : ℂ, Summable fun p : ℤ × ℤ => tm ((p.2 : ℂ) * L.ω₁ + (p.1 : ℂ) * L.ω₂) x := by
    intro x
    refine (((Equiv.prodComm ℤ ℤ).summable_iff).mpr (hS2 x)).congr fun p => ?_
    simp only [Function.comp, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, add_comm]
  have hZ1 : ∀ x : ℂ, wZeta L x = ∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * L.ω₁ + (p.1 : ℂ) * L.ω₂) x := by
    intro x
    rw [hZ2, ← (Equiv.prodComm ℤ ℤ).tsum_eq]
    refine tsum_congr fun p => ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, add_comm]
  have hE1 : wEta L L.ω₁ = 2 * wZeta L (L.ω₁ / 2) := by
    have := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 0
    simpa [wEta] using this
  have hE2 : wEta L L.ω₂ = 2 * wZeta L (L.ω₂ / 2) := by
    have := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 1
    simpa [wEta] using this
  constructor
  · rw [hE1, ← core L.ω₁ L.ω₂ hu1 hS1, ← hZ1, ← hZ1, ho]; ring
  · have h := core L.ω₂ L.ω₁ hu2 hS2
    rw [← hZ2, ← hZ2, ho] at h
    rw [hE2]
    calc 2 * wZeta L (L.ω₂ / 2) = wZeta L (L.ω₂ / 2) - -wZeta L (L.ω₂ / 2) := by ring
      _ = _ := h
      _ = _ := by
        congr 1
        refine tsum_congr fun m => tsum_congr fun n => ?_
        rw [add_comm]
end Formalism.L2.Th1.F
