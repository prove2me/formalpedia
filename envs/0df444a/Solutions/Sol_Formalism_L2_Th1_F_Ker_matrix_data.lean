-- Prove2me | solution 1 for Formalism.L2.Th1.F.Ker.matrix_data
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:37.81138+00:00
-- url     : https://prove2.me/submissions/620e55ae-a474-44d0-802e-b1b0968fce30

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral

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
open Formalism.L2.Th1.F.Ker
namespace Formalism.L2.Th1.F.Ker
theorem _root_.solution (L : PeriodPair) (α : ℂ) (h : MulStable L α) :
    ∃ a b c d : ℤ, α * L.ω₁ = a * L.ω₁ + c * L.ω₂ ∧ α * L.ω₂ = b * L.ω₁ + d * L.ω₂ ∧
      (2 * α.re = ((a + d : ℤ) : ℝ)) ∧ Complex.normSq α = ((a * d - b * c : ℤ) : ℝ) := by
  obtain ⟨a, c, hac⟩ := PeriodPair.mem_lattice.1 (h _ L.ω₁_mem_lattice)
  obtain ⟨b, d, hbd⟩ := PeriodPair.mem_lattice.1 (h _ L.ω₂_mem_lattice)
  refine ⟨a, b, c, d, hac.symm, hbd.symm, ?_⟩
  have hind := LinearIndependent.pair_iff.1 L.indep
  have hω1 : L.ω₁ ≠ 0 := by
    intro h0
    exact one_ne_zero (hind 1 0 (by simp [h0])).1
  have hω2 : L.ω₂ ≠ 0 := by
    intro h0
    exact one_ne_zero (hind 0 1 (by simp [h0])).2
  have e1 : (α - a) * L.ω₁ = c * L.ω₂ := by linear_combination -hac
  have e2 : (α - d) * L.ω₂ = b * L.ω₁ := by linear_combination -hbd
  have hq : α ^ 2 - ((a + d : ℤ) : ℂ) * α + ((a * d - b * c : ℤ) : ℂ) = 0 := by
    have h0 : ((α - a) * (α - d) - b * c) * (L.ω₁ * L.ω₂) = 0 := by
      linear_combination (α - d) * L.ω₂ * e1 + c * L.ω₂ * e2
    rcases mul_eq_zero.1 h0 with h1 | h1
    · push_cast
      linear_combination h1
    · exact absurd h1 (mul_ne_zero hω1 hω2)
  by_cases him : α.im = 0
  · have hαr : α = (α.re : ℂ) := Complex.ext (by simp) (by simp [him])
    obtain ⟨h1, h2⟩ := hind (α.re - a) (-c) (by
      rw [Complex.real_smul, Complex.real_smul]
      rw [hαr] at e1
      push_cast
      linear_combination e1)
    obtain ⟨h3, h4⟩ := hind (-b) (α.re - d) (by
      rw [Complex.real_smul, Complex.real_smul]
      rw [hαr] at e2
      push_cast
      linear_combination e2)
    have ha : (a : ℝ) = α.re := by linarith
    have hd : (d : ℝ) = α.re := by linarith
    have hb : (b : ℝ) = 0 := by linarith
    have hc : (c : ℝ) = 0 := by linarith
    constructor
    · push_cast
      linarith
    · rw [Complex.normSq_apply, him]
      push_cast
      rw [ha, hd, hb, hc]
      ring
  · have hq' : (starRingEnd ℂ α) ^ 2 - ((a + d : ℤ) : ℂ) * starRingEnd ℂ α + ((a * d - b * c : ℤ) : ℂ) = 0 := by
      have := congrArg (starRingEnd ℂ) hq
      simpa using this
    have hne : α - starRingEnd ℂ α ≠ 0 := by
      intro h0
      apply him
      have := congrArg Complex.im h0
      simp at this
      linarith
    have hsum : α + starRingEnd ℂ α = ((a + d : ℤ) : ℂ) := by
      have h0 : (α - starRingEnd ℂ α) * (α + starRingEnd ℂ α - ((a + d : ℤ) : ℂ)) = 0 := by
        linear_combination hq - hq'
      linear_combination (mul_eq_zero.1 h0).resolve_left hne
    have hprod : α * starRingEnd ℂ α = ((a * d - b * c : ℤ) : ℂ) := by
      linear_combination α * hsum - hq
    constructor
    · have h2 := Complex.add_conj α
      rw [hsum] at h2
      exact_mod_cast h2.symm
    · have h3 := Complex.mul_conj α
      rw [hprod] at h3
      exact_mod_cast h3.symm
end Formalism.L2.Th1.F.Ker
