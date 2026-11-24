-- Prove2me | solution 1 for Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.exists_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:50.275614+00:00
-- url     : https://prove2.me/submissions/f9ff40b8-8b2e-43b9-b072-29bb9ec5dcab

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaQuasi
import Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_isPreconnected_compl
import Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_add_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
namespace Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
theorem _root_.solution (hq : ZetaQuasi) (hl : SigmaLogDeriv) (hz : SigmaZero) (L : PeriodPair) {ω : ℂ}
    (hω : ω ∈ L.lattice) :
    ∃ c : ℂ, ∀ z : ℂ, wSigma L (z + ω) = c * Complex.exp (wEta L ω * z) * wSigma L z := by
  by_cases hne : ∃ z₀ : ℂ, z₀ ∉ L.lattice
  swap
  · simp only [not_exists, not_not] at hne
    refine ⟨0, fun z => ?_⟩
    rw [zero_mul, zero_mul]
    exact (hz L _).mpr (hne _)
  obtain ⟨z₀, hz₀⟩ := hne
  set g : ℂ → ℂ := fun y => Formalism.L2.Th1.F.wSigma L (y + ω) * Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * y) /
    Formalism.L2.Th1.F.wSigma L y with hg
  have H : ∀ y : ℂ, y ∉ L.lattice → HasDerivAt g
      ((((Formalism.L2.Th1.F.wZeta L (y + ω) * Formalism.L2.Th1.F.wSigma L (y + ω)) * Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * y)
        + Formalism.L2.Th1.F.wSigma L (y + ω) * (Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * y) * (-(Formalism.L2.Th1.F.wEta L ω) * 1)))
          * Formalism.L2.Th1.F.wSigma L y
        - Formalism.L2.Th1.F.wSigma L (y + ω) * Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * y)
          * (Formalism.L2.Th1.F.wZeta L y * Formalism.L2.Th1.F.wSigma L y))
        / Formalism.L2.Th1.F.wSigma L y ^ 2) y := by
    intro y hy
    have h1 : HasDerivAt (fun x => Formalism.L2.Th1.F.wSigma L (x + ω))
        (Formalism.L2.Th1.F.wZeta L (y + ω) * Formalism.L2.Th1.F.wSigma L (y + ω)) y := by
      have h' := (hl L (y + ω) (add_notMem hω hy)).comp y ((hasDerivAt_id' y).add_const ω)
      rw [mul_one] at h'
      exact h'
    have h2 : HasDerivAt (fun x => Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * x))
        (Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * y) * (-(Formalism.L2.Th1.F.wEta L ω) * 1)) y :=
      ((hasDerivAt_id' y).const_mul (-(Formalism.L2.Th1.F.wEta L ω))).cexp
    exact (h1.mul h2).div (hl L y hy) ((hz L y).not.mpr hy)
  have hconst : ∀ {x y : ℂ}, x ∈ (L.lattice : Set ℂ)ᶜ → y ∈ (L.lattice : Set ℂ)ᶜ → g x = g y :=
    IsOpen.is_const_of_deriv_eq_zero (isOpen_compl L) (isPreconnected_compl L)
    (f := g) (fun y hy => (H y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => by
      rw [Pi.zero_apply, (H y hy).deriv, hq L ω y hω hy]
      ring)
  refine ⟨g z₀, fun z => ?_⟩
  by_cases hzL : z ∈ L.lattice
  · rw [(hz L z).mpr hzL, (hz L _).mpr (L.lattice.add_mem hzL hω)]
    simp
  · have hs : Formalism.L2.Th1.F.wSigma L z ≠ 0 := (hz L z).not.mpr hzL
    have hgz : g z = g z₀ := hconst hzL hz₀
    have h1 : g z * Formalism.L2.Th1.F.wSigma L z =
        Formalism.L2.Th1.F.wSigma L (z + ω) * Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * z) := by
      rw [hg]
      dsimp only
      field_simp
    have he : Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * z) * Complex.exp (Formalism.L2.Th1.F.wEta L ω * z) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_zero]
      congr 1
      ring
    calc Formalism.L2.Th1.F.wSigma L (z + ω)
        = Formalism.L2.Th1.F.wSigma L (z + ω) *
            (Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * z) * Complex.exp (Formalism.L2.Th1.F.wEta L ω * z)) := by
          rw [he, mul_one]
      _ = g z * Formalism.L2.Th1.F.wSigma L z * Complex.exp (Formalism.L2.Th1.F.wEta L ω * z) := by
          rw [h1]; ring
      _ = g z₀ * Complex.exp (Formalism.L2.Th1.F.wEta L ω * z) * Formalism.L2.Th1.F.wSigma L z := by
          rw [hgz]; ring
end Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
