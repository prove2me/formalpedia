-- Prove2me | solution 1 for FiniteEnergyPlane.exists_hasLoopWind
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T20:36:34.358403+00:00
-- url     : https://prove2.me/submissions/baa3bfa8-4828-45ed-8eac-524696eaceab

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected



namespace FiniteEnergyPlane

open scoped Real

theorem exists_hasLoopWind_aux (f : ℝ → ℂ) (hf : Continuous f) (hper : Function.Periodic f 1)
    (h0 : ∀ t, f t ≠ 0) : ∃ k : ℤ, HasLoopWind f k := by
  let f' : C(ℝ, {z : ℂ // z ≠ 0}) := ⟨fun t => ⟨f t, h0 t⟩, hf.subtype_mk _⟩
  obtain ⟨F₀, hF₀⟩ : ∃ z : ℂ, Complex.exp z = f 0 :=
    ⟨Complex.log (f 0), Complex.exp_log (h0 0)⟩
  obtain ⟨F, ⟨-, hF⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f' 0 F₀
    (Subtype.ext hF₀)
  have hexp : ∀ t, Complex.exp (F t) = f t := fun t => by
    have := congrFun hF t
    simpa [f'] using congrArg Subtype.val this
  have h10 : f 1 = f 0 := by simpa using hper 0
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (((hexp 1).trans h10).trans (hexp 0).symm)
  refine ⟨n, hf, hper, h0, fun t => (F t).im, Complex.continuous_im.comp F.continuous,
    fun t => ?_, ?_⟩
  · rw [← hexp t, Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_add]
    conv_lhs => rw [← Complex.re_add_im (F t)]
  · have := congrArg Complex.im hn
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat] at this
    linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution (f : ℝ → ℂ) (hf : Continuous f) (hper : Function.Periodic f 1)
    (h0 : ∀ t, f t ≠ 0) : ∃ k : ℤ, HasLoopWind f k :=
  exists_hasLoopWind_aux f hf hper h0
