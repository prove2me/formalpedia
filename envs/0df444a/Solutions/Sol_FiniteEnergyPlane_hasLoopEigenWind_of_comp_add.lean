-- Prove2me | solution 1 for FiniteEnergyPlane.hasLoopEigenWind_of_comp_add
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T21:24:53.524181+00:00
-- url     : https://prove2.me/submissions/d55f4499-a467-4703-b9d7-840d5a1fd687

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_comp_add
import Mathlib.Analysis.Calculus.Deriv.Shift



/-! B3W: windings of loop eigenfunctions are invariant under a shift of the loop. -/

namespace FiniteEnergyPlane

open scoped ContDiff

lemma bt_isLoopEigen_comp_add {S : ℝ → CauchyRiemannIndex.Mat 1} {μ : ℝ}
    {e : ℝ → CauchyRiemannIndex.Vec 1} (he : IsLoopEigen S μ e) (c : ℝ) :
    IsLoopEigen (fun t => S (t + c)) μ (fun t => e (t + c)) := by
  obtain ⟨hs, hp, ⟨t₀, ht₀⟩, heq⟩ := he
  refine ⟨hs.comp (contDiff_id.add contDiff_const), fun t => ?_, ⟨t₀ - c, by simpa using ht₀⟩,
    fun t => ?_⟩
  · show e (t + 1 + c) = e (t + c)
    rw [add_right_comm]
    exact hp _
  · rw [deriv_comp_add_const]
    exact heq (t + c)

theorem hasLoopEigenWind_of_comp_add_aux (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (c μ : ℝ) (k : ℤ)
    (h : HasLoopEigenWind (fun t => Sinf (t + c)) μ k) : HasLoopEigenWind Sinf μ k := by
  obtain ⟨⟨e, he⟩, hw⟩ := h
  refine ⟨⟨fun t => e (t + -c), ?_⟩, fun f hf => ?_⟩
  · have := bt_isLoopEigen_comp_add he (-c)
    simpa only [neg_add_cancel_right] using this
  · have h1 := hasLoopWind_comp_add (hw _ (bt_isLoopEigen_comp_add hf c)) (-c)
    simpa only [neg_add_cancel_right, add_neg_cancel_right] using h1

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (c μ : ℝ) (k : ℤ)
    (h : HasLoopEigenWind (fun t => Sinf (t + c)) μ k) : HasLoopEigenWind Sinf μ k :=
  hasLoopEigenWind_of_comp_add_aux Sinf c μ k h
