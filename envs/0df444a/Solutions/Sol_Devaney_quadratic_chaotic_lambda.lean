-- Prove2me | solution 1 for Devaney.quadratic_chaotic_lambda
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T13:19:58.478465+00:00
-- url     : https://prove2.me/submissions/ec6a53fc-6740-439a-a2e0-5a3c6db279ef

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic
import Theorems.Thm_Devaney_quadratic_sensitiveDependence
import Theorems.Thm_Devaney_quadratic_exists_dense_orbit
import Theorems.Thm_Devaney_quadratic_dense_per
import Theorems.Thm_Devaney_lambda_isCantorSet

open Devaney

/-- If `f` maps `J` into itself, every point of `J` is an accumulation point of `J`, and some
point of `J` has a forward orbit that is dense in `J`, then `f` is topologically transitive
on `J`. -/
theorem topologicallyTransitive_of_denseOrbit {Y : Type*} [PseudoMetricSpace Y] [T1Space Y]
    (J : Set Y) (f : Y → Y) (hinv : Set.MapsTo f J J)
    (hacc : ∀ x ∈ J, AccPt x (Filter.principal J))
    (hdense : ∃ x ∈ J, J ⊆ closure {y : Y | ∃ n : ℕ, f^[n] x = y}) :
    TopologicallyTransitive J f := by
  obtain ⟨x, hxJ, hx⟩ := hdense
  intro U V hU hV hUJ hVJ
  obtain ⟨u, huU, huJ⟩ := hUJ
  obtain ⟨v, hvV, hvJ⟩ := hVJ
  -- some iterate of `x` lands in `U`
  obtain ⟨w, hwU, m, hmw⟩ := mem_closure_iff.mp (hx huJ) U hU huU
  have hmU : f^[m] x ∈ U := by rwa [hmw]
  have hmJ : f^[m] x ∈ J := hinv.iterate m hxJ
  -- the finitely many orbit points with time at most `m`
  set F : Set Y := (fun j => f^[j] x) '' Set.Iic m with hF
  have hFfin : F.Finite := (Set.finite_Iic m).image _
  -- find a point of `V ∩ J` avoiding `F`
  have hFv : (F \ {v}).Finite := hFfin.sdiff
  have hWopen : IsOpen (V \ (F \ {v})) := hV.sdiff hFv.isClosed
  have hvW : v ∈ V \ (F \ {v}) := ⟨hvV, by simp⟩
  obtain ⟨q, ⟨hqW, hqJ⟩, hqv⟩ := (accPt_iff_nhds.mp (hacc v hvJ)) _ (hWopen.mem_nhds hvW)
  have hqV : q ∈ V := hqW.1
  have hqF : q ∉ F := fun h => hqW.2 ⟨h, hqv⟩
  -- some iterate of `x` lands in `V`, at a time later than `m`
  have hVFopen : IsOpen (V \ F) := hV.sdiff hFfin.isClosed
  obtain ⟨z, hzVF, k, hkz⟩ := mem_closure_iff.mp (hx hqJ) _ hVFopen ⟨hqV, hqF⟩
  have hkV : f^[k] x ∈ V := by rw [hkz]; exact hzVF.1
  have hkF : f^[k] x ∉ F := by rw [hkz]; exact hzVF.2
  have hkm : m < k := by
    by_contra hc
    exact hkF ⟨k, by simpa using Nat.le_of_not_lt hc, rfl⟩
  refine ⟨k - m, by omega, f^[k] x, ⟨f^[m] x, ⟨hmU, hmJ⟩, ?_⟩, hkV⟩
  rw [← Function.iterate_add_apply f (k - m) m x]
  congr 1
  omega

theorem quadratic_topologicallyTransitive (μ : ℝ) (hμ : 2 + Real.sqrt 5 < μ) :
    TopologicallyTransitive (Lambda μ) (quadratic μ) := by
  obtain ⟨-, -, -, hacc⟩ := lambda_isCantorSet μ hμ
  exact topologicallyTransitive_of_denseOrbit _ _ (mapsTo_Lambda μ) hacc
    (quadratic_exists_dense_orbit μ hμ)

theorem solution (μ : ℝ) (hμ : 2 + Real.sqrt 5 < μ) :
    Chaotic (Lambda μ) (quadratic μ) :=
  ⟨quadratic_sensitiveDependence μ hμ, quadratic_topologicallyTransitive μ hμ,
    quadratic_dense_per μ hμ⟩
