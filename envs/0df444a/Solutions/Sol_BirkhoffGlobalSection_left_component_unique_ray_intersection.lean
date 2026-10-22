-- Prove2me | solution 1 for BirkhoffGlobalSection.left_component_unique_ray_intersection
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T09:58:53.348983+00:00
-- url     : https://prove2.me/submissions/1209e5c4-6c1a-4fb7-8fb0-bb870a4c9c97

import Mathlib
import Theorems.Thm_BirkhoffGlobalSection_left_component_ray_exists
import Theorems.Thm_BirkhoffGlobalSection_left_component_ray_unique_scale
import Theorems.Thm_BirkhoffGlobalSection_left_component_radial_norm_positive

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (f : LeftEnergyState μ c → {x : Phase // x ∈ unitThreeSphere})
    (hrad : ∀ s, (f s : Phase) =
      fun i => (s : Phase) i /
        Real.sqrt (zNormSq (s : Phase) + wNormSq (s : Phase))) :
    Function.Bijective f := by
  have hscale (x : Phase) (r : ℝ) :
      zNormSq (fun i : Fin 4 => r * x i) +
        wNormSq (fun i : Fin 4 => r * x i) =
        r ^ 2 * (zNormSq x + wNormSq x) := by
    dsimp [zNormSq, wNormSq]
    ring
  have hpositive (s : LeftEnergyState μ c) :
      0 < Real.sqrt (zNormSq (s : Phase) + wNormSq (s : Phase)) :=
    Real.sqrt_pos.2 (left_component_radial_norm_positive μ c hμ0 hμ1 hc
      (s : Phase) s.property)
  have hrepr (s : LeftEnergyState μ c) :
      (s : Phase) = fun i =>
        Real.sqrt (zNormSq (s : Phase) + wNormSq (s : Phase)) *
          (f s : Phase) i := by
    funext i
    have hi := congrFun (hrad s) i
    rw [hi]
    have hn : Real.sqrt (zNormSq (s : Phase) + wNormSq (s : Phase)) ≠ 0 :=
      ne_of_gt (hpositive s)
    field_simp [hn] <;> ring
  constructor
  · intro s t heq
    let x : Phase := (f s : Phase)
    have hx : x ∈ unitThreeSphere := (f s).property
    let rs : ℝ := Real.sqrt (zNormSq (s : Phase) + wNormSq (s : Phase))
    let rt : ℝ := Real.sqrt (zNormSq (t : Phase) + wNormSq (t : Phase))
    have hsrep : (s : Phase) = fun i : Fin 4 => rs * x i := hrepr s
    have htrep : (t : Phase) = fun i : Fin 4 => rt * x i := by
      simpa only [x, rt, heq] using hrepr t
    have hsr : (fun i : Fin 4 => rs * x i) ∈ leftEnergyComponent μ c := by
      rw [← hsrep]
      exact s.property
    have htr : (fun i : Fin 4 => rt * x i) ∈ leftEnergyComponent μ c := by
      rw [← htrep]
      exact t.property
    have hrs : 0 < rs := hpositive s
    have hrt : 0 < rt := hpositive t
    have hsame := left_component_ray_unique_scale μ c hμ0 hμ1 hc
      x hx rs rt hrs hrt hsr htr
    apply Subtype.ext
    calc
      (s : Phase) = (fun i : Fin 4 => rs * x i) := hsrep
      _ = (fun i : Fin 4 => rt * x i) := by rw [hsame]
      _ = (t : Phase) := htrep.symm
  · intro x
    obtain ⟨r, hr, hs⟩ := left_component_ray_exists μ c hμ0 hμ1 hc
      (x : Phase) x.property
    let s : LeftEnergyState μ c := ⟨fun i : Fin 4 => r * (x : Phase) i, hs⟩
    refine ⟨s, ?_⟩
    have hx : zNormSq (x : Phase) + wNormSq (x : Phase) = 1 := x.property
    have hnorm : zNormSq (s : Phase) + wNormSq (s : Phase) = r ^ 2 := by
      change zNormSq (fun i : Fin 4 => r * (x : Phase) i) +
        wNormSq (fun i : Fin 4 => r * (x : Phase) i) = r ^ 2
      rw [hscale, hx]
      ring
    have hsqrt : Real.sqrt (zNormSq (s : Phase) + wNormSq (s : Phase)) = r := by
      rw [hnorm, Real.sqrt_sq_eq_abs, abs_of_pos hr]
    apply Subtype.ext
    funext i
    have hi := congrFun (hrad s) i
    rw [hi, hsqrt]
    change r * (x : Phase) i / r = (x : Phase) i
    field_simp [ne_of_gt hr] <;> ring
