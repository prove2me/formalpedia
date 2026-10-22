-- Prove2me | solution 1 for BirkhoffGlobalSection.compact_unique_ray_graph_compact
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:04:59.855754+00:00
-- url     : https://prove2.me/submissions/c8a8087e-ac55-4f66-9bb1-a36700c692b8

import Mathlib
import Theorems.Thm_BirkhoffGlobalSection_phase_polar_homeomorph

open BirkhoffGlobalSection

theorem solution (S : Set Phase)
    (hcompact : IsCompact S)
    (hzero : (fun _ : Fin 4 => (0 : ℝ)) ∉ S) :
    IsCompact
      {p : {x : Phase // x ∈ unitThreeSphere} × ℝ |
        0 < p.2 ∧
        (fun i : Fin 4 => p.2 * (p.1 : Phase) i) ∈ S} := by
  obtain ⟨e, he⟩ := phase_polar_homeomorph
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hcompact
  let g : S → {s : Phase // s ≠ (fun _ : Fin 4 => (0 : ℝ))} :=
    fun s => ⟨s.val, by
      intro hz
      apply hzero
      simpa only [hz] using s.property⟩
  have hg : Continuous g := by
    exact continuous_subtype_val.subtype_mk _
  let f : S → ({x : Phase // x ∈ unitThreeSphere} × ℝ) :=
    fun s => ((e (g s)).1, ((e (g s)).2 : ℝ))
  have hf : Continuous f := by
    have hA : Continuous (fun s : S => e (g s)) := e.continuous.comp hg
    exact (continuous_fst.comp hA).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp hA))
  have himage : Set.range f =
      {p : {x : Phase // x ∈ unitThreeSphere} × ℝ |
        0 < p.2 ∧
        (fun i : Fin 4 => p.2 * (p.1 : Phase) i) ∈ S} := by
    ext p
    constructor
    · rintro ⟨s, rfl⟩
      have hback := he (e (g s)).1 (e (g s)).2
      rw [e.symm_apply_apply] at hback
      refine ⟨(e (g s)).2.property, ?_⟩
      rw [← hback]
      exact s.property
    · rintro ⟨hr, hp⟩
      let pair : {x : Phase // x ∈ unitThreeSphere} × {r : ℝ // 0 < r} :=
        (p.1, ⟨p.2, hr⟩)
      let s : S := ⟨(e.symm pair).val, by
        have hval := he p.1 ⟨p.2, hr⟩
        rw [hval]
        exact hp⟩
      refine ⟨s, ?_⟩
      have hgs : g s = e.symm pair := by
        apply Subtype.ext
        rfl
      simp [f, hgs, pair]
  rw [← himage]
  exact isCompact_range hf
