-- Prove2me | solution 1 for DeepONetUniversal.arzela_ascoli
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T23:29:16.803898+00:00
-- url     : https://prove2.me/submissions/17ce559e-c330-4d36-9ca7-a5f9e52e09c3

import Mathlib
import Definitions.Def_DeepONetUniversal_Basic

open MeasureTheory Filter Topology DeepONetUniversal

theorem solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (K : Set X) (hK : IsCompact K) (V : Set C(K, ℝ)) :
    IsCompact (closure V) ↔
      IsUniformlyBounded ((fun f : C(K, ℝ) => (f : K → ℝ)) '' V) ∧
        IsEquicontinuousFamily ((fun f : C(K, ℝ) => (f : K → ℝ)) '' V) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  constructor
  · intro hcomp
    constructor
    · -- Uniform boundedness
      obtain ⟨M, hM⟩ := (hcomp.isBounded.subset subset_closure).subset_closedBall (0 : C(K, ℝ))
      refine ⟨M, ?_⟩
      rintro _ ⟨f, hfV, rfl⟩ x
      have hfM : ‖f‖ ≤ M := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hM hfV
      exact (ContinuousMap.norm_coe_le_norm f x).trans hfM
    · -- Equicontinuity
      intro ε hε
      have htb : TotallyBounded V := hcomp.totallyBounded.subset subset_closure
      obtain ⟨T, hTfin, hTcov⟩ := Metric.totallyBounded_iff.mp htb (ε / 3) (by positivity)
      have huc : ∀ g ∈ T, ∃ δ > 0, ∀ x y : K, dist x y < δ → |g x - g y| < ε / 3 := by
        intro g _
        have hguc := CompactSpace.uniformContinuous_of_continuous g.continuous
        obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuous_iff.mp hguc (ε / 3) (by positivity)
        exact ⟨δ, hδpos, fun x y hxy => by simpa [Real.dist_eq] using hδ hxy⟩
      choose δf hδf_pos hδf using huc
      classical
      let sT : Finset C(K, ℝ) := hTfin.toFinset
      by_cases hsT : sT.Nonempty
      · let δ : ℝ := sT.inf' hsT (fun g => if hg : g ∈ T then δf g hg else 1)
        have hδ_pos : 0 < δ := by
          rw [Finset.lt_inf'_iff]
          intro g hg
          have hgT : g ∈ T := hTfin.mem_toFinset.mp hg
          simp only [dif_pos hgT]
          exact hδf_pos g hgT
        refine ⟨δ, hδ_pos, ?_⟩
        rintro _ ⟨f, hfV, rfl⟩ x y hxy
        have hfmem := hTcov hfV
        simp only [Set.mem_iUnion, Metric.mem_ball] at hfmem
        obtain ⟨g, hgT, hfg⟩ := hfmem
        have hfg_pt : ∀ z : K, |f z - g z| < ε / 3 := by
          intro z
          have := (ContinuousMap.dist_lt_iff (by positivity)).mp hfg z
          simpa [Real.dist_eq] using this
        have hδ_le : δ ≤ δf g hgT := by
          have hg_sT : g ∈ sT := hTfin.mem_toFinset.mpr hgT
          have hle := Finset.inf'_le (f := fun g => if hg : g ∈ T then δf g hg else 1) hg_sT
          simpa [dif_pos hgT] using hle
        have hg_xy : |g x - g y| < ε / 3 := hδf g hgT x y (hxy.trans_le hδ_le)
        have h1 := hfg_pt x
        have h2 := hfg_pt y
        calc |f x - f y|
            = |(f x - g x) + (g x - g y) + (g y - f y)| := by ring_nf
          _ ≤ |f x - g x| + |g x - g y| + |g y - f y| := by
              linarith [abs_add_le (f x - g x + (g x - g y)) (g y - f y),
                abs_add_le (f x - g x) (g x - g y)]
          _ = |f x - g x| + |g x - g y| + |f y - g y| := by rw [abs_sub_comm (g y) (f y)]
          _ < ε / 3 + ε / 3 + ε / 3 := by linarith
          _ = ε := by ring
      · refine ⟨1, zero_lt_one, ?_⟩
        rintro _ ⟨f, hfV, rfl⟩ x y _
        have hfmem := hTcov hfV
        simp only [Set.mem_iUnion] at hfmem
        obtain ⟨g, hgT, _⟩ := hfmem
        exact (hsT ⟨g, hTfin.mem_toFinset.mpr hgT⟩).elim
  · rintro ⟨⟨M, hM⟩, heq⟩
    -- Prove closure V is compact via completeness + total boundedness of V
    refine isCompact_iff_totallyBounded_isComplete.mpr ⟨?_, isClosed_closure.isComplete⟩
    refine TotallyBounded.closure ?_
    rw [Metric.totallyBounded_iff]
    intro ε hε
    by_cases hVne : V.Nonempty
    · obtain ⟨δ, hδpos, hδ⟩ := heq (ε / 4) (by positivity)
      -- Cover K by finitely many δ-balls
      obtain ⟨sK, hsKfin, hsKcov⟩ :=
        Metric.totallyBounded_iff.mp (isCompact_univ (X := K)).totallyBounded δ hδpos
      let FK : Finset K := hsKfin.toFinset
      -- Cover [-M, M] by finitely many (ε/4)-balls
      have hIcc_comp : IsCompact (Set.Icc (-M) M) := isCompact_Icc
      obtain ⟨sR, hsRfin, hsRcov⟩ :=
        Metric.totallyBounded_iff.mp hIcc_comp.totallyBounded (ε / 4) (by positivity)
      let FR : Finset ℝ := hsRfin.toFinset
      -- For each choice function φ : FK → FR, pick a representative f ∈ V if one exists
      let P (φ : FK → FR) (f : C(K, ℝ)) : Prop :=
        f ∈ V ∧ ∀ x : FK, |f x.1 - (φ x).1| < ε / 4
      classical
      let reps : Finset C(K, ℝ) :=
        Finset.univ.biUnion fun φ : FK → FR =>
          if h : ∃ f, P φ f then {h.choose} else ∅
      refine ⟨(reps : Set C(K, ℝ)), reps.finite_toSet, ?_⟩
      intro f hfV
      -- For each x : FK, pick y ∈ FR with |f x - y| < ε / 4
      have hchoose : ∀ x : FK, ∃ y : FR, |f x.1 - y.1| < ε / 4 := by
        intro x
        have hfx : f x.1 ∈ Set.Icc (-M) M := by
          have := hM f ⟨f, hfV, rfl⟩ x.1
          exact abs_le.mp this
        have hmem := hsRcov hfx
        simp only [Set.mem_iUnion, Metric.mem_ball, Real.dist_eq] at hmem
        obtain ⟨y, hyR, hfy⟩ := hmem
        exact ⟨⟨y, hsRfin.mem_toFinset.mpr hyR⟩, hfy⟩
      choose φ hφ using hchoose
      have hex : ∃ g, P φ g := ⟨f, hfV, hφ⟩
      let g := hex.choose
      have hgP : P φ g := hex.choose_spec
      have hg_mem : g ∈ (reps : Set C(K, ℝ)) := by
        simp only [reps, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨φ, by simp [dif_pos hex, g]⟩
      simp only [Set.mem_iUnion, Metric.mem_ball]
      refine ⟨g, hg_mem, ?_⟩
      rw [ContinuousMap.dist_lt_iff hε]
      intro x
      have hxmem := hsKcov (Set.mem_univ x)
      simp only [Set.mem_iUnion, Metric.mem_ball] at hxmem
      obtain ⟨x₀, hx₀K, hxx₀⟩ := hxmem
      let x₀' : FK := ⟨x₀, hsKfin.mem_toFinset.mpr hx₀K⟩
      have h1 : |f x - f x₀| < ε / 4 := hδ f ⟨f, hfV, rfl⟩ x x₀ hxx₀
      have h2 : |g x - g x₀| < ε / 4 := hδ g ⟨g, hgP.1, rfl⟩ x x₀ hxx₀
      have h3 : |f x₀ - (φ x₀').1| < ε / 4 := hφ x₀'
      have h4 : |g x₀ - (φ x₀').1| < ε / 4 := hgP.2 x₀'
      rw [Real.dist_eq]
      calc |f x - g x|
          = |(f x - f x₀) + (f x₀ - (φ x₀').1) + ((φ x₀').1 - g x₀) + (g x₀ - g x)| := by ring_nf
        _ ≤ |f x - f x₀| + |f x₀ - (φ x₀').1| + |(φ x₀').1 - g x₀| + |g x₀ - g x| := by
            have ha := abs_add_le ((f x - f x₀) + (f x₀ - (φ x₀').1) + ((φ x₀').1 - g x₀)) (g x₀ - g x)
            have hb := abs_add_le ((f x - f x₀) + (f x₀ - (φ x₀').1)) ((φ x₀').1 - g x₀)
            have hc := abs_add_le (f x - f x₀) (f x₀ - (φ x₀').1)
            linarith
        _ = |f x - f x₀| + |f x₀ - (φ x₀').1| + |g x₀ - (φ x₀').1| + |g x - g x₀| := by
            rw [abs_sub_comm (φ x₀').1 (g x₀), abs_sub_comm (g x₀) (g x)]
        _ < ε / 4 + ε / 4 + ε / 4 + ε / 4 := by linarith
        _ = ε := by ring
    · rw [Set.not_nonempty_iff_eq_empty] at hVne
      refine ⟨∅, Set.finite_empty, ?_⟩
      simp [hVne]
