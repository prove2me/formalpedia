-- Prove2me | solution 1 for EquiSegment.Multivalued.lemma_2_2_a
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:50:46.773786+00:00
-- url     : https://prove2.me/submissions/4ea3ba2f-119a-4a04-a176-df2fb47c9524

import Mathlib
import Definitions.Def_EquiSegment_Multivalued_Setting

set_option autoImplicit false
open EquiSegment.Multivalued Topology

theorem ES_nonempty (Z : Set ((ℝ × ℝ) × ℝ)) (hZ : IsNice Z) : Z.Nonempty := by
  obtain ⟨_, hsub, hsep⟩ := hZ
  have hs : ((0 : ℝ), (0 : ℝ)) ∈ Seg := ⟨le_refl _, le_refl _, zero_le_one⟩
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hSconn : IsPreconnected ((fun y : ℝ => (((0 : ℝ), (0 : ℝ)), y)) '' Set.Icc (-1 : ℝ) 1) :=
    isPreconnected_Icc.image _
      (by fun_prop : Continuous fun y : ℝ => (((0 : ℝ), (0 : ℝ)), y)).continuousOn
  have hSsub : (fun y : ℝ => (((0 : ℝ), (0 : ℝ)), y)) '' Set.Icc (-1 : ℝ) 1 ⊆ Cyl \ Z := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨⟨hs, hy⟩, fun hmem => ?_⟩
    rw [hcon] at hmem
    exact hmem
  have hb : (((0 : ℝ), (0 : ℝ)), (-1 : ℝ)) ∈ Bottom := ⟨hs, rfl⟩
  have ht : (((0 : ℝ), (0 : ℝ)), (1 : ℝ)) ∈ EquiSegment.Multivalued.Top := ⟨hs, rfl⟩
  apply hsep.2.2 _ hb _ ht
  exact hSconn.subset_connectedComponentIn (x := (((0 : ℝ), (0 : ℝ)), (-1 : ℝ)))
    ⟨-1, ⟨le_refl _, by norm_num⟩, rfl⟩ hSsub ⟨1, ⟨by norm_num, le_refl _⟩, rfl⟩

theorem ES_seg_convex : Convex ℝ Seg := by
  intro s hs t ht a b ha hb hab
  simp only [Seg, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at *
  refine ⟨by nlinarith [mul_nonneg ha hs.1, mul_nonneg hb ht.1],
    by nlinarith [mul_nonneg ha (sub_nonneg.2 hs.2.1), mul_nonneg hb (sub_nonneg.2 ht.2.1)],
    by nlinarith [mul_nonneg ha (sub_nonneg.2 hs.2.2), mul_nonneg hb (sub_nonneg.2 ht.2.2)]⟩

theorem solution (Z : Set ((ℝ × ℝ) × ℝ)) (hZ : IsNice Z) :
    ∃ φ : ℝ × ℝ → ℝ → ℝ, IsRep φ ∧ zeroSet φ = Z := by
  classical
  have hne := ES_nonempty Z hZ
  obtain ⟨hZk, hZsub, hsep⟩ := hZ
  have hZcl : IsClosed Z := hZk.isClosed
  have hZCyl : Z ⊆ Cyl := fun x hx => ⟨(hZsub hx).1, Set.Ioo_subset_Icc_self (hZsub hx).2⟩
  have hCylconv : Convex ℝ Cyl := ES_seg_convex.prod (convex_Icc _ _)
  -- the part of the cylinder joined to the bottom
  set U : Set ((ℝ × ℝ) × ℝ) :=
    {x | x ∈ Cyl \ Z ∧ ∃ a ∈ Bottom, x ∈ connectedComponentIn (Cyl \ Z) a} with hU
  set f : (ℝ × ℝ) × ℝ → ℝ := fun x => Metric.infDist x Z with hf
  have hfc : Continuous f := Metric.continuous_infDist_pt Z
  have hf0 : ∀ x, 0 ≤ f x := fun x => Metric.infDist_nonneg
  have hfZ : ∀ x, f x = 0 ↔ x ∈ Z := fun x => (hZcl.mem_iff_infDist_zero hne).symm
  -- local structure
  have hloc : ∀ x ∈ Cyl \ Z, ∃ ε > 0, ∀ y ∈ Metric.ball x ε ∩ Cyl,
      y ∈ Cyl \ Z ∧ (y ∈ U ↔ x ∈ U) := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hZcl.isOpen_compl x hx.2
    have hsub : Metric.ball x ε ∩ Cyl ⊆ Cyl \ Z := fun y hy => ⟨hy.2, hball hy.1⟩
    have hconn : IsPreconnected (Metric.ball x ε ∩ Cyl) :=
      ((convex_ball x ε).inter hCylconv).isPreconnected
    have hcomp := hconn.subset_connectedComponentIn ⟨Metric.mem_ball_self hε, hx.1⟩ hsub
    refine ⟨ε, hε, fun y hy => ⟨hsub hy, ?_⟩⟩
    have hyx : y ∈ connectedComponentIn (Cyl \ Z) x := hcomp hy
    have heq : connectedComponentIn (Cyl \ Z) x = connectedComponentIn (Cyl \ Z) y :=
      connectedComponentIn_eq hyx
    have hxx : x ∈ connectedComponentIn (Cyl \ Z) x := mem_connectedComponentIn hx
    constructor
    · rintro ⟨_, a, ha, hya⟩
      refine ⟨hx, a, ha, ?_⟩
      have h1 : connectedComponentIn (Cyl \ Z) a = connectedComponentIn (Cyl \ Z) y :=
        connectedComponentIn_eq hya
      rw [h1, ← heq]; exact hxx
    · rintro ⟨_, a, ha, hxa⟩
      refine ⟨hsub hy, a, ha, ?_⟩
      have h1 : connectedComponentIn (Cyl \ Z) a = connectedComponentIn (Cyl \ Z) x :=
        connectedComponentIn_eq hxa
      rw [h1]; exact hyx
  let φ : ℝ × ℝ → ℝ → ℝ := fun s y => if ((s, y) ∈ U) then -f (s, y) else f (s, y)
  have hφabs : ∀ x : (ℝ × ℝ) × ℝ, φ x.1 x.2 = 0 ↔ f x = 0 := by
    intro x
    show (if ((x.1, x.2) ∈ U) then -f (x.1, x.2) else f (x.1, x.2)) = 0 ↔ f x = 0
    split_ifs <;> simp
  have hcont : ContinuousOn (fun x : (ℝ × ℝ) × ℝ => φ x.1 x.2) Cyl := by
    intro x hxC
    by_cases hxZ : x ∈ Z
    · have hfx : f x = 0 := (hfZ x).2 hxZ
      have hgx : φ x.1 x.2 = 0 := (hφabs x).2 hfx
      rw [ContinuousWithinAt, hgx, Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      refine ⟨ε, hε, fun y hy hyd => ?_⟩
      have h1 : |φ y.1 y.2| = f y := by
        show |(if ((y.1, y.2) ∈ U) then -f (y.1, y.2) else f (y.1, y.2))| = f y
        split_ifs
        · rw [abs_neg]; exact abs_of_nonneg (hf0 _)
        · exact abs_of_nonneg (hf0 _)
      have h2 : f y ≤ dist y x := by
        exact Metric.infDist_le_dist_of_mem (x := y) hxZ
      rw [Real.dist_eq, sub_zero, h1]
      exact lt_of_le_of_lt h2 hyd
    · obtain ⟨ε, hε, hεy⟩ := hloc x ⟨hxC, hxZ⟩
      by_cases hxU : x ∈ U
      · have hcw : ContinuousWithinAt (fun y : (ℝ × ℝ) × ℝ => -f y) Cyl x :=
          (hfc.neg).continuousWithinAt
        refine hcw.congr_of_eventuallyEq ?_ ?_
        · have hmem : Metric.ball x ε ∩ Cyl ∈ 𝓝[Cyl] x :=
            Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hε))
              self_mem_nhdsWithin
          filter_upwards [hmem] with y hy
          have hyU : y ∈ U := (hεy y hy).2.2 hxU
          show (if ((y.1, y.2) ∈ U) then -f (y.1, y.2) else f (y.1, y.2)) = -f y
          rw [if_pos hyU]
        · show (if ((x.1, x.2) ∈ U) then -f (x.1, x.2) else f (x.1, x.2)) = -f x
          rw [if_pos hxU]
      · have hcw : ContinuousWithinAt f Cyl x := hfc.continuousWithinAt
        refine hcw.congr_of_eventuallyEq ?_ ?_
        · have hmem : Metric.ball x ε ∩ Cyl ∈ 𝓝[Cyl] x :=
            Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hε))
              self_mem_nhdsWithin
          filter_upwards [hmem] with y hy
          have hyU : y ∉ U := fun h => hxU ((hεy y hy).2.1 h)
          show (if ((y.1, y.2) ∈ U) then -f (y.1, y.2) else f (y.1, y.2)) = f y
          rw [if_neg hyU]
        · show (if ((x.1, x.2) ∈ U) then -f (x.1, x.2) else f (x.1, x.2)) = f x
          rw [if_neg hxU]
  refine ⟨φ, ⟨hcont, fun s hs => ?_⟩, ?_⟩
  · have hbot : (s, (-1 : ℝ)) ∈ Bottom := ⟨hs, rfl⟩
    have hbotC : (s, (-1 : ℝ)) ∈ Cyl \ Z := by
      refine ⟨⟨hs, by norm_num, by norm_num⟩, fun h => ?_⟩
      exact (hsep.1 hbot).2 h
    have hbotU : (s, (-1 : ℝ)) ∈ U := ⟨hbotC, _, hbot, mem_connectedComponentIn hbotC⟩
    have htop : (s, (1 : ℝ)) ∈ EquiSegment.Multivalued.Top := ⟨hs, rfl⟩
    have htopC : (s, (1 : ℝ)) ∈ Cyl \ Z := hsep.2.1 htop
    have htopU : (s, (1 : ℝ)) ∉ U := by
      rintro ⟨_, a, ha, hmem⟩
      exact hsep.2.2 a ha _ htop hmem
    have hp1 : 0 < f (s, (-1 : ℝ)) :=
      lt_of_le_of_ne (hf0 _) (fun h => hbotC.2 ((hfZ _).1 h.symm))
    have hp2 : 0 < f (s, (1 : ℝ)) :=
      lt_of_le_of_ne (hf0 _) (fun h => htopC.2 ((hfZ _).1 h.symm))
    constructor
    · show (if ((s, (-1 : ℝ)) ∈ U) then -f (s, (-1 : ℝ)) else f (s, (-1 : ℝ))) < 0
      rw [if_pos hbotU]; linarith
    · show 0 < (if ((s, (1 : ℝ)) ∈ U) then -f (s, (1 : ℝ)) else f (s, (1 : ℝ)))
      rw [if_neg htopU]; exact hp2
  · ext x
    constructor
    · rintro ⟨_, h⟩
      exact (hfZ x).1 ((hφabs x).1 h)
    · intro hx
      exact ⟨hZCyl hx, (hφabs x).2 ((hfZ x).2 hx)⟩
