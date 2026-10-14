-- Prove2me | solution 1 for DiscreteConvex.MConvexSetsB.base_polyhedron_integral
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:17:19.415484+00:00
-- url     : https://prove2.me/submissions/6cc153a9-3daa-4feb-a16a-18870ae196a3

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSetsB_BasePolyhedron
import Definitions.Def_DiscreteConvex_MConvexSetsB_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexSetsB_IsIntegralPolyhedron



namespace DiscreteConvex.MConvexSetsB

namespace BPI

open Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma coe_le_iff (r : ℝ) (t : WithTop ℝ) : ((r : WithTop ℝ) ≤ t) ↔ ∀ s : ℝ, t = s → r ≤ s := by
  cases t with
  | top => simp
  | coe s => simp

/-- A set `X` is tight for `y`. -/
def Tight (ρ : Finset V → WithTop ℝ) (y : V → ℝ) (X : Finset V) : Prop :=
  ((∑ v ∈ X, y v : ℝ) : WithTop ℝ) = ρ X

lemma tight_union_inter (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) (y : V → ℝ)
    (hy : y ∈ BasePolyhedron ρ) {X Y : Finset V} (hX : Tight ρ y X) (hY : Tight ρ y Y) :
    Tight ρ y (X ∪ Y) ∧ Tight ρ y (X ∩ Y) := by
  obtain ⟨_, _, hsub⟩ := hρ
  have h1 := hy.1 (X ∪ Y)
  have h2 := hy.1 (X ∩ Y)
  have hs := hsub X Y
  unfold Tight at *
  rw [← hX, ← hY] at hs
  have key : ∑ v ∈ X ∪ Y, y v + ∑ v ∈ X ∩ Y, y v = ∑ v ∈ X, y v + ∑ v ∈ Y, y v :=
    Finset.sum_union_inter
  have hU : ρ (X ∪ Y) ≠ ⊤ := by
    intro h
    rw [h, WithTop.top_add] at hs
    exact (WithTop.coe_ne_top (top_le_iff.mp (by simpa only [← WithTop.coe_add] using hs)))
  have hI : ρ (X ∩ Y) ≠ ⊤ := by
    intro h
    rw [h, WithTop.add_top] at hs
    exact (WithTop.coe_ne_top (top_le_iff.mp (by simpa only [← WithTop.coe_add] using hs)))
  obtain ⟨p, hp⟩ := WithTop.ne_top_iff_exists.mp hU
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hI
  rw [← hp] at h1 hs ⊢
  rw [← hq] at h2 hs ⊢
  have h1' : ∑ v ∈ X ∪ Y, y v ≤ p := WithTop.coe_le_coe.mp h1
  have h2' : ∑ v ∈ X ∩ Y, y v ≤ q := WithTop.coe_le_coe.mp h2
  have hs' : p + q ≤ ∑ v ∈ X, y v + ∑ v ∈ Y, y v := by
    have : ((p + q : ℝ) : WithTop ℝ) ≤ ((∑ v ∈ X, y v + ∑ v ∈ Y, y v : ℝ) : WithTop ℝ) := by
      simpa only [WithTop.coe_add] using hs
    exact WithTop.coe_le_coe.mp this
  constructor
  · exact congrArg _ (by linarith)
  · exact congrArg _ (by linarith)

lemma tight_sup (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) (y : V → ℝ)
    (hy : y ∈ BasePolyhedron ρ) (S : Finset (Finset V)) (hS : ∀ X ∈ S, Tight ρ y X) :
    Tight ρ y (S.sup id) := by
  induction S using Finset.induction_on with
  | empty => simp [Tight, hρ.1]
  | @insert a S ha ih =>
    rw [Finset.sup_insert]
    exact (tight_union_inter ρ hρ y hy (hS a (Finset.mem_insert_self _ _))
      (ih fun X hX => hS X (Finset.mem_insert_of_mem hX))).1

lemma sum_int (y : V → ℝ) (s : Finset V) (h : ∀ x ∈ s, ∃ k : ℤ, y x = k) :
    ∃ k : ℤ, ∑ x ∈ s, y x = k := by
  refine ⟨∑ x ∈ s, ⌊y x⌋, ?_⟩
  push_cast
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨k, hk⟩ := h x hx
  rw [hk, Int.floor_intCast]

lemma ev_lt {a b : ℝ} (c : ℝ) (h : a < b) : ∀ᶠ t in 𝓝 (0:ℝ), a + t * c < b := by
  have hc : Continuous (fun t : ℝ => a + t * c) := by continuity
  exact hc.continuousAt.eventually_lt (continuousAt_const (y := b)) (by simpa using h)

lemma ev_gt {a b : ℝ} (c : ℝ) (h : b < a) : ∀ᶠ t in 𝓝 (0:ℝ), b < a + t * c := by
  have hc : Continuous (fun t : ℝ => a + t * c) := by continuity
  exact (continuousAt_const (y := b)).eventually_lt hc.continuousAt (by simpa using h)

lemma extreme_integral (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ)
    (hInt : IsIntegerValued ρ) (l : V → ℤ) (y : V → ℝ)
    (hy : y ∈ (BasePolyhedron ρ ∩ {z : V → ℝ | ∀ v, (l v : ℝ) ≤ z v ∧ z v ≤ l v + 1}).extremePoints ℝ) :
    ∀ v, ∃ k : ℤ, y v = k := by
  classical
  obtain ⟨hyP, hext⟩ := mem_extremePoints.mp hy
  by_contra hcon
  push_neg at hcon
  obtain ⟨w, hw⟩ := hcon
  let F : Finset (Finset V) :=
    Finset.univ.filter (fun X => Tight ρ y X ∧ ∃ u ∈ X, ∀ k : ℤ, y u ≠ k)
  have hFne : F.Nonempty := ⟨Finset.univ, by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hyP.1.2, w, hw⟩⟩
  obtain ⟨T, hTF, hTmin⟩ := Finset.exists_min_image F Finset.card hFne
  simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hTF hTmin
  obtain ⟨hTt, u, huT, hu⟩ := hTF
  let G : Finset (Finset V) :=
    Finset.univ.filter (fun X => Tight ρ y X ∧ X ⊆ T ∧ ∀ v ∈ X, ∃ k : ℤ, y v = k)
  set W := G.sup id with hWdef
  have hWt : Tight ρ y W :=
    tight_sup ρ hρ y hyP.1 G (fun X hX => (Finset.mem_filter.mp hX).2.1)
  have hWT : W ⊆ T := Finset.sup_le (fun X hX => (Finset.mem_filter.mp hX).2.2.1)
  have hWint : ∀ v ∈ W, ∃ k : ℤ, y v = k := by
    intro v hv
    obtain ⟨X, hX, hvX⟩ := Finset.mem_sup.mp hv
    exact (Finset.mem_filter.mp hX).2.2.2 v hvX
  have hint_sum : ∃ k : ℤ, ∑ v ∈ T \ W, y v = k := by
    rcases hInt T with h | ⟨k1, hk1⟩
    · exact absurd (hTt.trans h) WithTop.coe_ne_top
    rcases hInt W with h | ⟨k2, hk2⟩
    · exact absurd (hWt.trans h) WithTop.coe_ne_top
    refine ⟨k1 - k2, ?_⟩
    have e1 : ∑ v ∈ T, y v = k1 := by
      have := hTt.trans hk1; exact_mod_cast this
    have e2 : ∑ v ∈ W, y v = k2 := by
      have := hWt.trans hk2; exact_mod_cast this
    rw [Finset.sum_sdiff_eq_sub hWT, e1, e2]; push_cast; ring
  have huW : u ∉ W := fun h => by
    obtain ⟨k, hk⟩ := hWint u h
    exact hu k hk
  have hmem : u ∈ T \ W := Finset.mem_sdiff.mpr ⟨huT, huW⟩
  obtain ⟨v, hvTW, hvu, hv⟩ : ∃ v ∈ T \ W, v ≠ u ∧ ∀ k : ℤ, y v ≠ k := by
    by_contra hne
    push_neg at hne
    obtain ⟨k, hk⟩ := hint_sum
    rw [← Finset.add_sum_erase _ _ hmem] at hk
    obtain ⟨m, hm⟩ := sum_int y ((T \ W).erase u) (fun x hx => by
      obtain ⟨hxu, hx'⟩ := Finset.mem_erase.mp hx
      exact hne x hx' hxu)
    exact hu (k - m) (by push_cast; linarith)
  have hvT : v ∈ T := (Finset.mem_sdiff.mp hvTW).1
  -- no tight set separates u and v
  have nosep : ∀ Y : Finset V, Tight ρ y Y → (u ∈ Y ↔ v ∈ Y) := by
    intro Y hY
    have hYT := (tight_union_inter ρ hρ y hyP.1 hY hTt).2
    constructor
    · intro huY
      by_contra hvY
      have hlt : (Y ∩ T).card < T.card := by
        apply Finset.card_lt_card
        refine ⟨Finset.inter_subset_right, fun h => hvY (Finset.mem_inter.mp (h hvT)).1⟩
      have := hTmin (Y ∩ T) ⟨hYT, u, Finset.mem_inter.mpr ⟨huY, huT⟩, hu⟩
      omega
    · intro hvY
      by_contra huY
      have hlt : (Y ∩ T).card < T.card := by
        apply Finset.card_lt_card
        refine ⟨Finset.inter_subset_right, fun h => huY (Finset.mem_inter.mp (h huT)).1⟩
      have := hTmin (Y ∩ T) ⟨hYT, v, Finset.mem_inter.mpr ⟨hvY, hvT⟩, hv⟩
      omega
  -- the perturbation direction
  let d : V → ℝ := fun x => (if x = u then 1 else 0) - (if x = v then 1 else 0)
  have hdsum : ∀ X : Finset V, ∑ x ∈ X, d x =
      (if u ∈ X then 1 else 0) - (if v ∈ X then 1 else 0) := by
    intro X
    simp only [d, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  have ev : ∀ᶠ t in 𝓝 (0:ℝ), (fun x => y x + t * d x) ∈
      (BasePolyhedron ρ ∩ {z : V → ℝ | ∀ v, (l v : ℝ) ≤ z v ∧ z v ≤ l v + 1}) := by
    have hX : ∀ X : Finset V, ∀ᶠ t in 𝓝 (0:ℝ),
        ((∑ x ∈ X, (y x + t * d x) : ℝ) : WithTop ℝ) ≤ ρ X := by
      intro X
      have hsplit : ∀ t : ℝ, ∑ x ∈ X, (y x + t * d x) = ∑ x ∈ X, y x + t * ∑ x ∈ X, d x := by
        intro t; rw [Finset.sum_add_distrib, Finset.mul_sum]
      by_cases hXt : Tight ρ y X
      · have h0 : ∑ x ∈ X, d x = 0 := by
          rw [hdsum]
          by_cases huX : u ∈ X
          · have := (nosep X hXt).mp huX; simp [huX, this]
          · have : v ∉ X := fun h => huX ((nosep X hXt).mpr h)
            simp [huX, this]
        refine Filter.Eventually.of_forall (fun t => ?_)
        rw [hsplit, h0, mul_zero, add_zero]
        exact hyP.1.1 X
      · have hle := hyP.1.1 X
        cases hρX : ρ X with
        | top => exact Filter.Eventually.of_forall (fun t => le_top)
        | coe r =>
          rw [hρX] at hle
          have hlt : ∑ x ∈ X, y x < r := by
            refine lt_of_le_of_ne (WithTop.coe_le_coe.mp hle) (fun h => hXt ?_)
            unfold Tight; rw [hρX, h]
          filter_upwards [ev_lt (∑ x ∈ X, d x) hlt] with t ht
          rw [hsplit]
          exact WithTop.coe_le_coe.mpr ht.le
    have hbox : ∀ x : V, ∀ᶠ t in 𝓝 (0:ℝ),
        (l x : ℝ) ≤ y x + t * d x ∧ y x + t * d x ≤ l x + 1 := by
      intro x
      by_cases hx : x = u ∨ x = v
      · have hfx : ∀ k : ℤ, y x ≠ k := by
          rcases hx with rfl | rfl
          · exact hu
          · exact hv
        have hb := hyP.2 x
        have h1 : (l x : ℝ) < y x := lt_of_le_of_ne hb.1 (fun h => hfx (l x) h.symm)
        have h2 : y x < l x + 1 := lt_of_le_of_ne hb.2 (fun h => hfx (l x + 1) (by push_cast; exact h))
        filter_upwards [ev_gt (d x) h1, ev_lt (d x) h2] with t ht1 ht2
        exact ⟨ht1.le, ht2.le⟩
      · push_neg at hx
        have : d x = 0 := by simp [d, hx.1, hx.2]
        refine Filter.Eventually.of_forall (fun t => ?_)
        rw [this, mul_zero, add_zero]
        exact hyP.2 x
    have hall := Filter.eventually_all.mpr hX
    have hallb := Filter.eventually_all.mpr hbox
    filter_upwards [hall, hallb] with t ht htb
    refine ⟨⟨ht, ?_⟩, htb⟩
    have hsplit : ∑ x, (y x + t * d x) = ∑ x, y x + t * ∑ x, d x := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsplit, hdsum]
    simp only [Finset.mem_univ, if_true, sub_self, mul_zero, add_zero]
    exact hyP.1.2
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp ev
  have hp1 := hεP (y := ε / 2) (by rw [Real.dist_eq]; rw [sub_zero, abs_of_pos (by linarith)]; linarith)
  have hp2 := hεP (y := -(ε / 2)) (by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith)
  have hseg : y ∈ openSegment ℝ (fun x => y x + ε / 2 * d x) (fun x => y x + -(ε / 2) * d x) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have := (hext _ hp1 _ hp2 hseg).1
  have hu' := congrFun this u
  simp only [d, if_true, if_neg hvu.symm, sub_zero, mul_one] at hu'
  linarith

theorem bpi_core (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ)
    (hInt : IsIntegerValued ρ) :
    IsIntegralPolyhedron (BasePolyhedron ρ) := by
  classical
  have hconvB : Convex ℝ (BasePolyhedron ρ) := by
    intro a ha b hb s t hs ht hst
    refine ⟨fun X => ?_, ?_⟩
    · have h1 := ha.1 X
      have h2 := hb.1 X
      rw [coe_le_iff] at h1 h2 ⊢
      intro r hr
      have e : ∑ v ∈ X, (s • a + t • b) v = s * ∑ v ∈ X, a v + t * ∑ v ∈ X, b v := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          Finset.mul_sum]
      rw [e]
      have ha' := h1 r hr
      have hb' := h2 r hr
      have hr' : r = s * r + t * r := by rw [← add_mul, hst, one_mul]
      nlinarith [mul_le_mul_of_nonneg_left ha' hs, mul_le_mul_of_nonneg_left hb' ht]
    · have h1 := ha.2
      have h2 := hb.2
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hρ.2.1
      rw [← hr] at h1 h2 ⊢
      have h1' := WithTop.coe_injective h1
      have h2' := WithTop.coe_injective h2
      have e : ∑ v, (s • a + t • b) v = s * ∑ v, a v + t * ∑ v, b v := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          Finset.mul_sum]
      congr 1
      rw [e, h1', h2', ← add_mul, hst, one_mul]
  unfold IsIntegralPolyhedron
  apply Set.Subset.antisymm
  · intro x hx
    let l : V → ℤ := fun v => ⌊x v⌋
    set P := BasePolyhedron ρ ∩ {z : V → ℝ | ∀ v, (l v : ℝ) ≤ z v ∧ z v ≤ l v + 1} with hPdef
    have hxP : x ∈ P := ⟨hx, fun v => ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩⟩
    have hclosedB : IsClosed (BasePolyhedron ρ) := by
      have : BasePolyhedron ρ = (⋂ X : Finset V,
          {z : V → ℝ | ((∑ v ∈ X, z v : ℝ) : WithTop ℝ) ≤ ρ X}) ∩
          {z : V → ℝ | ((∑ v : V, z v : ℝ) : WithTop ℝ) = ρ Finset.univ} := by
        ext z; simp [BasePolyhedron]
      rw [this]
      apply IsClosed.inter
      · apply isClosed_iInter
        intro X
        cases hX : ρ X with
        | top => simp
        | coe r =>
          have : {z : V → ℝ | ((∑ v ∈ X, z v : ℝ) : WithTop ℝ) ≤ (r : WithTop ℝ)} =
              {z : V → ℝ | ∑ v ∈ X, z v ≤ r} := by
            ext z; simp only [Set.mem_setOf_eq, WithTop.coe_le_coe]
          rw [this]
          exact isClosed_le (by fun_prop) continuous_const
      · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hρ.2.1
        rw [← hr]
        have : {z : V → ℝ | ((∑ v : V, z v : ℝ) : WithTop ℝ) = (r : WithTop ℝ)} =
            {z : V → ℝ | ∑ v, z v = r} := by
          ext z; simp only [Set.mem_setOf_eq, WithTop.coe_inj]
        rw [this]
        exact isClosed_eq (by fun_prop) continuous_const
    have hbox_eq : {z : V → ℝ | ∀ v, (l v : ℝ) ≤ z v ∧ z v ≤ l v + 1} =
        Set.univ.pi (fun v => Set.Icc (l v : ℝ) (l v + 1)) := by
      ext z; simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
    have hclosedBox : IsClosed {z : V → ℝ | ∀ v, (l v : ℝ) ≤ z v ∧ z v ≤ l v + 1} := by
      rw [hbox_eq]; exact isClosed_set_pi (fun v _ => isClosed_Icc)
    have hcomp : IsCompact P := by
      have hK : IsCompact (Set.univ.pi (fun v => Set.Icc (l v : ℝ) (l v + 1))) :=
        isCompact_univ_pi (fun v => isCompact_Icc)
      refine hK.of_isClosed_subset (hclosedB.inter hclosedBox) ?_
      rw [← hbox_eq]; exact Set.inter_subset_right
    have hconvBox : Convex ℝ {z : V → ℝ | ∀ v, (l v : ℝ) ≤ z v ∧ z v ≤ l v + 1} := by
      rw [hbox_eq]; exact convex_pi (fun v _ => convex_Icc _ _)
    have hconvP : Convex ℝ P := hconvB.inter hconvBox
    have hKM := closure_convexHull_extremePoints hcomp hconvP
    -- extreme points lie in a finite set of integer points
    have hfin : (P.extremePoints ℝ).Finite := by
      have hF : (Set.univ.pi (fun v => ({(l v : ℝ), (l v : ℝ) + 1} : Set ℝ))).Finite :=
        Set.Finite.pi (fun v => by simp)
      refine hF.subset ?_
      intro z hz
      have hzi := extreme_integral ρ hρ hInt l z hz
      have hzP := (mem_extremePoints.mp hz).1
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff,
        forall_const]
      intro v
      obtain ⟨k, hk⟩ := hzi v
      have hb := hzP.2 v
      rw [hk] at hb ⊢
      have h1 : l v ≤ k := by exact_mod_cast hb.1
      have h2 : k ≤ l v + 1 := by exact_mod_cast hb.2
      rcases (show k = l v ∨ k = l v + 1 by omega) with h | h
      · left; rw [h]
      · right; rw [h]; push_cast; ring
    have hclosedHull : IsClosed (convexHull ℝ (P.extremePoints ℝ)) :=
      (hfin.isCompact_convexHull (𝕜 := ℝ)).isClosed
    rw [hclosedHull.closure_eq] at hKM
    have hxH : x ∈ convexHull ℝ (P.extremePoints ℝ) := by rw [hKM]; exact hxP
    refine convexHull_mono ?_ hxH
    intro z hz
    exact ⟨(mem_extremePoints.mp hz).1.1, extreme_integral ρ hρ hInt l z hz⟩
  · exact convexHull_min Set.inter_subset_left hconvB

end BPI

end DiscreteConvex.MConvexSetsB

open DiscreteConvex.MConvexSetsB


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) (hInt : IsIntegerValued ρ) :
    IsIntegralPolyhedron (BasePolyhedron ρ) := by
  exact BPI.bpi_core ρ hρ hInt
