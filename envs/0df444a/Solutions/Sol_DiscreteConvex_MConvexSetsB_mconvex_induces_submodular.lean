-- Prove2me | solution 1 for DiscreteConvex.MConvexSetsB.mconvex_induces_submodular
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:24:30.450543+00:00
-- url     : https://prove2.me/submissions/6176fb43-93b9-4e90-9775-4af2d71fe712

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexSetsB_InducedRho
import Definitions.Def_DiscreteConvex_MConvexSetsB_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSetsB_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntEmbed
import Definitions.Def_DiscreteConvex_MConvexSetsB_BasePolyhedron
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

lemma bp_convex (ρ : Finset V → WithTop ℝ) (hV : ρ Finset.univ ≠ ⊤) :
    Convex ℝ (BasePolyhedron ρ) := by
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
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hV
    rw [← hr] at h1 h2 ⊢
    have h1' := WithTop.coe_injective h1
    have h2' := WithTop.coe_injective h2
    have e : ∑ v, (s • a + t • b) v = s * ∑ v, a v + t * ∑ v, b v := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        Finset.mul_sum]
    congr 1
    rw [e, h1', h2', ← add_mul, hst, one_mul]

/-! ### M-convex sets -/

/-- `x + χ_u - χ_v ∈ B`. -/
def Edge (B : Set (V → ℤ)) (x : V → ℤ) (u v : V) : Prop :=
  (fun w => x w + CharVec u w - CharVec v w) ∈ B

lemma sum_move (x : V → ℤ) (u v : V) (X : Finset V) :
    ∑ w ∈ X, (x w + CharVec u w - CharVec v w) =
      ∑ w ∈ X, x w + (if u ∈ X then 1 else 0) - (if v ∈ X then 1 else 0) := by
  simp only [CharVec, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq']

/-- distance decreases -/
lemma dist_lt (x z x' : V → ℤ) (a b : V) (ha : x a < z a) (hb : z b < x b)
    (hx' : ∀ w, x' w = x w + CharVec a w - CharVec b w) :
    ∑ w, (x' w - z w).natAbs < ∑ w, (x w - z w).natAbs := by
  have hab : a ≠ b := by rintro rfl; omega
  apply Finset.sum_lt_sum
  · intro w _
    rw [hx']
    simp only [CharVec]
    by_cases hwa : w = a
    · subst hwa; simp [hab]; omega
    · by_cases hwb : w = b
      · subst hwb; simp [hwa]; omega
      · simp [hwa, hwb]
  · refine ⟨a, Finset.mem_univ _, ?_⟩
    rw [hx']
    simp only [CharVec, if_true, if_neg hab]
    omega

lemma lemG (B : Set (V → ℤ)) (hExc : ExchangeAxiomB B) (L : Finset V) (x : V → ℤ) (hx : x ∈ B)
    (hloc : ∀ u v, Edge B x u v → u ∈ L → v ∈ L) :
    ∀ y ∈ B, ∑ w ∈ L, y w ≤ ∑ w ∈ L, x w := by
  suffices H : ∀ n : ℕ, ∀ y ∈ B, ∑ w, (y w - x w).natAbs = n → ∑ w ∈ L, y w ≤ ∑ w ∈ L, x w by
    intro y hy; exact H _ y hy rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hy hn
    by_contra hlt
    push_neg at hlt
    obtain ⟨u, huL, hu⟩ := Finset.exists_lt_of_sum_lt hlt
    obtain ⟨v, hv, hy', hx'⟩ := hExc y hy x hx u hu
    have hv' : y v < x v := hv
    have hvL : v ∈ L := hloc u v hx' huL
    have hlt2 := dist_lt y x (fun w => y w - CharVec u w + CharVec v w) v u hv' hu
      (fun w => by ring)
    have := ih _ (hn ▸ hlt2) _ hy' rfl
    have e : ∑ w ∈ L, (y w - CharVec u w + CharVec v w) = ∑ w ∈ L, y w := by
      have := sum_move y v u L
      rw [show (∑ w ∈ L, (y w - CharVec u w + CharVec v w)) =
        ∑ w ∈ L, (y w + CharVec v w - CharVec u w) from
          Finset.sum_congr rfl (fun w _ => by ring), this]
      simp [huL, hvL]
    rw [e] at this
    omega

lemma edge_trans (B : Set (V → ℤ)) (hExc : ExchangeAxiomB B) (x : V → ℤ)
    (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h1 : Edge B x a b) (h2 : Edge B x b c) : Edge B x a c := by
  obtain ⟨v, hv, hA, hB⟩ := hExc _ h2 _ h1 b (by
    show (x b + CharVec a b - CharVec b b) < (x b + CharVec b b - CharVec c b)
    simp [CharVec, hab.symm, hbc])
  have hv' : (x v + CharVec b v - CharVec c v) < (x v + CharVec a v - CharVec b v) := hv
  by_cases hva : v = a
  · subst hva
    unfold Edge
    convert hA using 1
    funext w
    simp only [CharVec]
    split_ifs <;> omega
  · by_cases hvc : v = c
    · subst hvc
      unfold Edge
      convert hB using 1
      funext w
      simp only [CharVec]
      split_ifs <;> omega
    · exfalso
      simp only [CharVec, if_neg hva, if_neg hvc] at hv'
      split_ifs at hv' <;> omega

/-! ### facts about `InducedRho` -/

lemma rho_ge (B : Set (V → ℤ)) (X : Finset V) (y : V → ℤ) (hy : y ∈ B) :
    ((((∑ v ∈ X, y v : ℤ) : ℝ)) : WithTop ℝ) ≤ InducedRho B X :=
  le_csSup (OrderTop.bddAbove _) ⟨y, hy, rfl⟩

lemma rho_eq (B : Set (V → ℤ)) (X : Finset V) (x : V → ℤ) (hx : x ∈ B)
    (hmax : ∀ y ∈ B, ∑ v ∈ X, y v ≤ ∑ v ∈ X, x v) :
    InducedRho B X = ((((∑ v ∈ X, x v : ℤ) : ℝ)) : WithTop ℝ) := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨x, hx, rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact WithTop.coe_le_coe.mpr (Int.cast_le.mpr (hmax y hy))

lemma rho_bdd (B : Set (V → ℤ)) (X : Finset V) (h : InducedRho B X ≠ ⊤) :
    ∃ b : ℤ, ∀ y ∈ B, ∑ v ∈ X, y v ≤ b := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp h
  refine ⟨⌊r⌋, fun y hy => ?_⟩
  have := rho_ge B X y hy
  rw [← hr] at this
  have h' : ((∑ v ∈ X, y v : ℤ) : ℝ) ≤ r := WithTop.coe_le_coe.mp this
  exact Int.le_floor.mpr h'

lemma max_exists (B S : Set (V → ℤ)) (hS : S ⊆ B) (hSne : S.Nonempty) (X : Finset V)
    (h : InducedRho B X ≠ ⊤) :
    ∃ x ∈ S, ∀ y ∈ S, ∑ v ∈ X, y v ≤ ∑ v ∈ X, x v := by
  classical
  obtain ⟨b, hb⟩ := rho_bdd B X h
  obtain ⟨ub, ⟨x, hxS, hx⟩, hub⟩ := Int.exists_greatest_of_bdd
    (P := fun n => ∃ y ∈ S, ∑ v ∈ X, y v = n)
    ⟨b, fun n ⟨y, hy, hyn⟩ => hyn ▸ hb y (hS hy)⟩
    (by obtain ⟨y, hy⟩ := hSne; exact ⟨_, y, hy, rfl⟩)
  exact ⟨x, hxS, fun y hy => hx ▸ hub _ ⟨y, hy, rfl⟩⟩

lemma sum_const (B : Set (V → ℤ)) (hExc : ExchangeAxiomB B) (x y : V → ℤ) (hx : x ∈ B)
    (hy : y ∈ B) : ∑ v, y v = ∑ v, x v := by
  apply le_antisymm
  · exact lemG B hExc Finset.univ x hx (fun _ _ _ _ => Finset.mem_univ _) y hy
  · exact lemG B hExc Finset.univ y hy (fun _ _ _ _ => Finset.mem_univ _) x hx

lemma rho_submod (B : Set (V → ℤ)) (hExc : ExchangeAxiomB B) (hBne : B.Nonempty)
    (X Y : Finset V) :
    InducedRho B X + InducedRho B Y ≥ InducedRho B (X ∪ Y) + InducedRho B (X ∩ Y) := by
  classical
  by_cases hX : InducedRho B X = ⊤
  · rw [hX, WithTop.top_add]; exact le_top
  by_cases hY : InducedRho B Y = ⊤
  · rw [hY, WithTop.add_top]; exact le_top
  obtain ⟨x1, hx1, hx1max⟩ := max_exists B B le_rfl hBne X hX
  set S2 := {x ∈ B | ∀ y ∈ B, ∑ v ∈ X, y v ≤ ∑ v ∈ X, x v} with hS2
  obtain ⟨x, ⟨hxB, hxX⟩, hxY⟩ := max_exists B S2 (fun z hz => hz.1) ⟨x1, hx1, hx1max⟩ Y hY
  -- local conditions
  have key : ∀ u v, Edge B x u v →
      (∑ w ∈ X, (x w + CharVec u w - CharVec v w) ≤ ∑ w ∈ X, x w) ∧
      (∑ w ∈ X, (x w + CharVec u w - CharVec v w) = ∑ w ∈ X, x w →
        ∑ w ∈ Y, (x w + CharVec u w - CharVec v w) ≤ ∑ w ∈ Y, x w) := by
    intro u v huv
    refine ⟨hxX _ huv, fun heq => hxY _ ⟨huv, fun y hy => heq ▸ hxX y hy⟩⟩
  have locI : ∀ u v, Edge B x u v → u ∈ X ∩ Y → v ∈ X ∩ Y := by
    intro u v huv hu
    obtain ⟨k1, k2⟩ := key u v huv
    rw [Finset.mem_inter] at hu ⊢
    rw [sum_move] at k1 k2
    rw [sum_move] at k2
    by_cases hvX : v ∈ X
    · refine ⟨hvX, ?_⟩
      by_contra hvY
      have := k2 (by simp [hu.1, hvX])
      simp [hu.2, hvY] at this
    · simp [hu.1, hvX] at k1
  have locU : ∀ u v, Edge B x u v → u ∈ X ∪ Y → v ∈ X ∪ Y := by
    intro u v huv hu
    obtain ⟨k1, k2⟩ := key u v huv
    rw [Finset.mem_union] at hu ⊢
    rw [sum_move] at k1 k2
    rw [sum_move] at k2
    by_contra hv
    push_neg at hv
    by_cases huX : u ∈ X
    · simp [huX, hv.1] at k1
    · have hu2 : u ∈ Y := hu.resolve_left huX
      have := k2 (by simp [huX, hv.1])
      simp [hu2, hv.2] at this
  have gI := lemG B hExc (X ∩ Y) x hxB locI
  have gU := lemG B hExc (X ∪ Y) x hxB locU
  rw [rho_eq B (X ∩ Y) x hxB gI, rho_eq B (X ∪ Y) x hxB gU, rho_eq B X x hxB hxX]
  have hYge := rho_ge B Y x hxB
  have e : ((((∑ v ∈ X ∪ Y, x v : ℤ) : ℝ)) : WithTop ℝ) +
      ((((∑ v ∈ X ∩ Y, x v : ℤ) : ℝ)) : WithTop ℝ) =
      ((((∑ v ∈ X, x v : ℤ) : ℝ)) : WithTop ℝ) + ((((∑ v ∈ Y, x v : ℤ) : ℝ)) : WithTop ℝ) := by
    rw [← WithTop.coe_add, ← WithTop.coe_add]
    congr 1
    push_cast
    exact_mod_cast (Finset.sum_union_inter (s₁ := X) (s₂ := Y) (f := x))
  rw [ge_iff_le, e]
  exact add_le_add le_rfl hYge

lemma rho_int (B : Set (V → ℤ)) (hBne : B.Nonempty) : IsIntegerValued (InducedRho B) := by
  intro X
  by_cases h : InducedRho B X = ⊤
  · exact Or.inl h
  · right
    obtain ⟨x, hx, hmax⟩ := max_exists B B le_rfl hBne X h
    exact ⟨_, rho_eq B X x hx hmax⟩

/-- integer points of the base polyhedron belong to `B` -/
lemma crux (B : Set (V → ℤ)) (hExc : ExchangeAxiomB B) (hBne : B.Nonempty) (z : V → ℤ)
    (hz : ∀ X : Finset V, ((((∑ v ∈ X, z v : ℤ) : ℝ)) : WithTop ℝ) ≤ InducedRho B X)
    (hzV : ∀ x ∈ B, ∑ v, z v = ∑ v, x v) : z ∈ B := by
  classical
  have hex : ∃ n : ℕ, ∃ x ∈ B, ∑ w, (x w - z w).natAbs = n := by
    obtain ⟨x, hx⟩ := hBne; exact ⟨_, x, hx, rfl⟩
  obtain ⟨x, hxB, hxn⟩ := Nat.find_spec hex
  have hmin := fun m (h : ∃ x ∈ B, ∑ w, (x w - z w).natAbs = m) => Nat.find_min' hex h
  by_contra hzB
  have hxz : x ≠ z := fun h => hzB (h ▸ hxB)
  set L : Finset V := Finset.univ.filter
    (fun w => x w < z w ∨ ∃ a, x a < z a ∧ Edge B x a w) with hL
  have hclosed : ∀ u v, Edge B x u v → u ∈ L → v ∈ L := by
    intro u v huv hu
    simp only [hL, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rcases hu with hu | ⟨a, ha, hau⟩
    · exact Or.inr ⟨u, hu, huv⟩
    · by_cases hva : v = a
      · exact Or.inl (hva ▸ ha)
      by_cases huv' : u = v
      · exact Or.inr ⟨a, ha, huv' ▸ hau⟩
      by_cases hau' : a = u
      · exact Or.inr ⟨a, ha, hau' ▸ huv⟩
      exact Or.inr ⟨a, ha, edge_trans B hExc x a u v hau' huv' (Ne.symm hva) hau huv⟩
  have hG := lemG B hExc L x hxB hclosed
  have hzL : ∑ w ∈ L, z w ≤ ∑ w ∈ L, x w := by
    have h1 := hz L
    rw [rho_eq B L x hxB hG] at h1
    exact_mod_cast WithTop.coe_le_coe.mp h1
  -- some coordinate with x < z
  have hA : ∃ a, x a < z a := by
    by_contra hne
    push_neg at hne
    apply hxz
    have hs := hzV x hxB
    funext w
    have := (Finset.sum_eq_sum_iff_of_le (fun i _ => hne i)).mp hs
    exact (this w (Finset.mem_univ _)).symm
  obtain ⟨a, ha⟩ := hA
  have haL : a ∈ L := by simp [hL, ha]
  obtain ⟨w, hwL, hw⟩ : ∃ w ∈ L, z w < x w := by
    by_contra hne
    push_neg at hne
    have : ∑ w ∈ L, x w < ∑ w ∈ L, z w :=
      Finset.sum_lt_sum (fun i hi => hne i hi) ⟨a, haL, ha⟩
    omega
  simp only [hL, Finset.mem_filter, Finset.mem_univ, true_and] at hwL
  rcases hwL with hw' | ⟨b, hb, hbw⟩
  · omega
  · have hlt := dist_lt x z (fun v => x v + CharVec b v - CharVec w v) b w hb hw (fun _ => rfl)
    have := hmin _ ⟨_, hbw, rfl⟩
    rw [hxn] at hlt
    omega

theorem mis_core (B : Set (V → ℤ)) (hExc : ExchangeAxiomB B) (hBne : B.Nonempty) :
    SubmodularSetFunction (InducedRho B) ∧ IsIntegerValued (InducedRho B) ∧
      convexHull ℝ (IntEmbed B) = BasePolyhedron (InducedRho B) := by
  classical
  obtain ⟨x0, hx0⟩ := hBne
  have hmaxV : ∀ y ∈ B, ∑ v ∈ Finset.univ, y v ≤ ∑ v ∈ Finset.univ, x0 v :=
    fun y hy => (sum_const B hExc x0 y hx0 hy).le
  have hρV : InducedRho B Finset.univ = ((((∑ v, x0 v : ℤ) : ℝ)) : WithTop ℝ) :=
    rho_eq B _ x0 hx0 hmaxV
  have hρV' : InducedRho B Finset.univ ≠ ⊤ := by rw [hρV]; exact WithTop.coe_ne_top
  have hsub : SubmodularSetFunction (InducedRho B) := by
    refine ⟨?_, hρV', rho_submod B hExc ⟨x0, hx0⟩⟩
    rw [rho_eq B ∅ x0 hx0 (fun y _ => by simp)]
    simp
  have hint := rho_int B ⟨x0, hx0⟩
  refine ⟨hsub, hint, ?_⟩
  apply Set.Subset.antisymm
  · apply convexHull_min _ (bp_convex _ hρV')
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨fun X => ?_, ?_⟩
    · have := rho_ge B X x hx
      simpa using this
    · rw [hρV, ← sum_const B hExc x0 x hx0 hx]
      simp
  · have hI := bpi_core (InducedRho B) hsub hint
    unfold IsIntegralPolyhedron at hI
    rw [hI]
    apply convexHull_mono
    rintro z ⟨hzB, hzI⟩
    choose k hk using hzI
    have hzk : z = fun v => (k v : ℝ) := funext hk
    subst hzk
    refine ⟨k, crux B hExc ⟨x0, hx0⟩ k (fun X => ?_) (fun x hx => ?_), rfl⟩
    · have := hzB.1 X
      simpa using this
    · have h2 := hzB.2
      rw [rho_eq B _ x hx (fun y hy => (sum_const B hExc x y hx hy).le)] at h2
      have h3 : ((∑ v, k v : ℤ) : ℝ) = ((∑ v, x v : ℤ) : ℝ) := by
        have := WithTop.coe_injective h2
        beta_reduce at this
        push_cast at this ⊢; exact this
      exact_mod_cast h3

end BPI

end DiscreteConvex.MConvexSetsB

open DiscreteConvex.MConvexSetsB


theorem solution {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ))
    (hExc : ExchangeAxiomB B) (hBne : B.Nonempty) :
    SubmodularSetFunction (InducedRho B) ∧ IsIntegerValued (InducedRho B) ∧
      convexHull ℝ (IntEmbed B) = BasePolyhedron (InducedRho B) := by
  exact BPI.mis_core B hExc hBne
