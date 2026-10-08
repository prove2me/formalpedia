-- Prove2me | solution 1 for Disjunctive.Dominants.general_dominant_facet_characterization_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T07:23:23.408112+00:00
-- url     : https://prove2.me/submissions/cd0b0859-c66e-4327-bdc3-37839bb90153

import Mathlib
import Definitions.Def_Disjunctive_Dominants_Basic

set_option autoImplicit false

open scoped Pointwise

namespace Sol6e9beebc

open Disjunctive.Dominants

/-- dot product with a vector supported on `S`, written as a sum over the subtype of `S`. -/
lemma dot_supp {n : ℕ} (S : Finset (Fin n)) (d v : Fin n → ℝ) (hd : ∀ j ∉ S, d j = 0) :
    dotProduct d v = ∑ k : {j // j ∈ S}, d k * v k := by
  unfold dotProduct
  rw [Finset.sum_coe_sort S (fun j => d j * v j)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  simp [hd j hj]

/-- dot products agree when the vector is supported on `S` and the arguments agree on `S`. -/
lemma dot_congr {n : ℕ} (S : Finset (Fin n)) (d x y : Fin n → ℝ) (hd : ∀ j ∉ S, d j = 0)
    (hxy : ∀ j ∈ S, x j = y j) : dotProduct d x = dotProduct d y := by
  rw [dot_supp S d x hd, dot_supp S d y hd]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hxy k k.2]

lemma pos_neg (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

lemma cont_dot {n : ℕ} (v : Fin n → ℝ) : Continuous fun p : Fin n → ℝ => dotProduct p v := by
  unfold dotProduct
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const

lemma inIS_nonneg {n : ℕ} {S : Finset (Fin n)} {P : Set (Fin n → ℝ)} {pi : Fin n → ℝ}
    (h : IsInIS S P pi) : 0 ≤ pi := by
  intro j
  by_cases hj : j ∈ S
  · exact (h.2.1 j hj).le
  · simp [h.1 j hj]

lemma inIS_valid {n : ℕ} {S : Finset (Fin n)} {P : Set (Fin n → ℝ)} {pi : Fin n → ℝ}
    (h : IsInIS S P pi) (y : Fin n → ℝ) (hy : y ∈ Dominant P) : 1 ≤ dotProduct pi y := by
  obtain ⟨_, x, hxP, hxy⟩ := hy
  have h1 : 1 ≤ dotProduct pi x := h.2.2.1 x ⟨x, hxP, fun _ _ => rfl⟩
  exact h1.trans (dotProduct_le_dotProduct_of_nonneg_left hxy (inIS_nonneg h))

/-- the linear functional `x ↦ π ⬝ x`. -/
def dotL {n : ℕ} (pi : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun x := dotProduct pi x
  map_add' x y := dotProduct_add pi x y
  map_smul' c x := by simp [dotProduct_smul]

lemma facet_part {n : ℕ} (P : Set (Fin n → ℝ)) (hcube : P ⊆ UnitCube n) (hP : P.Nonempty)
    (S : Finset (Fin n)) (pi : Fin n → ℝ) (h : IsInIS S P pi) :
    IsFacet (Dominant P) ({x ∈ Dominant P | dotProduct pi x = 1}) := by
  have hpi0 := inIS_nonneg h
  have hnn : ∀ x ∈ P, 0 ≤ x := fun x hx j => (hcube hx j).1
  obtain ⟨hoff, hon, hval, pts, hptsP, hpts1, hli⟩ := h
  choose xs hxsP hxsS using hptsP
  have hxs1 : ∀ i, dotProduct pi (xs i) = 1 := fun i => by
    rw [dot_congr S pi (xs i) (pts i) hoff (hxsS i)]; exact hpts1 i
  obtain ⟨x0, hx0⟩ := hP
  have hSne : S.Nonempty := by
    by_contra hS
    rw [Finset.not_nonempty_iff_eq_empty] at hS
    have := hval x0 ⟨x0, hx0, fun _ _ => rfl⟩
    rw [dot_supp S pi x0 hoff] at this
    subst hS
    simp at this
    linarith
  have hcard : 0 < S.card := Finset.card_pos.2 hSne
  set i0 : Fin S.card := ⟨0, hcard⟩
  set F := {x ∈ Dominant P | dotProduct pi x = 1} with hF
  have hxsD : ∀ i, xs i ∈ Dominant P := fun i => ⟨hnn _ (hxsP i), xs i, hxsP i, le_rfl⟩
  have hxsF : ∀ i, xs i ∈ F := fun i => ⟨hxsD i, hxs1 i⟩
  -- extreme
  have hext : IsExtreme ℝ (Dominant P) F := by
    refine ⟨Set.sep_subset _ _, ?_⟩
    rintro x1 hx1 x2 hx2 x ⟨_, hx⟩ ⟨a, b, ha, hb, hab, rfl⟩
    have e1 := inIS_valid ⟨hoff, hon, hval, pts, fun i => ⟨xs i, hxsP i, hxsS i⟩, hpts1, hli⟩ x1 hx1
    have e2 := inIS_valid ⟨hoff, hon, hval, pts, fun i => ⟨xs i, hxsP i, hxsS i⟩, hpts1, hli⟩ x2 hx2
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hx
    have q1 : dotProduct pi x1 = 1 := by
      by_contra hne
      have : 1 < dotProduct pi x1 := lt_of_le_of_ne e1 (Ne.symm hne)
      nlinarith
    have q2 : dotProduct pi x2 = 1 := by
      by_contra hne
      have : 1 < dotProduct pi x2 := lt_of_le_of_ne e2 (Ne.symm hne)
      nlinarith
    rw [hF]
    exact ⟨hx1, q1⟩
  -- vector span of D is ⊤
  have hD : vectorSpan ℝ (Dominant P) = ⊤ := by
    rw [eq_top_iff]
    intro d _
    have hp : (x0 + fun j => max (d j) 0) ∈ Dominant P :=
      ⟨add_nonneg (hnn _ hx0) (fun j => le_max_right _ _), x0, hx0,
        le_add_of_nonneg_right (fun j => le_max_right _ _)⟩
    have hm : (x0 + fun j => max (-d j) 0) ∈ Dominant P :=
      ⟨add_nonneg (hnn _ hx0) (fun j => le_max_right _ _), x0, hx0,
        le_add_of_nonneg_right (fun j => le_max_right _ _)⟩
    have := vsub_mem_vectorSpan ℝ hp hm
    convert this using 1
    funext j
    simp [vsub_eq_sub]
  -- vectors vanishing on S lie in the span of F
  have hzero : ∀ z : Fin n → ℝ, (∀ j ∈ S, z j = 0) → z ∈ vectorSpan ℝ F := by
    intro z hz
    have hsupp : ∀ w : Fin n → ℝ, (∀ j, 0 ≤ w j) → (∀ j ∈ S, w j = 0) → xs i0 + w ∈ F := by
      intro w hw0 hwS
      refine ⟨⟨add_nonneg (hnn _ (hxsP i0)) hw0, xs i0, hxsP i0, le_add_of_nonneg_right hw0⟩, ?_⟩
      rw [dotProduct_add, hxs1 i0, dot_congr S pi w 0 hoff (fun j hj => hwS j hj)]
      simp
    have hp := hsupp (fun j => max (z j) 0) (fun j => le_max_right _ _)
      (fun j hj => by simp [hz j hj])
    have hm := hsupp (fun j => max (-z j) 0) (fun j => le_max_right _ _)
      (fun j hj => by simp [hz j hj])
    have := vsub_mem_vectorSpan ℝ hp hm
    convert this using 1
    funext j
    simp [vsub_eq_sub]
  have hF_eq : vectorSpan ℝ F = LinearMap.ker (dotL pi) := by
    apply le_antisymm
    · rw [vectorSpan_def, Submodule.span_le]
      rintro _ ⟨a, ha, b, hb, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, dotL, LinearMap.coe_mk, AddHom.coe_mk,
        vsub_eq_sub, dotProduct_sub, ha.2, hb.2, sub_self]
    · intro d hd
      rw [LinearMap.mem_ker] at hd
      change dotProduct pi d = 0 at hd
      have hspan : Submodule.span ℝ (Set.range fun i => fun j : {j // j ∈ S} => pts i j) = ⊤ :=
        hli.span_eq_top_of_card_eq_finrank' (by
          rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_coe])
      have hr : (fun j : {j // j ∈ S} => d j) ∈
          Submodule.span ℝ (Set.range fun i => fun j : {j // j ∈ S} => pts i j) := by
        rw [hspan]; trivial
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hr
      have hcj : ∀ j : {j // j ∈ S}, ∑ i, c i * pts i j = d j := by
        intro j
        have := congrFun hc j
        simpa [Finset.sum_apply, smul_eq_mul] using this
      have hcsum : ∑ i, c i = 0 := by
        have h1 : dotProduct pi d = ∑ i, c i * dotProduct pi (pts i) := by
          rw [dot_supp S pi d hoff]
          simp_rw [dot_supp S pi _ hoff, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← hcj j, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        rw [hd] at h1
        simpa [hpts1] using h1.symm
      set w : Fin n → ℝ := ∑ i, c i • (xs i - xs i0) with hw
      have hwmem : w ∈ vectorSpan ℝ F := by
        refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
        have := vsub_mem_vectorSpan ℝ (hxsF i) (hxsF i0)
        simpa [vsub_eq_sub] using this
      have hdw : d - w ∈ vectorSpan ℝ F := by
        apply hzero
        intro j hj
        have hwj : w j = ∑ i, c i * pts i j - (∑ i, c i) * xs i0 j := by
          rw [hw, Finset.sum_apply, Finset.sum_mul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          rw [hxsS i j hj]
          ring
        rw [Pi.sub_apply, hwj, hcsum, zero_mul, sub_zero, hcj ⟨j, hj⟩, sub_self]
      have := Submodule.add_mem _ hdw hwmem
      simpa using this
  -- finrank of the kernel
  obtain ⟨j0, hj0⟩ := hSne
  have hrange : LinearMap.range (dotL pi) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    refine ⟨t • Pi.single j0 (1 / pi j0), ?_⟩
    simp only [dotL, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_smul, dotProduct_single,
      smul_eq_mul]
    have := hon j0 hj0
    field_simp
  have hrn := LinearMap.finrank_range_add_finrank_ker (dotL pi)
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at hrn
  refine ⟨hext, ⟨xs i0, hxsF i0⟩, ?_⟩
  unfold PolyDim
  rw [if_pos ⟨xs i0, hxsF i0⟩, if_pos ⟨xs i0, hxsD i0⟩, hF_eq, hD, finrank_top,
    Module.finrank_fin_fun]
  omega

/-- separation: a point `x ≥ 0` outside the dominant is cut off by some `p ≥ 0` valid on `V`. -/
lemma separate {n : ℕ} (V : Finset (Fin n → ℝ))
    (hcube : convexHull ℝ (V : Set (Fin n → ℝ)) ⊆ UnitCube n)
    (hP : (convexHull ℝ (V : Set (Fin n → ℝ))).Nonempty)
    (x : Fin n → ℝ) (hx0 : 0 ≤ x) (hxD : x ∉ Dominant (convexHull ℝ (V : Set (Fin n → ℝ)))) :
    ∃ p : Fin n → ℝ, 0 ≤ p ∧ (∀ v ∈ V, 1 ≤ dotProduct p v) ∧ dotProduct p x < 1 := by
  set P := convexHull ℝ (V : Set (Fin n → ℝ)) with hPdef
  have hnn : ∀ y ∈ P, 0 ≤ y := fun y hy j => (hcube hy j).1
  have hDeq : Dominant P = P + Set.Ici (0 : Fin n → ℝ) := by
    ext y
    constructor
    · rintro ⟨_, z, hz, hzy⟩
      exact Set.mem_add.2 ⟨z, hz, y - z, sub_nonneg.2 hzy, add_sub_cancel _ _⟩
    · intro hy
      obtain ⟨z, hz, r, hr, rfl⟩ := Set.mem_add.1 hy
      exact ⟨add_nonneg (hnn z hz) hr, z, hz, le_add_of_nonneg_right hr⟩
  have hPc : IsCompact P := by rw [hPdef]; exact Set.Finite.isCompact_convexHull (𝕜 := ℝ) V.finite_toSet
  have hclosed : IsClosed (Dominant P) := by
    rw [hDeq]; exact IsClosed.add_left_of_isCompact isClosed_Ici hPc
  have hconv : Convex ℝ (Dominant P) := by
    rw [hDeq]; exact (convex_convexHull ℝ _).add (convex_Ici 0)
  obtain ⟨f, u, hfx, hfb⟩ := geometric_hahn_banach_point_closed hconv hclosed hxD
  set p : Fin n → ℝ := fun i => f (fun j => if i = j then 1 else 0) with hp
  have hf : ∀ y, f y = dotProduct p y := by
    intro y
    have := LinearMap.pi_apply_eq_sum_univ (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) y
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  obtain ⟨y0, hy0⟩ := hP
  have hy0D : y0 ∈ Dominant P := ⟨hnn y0 hy0, y0, hy0, le_rfl⟩
  have hp0 : 0 ≤ p := by
    intro j
    by_contra hneg
    push Not at hneg
    set e : Fin n → ℝ := fun k => if j = k then 1 else 0 with he
    have he0 : 0 ≤ e := fun k => by simp only [e, Pi.zero_apply]; split_ifs <;> norm_num
    have hpe : dotProduct p e = p j := by simp [e, dotProduct]
    have hu0 := hfb y0 hy0D
    have hpj : p j ≠ 0 := ne_of_lt hneg
    set t : ℝ := (f y0 - u) / (- p j) + 1 with htdef
    have ht : 0 ≤ t := by
      have : 0 < (f y0 - u) / (- p j) := div_pos (by linarith) (by simp at hneg ⊢; linarith)
      linarith
    have hmem : y0 + t • e ∈ Dominant P :=
      ⟨add_nonneg (hnn y0 hy0) (smul_nonneg ht he0), y0, hy0,
        le_add_of_nonneg_right (smul_nonneg ht he0)⟩
    have h1 := hfb _ hmem
    rw [hf, dotProduct_add, dotProduct_smul, hpe, smul_eq_mul, ← hf] at h1
    have : t * p j = -(f y0 - u) + p j := by
      rw [htdef, add_mul, div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hpj]; ring
    simp only [Pi.zero_apply] at hneg
    linarith
  have hfx0 : 0 ≤ f x := by rw [hf]; exact dotProduct_nonneg_of_nonneg hp0 hx0
  have hu : 0 < u := by linarith
  refine ⟨u⁻¹ • p, smul_nonneg (inv_nonneg.2 hu.le) hp0, fun v hv => ?_, ?_⟩
  · have hvP : v ∈ P := subset_convexHull ℝ _ (Finset.mem_coe.2 hv)
    have hvD : v ∈ Dominant P := ⟨hnn v hvP, v, hvP, le_rfl⟩
    have := hfb v hvD
    rw [hf] at this
    rw [smul_dotProduct, smul_eq_mul, show u⁻¹ * dotProduct p v = dotProduct p v / u by ring,
      le_div_iff₀ hu]
    linarith
  · rw [smul_dotProduct, smul_eq_mul, show u⁻¹ * dotProduct p x = dotProduct p x / u by ring,
      div_lt_one hu]
    rw [hf] at hfx; linarith

/-- the hard inclusion: a point `x ≥ 0` outside the dominant violates some member of `I^S`. -/
lemma hard {n : ℕ} (V : Finset (Fin n → ℝ))
    (hcube : convexHull ℝ (V : Set (Fin n → ℝ)) ⊆ UnitCube n)
    (hP : (convexHull ℝ (V : Set (Fin n → ℝ))).Nonempty)
    (x : Fin n → ℝ) (hx0 : 0 ≤ x) (hxD : x ∉ Dominant (convexHull ℝ (V : Set (Fin n → ℝ)))) :
    ∃ (S : Finset (Fin n)) (pi : Fin n → ℝ), IsInIS S (convexHull ℝ (V : Set (Fin n → ℝ))) pi ∧
      dotProduct pi x < 1 := by
  obtain ⟨p0, hp00, hp0V, hp0x⟩ := separate V hcube hP x hx0 hxD
  have hx0' : ∀ j, 0 ≤ x j := fun j => hx0 j
  set s0 := ∑ j, p0 j with hs0def
  have hs0 : 0 ≤ s0 := Finset.sum_nonneg fun j _ => hp00 j
  set ε : ℝ := (1 - dotProduct p0 x) / (2 * (s0 + 1)) with hεdef
  have hε : 0 < ε := div_pos (by linarith) (by linarith)
  set c : Fin n → ℝ := x + fun _ => ε with hcdef
  have hcx : x ≤ c := fun j => by simp [c, hε.le]
  have hc0 : ∀ j, 0 ≤ c j := fun j => by simp only [c, Pi.add_apply]; linarith [hx0' j]
  have hc : ∀ q : Fin n → ℝ, dotProduct q c = dotProduct q x + ε * ∑ j, q j := by
    intro q
    simp only [c, dotProduct_add]
    simp [dotProduct, Finset.sum_mul, mul_comm]
  have hp0c : dotProduct p0 c < 1 := by
    rw [hc]
    have h2 : ε * s0 < 1 - dotProduct p0 x := by
      have h3 : ε * s0 = (1 - dotProduct p0 x) * (s0 / (2 * (s0 + 1))) := by
        rw [hεdef]; ring
      rw [h3]
      have h4 : s0 / (2 * (s0 + 1)) < 1 := by rw [div_lt_one (by linarith)]; linarith
      have h5 : 0 < 1 - dotProduct p0 x := by linarith
      nlinarith
    linarith
  set K : Set (Fin n → ℝ) := Set.Ici 0 ∩ (⋂ v ∈ V, {q | 1 ≤ dotProduct q v}) ∩
    {q | dotProduct q c ≤ dotProduct p0 c} with hK
  have hmemK : ∀ q, q ∈ K ↔
      0 ≤ q ∧ (∀ v ∈ V, 1 ≤ dotProduct q v) ∧ dotProduct q c ≤ dotProduct p0 c := by
    intro q; simp [K, and_assoc]
  have hKclosed : IsClosed K :=
    (isClosed_Ici.inter (isClosed_biInter fun v _ => isClosed_le continuous_const (cont_dot v))).inter
      (isClosed_le (cont_dot c) continuous_const)
  have hKsub : K ⊆ Set.Icc 0 (fun _ => dotProduct p0 c / ε) := by
    intro q hq
    rw [hmemK] at hq
    refine ⟨hq.1, fun j => ?_⟩
    rw [le_div_iff₀ hε]
    have h1 : q j * ε ≤ q j * c j :=
      mul_le_mul_of_nonneg_left (by simp only [c, Pi.add_apply]; linarith [hx0' j]) (hq.1 j)
    have h2 : q j * c j ≤ dotProduct q c :=
      Finset.single_le_sum (f := fun k => q k * c k) (fun k _ => mul_nonneg (hq.1 k) (hc0 k))
        (Finset.mem_univ j)
    linarith [hq.2.2]
  have hKc : IsCompact K := isCompact_Icc.of_isClosed_subset hKclosed hKsub
  have hp0K : p0 ∈ K := (hmemK p0).2 ⟨hp00, hp0V, le_rfl⟩
  obtain ⟨pm, hpmK, hmin⟩ := hKc.exists_isMinOn ⟨p0, hp0K⟩ (cont_dot c).continuousOn
  rw [isMinOn_iff] at hmin
  set m := dotProduct pm c with hm
  have hmp0 : m ≤ dotProduct p0 c := hmin p0 hp0K
  have hglob : ∀ q : Fin n → ℝ, 0 ≤ q → (∀ v ∈ V, 1 ≤ dotProduct q v) → m ≤ dotProduct q c := by
    intro q hq0 hqV
    by_cases hqc : dotProduct q c ≤ dotProduct p0 c
    · exact hmin q ((hmemK q).2 ⟨hq0, hqV, hqc⟩)
    · push Not at hqc; linarith
  set A := K ∩ {q | dotProduct q c ≤ m} with hA
  have hAc : IsCompact A := hKc.inter_right (isClosed_le (cont_dot c) continuous_const)
  obtain ⟨e, he⟩ := hAc.extremePoints_nonempty ⟨pm, hpmK, show dotProduct pm c ≤ m from le_rfl⟩
  have heA : e ∈ A := he.1
  have heK := heA.1
  rw [hmemK] at heK
  obtain ⟨he0, heV, _⟩ := heK
  have hem : dotProduct e c ≤ m := heA.2
  have hex : dotProduct e x < 1 := by
    have : dotProduct e x ≤ dotProduct e c := dotProduct_le_dotProduct_of_nonneg_left hcx he0
    linarith
  set S : Finset (Fin n) := Finset.univ.filter (fun j => 0 < e j) with hSdef
  have hoff : ∀ j ∉ S, e j = 0 := by
    intro j hj
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
    exact le_antisymm hj (he0 j)
  have hon : ∀ j ∈ S, 0 < e j := by
    intro j hj; simpa [S] using hj
  set T : Finset (Fin n → ℝ) := V.filter (fun v => dotProduct e v = 1) with hTdef
  have key : ∀ d : Fin n → ℝ, (∀ j ∉ S, d j = 0) → (∀ v ∈ T, dotProduct d v = 0) → d = 0 := by
    intro d hdS hdT
    by_contra hd
    have hev : ∀ᶠ t in nhds (0:ℝ), (∀ j ∈ S, 0 < e j + t * d j) ∧
        (∀ v ∈ V \ T, 1 < dotProduct e v + t * dotProduct d v) := by
      refine Filter.Eventually.and ?_ ?_
      · rw [Filter.eventually_all_finset]
        intro j hj
        have hcont : Continuous fun t : ℝ => e j + t * d j := by fun_prop
        have := hcont.tendsto 0
        simp only [zero_mul, add_zero] at this
        exact this.eventually (lt_mem_nhds (hon j hj))
      · rw [Filter.eventually_all_finset]
        intro v hv
        rw [Finset.mem_sdiff] at hv
        have hgt : 1 < dotProduct e v :=
          lt_of_le_of_ne (heV v hv.1) (fun h => hv.2 (Finset.mem_filter.2 ⟨hv.1, h.symm⟩))
        have hcont : Continuous fun t : ℝ => dotProduct e v + t * dotProduct d v := by fun_prop
        have := hcont.tendsto 0
        simp only [zero_mul, add_zero] at this
        exact this.eventually (lt_mem_nhds hgt)
    have hev2 := hev.and ((continuous_neg.tendsto' (0:ℝ) 0 neg_zero).eventually hev)
    have hev3 := (hev2.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))).and
      self_mem_nhdsWithin
    obtain ⟨t, ⟨⟨hS1, hV1⟩, ⟨hS2, hV2⟩⟩, ht⟩ := hev3.exists
    have ht0 : 0 < t := ht
    have inB : ∀ s : ℝ, (∀ j ∈ S, 0 < e j + s * d j) →
        (∀ v ∈ V \ T, 1 < dotProduct e v + s * dotProduct d v) →
        0 ≤ e + s • d ∧ ∀ v ∈ V, 1 ≤ dotProduct (e + s • d) v := by
      intro s h1 h2
      refine ⟨fun j => ?_, fun v hv => ?_⟩
      · by_cases hj : j ∈ S
        · have := h1 j hj
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; linarith
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hdS j hj, mul_zero,
            add_zero]
          exact he0 j
      · rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
        by_cases hvT : v ∈ T
        · rw [hdT v hvT]
          have := (Finset.mem_filter.1 hvT).2
          linarith
        · linarith [h2 v (Finset.mem_sdiff.2 ⟨hv, hvT⟩)]
    obtain ⟨hB1, hB1'⟩ := inB t hS1 hV1
    obtain ⟨hB2, hB2'⟩ := inB (-t) hS2 (fun v hv => by simpa using hV2 v hv)
    have hg1 := hglob _ hB1 hB1'
    have hg2 := hglob _ hB2 hB2'
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul] at hg1 hg2
    have hA1 : e + t • d ∈ A := by
      refine ⟨(hmemK _).2 ⟨hB1, hB1', ?_⟩, ?_⟩
      · rw [add_dotProduct, smul_dotProduct, smul_eq_mul]; linarith
      · show dotProduct (e + t • d) c ≤ m
        rw [add_dotProduct, smul_dotProduct, smul_eq_mul]; linarith
    have hA2 : e + (-t) • d ∈ A := by
      refine ⟨(hmemK _).2 ⟨hB2, hB2', ?_⟩, ?_⟩
      · rw [add_dotProduct, smul_dotProduct, smul_eq_mul]; linarith
      · show dotProduct (e + (-t) • d) c ≤ m
        rw [add_dotProduct, smul_dotProduct, smul_eq_mul]; linarith
    have hseg : e ∈ openSegment ℝ (e + t • d) (e + (-t) • d) := by
      refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
      funext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have := ((mem_extremePoints.1 he).2 _ hA1 _ hA2 hseg).1
    have htd : t • d = 0 := by
      have h' := congrArg (fun w => w - e) this
      simpa using h'
    rcases smul_eq_zero.1 htd with h | h
    · linarith
    · exact hd h
  have hspan : Submodule.span ℝ
      (Set.range fun v : T => fun j : {j // j ∈ S} => (v : Fin n → ℝ) j) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    set d : Fin n → ℝ := fun j =>
      if h : j ∈ S then φ (fun k => if (⟨j, h⟩ : {j // j ∈ S}) = k then 1 else 0) else 0 with hd
    have hdS : ∀ j ∉ S, d j = 0 := fun j hj => by simp [d, hj]
    have hdk : ∀ k : {j // j ∈ S}, d k = φ (fun k' => if k = k' then 1 else 0) :=
      fun k => by simp [d, k.2]
    have hd0 := key d hdS (by
      intro v hv
      rw [dot_supp S d v hdS]
      have hmem : (fun j : {j // j ∈ S} => v j) ∈ LinearMap.ker φ :=
        hle (Submodule.subset_span ⟨⟨v, hv⟩, rfl⟩)
      rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ φ] at hmem
      rw [← hmem]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hdk, smul_eq_mul, mul_comm])
    have hφk : ∀ k : {j // j ∈ S}, φ (fun k' => if k = k' then 1 else 0) = 0 := fun k => by
      rw [← hdk, hd0]; rfl
    apply hφ0
    apply LinearMap.ext
    intro y
    rw [LinearMap.pi_apply_eq_sum_univ φ y]
    simp [hφk]
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' ℝ
    (fun v : T => fun j : {j // j ∈ S} => (v : Fin n → ℝ) j)
  have : Finite κ := hli.finite
  let _ : Fintype κ := Fintype.ofFinite κ
  have hcardκ : Fintype.card κ = S.card := by
    have := finrank_span_eq_card hli
    rw [hsp, hspan, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
    exact this.symm
  let eqv : Fin S.card ≃ κ := (Fintype.equivFinOfCardEq hcardκ).symm
  refine ⟨S, e, ⟨hoff, hon, ?_, fun i => ((a (eqv i) : T) : Fin n → ℝ), ?_, ?_, ?_⟩, hex⟩
  · rintro y ⟨z, hz, hzy⟩
    rw [← dot_congr S e z y hoff hzy]
    have hconv : Convex ℝ {w : Fin n → ℝ | 1 ≤ dotProduct e w} := by
      intro w1 hw1 w2 hw2 s t hs ht hst
      simp only [Set.mem_setOf_eq, dotProduct_add, dotProduct_smul, smul_eq_mul] at *
      nlinarith
    exact convexHull_min (fun v hv => heV v hv) hconv hz
  · intro i
    have hvV : ((a (eqv i) : T) : Fin n → ℝ) ∈ V := (Finset.mem_filter.1 (a (eqv i)).2).1
    exact ⟨_, subset_convexHull ℝ _ (Finset.mem_coe.2 hvV), fun _ _ => rfl⟩
  · intro i; exact (Finset.mem_filter.1 (a (eqv i)).2).2
  · exact hli.comp eqv eqv.injective

end Sol6e9beebc

open Disjunctive.Dominants in
theorem solution {n : ℕ} (P : Set (Fin n → ℝ))
    (hPoly : ∃ V : Finset (Fin n → ℝ), P = convexHull ℝ (V : Set (Fin n → ℝ)))
    (hcube : P ⊆ UnitCube n) (hP : P.Nonempty) :
    Dominant P = {x | 0 ≤ x ∧ ∀ (S : Finset (Fin n)) (pi : Fin n → ℝ), IsInIS S P pi →
        1 ≤ dotProduct pi x} ∧
      ∀ (S : Finset (Fin n)) (pi : Fin n → ℝ), IsInIS S P pi →
        IsFacet (Dominant P) ({x ∈ Dominant P | dotProduct pi x = 1}) := by
  refine ⟨?_, fun S pi h => Sol6e9beebc.facet_part P hcube hP S pi h⟩
  obtain ⟨V, rfl⟩ := hPoly
  ext y
  constructor
  · intro hy
    exact ⟨hy.1, fun S pi h => Sol6e9beebc.inIS_valid h y hy⟩
  · rintro ⟨hy0, hy⟩
    by_contra hyD
    obtain ⟨S, pi, h, hlt⟩ := Sol6e9beebc.hard V hcube hP y hy0 hyD
    linarith [hy S pi h]
