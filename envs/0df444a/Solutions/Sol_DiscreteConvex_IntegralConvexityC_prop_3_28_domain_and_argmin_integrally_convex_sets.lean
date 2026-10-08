-- Prove2me | solution 1 for DiscreteConvex.IntegralConvexityC.prop_3_28_domain_and_argmin_integrally_convex_sets
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T00:30:46.841916+00:00
-- url     : https://prove2.me/submissions/5ea49dbc-54cb-40ad-b10b-c639e35c14ed

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvexSet
import Definitions.Def_DiscreteConvex_IntegralConvexityC_DomZ
import Definitions.Def_DiscreteConvex_IntegralConvexityC_ArgMinPerturbed



namespace DiscreteConvex.IntegralConvexityC

/-- integer points as real vectors -/
def icEmb {n : ℕ} (y : Fin n → ℤ) : Fin n → ℝ := fun i => (y i : ℝ)

lemma icEmb_inj {n : ℕ} : Function.Injective (@icEmb n) := by
  intro a b h; funext i; have := congrFun h i; simp only [icEmb] at this; exact_mod_cast this

lemma ic_sep {n : ℕ} {C : Set (Fin n → ℝ)} (hc : Convex ℝ C) (hC : IsClosed C)
    {x : Fin n → ℝ} (hx : x ∉ C) :
    ∃ (p : Fin n → ℝ) (a : ℝ), (∀ c ∈ C, a + ∑ i, p i * c i ≤ 0) ∧ 0 < a + ∑ i, p i * x i := by
  classical
  obtain ⟨φ, u, hxu, hb⟩ := geometric_hahn_banach_point_closed hc hC hx
  have hφ : ∀ v : Fin n → ℝ, φ v = ∑ i, v i * φ (fun j => if i = j then 1 else 0) := by
    intro v
    have := LinearMap.pi_apply_eq_sum_univ (φ : (Fin n → ℝ) →ₗ[ℝ] ℝ) v
    simpa [smul_eq_mul] using this
  refine ⟨fun i => -φ (fun j => if i = j then 1 else 0), u, fun c hc' => ?_, ?_⟩
  · have := hb c hc'
    rw [hφ c] at this
    have e : ∑ i, -φ (fun j => if i = j then 1 else 0) * c i
        = -∑ i, c i * φ (fun j => if i = j then 1 else 0) := by
      rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl (fun i _ => ?_); ring
    rw [e]; linarith
  · rw [hφ x] at hxu
    have e : ∑ i, -φ (fun j => if i = j then 1 else 0) * x i
        = -∑ i, x i * φ (fun j => if i = j then 1 else 0) := by
      rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl (fun i _ => ?_); ring
    rw [e]; linarith

lemma ic_half {n : ℕ} {S : Set (Fin n → ℝ)} {a b : ℝ} {p q : Fin n → ℝ}
    (h : ∀ c ∈ S, a + ∑ i, p i * c i ≤ b + ∑ i, q i * c i) {x : Fin n → ℝ}
    (hx : x ∈ closure (convexHull ℝ S)) : a + ∑ i, p i * x i ≤ b + ∑ i, q i * x i := by
  let H : Set (Fin n → ℝ) := {v | a + ∑ i, p i * v i ≤ b + ∑ i, q i * v i}
  have hconv : Convex ℝ H := by
    intro u hu v hv s t hs ht hst
    simp only [H, Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hu hv ⊢
    have e1 : ∑ i, p i * (s * u i + t * v i) = s * ∑ i, p i * u i + t * ∑ i, p i * v i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_); ring
    have e2 : ∑ i, q i * (s * u i + t * v i) = s * ∑ i, q i * u i + t * ∑ i, q i * v i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_); ring
    rw [e1, e2]
    have : a = s * a + t * a := by rw [← add_mul, hst, one_mul]
    have : b = s * b + t * b := by rw [← add_mul, hst, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hu hs, mul_le_mul_of_nonneg_left hv ht]
  have hclosed : IsClosed H := by
    apply isClosed_le <;> fun_prop
  exact closure_minimal (convexHull_min (fun c hc => h c hc) hconv) hclosed hx

lemma ic_nbhd {n : ℕ} {x : Fin n → ℝ} {a m : ℝ} {p : Fin n → ℝ}
    (h : ∀ y ∈ IntegralNeighborhood x, a + ∑ i, p i * (y i : ℝ) ≤ m) :
    a + ∑ i, p i * x i ≤ m := by
  classical
  let v : Fin n → ℤ := fun i => if 0 ≤ p i then ⌈x i⌉ else ⌊x i⌋
  have hv : v ∈ IntegralNeighborhood x := by
    intro i; simp only [v]; split_ifs
    · exact ⟨Int.floor_le_ceil _, le_rfl⟩
    · exact ⟨le_rfl, Int.floor_le_ceil _⟩
  have := h v hv
  have hle : ∑ i, p i * x i ≤ ∑ i, p i * (v i : ℝ) := by
    apply Finset.sum_le_sum; intro i _
    simp only [v]; split_ifs with hp
    · exact mul_le_mul_of_nonneg_left (Int.le_ceil _) hp
    · push_neg at hp; exact mul_le_mul_of_nonpos_left (Int.floor_le _) hp.le
  linarith

lemma ic_C_le_L {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (x : Fin n → ℝ) :
    ConvexClosure f x ≤ LocalConvexExtension f x := by
  unfold ConvexClosure LocalConvexExtension
  apply sSup_le_sSup
  rintro v ⟨p, a, h, rfl⟩
  exact ⟨p, a, fun y _ => h y, rfl⟩

lemma ic_ind_le {n : ℕ} (S : Set (Fin n → ℤ)) (y : Fin n → ℤ) (r : ℝ) :
    ((r : ℝ) : EReal) ≤ WithBot.some (IndicatorZ S y) ↔ (y ∈ S → r ≤ 0) := by
  unfold IndicatorZ
  split_ifs with h
  · simp only [h, forall_const]
    exact EReal.coe_le_coe_iff
  · simp only [h, false_implies, iff_true]
    exact le_top

lemma ic_finite_sub {n : ℕ} {S : Set (Fin n → ℤ)} {z : Fin n → ℝ}
    (hz : z ∈ convexHull ℝ (icEmb '' S)) :
    ∃ T ⊆ S, T.Finite ∧ z ∈ convexHull ℝ (icEmb '' T) := by
  rw [convexHull_eq_union_convexHull_finite_subsets] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨t, ht, hzt⟩ := hz
  refine ⟨S ∩ icEmb ⁻¹' (t : Set (Fin n → ℝ)), Set.inter_subset_left, ?_, ?_⟩
  · exact (t.finite_toSet.preimage (icEmb_inj.injOn)).subset Set.inter_subset_right
  · refine convexHull_mono ?_ hzt
    intro v hv
    obtain ⟨y, hy, rfl⟩ := ht hv
    exact ⟨y, ⟨hy, hv⟩, rfl⟩

lemma ic_nbhd_finite {n : ℕ} (x : Fin n → ℝ) : (IntegralNeighborhood x).Finite := by
  refine (Set.finite_Icc (fun i => ⌊x i⌋) (fun i => ⌈x i⌉)).subset ?_
  intro y hy
  exact ⟨fun i => (hy i).1, fun i => (hy i).2⟩

/-- the core set criterion -/
lemma ic_set_of_local {n : ℕ} (S : Set (Fin n → ℤ))
    (hQ : ∀ z : Fin n → ℝ, z ∈ convexHull ℝ (icEmb '' S) →
      z ∈ convexHull ℝ (icEmb '' (IntegralNeighborhood z ∩ S))) :
    IntegrallyConvexSet S := by
  intro x
  apply le_antisymm _ (ic_C_le_L _ x)
  -- key closure step
  have key : x ∈ closure (convexHull ℝ (icEmb '' S)) →
      x ∈ convexHull ℝ (icEmb '' (IntegralNeighborhood x ∩ S)) := by
    intro hx
    let B : Set (Fin n → ℤ) := Set.Icc (fun i => ⌊x i⌋ - 2) (fun i => ⌈x i⌉ + 2)
    let H := convexHull ℝ (icEmb '' (B ∩ S))
    have hHc : IsClosed H :=
      (((Set.finite_Icc _ _).inter_of_left S).image icEmb).isClosed_convexHull ℝ
    have hxH : x ∈ H := by
      rw [← hHc.closure_eq, Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.mp hx (min ε 1) (lt_min hε one_pos)
      refine ⟨z, ?_, lt_of_lt_of_le hdist (min_le_left _ _)⟩
      refine convexHull_mono (Set.image_mono ?_) (hQ z hz)
      rintro w ⟨hw, hwS⟩
      refine ⟨?_, hwS⟩
      have hdi : ∀ i, |x i - z i| < 1 := fun i => by
        have := dist_le_pi_dist x z i
        rw [Real.dist_eq] at this
        exact lt_of_le_of_lt this (lt_of_lt_of_le hdist (min_le_right _ _))
      constructor
      · intro i
        have h1 := (hw i).1
        have h2 := Int.sub_one_lt_floor (z i)
        have h3 := Int.floor_le (x i)
        have h4 := (abs_lt.mp (hdi i))
        have : ((⌊x i⌋ - 2 : ℤ) : ℝ) < (⌊z i⌋ : ℝ) := by push_cast; linarith
        have : ⌊x i⌋ - 2 < ⌊z i⌋ := by exact_mod_cast this
        show ⌊x i⌋ - 2 ≤ w i
        omega
      · intro i
        have h1 := (hw i).2
        have h2 := Int.ceil_lt_add_one (z i)
        have h3 := Int.le_ceil (x i)
        have h4 := (abs_lt.mp (hdi i))
        have : (⌈z i⌉ : ℝ) < ((⌈x i⌉ + 2 : ℤ) : ℝ) := by push_cast; linarith
        have : ⌈z i⌉ < ⌈x i⌉ + 2 := by exact_mod_cast this
        show w i ≤ ⌈x i⌉ + 2
        omega
    exact hQ x (convexHull_mono (Set.image_mono Set.inter_subset_right) hxH)
  by_cases hA : x ∈ convexHull ℝ (icEmb '' (IntegralNeighborhood x ∩ S))
  · have h1 : LocalConvexExtension (IndicatorZ S) x ≤ 0 := by
      unfold LocalConvexExtension
      refine sSup_le (fun v hv => ?_)
      obtain ⟨p, a, hmin, rfl⟩ := hv
      have : a + ∑ i, p i * x i ≤ 0 + ∑ i, (0 : Fin n → ℝ) i * x i := by
        refine ic_half (S := icEmb '' (IntegralNeighborhood x ∩ S)) ?_ (subset_closure hA)
        rintro c ⟨y, ⟨hy, hyS⟩, rfl⟩
        have := (ic_ind_le S y _).mp (hmin y hy) hyS
        simpa [icEmb] using this
      simp at this
      exact_mod_cast this
    have h2 : (0 : EReal) ≤ ConvexClosure (IndicatorZ S) x := by
      unfold ConvexClosure
      refine le_sSup ⟨0, 0, fun y => ?_, by simp⟩
      rw [ic_ind_le]; intro; simp
    exact le_trans h1 h2
  · have hnot : x ∉ closure (convexHull ℝ (icEmb '' S)) := fun h => hA (key h)
    obtain ⟨p, a, hle, hpos⟩ := ic_sep (convex_convexHull ℝ _).closure isClosed_closure hnot
    have : ConvexClosure (IndicatorZ S) x = ⊤ := by
      rw [EReal.eq_top_iff_forall_lt]
      intro R
      set hx := a + ∑ i, p i * x i with hhx
      set t := (|R| + 1) / hx with ht
      have ht0 : 0 < t := by positivity
      refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr
        (show R < |R| + 1 by linarith [le_abs_self R])) ?_
      unfold ConvexClosure
      refine le_sSup ⟨fun i => t * p i, t * a, fun y => ?_, ?_⟩
      · rw [ic_ind_le]; intro hyS
        have := hle (icEmb y) (subset_closure (subset_convexHull ℝ _ ⟨y, hyS, rfl⟩))
        have e : t * a + ∑ i, t * p i * (y i : ℝ) = t * (a + ∑ i, p i * icEmb y i) := by
          rw [mul_add, Finset.mul_sum]; congr 1
          refine Finset.sum_congr rfl (fun i _ => ?_); simp [icEmb]; ring
        rw [e]; exact mul_nonpos_of_nonneg_of_nonpos ht0.le this
      · have e : t * a + ∑ i, t * p i * x i = t * hx := by
          rw [hhx, mul_add, Finset.mul_sum]; congr 1
          refine Finset.sum_congr rfl (fun i _ => ?_); ring
        rw [e, ht, div_mul_cancel₀ _ hpos.ne']
    rw [this]; exact le_top


lemma ic_sum_aff {n : ℕ} (m0 t a : ℝ) (p0 p v : Fin n → ℝ) :
    (m0 + t * a) + ∑ i, (p0 i + t * p i) * v i
      = (m0 + ∑ i, p0 i * v i) + t * (a + ∑ i, p i * v i) := by
  have : ∑ i, (p0 i + t * p i) * v i = ∑ i, p0 i * v i + t * ∑ i, p i * v i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_); ring
  rw [this]; ring

lemma ic_L_ge {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (x : Fin n → ℝ) (p : Fin n → ℝ) (a : ℝ)
    (h : ∀ y ∈ IntegralNeighborhood x, ((a + ∑ i, p i * (y i : ℝ) : ℝ) : EReal) ≤
      WithBot.some (f y)) :
    ((a + ∑ i, p i * x i : ℝ) : EReal) ≤ LocalConvexExtension f x :=
  le_sSup ⟨p, a, h, rfl⟩

lemma ic_C_le {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (T : Set (Fin n → ℤ)) (z : Fin n → ℝ)
    (hz : z ∈ convexHull ℝ (icEmb '' T)) (b : ℝ) (q : Fin n → ℝ)
    (hT : ∀ y ∈ T, f y ≤ ((b + ∑ i, q i * (y i : ℝ) : ℝ) : WithTop ℝ)) :
    ConvexClosure f z ≤ ((b + ∑ i, q i * z i : ℝ) : EReal) := by
  unfold ConvexClosure
  refine sSup_le (fun v hv => ?_)
  obtain ⟨p, a, hmin, rfl⟩ := hv
  have := ic_half (S := icEmb '' T) (a := a) (b := b) (p := p) (q := q) ?_ (subset_closure hz)
  · exact_mod_cast this
  rintro c ⟨y, hy, rfl⟩
  have h1 : ((a + ∑ i, p i * (y i : ℝ) : ℝ) : EReal) ≤ ((b + ∑ i, q i * (y i : ℝ) : ℝ) : EReal) :=
    le_trans (hmin y) (WithBot.coe_le_coe.mpr (hT y hy))
  exact EReal.coe_le_coe_iff.mp h1

lemma ic_bdd_above {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (T : Set (Fin n → ℤ)) (hT : T.Finite)
    (hfin : ∀ y ∈ T, f y ≠ ⊤) : ∃ b : ℝ, ∀ y ∈ T, f y ≤ (b : WithTop ℝ) := by
  obtain ⟨b, hb⟩ := (hT.image (fun y => (f y).untopD 0)).bddAbove
  refine ⟨b, fun y hy => ?_⟩
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (hfin y hy)
  have := hb ⟨y, hy, rfl⟩
  simp only at this
  rw [← hr, WithTop.untopD_coe] at this
  rw [← hr]; exact_mod_cast this

lemma ic_bdd_below {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (T : Set (Fin n → ℤ)) (hT : T.Finite) :
    ∃ m : ℝ, ∀ y ∈ T, (m : WithTop ℝ) ≤ f y := by
  obtain ⟨m, hm⟩ := (hT.image (fun y => (f y).untopD 0)).bddBelow
  refine ⟨m, fun y hy => ?_⟩
  rcases eq_or_ne (f y) ⊤ with h | h
  · rw [h]; exact le_top
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp h
  have := hm ⟨y, hy, rfl⟩
  simp only at this
  rw [← hr, WithTop.untopD_coe] at this
  rw [← hr]; exact_mod_cast this

lemma ic_QD {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (hf : IntegrallyConvex f) :
    ∀ z : Fin n → ℝ, z ∈ convexHull ℝ (icEmb '' DomZ f) →
      z ∈ convexHull ℝ (icEmb '' (IntegralNeighborhood z ∩ DomZ f)) := by
  intro z hz
  by_contra hA
  obtain ⟨T, hTD, hTf, hzT⟩ := ic_finite_sub hz
  obtain ⟨b, hb⟩ := ic_bdd_above f T hTf (fun y hy => hTD hy)
  have hC : ConvexClosure f z ≤ ((b + ∑ i, (0 : Fin n → ℝ) i * z i : ℝ) : EReal) :=
    ic_C_le f T z hzT b 0 (fun y hy => by simpa using hb y hy)
  have hfinN : (IntegralNeighborhood z ∩ DomZ f).Finite :=
    (ic_nbhd_finite z).inter_of_left _
  obtain ⟨p, a, hle, hpos⟩ := ic_sep (convex_convexHull ℝ _)
    ((hfinN.image icEmb).isClosed_convexHull ℝ) hA
  obtain ⟨m, hm⟩ := ic_bdd_below f _ hfinN
  have hL : LocalConvexExtension f z = ⊤ := by
    rw [EReal.eq_top_iff_forall_lt]
    intro R
    set hx := a + ∑ i, p i * z i with hhx
    set t := (|R| + |m| + 1) / hx with ht
    have ht0 : 0 < t := by positivity
    have hv := ic_L_ge f z (fun i => 0 + t * p i) (m + t * a) ?_
    · refine lt_of_lt_of_le ?_ hv
      have e := ic_sum_aff m t a 0 p z
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] at e
      simp only [zero_add] at e ⊢
      rw [e, ← hhx, ht, div_mul_cancel₀ _ hpos.ne']
      exact EReal.coe_lt_coe_iff.mpr (by linarith [le_abs_self R, neg_abs_le m])
    · intro y hy
      rcases eq_or_ne (f y) ⊤ with h | h
      · rw [h]; exact le_top
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp h
      have hmr : m ≤ r := by have := hm y ⟨hy, h⟩; rw [← hr] at this; exact_mod_cast this
      have hhy := hle (icEmb y) (subset_convexHull ℝ _ ⟨y, ⟨hy, h⟩, rfl⟩)
      have e := ic_sum_aff m t a 0 p (fun i => (y i : ℝ))
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, zero_add] at e
      simp only [zero_add]
      rw [← hr, e]
      apply EReal.coe_le_coe_iff.mpr
      have : t * (a + ∑ i, p i * (y i : ℝ)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht0.le (by simpa [icEmb] using hhy)
      linarith
  have := hf z
  rw [hL] at this
  rw [← this] at hC
  exact absurd hC (by simp)

lemma ic_QM {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (hf : IntegrallyConvex f) (p0 : Fin n → ℝ) :
    ∀ z : Fin n → ℝ, z ∈ convexHull ℝ (icEmb '' ArgMinPerturbed f p0) →
      z ∈ convexHull ℝ (icEmb '' (IntegralNeighborhood z ∩ ArgMinPerturbed f p0)) := by
  intro z hz
  by_contra hA
  set M := ArgMinPerturbed f p0 with hMdef
  obtain ⟨T, hTM, hTf, hzT⟩ := ic_finite_sub hz
  rcases Set.eq_empty_or_nonempty T with hTe | ⟨y0, hy0T⟩
  · rw [hTe, Set.image_empty, convexHull_empty] at hzT; exact hzT
  have hy0 : y0 ∈ M := hTM hy0T
  have hM0 : ∀ y, f y0 + ((∑ i, p0 i * (y i : ℝ) : ℝ) : WithTop ℝ) ≤
      f y + ((∑ i, p0 i * (y0 i : ℝ) : ℝ) : WithTop ℝ) := hy0
  have hfinN : (IntegralNeighborhood z ∩ M).Finite := (ic_nbhd_finite z).inter_of_left _
  obtain ⟨p, a, hle, hpos⟩ := ic_sep (convex_convexHull ℝ _)
    ((hfinN.image icEmb).isClosed_convexHull ℝ) hA
  rcases eq_or_ne (f y0) ⊤ with htop | hc
  · -- f ≡ ⊤
    have hall : ∀ y, f y = ⊤ := by
      intro y
      have := hM0 y
      rw [htop, top_add, top_le_iff, WithTop.add_eq_top] at this
      rcases this with h | h
      · exact h
      · exact absurd h WithTop.coe_ne_top
    have hmemM : ∀ y, y ∈ M := by
      intro y y'
      rw [hall y, hall y', top_add, top_add]
    have := ic_nbhd (x := z) (a := a) (m := 0) (p := p) (fun y hy => by
      have := hle (icEmb y) (subset_convexHull ℝ _ ⟨y, ⟨hy, hmemM y⟩, rfl⟩)
      simpa [icEmb] using this)
    linarith
  obtain ⟨c, hcr⟩ := WithTop.ne_top_iff_exists.mp hc
  set P : (Fin n → ℤ) → ℝ := fun y => ∑ i, p0 i * (y i : ℝ) with hP
  set m0 := c - P y0 with hm0
  have low : ∀ y (r : ℝ), f y = r → m0 + P y ≤ r := by
    intro y r hr
    have := hM0 y
    rw [hr, ← hcr] at this
    have : c + P y ≤ r + P y0 := by exact_mod_cast this
    simp only [hm0]; linarith
  have memM : ∀ y, y ∈ M → f y = ((m0 + P y : ℝ) : WithTop ℝ) := by
    intro y hy
    have h1 : f y + ((P y0 : ℝ) : WithTop ℝ) ≤ f y0 + ((P y : ℝ) : WithTop ℝ) := hy y0
    rw [← hcr] at h1
    rcases eq_or_ne (f y) ⊤ with h | h
    · rw [h, top_add] at h1
      exact absurd h1 (by rw [top_le_iff]; exact WithTop.coe_ne_top)
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp h
    rw [← hr] at h1 ⊢
    have h2 : r + P y0 ≤ c + P y := by exact_mod_cast h1
    have h3 := low y r hr.symm
    have : r = m0 + P y := by simp only [hm0]; linarith
    rw [this]
  have memM' : ∀ y, f y = ((m0 + P y : ℝ) : WithTop ℝ) → y ∈ M := by
    intro y hy y'
    rcases eq_or_ne (f y') ⊤ with h | h
    · rw [h, top_add]; exact le_top
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp h
    have h3 := low y' r hr.symm
    rw [hy, ← hr]
    show (((m0 + P y : ℝ) : WithTop ℝ) + ((P y' : ℝ) : WithTop ℝ)) ≤
      ((r : ℝ) : WithTop ℝ) + ((P y : ℝ) : WithTop ℝ)
    rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
    linarith
  have hC : ConvexClosure f z ≤ ((m0 + ∑ i, p0 i * z i : ℝ) : EReal) :=
    ic_C_le f T z hzT m0 p0 (fun y hy => le_of_eq (memM y (hTM hy)))
  -- finite set of strict points
  set h : (Fin n → ℤ) → ℝ := fun y => a + ∑ i, p i * (y i : ℝ) with hh
  set F := {y ∈ IntegralNeighborhood z | f y ≠ ⊤ ∧ y ∉ M} with hF
  have hFfin : F.Finite := (ic_nbhd_finite z).subset (fun y hy => hy.1)
  have hgap : ∀ y ∈ F, 0 < (f y).untopD 0 - m0 - P y := by
    intro y hy
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hy.2.1
    rw [← hr, WithTop.untopD_coe]
    have h1 := low y r hr.symm
    rcases h1.lt_or_eq with h2 | h2
    · linarith
    · exact absurd (memM' y (by rw [← hr, h2])) hy.2.2
  have hev : ∀ᶠ t in nhds (0 : ℝ), ∀ y ∈ F, t * h y < (f y).untopD 0 - m0 - P y := by
    rw [Filter.eventually_all_finite hFfin]
    intro y hy
    have hc : Filter.Tendsto (fun t : ℝ => t * h y) (nhds 0) (nhds (0 * h y)) :=
      (continuous_id.mul continuous_const).tendsto 0
    rw [zero_mul] at hc
    exact hc.eventually (eventually_lt_nhds (hgap y hy))
  obtain ⟨t, ht, ht0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0))).exists
  have ht0 : 0 < t := ht0
  have hv := ic_L_ge f z (fun i => p0 i + t * p i) (m0 + t * a) ?_
  · have e := ic_sum_aff m0 t a p0 p z
    rw [e] at hv
    have := hf z
    rw [this] at hv
    have hfin := le_trans hv hC
    have := EReal.coe_le_coe_iff.mp hfin
    have : 0 < t * (a + ∑ i, p i * z i) := mul_pos ht0 hpos
    linarith
  · intro y hy
    have e := ic_sum_aff m0 t a p0 p (fun i => (y i : ℝ))
    beta_reduce at e
    rw [e]
    rcases eq_or_ne (f y) ⊤ with hT | hT
    · rw [hT]; exact le_top
    by_cases hyM : y ∈ M
    · rw [memM y hyM]
      apply EReal.coe_le_coe_iff.mpr
      have hhy := hle (icEmb y) (subset_convexHull ℝ _ ⟨y, ⟨hy, hyM⟩, rfl⟩)
      have : t * (a + ∑ i, p i * (y i : ℝ)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht0.le (by simpa [icEmb] using hhy)
      simp only [hP]; linarith
    · have hyF : y ∈ F := ⟨hy, hT, hyM⟩
      have h1 := ht y hyF
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hT
      rw [← hr, WithTop.untopD_coe] at h1
      rw [← hr]
      apply EReal.coe_le_coe_iff.mpr
      simp only [hh, hP] at h1 ⊢
      linarith

theorem p328_core {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (hf : IntegrallyConvex f) :
    IntegrallyConvexSet (DomZ f) ∧
      ∀ p : Fin n → ℝ, IntegrallyConvexSet (ArgMinPerturbed f p) :=
  ⟨ic_set_of_local _ (ic_QD f hf), fun p => ic_set_of_local _ (ic_QM f hf p)⟩

end DiscreteConvex.IntegralConvexityC

open DiscreteConvex.IntegralConvexityC


theorem solution {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ)
    (hf : IntegrallyConvex f) :
    IntegrallyConvexSet (DomZ f) ∧
      ∀ p : Fin n → ℝ, IntegrallyConvexSet (ArgMinPerturbed f p) := by
  exact p328_core f hf
