-- Prove2me | solution 1 for DiscreteConvex.IntegralConvexityC.theorem_3_29_integrally_convex_iff_argmin_sets
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T00:40:11.066198+00:00
-- url     : https://prove2.me/submissions/5022b575-b0be-41fe-846d-41fab0961574

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvexSet
import Definitions.Def_DiscreteConvex_IntegralConvexityC_DomZ
import Definitions.Def_DiscreteConvex_IntegralConvexityC_ArgMinPerturbed
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IsBoundedZ



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

lemma ic_hull_of_set {n : ℕ} {S : Set (Fin n → ℤ)} (hS : IntegrallyConvexSet S) {z : Fin n → ℝ}
    (hz : z ∈ convexHull ℝ (icEmb '' S)) :
    z ∈ convexHull ℝ (icEmb '' (IntegralNeighborhood z ∩ S)) := by
  by_contra hA
  have hfin : (IntegralNeighborhood z ∩ S).Finite := (ic_nbhd_finite z).inter_of_left _
  obtain ⟨p, a, hle, hpos⟩ := ic_sep (convex_convexHull ℝ _)
    ((hfin.image icEmb).isClosed_convexHull ℝ) hA
  have hL : LocalConvexExtension (IndicatorZ S) z = ⊤ := by
    rw [EReal.eq_top_iff_forall_lt]; intro R
    set hx := a + ∑ i, p i * z i with hhx
    set t := (|R| + 1) / hx with ht
    have ht0 : 0 < t := by positivity
    refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr
      (show R < |R| + 1 by linarith [le_abs_self R])) ?_
    unfold LocalConvexExtension
    refine le_sSup ⟨fun i => t * p i, t * a, fun y hy => ?_, ?_⟩
    · rw [ic_ind_le]; intro hyS
      have := hle (icEmb y) (subset_convexHull ℝ _ ⟨y, ⟨hy, hyS⟩, rfl⟩)
      have e : t * a + ∑ i, t * p i * (y i : ℝ) = t * (a + ∑ i, p i * icEmb y i) := by
        rw [mul_add, Finset.mul_sum]; congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_); simp [icEmb]; ring
      rw [e]; exact mul_nonpos_of_nonneg_of_nonpos ht0.le this
    · have e : t * a + ∑ i, t * p i * z i = t * hx := by
        rw [hhx, mul_add, Finset.mul_sum]; congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_); ring
      rw [e, ht, div_mul_cancel₀ _ hpos.ne']
  have hC : ConvexClosure (IndicatorZ S) z ≤ 0 := by
    unfold ConvexClosure
    refine sSup_le (fun v hv => ?_)
    obtain ⟨p, a, hmin, rfl⟩ := hv
    have : a + ∑ i, p i * z i ≤ 0 + ∑ i, (0 : Fin n → ℝ) i * z i := by
      refine ic_half (S := icEmb '' S) ?_ (subset_closure hz)
      rintro c ⟨y, hyS, rfl⟩
      have := (ic_ind_le S y _).mp (hmin y) hyS
      simpa [icEmb] using this
    simp at this
    exact_mod_cast this
  have := hS z
  rw [hL] at this
  rw [← this] at hC
  exact absurd hC (by simp)

lemma ic_one_side {n : ℕ} {G : Set (Fin n → ℤ)} (hG : G.Finite) (c : Fin n → ℤ)
    (hc : ∀ y ∈ G, ∀ i, c i ≤ y i ∧ y i ≤ c i + 1) {x : Fin n → ℝ}
    (hx : x ∈ convexHull ℝ (icEmb '' G)) :
    x ∈ convexHull ℝ (icEmb '' (G ∩ IntegralNeighborhood x)) := by
  classical
  set Gf := (hG.image icEmb).toFinset with hGf_def
  have hGf : (Gf : Set (Fin n → ℝ)) = icEmb '' G := (hG.image icEmb).coe_toFinset
  rw [← hGf, Finset.mem_convexHull'] at hx
  obtain ⟨w, hw0, hw1, hwx⟩ := hx
  have hcoord : ∀ i, x i = ∑ v ∈ Gf, w v * v i := by
    intro i; rw [← hwx]; simp [Finset.sum_apply]
  have hb : ∀ i, ∀ u ∈ Gf, (c i : ℝ) ≤ u i ∧ u i ≤ c i + 1 := by
    intro i u hu
    have hu' : u ∈ icEmb '' G := by rw [← hGf]; exact hu
    obtain ⟨y', hy', rfl⟩ := hu'
    have := hc y' hy' i
    simp only [icEmb]
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
  have key : ∀ v ∈ Gf, w v ≠ 0 → v ∈ icEmb '' (G ∩ IntegralNeighborhood x) := by
    intro v hv hwv
    have hv' : v ∈ icEmb '' G := by rw [← hGf]; exact hv
    obtain ⟨y, hyG, rfl⟩ := hv'
    have hwpos : 0 < w (icEmb y) := lt_of_le_of_ne (hw0 _ hv) (Ne.symm hwv)
    refine ⟨y, ⟨hyG, fun i => ?_⟩, rfl⟩
    have hxl : (c i : ℝ) ≤ x i := by
      rw [hcoord i]
      calc (c i : ℝ) = ∑ u ∈ Gf, w u * c i := by rw [← Finset.sum_mul, hw1, one_mul]
        _ ≤ _ := Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left (hb i u hu).1 (hw0 u hu))
    have hxu : x i ≤ c i + 1 := by
      rw [hcoord i]
      calc ∑ u ∈ Gf, w u * u i ≤ ∑ u ∈ Gf, w u * (c i + 1) :=
            Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left (hb i u hu).2 (hw0 u hu))
        _ = c i + 1 := by rw [← Finset.sum_mul, hw1, one_mul]
    have hyi := hc y hyG i
    have hyv : ((y i : ℤ) : ℝ) = icEmb y i := rfl
    rcases (show y i = c i ∨ y i = c i + 1 by omega) with h | h
    · -- x i < c i + 1
      have hlt : x i < c i + 1 := by
        by_contra hge
        push_neg at hge
        have heq : ∑ u ∈ Gf, w u * ((c i + 1) - u i) = 0 := by
          rw [Finset.sum_congr rfl (fun u _ => mul_sub (w u) _ _), Finset.sum_sub_distrib,
            ← Finset.sum_mul, hw1, ← hcoord i]
          linarith
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun u hu =>
          mul_nonneg (hw0 u hu) (by linarith [(hb i u hu).2]))).mp heq (icEmb y) hv
        rw [← hyv, h] at this
        have : w (icEmb y) = 0 := by linarith
        linarith
      constructor
      · have : ⌊x i⌋ < c i + 1 := Int.floor_lt.mpr (by push_cast; exact hlt)
        omega
      · have : c i - 1 < ⌈x i⌉ := Int.lt_ceil.mpr (by push_cast; linarith)
        omega
    · have hgt : (c i : ℝ) < x i := by
        by_contra hle
        push_neg at hle
        have heq : ∑ u ∈ Gf, w u * (u i - c i) = 0 := by
          rw [Finset.sum_congr rfl (fun u _ => mul_sub (w u) _ _), Finset.sum_sub_distrib,
            ← Finset.sum_mul, hw1, ← hcoord i]
          linarith
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun u hu =>
          mul_nonneg (hw0 u hu) (by linarith [(hb i u hu).1]))).mp heq (icEmb y) hv
        rw [← hyv, h] at this
        push_cast at this
        have : w (icEmb y) = 0 := by linarith
        linarith
      constructor
      · have : ⌊x i⌋ < c i + 2 := Int.floor_lt.mpr (by push_cast; linarith)
        omega
      · have : c i < ⌈x i⌉ := Int.lt_ceil.mpr hgt
        omega
  have hfilt : x ∈ convexHull ℝ ((Gf.filter (fun v => w v ≠ 0) : Finset (Fin n → ℝ)) :
      Set (Fin n → ℝ)) := by
    rw [Finset.mem_convexHull']
    refine ⟨w, fun v hv => hw0 v (Finset.mem_filter.mp hv).1, ?_, ?_⟩
    · rw [Finset.sum_filter_ne_zero]; exact hw1
    · rw [Finset.sum_filter, ← hwx]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      split_ifs with h
      · rfl
      · push_neg at h; simp [h]
  refine convexHull_mono ?_ hfilt
  intro v hv
  have hv' := Finset.mem_filter.mp hv
  exact key v hv'.1 hv'.2

lemma ic_sum_pert {n : ℕ} (p d v : Fin n → ℝ) (t : ℝ) :
    ∑ i, (p i + t * d i) * v i = ∑ i, p i * v i + t * ∑ i, d i * v i := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_); ring

theorem p329_back {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ)
    (hne : (DomZ f).Nonempty) (hbdd : IsBoundedZ (DomZ f))
    (hS : ∀ p : Fin n → ℝ, IntegrallyConvexSet (ArgMinPerturbed f p)) :
    IntegrallyConvex f := by
  classical
  intro x
  apply le_antisymm _ (ic_C_le_L f x)
  obtain ⟨lo, hi, hsub⟩ := hbdd
  have hDfin : (DomZ f).Finite := (Set.finite_Icc lo hi).subset
    (fun y hy => ⟨fun i => (hsub hy i).1, fun i => (hsub hy i).2⟩)
  set D := DomZ f with hDdef
  set fr : (Fin n → ℤ) → ℝ := fun y => (f y).untopD 0 with hfr
  have hfrD : ∀ y ∈ D, f y = ((fr y : ℝ) : WithTop ℝ) := by
    intro y hy
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hy
    simp only [hfr, ← hr, WithTop.untopD_coe]
  have hnotD : ∀ y, y ∉ D → f y = ⊤ := fun y hy => by
    by_contra h; exact hy h
  obtain ⟨b, hb⟩ := ic_bdd_above f D hDfin (fun y hy => hy)
  obtain ⟨m, hm⟩ := ic_bdd_below f D hDfin
  by_cases hx : x ∉ convexHull ℝ (icEmb '' D)
  · obtain ⟨p, a, hle, hpos⟩ := ic_sep (convex_convexHull ℝ _)
      ((hDfin.image icEmb).isClosed_convexHull ℝ) hx
    have hCt : ConvexClosure f x = ⊤ := by
      rw [EReal.eq_top_iff_forall_lt]
      intro R
      set hx' := a + ∑ i, p i * x i with hhx
      set t := (|R| + |m| + 1) / hx' with ht
      have ht0 : 0 < t := by positivity
      have hv : ((m + t * a + ∑ i, (fun i => 0 + t * p i) i * x i : ℝ) : EReal)
          ≤ ConvexClosure f x := by
        unfold ConvexClosure
        refine le_sSup ⟨fun i => 0 + t * p i, m + t * a, fun y => ?_, rfl⟩
        rcases em (y ∈ D) with hy | hy
        · rw [hfrD y hy]
          have hmr : m ≤ fr y := by
            have := hm y hy; rw [hfrD y hy] at this; exact_mod_cast this
          have hhy := hle (icEmb y) (subset_convexHull ℝ _ ⟨y, hy, rfl⟩)
          have e := ic_sum_aff m t a 0 p (fun i => (y i : ℝ))
          simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, zero_add] at e
          simp only [zero_add]
          rw [e]
          apply EReal.coe_le_coe_iff.mpr
          have : t * (a + ∑ i, p i * (y i : ℝ)) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos ht0.le (by simpa [icEmb] using hhy)
          linarith
        · rw [hnotD y hy]; exact le_top
      refine lt_of_lt_of_le ?_ hv
      have e := ic_sum_aff m t a 0 p x
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] at e
      simp only [zero_add] at e ⊢
      rw [e, ← hhx, ht, div_mul_cancel₀ _ hpos.ne']
      exact EReal.coe_lt_coe_iff.mpr (by linarith [le_abs_self R, neg_abs_le m])
    rw [hCt]; exact le_top
  push_neg at hx
  -- neighbourhood property
  set B : Set (Fin n → ℤ) := Set.Icc (fun i => ⌊x i⌋ - 2) (fun i => ⌈x i⌉ + 2) with hB
  have hBfin : B.Finite := Set.finite_Icc _ _
  have hev : ∀ᶠ x' in nhds x, ∀ G ∈ {G : Set (Fin n → ℤ) | G ⊆ B},
      x ∉ convexHull ℝ (icEmb '' G) → x' ∉ convexHull ℝ (icEmb '' G) := by
    rw [Filter.eventually_all_finite hBfin.finite_subsets]
    intro G hG
    by_cases hxG : x ∈ convexHull ℝ (icEmb '' G)
    · exact Filter.Eventually.of_forall (fun _ h => absurd hxG h)
    · have hcl : IsClosed (convexHull ℝ (icEmb '' G)) :=
        ((hBfin.subset hG).image icEmb).isClosed_convexHull ℝ
      filter_upwards [hcl.isOpen_compl.mem_nhds hxG] with x' hx' _ using hx'
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp hev
  set δ := min ε 1 / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδε : δ < ε := by
    have := min_le_left ε 1; rw [hδ]; linarith
  have hδ1 : δ < 1 := by
    have := min_le_right ε 1; rw [hδ]; linarith
  set ε0 := δ / 2 with hε0
  have hε00 : 0 < ε0 := by positivity
  -- finset and dual function
  set Df := hDfin.toFinset with hDf_def
  have hDf : ∀ y, y ∈ Df ↔ y ∈ D := fun y => hDfin.mem_toFinset
  have hDfne : Df.Nonempty := by obtain ⟨y, hy⟩ := hne; exact ⟨y, (hDf y).mpr hy⟩
  set ψ : (Fin n → ℝ) → ℝ := fun p => Df.inf' hDfne
    (fun y => fr y + (∑ i, p i * x i - ∑ i, p i * (y i : ℝ))) with hψ
  have ψ1 : ∀ p, ∀ y ∈ D, ψ p ≤ fr y + (∑ i, p i * x i - ∑ i, p i * (y i : ℝ)) :=
    fun p y hy => Finset.inf'_le _ ((hDf y).mpr hy)
  have ψ2 : ∀ p, ∃ y ∈ D, ψ p = fr y + (∑ i, p i * x i - ∑ i, p i * (y i : ℝ)) := by
    intro p
    obtain ⟨y, hy, h⟩ := Finset.exists_mem_eq_inf' hDfne
      (fun y => fr y + (∑ i, p i * x i - ∑ i, p i * (y i : ℝ)))
    exact ⟨y, (hDf y).mp hy, h⟩
  have ψcont : Continuous ψ :=
    Continuous.finset_inf'_apply hDfne (fun y _ => by fun_prop)
  have ψb : ∀ p, ψ p ≤ b := by
    intro p
    have := ic_half (S := icEmb '' D) (a := ψ p - ∑ i, p i * x i) (p := p) (b := b)
      (q := 0) ?_ (subset_closure hx)
    · simp at this; linarith
    rintro c ⟨y, hy, rfl⟩
    have h1 := ψ1 p y hy
    have h2 : fr y ≤ b := by have := hb y hy; rw [hfrD y hy] at this; exact_mod_cast this
    simp only [icEmb, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    linarith
  set Φ : (Fin n → ℝ) → ℝ := fun p => ψ p - ε0 * ∑ i, |p i| with hΦ
  have Φcont : Continuous Φ :=
    ψcont.sub (continuous_const.mul (continuous_finset_sum _ (fun i _ => (continuous_apply i).abs)))
  set R := (b - ψ 0) / ε0 + 1 with hR
  have hR0 : 0 < R := by
    have : 0 ≤ (b - ψ 0) / ε0 := div_nonneg (by linarith [ψb 0]) hε00.le
    linarith
  obtain ⟨ps, hps, hmax⟩ := (isCompact_closedBall (0 : Fin n → ℝ) R).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self hR0.le⟩ Φcont.continuousOn
  have hglob : ∀ q, Φ q ≤ Φ ps := by
    intro q
    by_cases hq : q ∈ Metric.closedBall (0 : Fin n → ℝ) R
    · exact hmax hq
    · have h0 : Φ 0 ≤ Φ ps := hmax (Metric.mem_closedBall_self hR0.le)
      have hn : R < ‖q‖ := by
        rw [Metric.mem_closedBall, dist_zero_right] at hq; push_neg at hq; exact hq
      have hsum : ‖q‖ ≤ ∑ i, |q i| := by
        refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _))).mpr
          (fun i => ?_)
        rw [Real.norm_eq_abs]
        exact Finset.single_le_sum (f := fun i => |q i|) (fun i _ => abs_nonneg _)
          (Finset.mem_univ i)
      have hΦ0 : Φ 0 = ψ 0 := by simp [hΦ]
      have hq' : Φ q ≤ b - ε0 * ∑ i, |q i| := by
        simp only [hΦ]; linarith [ψb q]
      have hεR : ε0 * R = b - ψ 0 + ε0 := by
        rw [hR, mul_add, mul_div_cancel₀ _ hε00.ne']; ring
      have : ε0 * R < ε0 * ∑ i, |q i| := mul_lt_mul_of_pos_left (by linarith) hε00
      linarith
  -- active set
  set A := {y ∈ D | fr y + (∑ i, ps i * x i - ∑ i, ps i * (y i : ℝ)) = ψ ps} with hA
  have hAfin : A.Finite := hDfin.subset (fun y hy => hy.1)
  have hnear : ∃ x' ∈ convexHull ℝ (icEmb '' A), dist x' x ≤ δ := by
    by_contra hcon
    push_neg at hcon
    have hdisj : Disjoint (Metric.closedBall x δ) (convexHull ℝ (icEmb '' A)) := by
      rw [Set.disjoint_left]; intro a ha haA
      have := hcon a haA; rw [Metric.mem_closedBall] at ha; linarith
    obtain ⟨φ, u, v, hφs, huv, hφt⟩ := geometric_hahn_banach_compact_closed
      (convex_closedBall x δ) (isCompact_closedBall x δ) (convex_convexHull ℝ _)
      ((hAfin.image icEmb).isClosed_convexHull ℝ) hdisj
    set cφ : Fin n → ℝ := fun i => φ (fun j => if i = j then 1 else 0) with hcφ
    have hφ : ∀ w : Fin n → ℝ, φ w = ∑ i, w i * cφ i := by
      intro w
      have := LinearMap.pi_apply_eq_sum_univ (φ : (Fin n → ℝ) →ₗ[ℝ] ℝ) w
      simpa [smul_eq_mul] using this
    set d : Fin n → ℝ := fun i => -cφ i with hd
    -- test point in the ball
    set a : Fin n → ℝ := fun i => x i + δ * (if 0 ≤ cφ i then 1 else -1) with ha
    have haball : a ∈ Metric.closedBall x δ := by
      rw [Metric.mem_closedBall, dist_pi_le_iff hδ0.le]
      intro i
      rw [Real.dist_eq]
      simp only [ha]
      split_ifs <;> simp [abs_of_pos hδ0]
    have hφa : φ a = φ x + δ * ∑ i, |cφ i| := by
      rw [hφ a, hφ x, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [ha]
      split_ifs with h
      · rw [abs_of_nonneg h]; ring
      · push_neg at h; rw [abs_of_neg h]; ring
    set κ := u - φ x with hκ
    have hκ1 : δ * ∑ i, |cφ i| < κ := by have := hφs a haball; rw [hφa] at this; linarith
    have hsabs : 0 ≤ ∑ i, |cφ i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have hκ0 : 0 < κ := by nlinarith
    -- active directions
    have hact : ∀ y ∈ A, κ < ∑ i, d i * x i - ∑ i, d i * (y i : ℝ) := by
      intro y hy
      have h1 := hφt (icEmb y) (subset_convexHull ℝ _ ⟨y, hy, rfl⟩)
      rw [hφ] at h1
      have e1 : ∑ i, d i * x i = -∑ i, x i * cφ i := by
        rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [hd]; ring
      have e2 : ∑ i, d i * (y i : ℝ) = -∑ i, icEmb y i * cφ i := by
        rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [hd, icEmb]; ring
      rw [e1, e2, hκ, hφ x]
      linarith
    -- inactive: small t
    set F := {y ∈ D | y ∉ A} with hF
    have hFfin : F.Finite := hDfin.subset (fun y hy => hy.1)
    have hgap : ∀ y ∈ F, 0 < fr y + (∑ i, ps i * x i - ∑ i, ps i * (y i : ℝ)) - ψ ps := by
      intro y hy
      have h1 := ψ1 ps y hy.1
      rcases h1.lt_or_eq with h2 | h2
      · linarith
      · exact absurd ⟨hy.1, h2.symm⟩ hy.2
    have hev2 : ∀ᶠ t in nhds (0 : ℝ), ∀ y ∈ F,
        t * (κ - (∑ i, d i * x i - ∑ i, d i * (y i : ℝ))) <
          fr y + (∑ i, ps i * x i - ∑ i, ps i * (y i : ℝ)) - ψ ps := by
      rw [Filter.eventually_all_finite hFfin]
      intro y hy
      have hc : Filter.Tendsto
          (fun t : ℝ => t * (κ - (∑ i, d i * x i - ∑ i, d i * (y i : ℝ))))
          (nhds 0) (nhds (0 * (κ - (∑ i, d i * x i - ∑ i, d i * (y i : ℝ))))) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at hc
      exact hc.eventually (eventually_lt_nhds (hgap y hy))
    obtain ⟨t, ht, ht0⟩ := ((hev2.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0))).exists
    have ht0 : 0 < t := ht0
    set pt : Fin n → ℝ := fun i => ps i + t * d i with hpt
    have hψt : ψ ps + t * κ ≤ ψ pt := by
      apply Finset.le_inf'
      intro y hy
      have hyD := (hDf y).mp hy
      have e1 := ic_sum_pert ps d x t
      have e2 := ic_sum_pert ps d (fun i => (y i : ℝ)) t
      beta_reduce at e2
      show ψ ps + t * κ ≤ fr y + (∑ i, (ps i + t * d i) * x i - ∑ i, (ps i + t * d i) * (y i : ℝ))
      rw [e1, e2]
      by_cases hyA : y ∈ A
      · have h1 := hact y hyA
        have h2 := hyA.2
        nlinarith
      · have h1 := ht y ⟨hyD, hyA⟩
        nlinarith
    have hpen : ∑ i, |pt i| ≤ ∑ i, |ps i| + t * ∑ i, |cφ i| := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun i _ => ?_)
      simp only [hpt, hd]
      calc |ps i + t * -cφ i| ≤ |ps i| + |t * -cφ i| := abs_add_le _ _
        _ = |ps i| + t * |cφ i| := by rw [abs_mul, abs_neg, abs_of_pos ht0]
    have := hglob pt
    simp only [hΦ] at this
    have hδe : δ = 2 * ε0 := by rw [hε0]; ring
    have hk : ε0 * ∑ i, |cφ i| < κ := by nlinarith
    have hk2 := mul_pos ht0 (sub_pos.mpr hk)
    have hk3 := mul_le_mul_of_nonneg_left hpen hε00.le
    nlinarith
  obtain ⟨x', hx'A, hx'd⟩ := hnear
  set M := ArgMinPerturbed f ps with hMdef
  set mm := ψ ps - ∑ i, ps i * x i with hmm
  have hAM : A ⊆ M := by
    intro y hy y'
    rw [hfrD y hy.1]
    rcases em (y' ∈ D) with hy' | hy'
    · rw [hfrD y' hy', ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
      have := ψ1 ps y' hy'
      have := hy.2
      linarith
    · rw [hnotD y' hy', top_add]; exact le_top
  have memM : ∀ y ∈ M, f y = ((mm + ∑ i, ps i * (y i : ℝ) : ℝ) : WithTop ℝ) := by
    intro y hy
    obtain ⟨y'', hy''D, hy''⟩ := ψ2 ps
    have h : f y + ((∑ i, ps i * (y'' i : ℝ) : ℝ) : WithTop ℝ) ≤
        f y'' + ((∑ i, ps i * (y i : ℝ) : ℝ) : WithTop ℝ) := hy y''
    rw [hfrD y'' hy''D] at h
    have hyD : y ∈ D := by
      by_contra hyD
      rw [hnotD y hyD, top_add, ← WithTop.coe_add] at h
      exact WithTop.coe_ne_top (top_le_iff.mp h)
    rw [hfrD y hyD] at h ⊢
    rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h
    have := ψ1 ps y hyD
    congr 1
    simp only [hmm]
    apply le_antisymm <;> linarith
  have hx'M : x' ∈ convexHull ℝ (icEmb '' M) := convexHull_mono (Set.image_mono hAM) hx'A
  have h1 := ic_hull_of_set (hS ps) hx'M
  set G := IntegralNeighborhood x' ∩ M with hG
  have hGB : G ⊆ B := by
    rintro w ⟨hw, -⟩
    have hdi : ∀ i, |x i - x' i| < 1 := fun i => by
      have := dist_le_pi_dist x x' i
      rw [Real.dist_eq] at this
      rw [dist_comm] at hx'd
      linarith
    constructor
    · intro i
      have h1 := (hw i).1
      have h2 := Int.sub_one_lt_floor (x' i)
      have h3 := Int.floor_le (x i)
      have h4 := (abs_lt.mp (hdi i))
      have : ((⌊x i⌋ - 2 : ℤ) : ℝ) < (⌊x' i⌋ : ℝ) := by push_cast; linarith
      have : ⌊x i⌋ - 2 < ⌊x' i⌋ := by exact_mod_cast this
      show ⌊x i⌋ - 2 ≤ w i
      omega
    · intro i
      have h1 := (hw i).2
      have h2 := Int.ceil_lt_add_one (x' i)
      have h3 := Int.le_ceil (x i)
      have h4 := (abs_lt.mp (hdi i))
      have : (⌈x' i⌉ : ℝ) < ((⌈x i⌉ + 2 : ℤ) : ℝ) := by push_cast; linarith
      have : ⌈x' i⌉ < ⌈x i⌉ + 2 := by exact_mod_cast this
      show w i ≤ ⌈x i⌉ + 2
      omega
  have hxG : x ∈ convexHull ℝ (icEmb '' G) := by
    by_contra hn
    exact hεP (show dist x' x < ε by linarith) G hGB hn h1
  have hGfin : G.Finite := (ic_nbhd_finite x').inter_of_left _
  have h2 := ic_one_side hGfin (fun i => ⌊x' i⌋)
    (fun y hy i => ⟨(hy.1 i).1, le_trans (hy.1 i).2 (Int.ceil_le_floor_add_one _)⟩) hxG
  have hL : LocalConvexExtension f x ≤ ((ψ ps : ℝ) : EReal) := by
    unfold LocalConvexExtension
    refine sSup_le (fun v hv => ?_)
    obtain ⟨q, a, hmin, rfl⟩ := hv
    have := ic_half (S := icEmb '' (G ∩ IntegralNeighborhood x)) (a := a) (p := q) (b := mm)
      (q := ps) ?_ (subset_closure h2)
    · have : a + ∑ i, q i * x i ≤ ψ ps := by simp only [hmm] at this; linarith
      exact_mod_cast this
    rintro c ⟨y, ⟨hyG, hyN⟩, rfl⟩
    have h3 := hmin y hyN
    rw [memM y hyG.2] at h3
    exact EReal.coe_le_coe_iff.mp h3
  have hC : ((ψ ps : ℝ) : EReal) ≤ ConvexClosure f x := by
    unfold ConvexClosure
    refine le_sSup ⟨ps, mm, fun y => ?_, ?_⟩
    · rcases em (y ∈ D) with hy | hy
      · rw [hfrD y hy]
        apply EReal.coe_le_coe_iff.mpr
        have := ψ1 ps y hy
        simp only [hmm]; linarith
      · rw [hnotD y hy]; exact le_top
    · congr 1; simp only [hmm]; ring
  exact le_trans hL hC

theorem p329_core {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ)
    (hne : (DomZ f).Nonempty) (hbdd : IsBoundedZ (DomZ f)) :
    IntegrallyConvex f ↔ ∀ p : Fin n → ℝ, IntegrallyConvexSet (ArgMinPerturbed f p) :=
  ⟨fun hf => (p328_core f hf).2, fun h => p329_back f hne hbdd h⟩

end DiscreteConvex.IntegralConvexityC

open DiscreteConvex.IntegralConvexityC


theorem solution {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ)
    (hne : (DomZ f).Nonempty) (hbdd : IsBoundedZ (DomZ f)) :
    IntegrallyConvex f ↔ ∀ p : Fin n → ℝ, IntegrallyConvexSet (ArgMinPerturbed f p) := by
  exact p329_core f hne hbdd
