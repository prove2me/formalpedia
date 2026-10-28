-- Prove2me | solution 1 for ErrBoundQG.ProxLin.theorem_5_10
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T17:04:27.332459+00:00
-- url     : https://prove2.me/submissions/09b74f58-dbc5-45d7-87b9-6249a0f02469

import Mathlib
import Definitions.Def_ErrBoundQG_ProxLin_Setting

set_option autoImplicit false

open scoped InnerProductSpace

namespace P6e20

abbrev PV (n m : ℕ) := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)

lemma ereal_step (e1 e2 : EReal) (s a b : ℝ) (hgs : e1 + (s : EReal) ≤ e2)
    (hab : a ≤ s + b) : e1 + (a : EReal) ≤ e2 + (b : EReal) := by
  calc e1 + (a : EReal) ≤ e1 + ((s + b : ℝ) : EReal) := by
        gcongr
    _ = (e1 + (s : EReal)) + (b : EReal) := by rw [EReal.coe_add, add_assoc]
    _ ≤ e2 + (b : EReal) := by gcongr

lemma ereal_cancel (e : EReal) (he : e ≠ ⊤) (hb : e ≠ ⊥) (a b : ℝ)
    (h : e + (a : EReal) ≤ e + (b : EReal)) : a ≤ b := by
  rw [← EReal.coe_toReal he hb, ← EReal.coe_add, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at h
  linarith

lemma ne_top_of_le (e1 e2 : EReal) (a b : ℝ) (h : e1 + (a : EReal) ≤ e2 + (b : EReal))
    (h2 : e2 ≠ ⊤) : e1 ≠ ⊤ := by
  intro h1
  rw [h1, EReal.top_add_coe] at h
  exact (ne_of_lt (EReal.add_lt_top h2 (EReal.coe_ne_top b))) (top_le_iff.mp h)

lemma sep {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f1 : V → EReal) (f2 : V → ℝ)
    (h1 : Convex ℝ {q : V × ℝ | f1 q.1 ≤ (q.2 : EReal)})
    (h2 : ConvexOn ℝ Set.univ f2) (hc : Continuous f2) (p : V) (a : ℝ)
    (hpa : f1 p = a) (hmin : ∀ y, (a : EReal) + (f2 p : EReal) ≤ f1 y + (f2 y : EReal)) :
    ∃ φ : V →L[ℝ] ℝ, (∀ y, ((a + φ (y - p) : ℝ) : EReal) ≤ f1 y) ∧
      ∀ y, f2 p - φ (y - p) ≤ f2 y := by
  set C1 : Set (V × ℝ) := {q | f1 q.1 ≤ (q.2 : EReal)} with hC1
  set C2 : Set (V × ℝ) := {q | q.2 + f2 q.1 < a + f2 p} with hC2
  have hC2o : IsOpen C2 := isOpen_lt (by fun_prop) continuous_const
  have hC2c : Convex ℝ C2 := by
    have hcv : ConvexOn ℝ Set.univ (fun q : V × ℝ => q.2 + f2 q.1) := by
      refine ⟨convex_univ, ?_⟩
      intro x _ y _ α β hα hβ hαβ
      have := h2.2 (Set.mem_univ x.1) (Set.mem_univ y.1) hα hβ hαβ
      simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul] at this ⊢
      linarith
    simpa using hcv.convex_lt (a + f2 p)
  have hdisj : Disjoint C2 C1 := by
    rw [Set.disjoint_left]
    rintro ⟨y, r⟩ h2' h1'
    simp only [hC1, hC2, Set.mem_setOf_eq] at h1' h2'
    have hm := hmin y
    have h3 : f1 y + (f2 y : EReal) ≤ ((r + f2 y : ℝ) : EReal) := by
      rw [EReal.coe_add]; gcongr
    have h4 : ((r + f2 y : ℝ) : EReal) < ((a + f2 p : ℝ) : EReal) := by exact_mod_cast h2'
    rw [EReal.coe_add] at h4
    exact absurd (lt_of_le_of_lt (hm.trans h3) h4) (lt_irrefl _)
  obtain ⟨Φ, u, hΦ2, hΦ1⟩ := geometric_hahn_banach_open hC2c hC2o h1 hdisj
  set α : ℝ := Φ ((0 : V), (1 : ℝ)) with hαdef
  set φ0 : V →L[ℝ] ℝ := Φ.comp (ContinuousLinearMap.inl ℝ V ℝ) with hφ0
  have hΦ : ∀ (y : V) (r : ℝ), Φ (y, r) = φ0 y + r * α := by
    intro y r
    have e : ((y, r) : V × ℝ) = (y, 0) + r • ((0 : V), (1 : ℝ)) := by
      ext <;> simp
    rw [e, map_add, map_smul]
    simp [φ0, α, smul_eq_mul]
  have hpC1 : ((p, a) : V × ℝ) ∈ C1 := by simp [hC1, hpa]
  have hu1 := hΦ1 _ hpC1
  have hpC2 : ((p, a - 1) : V × ℝ) ∈ C2 := by simp only [hC2, Set.mem_setOf_eq]; linarith
  have hu2 := hΦ2 _ hpC2
  rw [hΦ] at hu1 hu2
  have hα : 0 < α := by nlinarith
  have hsup : ∀ y, φ0 y + (a + f2 p - f2 y) * α ≤ u := by
    intro y
    by_contra hcon
    push_neg at hcon
    set δ := (φ0 y + (a + f2 p - f2 y) * α - u) / (2 * α) with hδdef
    have hδ : 0 < δ := div_pos (by linarith) (by linarith)
    have hm : ((y, a + f2 p - f2 y - δ) : V × ℝ) ∈ C2 := by
      simp only [hC2, Set.mem_setOf_eq]; linarith
    have hh := hΦ2 _ hm
    rw [hΦ] at hh
    have e2 : δ * α * 2 = φ0 y + (a + f2 p - f2 y) * α - u := by
      rw [hδdef]; field_simp
    nlinarith
  have hup : u = φ0 p + a * α := by
    have := hsup p; linarith
  refine ⟨-(α⁻¹) • φ0, ?_, ?_⟩
  · intro y
    rcases eq_or_ne (f1 y) ⊤ with htop | hne
    · rw [htop]; exact le_top
    · have hbot : f1 y ≠ ⊥ := by
        intro hb
        have hm : ((y, (u - φ0 y) / α - 1) : V × ℝ) ∈ C1 := by
          simp [hC1, hb]
        have hh := hΦ1 _ hm
        rw [hΦ] at hh
        have e3 : ((u - φ0 y) / α - 1) * α = u - φ0 y - α := by field_simp
        linarith
      set s := (f1 y).toReal with hsdef
      have hs : f1 y = (s : EReal) := (EReal.coe_toReal hne hbot).symm
      have hm : ((y, s) : V × ℝ) ∈ C1 := by simp [hC1, hs]
      have hh := hΦ1 _ hm
      rw [hΦ] at hh
      rw [hs, EReal.coe_le_coe_iff]
      simp only [ContinuousLinearMap.smul_apply, map_sub, smul_eq_mul]
      set w := α⁻¹ * (φ0 y - φ0 p) with hwdef
      have hw : w * α = φ0 y - φ0 p := by rw [hwdef]; field_simp
      have : a - w ≤ s := by nlinarith
      linarith
  · intro y
    have hh := hsup y
    simp only [ContinuousLinearMap.smul_apply, map_sub, smul_eq_mul]
    set w := α⁻¹ * (φ0 y - φ0 p) with hwdef
    have hw : w * α = φ0 y - φ0 p := by rw [hwdef]; field_simp
    have : f2 p + w ≤ f2 y := by nlinarith
    linarith

/-- Convexity of a real convex combination for a proper convex `EReal` function. -/
lemma gconv_real {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (g : V → EReal)
    (hgb : ∀ x, g x ≠ ⊥)
    (hgc : ∀ (x y : V) (t : ℝ), 0 < t → t < 1 →
      g ((1 - t) • x + t • y) ≤ ((1 - t : ℝ) : EReal) * g x + ((t : ℝ) : EReal) * g y)
    (y1 y2 : V) (r1 r2 α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (h1 : g y1 ≤ (r1 : EReal)) (h2 : g y2 ≤ (r2 : EReal)) :
    g (α • y1 + β • y2) ≤ ((α * r1 + β * r2 : ℝ) : EReal) := by
  rcases eq_or_lt_of_le hβ with hb0 | hbpos
  · have : α = 1 := by linarith
    subst this; rw [← hb0]; simpa using h1
  rcases eq_or_lt_of_le hα with ha0 | hapos
  · have : β = 1 := by linarith
    subst this; rw [← ha0]; simpa using h2
  have hβ1 : β < 1 := by linarith
  have e : α = 1 - β := by linarith
  have h1t : g y1 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top r1) h1
  have h2t : g y2 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top r2) h2
  have hs1 := EReal.coe_toReal h1t (hgb y1)
  have hs2 := EReal.coe_toReal h2t (hgb y2)
  have hc := hgc y1 y2 β hbpos hβ1
  rw [← hs1, ← hs2] at hc
  rw [← hs1] at h1; rw [← hs2] at h2
  rw [EReal.coe_le_coe_iff] at h1 h2
  rw [e]
  refine hc.trans ?_
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have : 0 ≤ 1 - β := by linarith
  nlinarith

lemma opt {n m : ℕ} (g : EuclideanSpace ℝ (Fin n) → EReal)
    (hgb : ∀ x, g x ≠ ⊥)
    (hgc : ∀ (x y : EuclideanSpace ℝ (Fin n)) (t : ℝ), 0 < t → t < 1 →
      g ((1 - t) • x + t • y) ≤ ((1 - t : ℝ) : EReal) * g x + ((t : ℝ) : EReal) * g y)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (hh : ConvexOn ℝ Set.univ h) (hhc : Continuous h)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m))
    (q : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ConvexOn ℝ Set.univ q) (hqc : Continuous q)
    (p : EuclideanSpace ℝ (Fin n)) (hp : g p ≠ ⊤)
    (hmin : ∀ y, g p + ((h b + q p : ℝ) : EReal) ≤
      g y + ((h (b + A (y - p)) + q y : ℝ) : EReal)) :
    ∃ (z : EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin m)),
      (∀ y, g p + ((⟪z, y - p⟫_ℝ : ℝ) : EReal) ≤ g y) ∧
      (∀ u, h b + ⟪w, u - b⟫_ℝ ≤ h u) ∧
      (∀ y, q p - ⟪z + ContinuousLinearMap.adjoint A w, y - p⟫_ℝ ≤ q y) := by
  classical
  set f1 : PV n m → EReal := fun v => if v.2 = A (v.1 - p) then g v.1 else ⊤ with hf1
  set f2 : PV n m → ℝ := fun v => h (b + v.2) + q v.1 with hf2
  set a : ℝ := (g p).toReal with ha
  have hga : g p = (a : EReal) := (EReal.coe_toReal hp (hgb p)).symm
  have hpa : f1 ((p, 0) : PV n m) = (a : EReal) := by
    simp [hf1, hga]
  have hmin' : ∀ v, (a : EReal) + (f2 ((p, 0) : PV n m) : EReal) ≤ f1 v + (f2 v : EReal) := by
    intro v
    simp only [hf1, hf2]
    split_ifs with hv
    · have := hmin v.1
      rw [← hga]; simp only [add_zero]
      rw [hv]; exact this
    · rw [EReal.top_add_coe]; exact le_top
  have hepi : Convex ℝ {w : PV n m × ℝ | f1 w.1 ≤ (w.2 : EReal)} := by
    intro w1 hw1 w2 hw2 α β hα hβ hαβ
    simp only [Set.mem_setOf_eq, hf1] at hw1 hw2 ⊢
    split_ifs at hw1 with e1
    · split_ifs at hw2 with e2
      · have ecomb : (α • w1 + β • w2).1.2 = A ((α • w1 + β • w2).1.1 - p) := by
          simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd]
          rw [e1, e2]
          have : α • w1.1.1 + β • w2.1.1 - p = α • (w1.1.1 - p) + β • (w2.1.1 - p) := by
            have hp' : p = α • p + β • p := by rw [← add_smul, hαβ, one_smul]
            conv_lhs => rw [hp']
            simp only [smul_sub]; abel
          rw [this, map_add, map_smul, map_smul]
        rw [if_pos ecomb]
        simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        exact gconv_real g hgb hgc _ _ _ _ α β hα hβ hαβ hw1 hw2
      · exact absurd hw2 (by simp)
    · exact absurd hw1 (by simp)
  have hf2c : ConvexOn ℝ Set.univ f2 := by
    refine ⟨convex_univ, ?_⟩
    intro v1 _ v2 _ α β hα hβ hαβ
    simp only [hf2, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    have e : b + (α • v1.2 + β • v2.2) = α • (b + v1.2) + β • (b + v2.2) := by
      have hb' : b = α • b + β • b := by rw [← add_smul, hαβ, one_smul]
      conv_lhs => rw [hb']
      simp only [smul_add]; abel
    rw [e]
    have := hh.2 (Set.mem_univ (b + v1.2)) (Set.mem_univ (b + v2.2)) hα hβ hαβ
    have := hq.2 (Set.mem_univ v1.1) (Set.mem_univ v2.1) hα hβ hαβ
    simp only [smul_eq_mul] at *
    linarith
  have hf2cont : Continuous f2 := by
    simp only [hf2]; fun_prop
  obtain ⟨φ, hφ1, hφ2⟩ := sep f1 f2 hepi hf2c hf2cont ((p, 0) : PV n m) a hpa hmin'
  set φ1 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := φ.comp (ContinuousLinearMap.inl ℝ _ _)
  set φ2 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := φ.comp (ContinuousLinearMap.inr ℝ _ _)
  have hφ : ∀ y u, φ ((y, u) : PV n m) = φ1 y + φ2 u := by
    intro y u
    have e : ((y, u) : PV n m) = (y, 0) + (0, u) := by ext <;> simp
    rw [e, map_add]; rfl
  set z' := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm φ1
  set w2 := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm φ2
  have hz' : ∀ y, ⟪z', y⟫_ℝ = φ1 y := fun y => InnerProductSpace.toDual_symm_apply
  have hw2 : ∀ u, ⟪w2, u⟫_ℝ = φ2 u := fun u => InnerProductSpace.toDual_symm_apply
  refine ⟨z' + ContinuousLinearMap.adjoint A w2, -w2, ?_, ?_, ?_⟩
  · intro y
    have hh1 := hφ1 ((y, A (y - p)) : PV n m)
    simp only [hf1, if_pos rfl] at hh1
    have e : ((y, A (y - p)) : PV n m) - (p, 0) = (y - p, A (y - p)) := by ext <;> simp
    rw [e, hφ] at hh1
    rw [hga, ← EReal.coe_add]
    convert hh1 using 3
    rw [inner_add_left, ContinuousLinearMap.adjoint_inner_left, hz', hw2]
  · intro u
    have hh2 := hφ2 ((p, u - b) : PV n m)
    have e : ((p, u - b) : PV n m) - (p, 0) = (0, u - b) := by ext <;> simp
    rw [e, hφ] at hh2
    simp only [hf2, add_zero, map_zero, zero_add, add_sub_cancel] at hh2
    rw [inner_neg_left, hw2]
    linarith
  · intro y
    have hh2 := hφ2 ((y, 0) : PV n m)
    have e : ((y, 0) : PV n m) - (p, 0) = (y - p, 0) := by ext <;> simp
    rw [e, hφ] at hh2
    simp only [hf2, add_zero, map_zero] at hh2
    rw [map_neg, add_neg_cancel_right, hz']
    linarith

lemma taylor {n m : ℕ} (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hc : ContDiff ℝ 1 c) (β : ℝ)
    (hcβ : ∀ x y, ‖fderiv ℝ c x - fderiv ℝ c y‖ ≤ β * ‖x - y‖)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ‖c y - c x - fderiv ℝ c x (y - x)‖ ≤ β / 2 * ‖y - x‖ ^ 2 := by
  have hd : Differentiable ℝ c := hc.differentiable (by norm_num)
  set v := y - x with hv
  set f : ℝ → EuclideanSpace ℝ (Fin m) := fun τ => c (x + τ • v) - c x - τ • fderiv ℝ c x v
    with hfdef
  set f' : ℝ → EuclideanSpace ℝ (Fin m) := fun τ => fderiv ℝ c (x + τ • v) v - fderiv ℝ c x v
  have hderiv : ∀ τ : ℝ, HasDerivAt f (f' τ) τ := by
    intro τ
    have hl : HasDerivAt (fun τ : ℝ => x + τ • v) v τ := by
      simpa using ((hasDerivAt_id τ).smul_const v).const_add x
    have h1 : HasDerivAt (fun τ : ℝ => c (x + τ • v)) (fderiv ℝ c (x + τ • v) v) τ :=
      (hd _).hasFDerivAt.comp_hasDerivAt τ hl
    have h2 : HasDerivAt (fun τ : ℝ => τ • fderiv ℝ c x v) (fderiv ℝ c x v) τ := by
      simpa using (hasDerivAt_id τ).smul_const (fderiv ℝ c x v)
    exact (h1.sub_const (c x)).sub h2
  have hB : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => β / 2 * ‖v‖ ^ 2 * τ ^ 2)
      (β * ‖v‖ ^ 2 * τ) τ := by
    intro τ
    have := (hasDerivAt_pow 2 τ).const_mul (β / 2 * ‖v‖ ^ 2)
    convert this using 1 <;> first | rfl | (norm_num; ring) | norm_num | ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1) (f := f)
    (f' := f') (fun τ _ => (hderiv τ).continuousAt.continuousWithinAt)
    (fun τ _ => (hderiv τ).hasDerivWithinAt) (B := fun τ => β / 2 * ‖v‖ ^ 2 * τ ^ 2)
    (B' := fun τ => β * ‖v‖ ^ 2 * τ) (by simp [hfdef]) hB
    (by
      intro τ hτ
      have hτ0 : 0 ≤ τ := hτ.1
      calc ‖f' τ‖ = ‖(fderiv ℝ c (x + τ • v) - fderiv ℝ c x) v‖ := rfl
        _ ≤ ‖fderiv ℝ c (x + τ • v) - fderiv ℝ c x‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (β * ‖x + τ • v - x‖) * ‖v‖ := by gcongr; exact hcβ _ _
        _ = β * ‖v‖ ^ 2 * τ := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ0]; ring)
    (x := 1) ⟨zero_le_one, le_rfl⟩
  simp only [hfdef, one_smul, one_pow, mul_one] at key
  rw [hv, add_sub_cancel] at key
  exact key

lemma cvx_norm_sub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) :
    ConvexOn ℝ Set.univ (fun y : V => ‖y - a‖) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ α β hα hβ hαβ
  have e : α • x + β • y - a = α • (x - a) + β • (y - a) := by
    have ha' : a = α • a + β • a := by rw [← add_smul, hαβ, one_smul]
    conv_lhs => rw [ha']
    simp only [smul_sub]; abel
  simp only [smul_eq_mul]
  rw [e]
  calc ‖α • (x - a) + β • (y - a)‖ ≤ ‖α • (x - a)‖ + ‖β • (y - a)‖ := norm_add_le _ _
    _ = α * ‖x - a‖ + β * ‖y - a‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hα, Real.norm_of_nonneg hβ]

lemma cvx_sq_sub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) :
    ConvexOn ℝ Set.univ (fun y : V => ‖y - a‖ ^ 2) :=
  (cvx_norm_sub a).pow (fun _ _ => norm_nonneg _) 2


lemma ereal_shift (e1 e2 : EReal) (a1 a2 b1 b2 : ℝ)
    (h : e1 + (a1 : EReal) ≤ e2 + (a2 : EReal)) (hb : b1 - a1 ≤ b2 - a2) :
    e1 + (b1 : EReal) ≤ e2 + (b2 : EReal) := by
  calc e1 + (b1 : EReal) = (e1 + (a1 : EReal)) + ((b1 - a1 : ℝ) : EReal) := by
        rw [add_assoc, ← EReal.coe_add]; congr 2; ring
    _ ≤ (e2 + (a2 : EReal)) + ((b1 - a1 : ℝ) : EReal) := by gcongr
    _ ≤ (e2 + (a2 : EReal)) + ((b2 - a2 : ℝ) : EReal) := by
        gcongr
    _ = e2 + (b2 : EReal) := by rw [add_assoc, ← EReal.coe_add]; congr 2; ring

lemma cvx_q {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (k : ℝ) (hk : 0 ≤ k) :
    ConvexOn ℝ Set.univ (fun y : V => k * ‖y - a‖ ^ 2) := by
  simpa [smul_eq_mul] using (cvx_sq_sub a).smul hk

lemma cvx_n {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (k : ℝ) (hk : 0 ≤ k) :
    ConvexOn ℝ Set.univ (fun y : V => k * ‖y - a‖) := by
  simpa [smul_eq_mul] using (cvx_norm_sub a).smul hk

lemma qbound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u xh x p : E) (a c1 e : ℝ) (ha : 0 ≤ a) (hc1 : 0 ≤ c1) (he : 0 ≤ e)
    (hs : ∀ y, (a * ‖xh - xh‖ ^ 2 + c1 * ‖xh - x‖ ^ 2 + e * ‖xh - p‖) - ⟪u, y - xh⟫_ℝ ≤
      a * ‖y - xh‖ ^ 2 + c1 * ‖y - x‖ ^ 2 + e * ‖y - p‖) :
    ‖u‖ ≤ 2 * c1 * ‖xh - x‖ + e := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N, hNdef⟩ : ∃ N, N = ‖u‖ := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = ‖xh - x‖ := ⟨_, rfl⟩
  have hN : 0 ≤ N := hNdef ▸ norm_nonneg _
  have hD : 0 ≤ D := hDdef ▸ norm_nonneg _
  have hden : 0 < N * (a + c1) + 1 := by nlinarith
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = ε / (N * (a + c1) + 1) := ⟨_, rfl⟩
  have hτpos : 0 < τ := hτ ▸ div_pos hε hden
  have hτN : τ * (N * (a + c1)) ≤ ε := by
    rw [hτ, div_mul_eq_mul_div, div_le_iff₀ hden]; nlinarith
  have hy := hs (xh - τ • u)
  have e1 : xh - τ • u - xh = -(τ • u) := by abel
  have i1 : ⟪u, -(τ • u)⟫_ℝ = -(τ * N ^ 2) := by
    rw [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq, hNdef]
  have i2 : ‖-(τ • u)‖ = τ * N := by rw [norm_neg, norm_smul, Real.norm_of_nonneg hτpos.le, hNdef]
  have i3 : ‖xh - xh‖ = 0 := by simp
  have e2 : ‖xh - τ • u - x‖ ≤ D + τ * N := by
    calc ‖xh - τ • u - x‖ = ‖(xh - x) - τ • u‖ := by congr 1; abel
      _ ≤ ‖xh - x‖ + ‖τ • u‖ := norm_sub_le _ _
      _ = D + τ * N := by rw [norm_smul, Real.norm_of_nonneg hτpos.le, hNdef, hDdef]
  have e3 : ‖xh - τ • u - p‖ ≤ ‖xh - p‖ + τ * N := by
    calc ‖xh - τ • u - p‖ = ‖(xh - p) - τ • u‖ := by congr 1; abel
      _ ≤ ‖xh - p‖ + ‖τ • u‖ := norm_sub_le _ _
      _ = ‖xh - p‖ + τ * N := by rw [norm_smul, Real.norm_of_nonneg hτpos.le, hNdef]
  rw [e1, i1, i2, i3] at hy
  rw [← hDdef] at hy
  have e2' : ‖xh - τ • u - x‖ ^ 2 ≤ (D + τ * N) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) e2 2
  have k2 := mul_le_mul_of_nonneg_left e2' hc1
  have k3 := mul_le_mul_of_nonneg_left e3 he
  have key : τ * N ^ 2 ≤ τ * (N * (2 * c1 * D + e) + τ * N ^ 2 * (a + c1)) := by
    nlinarith
  have key2 : N ^ 2 ≤ N * (2 * c1 * D + e) + τ * N ^ 2 * (a + c1) :=
    le_of_mul_le_mul_left key hτpos
  rw [← hNdef, ← hDdef]
  rcases eq_or_lt_of_le hN with h0 | hpos
  · rw [← h0]; nlinarith
  · have key3 : N * N ≤ N * (2 * c1 * D + e + τ * N * (a + c1)) := by nlinarith
    have := le_of_mul_le_mul_left key3 hpos
    nlinarith

lemma exists_global_min {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [ProperSpace V] (F : V → EReal) (hF : LowerSemicontinuous F) (a : V) (R : ℝ) (hR : 0 ≤ R)
    (hout : ∀ y, R < ‖y - a‖ → F a ≤ F y) : ∃ p, ‖p - a‖ ≤ R ∧ ∀ y, F p ≤ F y := by
  obtain ⟨p, hp, hmin⟩ := (hF.lowerSemicontinuousOn (Metric.closedBall a R)).exists_isMinOn
    ⟨a, Metric.mem_closedBall_self hR⟩ (isCompact_closedBall a R)
  rw [isMinOn_iff] at hmin
  refine ⟨p, by simpa [dist_eq_norm] using hp, fun y => ?_⟩
  by_cases hy : y ∈ Metric.closedBall a R
  · exact hmin y hy
  · have : R < ‖y - a‖ := by simpa [dist_eq_norm] using hy
    exact (hmin a (Metric.mem_closedBall_self hR)).trans (hout y this)

lemma lsc_aux {V : Type*} [TopologicalSpace V] (g : V → EReal) (hgc : LowerSemicontinuous g)
    (f : V → ℝ) (hf : Continuous f) :
    LowerSemicontinuous (fun y => g y + ((f y : ℝ) : EReal)) :=
  LowerSemicontinuous.add' hgc (continuous_coe_real_ereal.comp hf).lowerSemicontinuous
    (fun _ => EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _)))

section Spec
open ErrBoundQG.ProxLin

variable {n m : ℕ}

lemma phiT_eq (g : En n → EReal) (h : En m → ℝ) (c : En n → En m) (t : ℝ) (x y : En n) :
    phiT g h c t x y =
      g y + ((h (c x + fderiv ℝ c x (y - x)) + ‖x - y‖ ^ 2 / (2 * t) : ℝ) : EReal) := by
  simp only [phiT, phiLin, EReal.coe_add, add_assoc]

lemma hsub_real {h : En m → ℝ} {b w : En m}
    (hw : w ∈ ProxAlg.FixedPoint.subdifferential (fun y : En m => ((h y : ℝ) : EReal)) b) :
    ∀ u, h b + ⟪w, u - b⟫_ℝ ≤ h u := by
  intro u
  have h2 : ((h b : ℝ) : EReal) + ((⟪w, u - b⟫_ℝ : ℝ) : EReal) ≤ ((h u : ℝ) : EReal) := hw.2 u
  exact_mod_cast h2

lemma mem_hsub {h : En m → ℝ} {b w : En m} (hw : ∀ u, h b + ⟪w, u - b⟫_ℝ ≤ h u) :
    w ∈ ProxAlg.FixedPoint.subdifferential (fun y : En m => ((h y : ℝ) : EReal)) b := by
  refine ⟨EReal.coe_lt_top _, fun u => ?_⟩
  show ((h b : ℝ) : EReal) + ((⟪w, u - b⟫_ℝ : ℝ) : EReal) ≤ ((h u : ℝ) : EReal)
  exact_mod_cast hw u

lemma stat_fix (g : En n → EReal) (h : En m → ℝ) (c : En n → En m) (t : ℝ)
    (x : En n) (hx : IsStationary g h c x) (ht : 0 < t) : (0 : En n) ∈ proxGradMap g h c t x := by
  obtain ⟨z, hz, w, hw, hu⟩ := hx
  have hw' := hsub_real hw
  refine ⟨x, ?_, by simp⟩
  intro y
  rw [phiT_eq, phiT_eq]
  have e : c x + fderiv ℝ c x (x - x) = c x := by simp
  rw [e]
  refine ereal_step (g x) (g y) (⟪z, y - x⟫_ℝ) _ _ (hz.2 y) ?_
  have h1 := hw' (c x + fderiv ℝ c x (y - x))
  rw [add_sub_cancel_left, ← ContinuousLinearMap.adjoint_inner_left] at h1
  have h2 : ⟪z, y - x⟫_ℝ + ⟪ContinuousLinearMap.adjoint (fderiv ℝ c x) w, y - x⟫_ℝ = 0 := by
    rw [← inner_add_left, ← hu, inner_zero_left]
  have h3 : 0 ≤ ‖x - y‖ ^ 2 / (2 * t) := div_nonneg (sq_nonneg _) (by linarith)
  have h4 : ‖x - x‖ ^ 2 / (2 * t) = 0 := by simp
  rw [h4]
  linarith

lemma quad_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p s : E) (k : ℝ) (hk : 0 ≤ k)
    (hs : ∀ y, k * ‖p - p‖ ^ 2 - ⟪s, y - p⟫_ℝ ≤ k * ‖y - p‖ ^ 2) : s = 0 := by
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = 1 / (2 * (k + 1)) := ⟨_, rfl⟩
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have hkτ : k * τ < 1 := by
    rw [hτ, mul_one_div, div_lt_one (by positivity)]; linarith
  have hy := hs (p - τ • s)
  have e1 : p - τ • s - p = -(τ • s) := by abel
  rw [e1, sub_self, norm_zero, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_of_nonneg hτpos.le] at hy
  have h1 : τ * ‖s‖ ^ 2 * (1 - k * τ) ≤ 0 := by nlinarith
  have h2 : ‖s‖ ^ 2 ≤ 0 := by
    by_contra hc
    push_neg at hc
    have : 0 < τ * ‖s‖ ^ 2 * (1 - k * τ) := by
      apply mul_pos (mul_pos hτpos hc); linarith
    linarith
  have : ‖s‖ = 0 := by nlinarith [norm_nonneg s]
  exact norm_eq_zero.mp this

lemma fix_stat (g : En n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (h : En m → ℝ) (hh : ConvexOn ℝ Set.univ h) (hhc : Continuous h)
    (c : En n → En m) (t : ℝ) (ht : 0 < t) (x : En n)
    (hx : (0 : En n) ∈ proxGradMap g h c t x) : IsStationary g h c x := by
  obtain ⟨p, hp, h0⟩ := hx
  have hpx : p = x := by
    have h1 : t⁻¹ • (x - p) = 0 := h0.symm
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (inv_ne_zero ht.ne')
    · exact (sub_eq_zero.mp h2).symm
  subst hpx
  obtain ⟨y0, hy0⟩ := hg.2.1
  have sq : ∀ y : En n, ‖p - y‖ ^ 2 / (2 * t) = (2 * t)⁻¹ * ‖y - p‖ ^ 2 := by
    intro y; rw [norm_sub_rev]; ring
  have e : c p + fderiv ℝ c p (p - p) = c p := by simp
  have hmin : ∀ y, g p + ((h (c p) + (2 * t)⁻¹ * ‖p - p‖ ^ 2 : ℝ) : EReal) ≤
      g y + ((h (c p + fderiv ℝ c p (y - p)) + (2 * t)⁻¹ * ‖y - p‖ ^ 2 : ℝ) : EReal) := by
    intro y
    have hy := hp y
    rw [phiT_eq, phiT_eq, sq, sq, e] at hy
    exact hy
  have hgp : g p ≠ ⊤ := ne_top_of_le _ _ _ _ (hmin y0) hy0
  have hk : (0 : ℝ) ≤ (2 * t)⁻¹ := by positivity
  obtain ⟨z, w, hz, hw, hs⟩ := opt g hg.1 hg.2.2 h hh hhc (fderiv ℝ c p) (c p)
    (fun y => (2 * t)⁻¹ * ‖y - p‖ ^ 2) (cvx_q p _ hk) (by fun_prop) p hgp hmin
  have h0' := quad_zero p _ _ hk hs
  exact ⟨z, ⟨lt_top_iff_ne_top.mpr hgp, hz⟩, w, mem_hsub hw, h0'.symm⟩

lemma part1 (g : En n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g) (h : En m → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (hhc : Continuous h) (c : En n → En m) (xbar : En n) (hxbar : IsStationary g h c xbar)
    (t : ℝ) (ht : 0 < t) (lhat : ℝ)
    (H : IsSubregularAt (proxGradMap g h c t) xbar 0 lhat) :
    IsSubregularAt (subdiffPhi g h c) xbar 0 (2 * lhat) := by
  obtain ⟨h0, hl, X, hX, hXb⟩ := H
  refine ⟨hxbar, by linarith, X, hX, ?_⟩
  intro x hx v hv
  obtain ⟨z, hz, w, hw, hveq⟩ := hv
  have hw' := hsub_real hw
  have hlow : ∀ y, g x + ((h (c x) + ⟪v, y - x⟫_ℝ + ‖x - y‖ ^ 2 / (2 * t) : ℝ) : EReal) ≤
      phiT g h c t x y := by
    intro y
    rw [phiT_eq]
    refine ereal_step (g x) (g y) (⟪z, y - x⟫_ℝ) _ _ (hz.2 y) ?_
    have h1 := hw' (c x + fderiv ℝ c x (y - x))
    rw [add_sub_cancel_left, ← ContinuousLinearMap.adjoint_inner_left] at h1
    rw [hveq, inner_add_left]
    linarith
  have hFx : phiT g h c t x x = g x + ((h (c x) : ℝ) : EReal) := by
    rw [phiT_eq]; simp
  have hlsc : LowerSemicontinuous (phiT g h c t x) := by
    have e : phiT g h c t x = fun y =>
        g y + ((h (c x + fderiv ℝ c x (y - x)) + ‖x - y‖ ^ 2 / (2 * t) : ℝ) : EReal) := by
      funext y; exact phiT_eq g h c t x y
    rw [e]
    exact lsc_aux g hgc _ (by fun_prop)
  have hR : 0 ≤ 2 * t * ‖v‖ := mul_nonneg (by linarith) (norm_nonneg _)
  obtain ⟨p, -, hpmin⟩ := exists_global_min (phiT g h c t x) hlsc x (2 * t * ‖v‖) hR (by
    intro y hy
    rw [hFx]
    refine le_trans ?_ (hlow y)
    refine add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_)
    have hi : -(‖v‖ * ‖y - x‖) ≤ ⟪v, y - x⟫_ℝ := neg_le_of_abs_le (abs_real_inner_le_norm v (y - x))
    have hn : ‖x - y‖ = ‖y - x‖ := norm_sub_rev _ _
    have h2 : ‖v‖ * ‖y - x‖ ≤ ‖y - x‖ ^ 2 / (2 * t) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith [norm_nonneg (y - x), norm_nonneg v]
    rw [hn]; linarith)
  have hG : t⁻¹ • (x - p) ∈ proxGradMap g h c t x := ⟨p, fun y => hpmin y, rfl⟩
  have hd : ‖x - p‖ ≤ 2 * t * ‖v‖ := by
    have h1 := (hlow p).trans (hpmin x)
    rw [hFx] at h1
    have h2 := ereal_cancel (g x) (ne_of_lt hz.1) (hg.1 x) _ _ h1
    have hi : -(‖v‖ * ‖p - x‖) ≤ ⟪v, p - x⟫_ℝ :=
      neg_le_of_abs_le (abs_real_inner_le_norm v (p - x))
    have hn : ‖p - x‖ = ‖x - p‖ := norm_sub_rev _ _
    rw [hn] at hi
    have h3 : ‖x - p‖ ^ 2 / (2 * t) ≤ ‖v‖ * ‖x - p‖ := by linarith
    have h4 : ‖x - p‖ ^ 2 ≤ ‖v‖ * ‖x - p‖ * (2 * t) := (div_le_iff₀ (by linarith)).mp h3
    nlinarith [norm_nonneg (x - p), norm_nonneg v]
  have hsub := hXb x hx _ hG
  have hFS : {z : En n | (0 : En n) ∈ proxGradMap g h c t z} ⊆
      {z : En n | (0 : En n) ∈ subdiffPhi g h c z} :=
    fun z hz => fix_stat g hg h hh hhc c t ht z hz
  have hle := Metric.infDist_le_infDist_of_subset (x := x) hFS ⟨xbar, h0⟩
  have hnG : ‖(0 : En n) - t⁻¹ • (x - p)‖ ≤ 2 * ‖v‖ := by
    rw [zero_sub, norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le),
      inv_mul_le_iff₀ ht]
    nlinarith
  rw [zero_sub, norm_neg]
  calc Metric.infDist x {z : En n | (0 : En n) ∈ subdiffPhi g h c z}
      ≤ lhat * ‖(0 : En n) - t⁻¹ • (x - p)‖ := hle.trans hsub
    _ ≤ lhat * (2 * ‖v‖) := mul_le_mul_of_nonneg_left hnG hl.le
    _ = 2 * lhat * ‖v‖ := by ring

lemma part2 (g : En n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g) (h : En m → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (hhc : Continuous h) (c : En n → En m) (hc : ContDiff ℝ 1 c) (L β : ℝ) (hL : 0 ≤ L)
    (hβ : 0 ≤ β) (hhL : ∀ a b, |h a - h b| ≤ L * ‖a - b‖)
    (hcβ : ∀ x y, ‖fderiv ℝ c x - fderiv ℝ c y‖ ≤ β * ‖x - y‖)
    (xbar : En n) (hxbar : IsStationary g h c xbar) (t : ℝ) (ht : 0 < t) (l : ℝ)
    (H : IsSubregularAt (subdiffPhi g h c) xbar 0 l) :
    IsSubregularAt (proxGradMap g h c t) xbar 0 ((3 * L * β * t + 2) * l + 2 * t) := by
  obtain ⟨-, hl, X, hX, hXb⟩ := H
  obtain ⟨r, hr, hrX⟩ := Metric.mem_nhds_iff.mp hX
  have hLβt : 0 ≤ L * β * t := mul_nonneg (mul_nonneg hL hβ) ht.le
  refine ⟨stat_fix g h c t xbar hxbar ht, by nlinarith, Metric.ball xbar (r / 3),
    Metric.ball_mem_nhds _ (by linarith), ?_⟩
  intro x hx v hv
  obtain ⟨p, hp, hveq⟩ := hv
  have hcc : Continuous c := hc.continuous
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = L * β := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := hκ ▸ mul_nonneg hL hβ
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = ‖x - p‖ := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := hd ▸ norm_nonneg _
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℝ, c1 = 1 / (2 * t) + κ / 2 := ⟨_, rfl⟩
  have hc10 : 0 ≤ c1 := by
    rw [hc1]; have : 0 ≤ 1 / (2 * t) := div_nonneg zero_le_one (by linarith)
    linarith
  have htay : ∀ y0 y, |h (c y) - h (c y0 + fderiv ℝ c y0 (y - y0))| ≤ κ / 2 * ‖y - y0‖ ^ 2 := by
    intro y0 y
    have h1 := hhL (c y) (c y0 + fderiv ℝ c y0 (y - y0))
    have h2 := taylor c hc β hcβ y0 y
    have e : c y - (c y0 + fderiv ℝ c y0 (y - y0)) = c y - c y0 - fderiv ℝ c y0 (y - y0) := by
      abel
    rw [e] at h1
    calc _ ≤ L * ‖c y - c y0 - fderiv ℝ c y0 (y - y0)‖ := h1
      _ ≤ L * (β / 2 * ‖y - y0‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hL
      _ = κ / 2 * ‖y - y0‖ ^ 2 := by rw [hκ]; ring
  obtain ⟨y0, hy0⟩ := hg.2.1
  have hgp : g p ≠ ⊤ := by
    have h1 := hp y0
    rw [phiT_eq, phiT_eq] at h1
    exact ne_top_of_le _ _ _ _ h1 hy0
  obtain ⟨ψ, hψ⟩ : ∃ ψ : En n → EReal, ψ = fun y =>
      g y + ((h (c y) + c1 * ‖y - x‖ ^ 2 + κ * d * ‖y - p‖ : ℝ) : EReal) := ⟨_, rfl⟩
  have hψlsc : LowerSemicontinuous ψ := by
    rw [hψ]; exact lsc_aux g hgc _ (by fun_prop)
  have hout : ∀ y, d < ‖y - p‖ → ψ p ≤ ψ y := by
    intro y hy
    have h1 := hp y
    rw [phiT_eq, phiT_eq] at h1
    simp only [hψ]
    refine ereal_shift _ _ _ _ _ _ h1 ?_
    have t1 := htay x p
    have t2 := htay x y
    rw [abs_le] at t1 t2
    rw [norm_sub_rev p x, ← hd] at t1
    rw [norm_sub_rev p x, ← hd, norm_sub_rev x y, sub_self, norm_zero]
    have k1 := mul_le_mul_of_nonneg_left hy.le (mul_nonneg hκ0 hd0)
    have k2 : 0 ≤ κ / 2 * ‖y - x‖ ^ 2 := by positivity
    rw [hc1]
    have e1 : (1 / (2 * t) + κ / 2) * d ^ 2 - d ^ 2 / (2 * t) = κ / 2 * d ^ 2 := by
      field_simp; ring
    have e2 : (1 / (2 * t) + κ / 2) * ‖y - x‖ ^ 2 - ‖y - x‖ ^ 2 / (2 * t) =
        κ / 2 * ‖y - x‖ ^ 2 := by
      field_simp; ring
    nlinarith
  obtain ⟨xh, hxhB, hxhmin⟩ := exists_global_min ψ hψlsc p d hd0 hout
  have hxhmin' : ∀ y, g xh + ((h (c xh) + c1 * ‖xh - x‖ ^ 2 + κ * d * ‖xh - p‖ : ℝ) : EReal) ≤
      g y + ((h (c y) + c1 * ‖y - x‖ ^ 2 + κ * d * ‖y - p‖ : ℝ) : EReal) := by
    intro y; have := hxhmin y; simp only [hψ] at this; exact this
  have hgxh : g xh ≠ ⊤ := ne_top_of_le _ _ _ _ (hxhmin' p) hgp
  have hq : ConvexOn ℝ Set.univ
      (fun y : En n => κ / 2 * ‖y - xh‖ ^ 2 + c1 * ‖y - x‖ ^ 2 + κ * d * ‖y - p‖) :=
    ((cvx_q xh (κ / 2) (by linarith)).add (cvx_q x c1 hc10)).add
      (cvx_n p (κ * d) (mul_nonneg hκ0 hd0))
  have hmin : ∀ y, g xh + ((h (c xh) + (κ / 2 * ‖xh - xh‖ ^ 2 + c1 * ‖xh - x‖ ^ 2 +
        κ * d * ‖xh - p‖) : ℝ) : EReal) ≤
      g y + ((h (c xh + fderiv ℝ c xh (y - xh)) + (κ / 2 * ‖y - xh‖ ^ 2 + c1 * ‖y - x‖ ^ 2 +
        κ * d * ‖y - p‖) : ℝ) : EReal) := by
    intro y
    refine ereal_shift _ _ _ _ _ _ (hxhmin' y) ?_
    have t2 := htay xh y
    rw [abs_le] at t2
    rw [sub_self, norm_zero]
    nlinarith
  obtain ⟨z, w, hz, hw, hs⟩ := opt g hg.1 hg.2.2 h hh hhc (fderiv ℝ c xh) (c xh)
    (fun y => κ / 2 * ‖y - xh‖ ^ 2 + c1 * ‖y - x‖ ^ 2 + κ * d * ‖y - p‖) hq (by fun_prop)
    xh hgxh hmin
  set u := z + ContinuousLinearMap.adjoint (fderiv ℝ c xh) w with hu
  have hub : ‖u‖ ≤ 2 * c1 * ‖xh - x‖ + κ * d :=
    qbound u xh x p (κ / 2) c1 (κ * d) (by linarith) hc10 (mul_nonneg hκ0 hd0) hs
  have huS : u ∈ subdiffPhi g h c xh :=
    ⟨z, ⟨lt_top_iff_ne_top.mpr hgxh, hz⟩, w, mem_hsub hw, rfl⟩
  have hxp : ‖xh - p‖ ≤ d := hxhB
  have hxx : ‖x - xh‖ ≤ 2 * d := by
    have := norm_sub_le_norm_sub_add_norm_sub x p xh
    rw [norm_sub_rev p xh, ← hd] at this; linarith
  have hSF : {z : En n | (0 : En n) ∈ subdiffPhi g h c z} ⊆
      {z : En n | (0 : En n) ∈ proxGradMap g h c t z} :=
    fun z hz => stat_fix g h c t z hz ht
  have hle := Metric.infDist_le_infDist_of_subset (x := x) hSF ⟨xbar, hxbar⟩
  have hn : ‖(0 : En n) - v‖ = t⁻¹ * d := by
    rw [hveq, zero_sub, norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le), hd]
  have hK : ((3 * L * β * t + 2) * l + 2 * t) * (t⁻¹ * d) =
      2 * d + l * (3 * κ * d + 2 * t⁻¹ * d) := by
    rw [hκ]; field_simp; ring
  rw [hn, hK]
  have hpos : 0 ≤ l * (3 * κ * d + 2 * t⁻¹ * d) := by
    apply mul_nonneg hl.le
    have : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
    positivity
  have hxb : dist x xbar < r / 3 := hx
  by_cases hcase : dist xh xbar < r
  · have hxhX : xh ∈ X := hrX hcase
    have h1 := hXb xh hxhX u huS
    rw [zero_sub, norm_neg] at h1
    have h2 := Metric.infDist_le_infDist_add_dist (x := x) (y := xh)
      (s := {z : En n | (0 : En n) ∈ subdiffPhi g h c z})
    rw [dist_eq_norm] at h2
    have h3 : ‖xh - x‖ ≤ 2 * d := by rw [norm_sub_rev]; exact hxx
    have h4 : l * ‖u‖ ≤ l * (3 * κ * d + 2 * t⁻¹ * d) := by
      apply mul_le_mul_of_nonneg_left _ hl.le
      have e : 2 * c1 = t⁻¹ + κ := by rw [hc1]; field_simp; try ring
      have hm : 2 * c1 * ‖xh - x‖ ≤ 2 * c1 * (2 * d) := mul_le_mul_of_nonneg_left h3 (by linarith)
      have : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
      rw [e] at hm hub
      nlinarith
    linarith
  · push_neg at hcase
    have h1 := Metric.infDist_le_dist_of_mem (x := x)
      (s := {z : En n | (0 : En n) ∈ subdiffPhi g h c z}) hxbar
    have h2 : dist xh xbar ≤ dist xh x + dist x xbar := dist_triangle _ _ _
    rw [dist_eq_norm xh x, norm_sub_rev] at h2
    linarith

end Spec

end P6e20

open ErrBoundQG.ProxLin in
theorem solution {n m : ℕ}
    (g : En n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g)
    (h : En m → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (c : En n → En m) (hc : ContDiff ℝ 1 c)
    (L β : ℝ) (hL : 0 ≤ L) (hβ : 0 ≤ β)
    (hhL : ∀ a b, |h a - h b| ≤ L * ‖a - b‖)
    (hcβ : ∀ x y, ‖fderiv ℝ c x - fderiv ℝ c y‖ ≤ β * ‖x - y‖)
    (xbar : En n) (hxbar : IsStationary g h c xbar)
    (t : ℝ) (ht : 0 < t) :
    (∀ lhat : ℝ,
      IsSubregularAt (proxGradMap g h c t) xbar 0 lhat →
      IsSubregularAt (subdiffPhi g h c) xbar 0 (2 * lhat)) ∧
    (∀ l : ℝ,
      IsSubregularAt (subdiffPhi g h c) xbar 0 l →
      IsSubregularAt (proxGradMap g h c t) xbar 0
        ((3 * L * β * t + 2) * l + 2 * t)) := by
  have hhc : Continuous h :=
    (LipschitzWith.of_dist_le_mul (K := ⟨L, hL⟩) fun a b => by
      rw [Real.dist_eq, dist_eq_norm]; exact hhL a b).continuous
  exact ⟨fun lhat H => P6e20.part1 g hg hgc h hh hhc c xbar hxbar t ht lhat H,
    fun l H => P6e20.part2 g hg hgc h hh hhc c hc L β hL hβ hhL hcβ xbar hxbar t ht l H⟩
