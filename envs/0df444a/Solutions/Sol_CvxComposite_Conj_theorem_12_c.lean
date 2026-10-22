-- Prove2me | solution 1 for CvxComposite.Conj.theorem_12_c
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T16:50:33.9301+00:00
-- url     : https://prove2.me/submissions/7a209c4d-c6dd-4a1d-8ab7-1a889863a47b

import Mathlib
import Definitions.Def_CvxComposite_Conj_Setting
open scoped InnerProductSpace Pointwise
open CvxComposite.Conj MoreauProx.Characterization MoreauProx.Decomposition

theorem coreSep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (S : Set (E × ℝ)) (hS : Convex ℝ S)
    (hup : ∀ u r r', (u, r) ∈ S → r ≤ r' → (u, r') ∈ S)
    (a : ℝ) (ha : ∀ r, ((0 : E), r) ∈ S → a ≤ r) (h0 : ∃ r, ((0 : E), r) ∈ S)
    (hcore : ∀ u r, (u, r) ∈ S → ∃ ε > (0 : ℝ), ∃ r', (-(ε • u), r') ∈ S) :
    ∃ w : E, ∀ u r, (u, r) ∈ S → a + ⟪w, u⟫_ℝ ≤ r := by
  classical
  obtain ⟨r0, hr0⟩ := h0
  set U : Set E := Prod.fst '' S with hU
  set L : Submodule ℝ E := Submodule.span ℝ U with hL
  obtain ⟨M, hLM⟩ := Submodule.exists_isCompl L
  set T : Set (E × ℝ) := S + (LinearMap.inl ℝ E ℝ) '' (M : Set E) with hT
  have hTc : Convex ℝ T := hS.add ((M.convex).linear_image _)
  have hST : S ⊆ T := by
    intro s hs
    exact ⟨s, hs, (0, 0), ⟨0, M.zero_mem, rfl⟩, by simp⟩
  have hMT : ∀ (m : E), m ∈ M → ∀ u r, (u, r) ∈ S → (u + m, r) ∈ T := by
    intro m hm u r hur
    exact ⟨(u, r), hur, (m, 0), ⟨m, hm, rfl⟩, by simp⟩
  -- interior nonempty
  have hspan : affineSpan ℝ T = ⊤ := by
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ (E × ℝ) (E × ℝ)
      ⟨_, hST hr0⟩]
    set V := vectorSpan ℝ T
    have h01 : ((0 : E), (1 : ℝ)) ∈ V := by
      have := vsub_mem_vectorSpan ℝ (hST (hup 0 r0 (r0 + 1) hr0 (by linarith))) (hST hr0)
      simpa using this
    have hinl : ∀ e : E, e ∈ L → ((e, (0 : ℝ)) ∈ V) := by
      intro e he
      have : L ≤ V.comap (LinearMap.inl ℝ E ℝ) := by
        rw [hL, Submodule.span_le]
        rintro u ⟨⟨u', r⟩, hur, rfl⟩
        show ((u', (0:ℝ)) ∈ V)
        have h1 := vsub_mem_vectorSpan ℝ (hST hur) (hST hr0)
        have h2 := V.smul_mem (r - r0) h01
        have := V.sub_mem h1 h2
        convert this using 1
        simp
      exact this he
    have hinM : ∀ e : E, e ∈ M → ((e, (0 : ℝ)) ∈ V) := by
      intro e he
      have := vsub_mem_vectorSpan ℝ (hMT e he 0 r0 hr0) (hST hr0)
      simpa using this
    rw [eq_top_iff]
    rintro ⟨e, r⟩ -
    have he : e ∈ L ⊔ M := by rw [hLM.sup_eq_top]; trivial
    obtain ⟨l, hl, m, hm, rfl⟩ := Submodule.mem_sup.mp he
    have := V.add_mem (V.add_mem (hinl l hl) (hinM m hm)) (V.smul_mem r h01)
    convert this using 1
    simp
  have hint : (interior T).Nonempty := (hTc.interior_nonempty_iff_affineSpan_eq_top).mpr hspan
  -- (0,a) not in interior
  have hnot : ((0 : E), a) ∉ interior T := by
    intro hin
    have hn : interior T ∈ nhds ((0 : E), a) := isOpen_interior.mem_nhds hin
    have hc : Continuous (fun t : ℝ => ((0 : E), a - t)) := by fun_prop
    have := hc.tendsto 0
    simp only [sub_zero] at this
    have hev := Filter.mem_map.mp (this hn)
    rw [Metric.mem_nhds_iff] at hev
    obtain ⟨δ, hδ, hball⟩ := hev
    have hmem : (δ / 2) ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith
    have hT' := interior_subset (hball hmem)
    obtain ⟨⟨s1, s2⟩, hs, q, ⟨m, hm, rfl⟩, hsum⟩ := hT'
    simp only [LinearMap.inl_apply, Prod.mk_add_mk, add_zero, Prod.mk.injEq] at hsum
    obtain ⟨h1, h2⟩ := hsum
    have hs1 : s1 = -m := by rw [eq_neg_iff_add_eq_zero]; exact h1
    have hsL : s1 ∈ L := Submodule.subset_span ⟨_, hs, rfl⟩
    have hmL : m ∈ L := by
      have := L.neg_mem hsL; rw [hs1, neg_neg] at this; exact this
    have hm0 : m = 0 := by
      have := hLM.inf_eq_bot
      have hmm : m ∈ L ⊓ M := ⟨hmL, hm⟩
      rw [this] at hmm; exact hmm
    subst hm0
    simp only [neg_zero] at hs1
    subst hs1
    have := ha _ hs
    linarith
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point (hTc.interior) isOpen_interior hnot
  have hfT : ∀ t ∈ T, f t ≤ f ((0 : E), a) := by
    intro t ht
    have : t ∈ closure (interior T) := by
      rw [hTc.closure_interior_eq_closure_of_nonempty_interior hint]; exact subset_closure ht
    have hcl : closure (interior T) ⊆ {q | f q ≤ f ((0 : E), a)} :=
      closure_minimal (fun q hq => (hf q hq).le) (isClosed_le f.continuous continuous_const)
    exact hcl this
  set φ : E →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ E ℝ) with hφ
  set c : ℝ := f ((0 : E), 1) with hc
  have hfd : ∀ u r, f (u, r) = φ u + r * c := by
    intro u r
    have : ((u, r) : E × ℝ) = (u, 0) + r • ((0 : E), (1 : ℝ)) := by simp
    rw [this, map_add, map_smul, smul_eq_mul]
    simp [hφ, hc]
  have hfa : f ((0 : E), a) = a * c := by rw [hfd]; simp
  have hineq : ∀ u r, (u, r) ∈ S → φ u + r * c ≤ a * c := by
    intro u r hur; rw [← hfd, ← hfa]; exact hfT _ (hST hur)
  -- c ≤ 0
  have hc0 : c ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have := hineq 0 (r0 + (|a - r0| + 1)) (hup _ _ _ hr0 (by linarith [abs_nonneg (a - r0)]))
    simp at this
    have h1 : a - r0 ≤ |a - r0| := le_abs_self _
    nlinarith
  -- φ vanishes on M
  have hφM : ∀ m ∈ M, φ m = 0 := by
    intro m hm
    have key : ∀ t : ℝ, t * φ m + r0 * c ≤ a * c := by
      intro t
      have hmt : t • m ∈ M := M.smul_mem t hm
      have := hfT _ (hMT _ hmt 0 r0 hr0)
      rw [zero_add, hfd, hfa, map_smul, smul_eq_mul] at this
      exact this
    by_contra hne
    have h1 := key ((r0 * c - a * c + 1) / φ m * (-1))
    have h2 := key ((a * c - r0 * c + 1) / φ m)
    field_simp at h1 h2
    rcases lt_or_gt_of_ne hne with h | h
    · nlinarith
    · nlinarith
  have hcneg : c < 0 := by
    rcases lt_or_eq_of_le hc0 with h | h
    · exact h
    exfalso
    have hφU : ∀ u ∈ U, φ u = 0 := by
      rintro u ⟨⟨u', r⟩, hur, rfl⟩
      have h1 := hineq u' r hur
      rw [h] at h1; simp at h1
      obtain ⟨ε, hε, r', hr'⟩ := hcore u' r hur
      have h2 := hineq _ _ hr'
      rw [h] at h2; simp [map_neg, map_smul] at h2
      have : 0 ≤ φ u' := by
        by_contra hneg; push Not at hneg
        have : 0 < ε * φ u' * (-1) := by nlinarith
        linarith
      linarith
    have hφL : ∀ e ∈ L, φ e = 0 := by
      intro e he
      have : L ≤ LinearMap.ker (φ : E →ₗ[ℝ] ℝ) := by
        rw [hL, Submodule.span_le]; intro u hu; exact hφU u hu
      exact this he
    have hφ0 : ∀ e, φ e = 0 := by
      intro e
      have he : e ∈ L ⊔ M := by rw [hLM.sup_eq_top]; trivial
      obtain ⟨l, hl, m, hm, rfl⟩ := Submodule.mem_sup.mp he
      rw [map_add, hφL l hl, hφM m hm, add_zero]
    obtain ⟨⟨t1, t2⟩, ht⟩ := hint
    have := hf _ ht
    rw [hfd, hfd, hφ0, hφ0, h] at this
    simp at this
  refine ⟨(InnerProductSpace.toDual ℝ E).symm ((-c⁻¹) • φ), ?_⟩
  intro u r hur
  rw [InnerProductSpace.toDual_symm_apply]
  have := hineq u r hur
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hcinv : c⁻¹ < 0 := inv_lt_zero.mpr hcneg
  have : (φ u + r * c) * c⁻¹ ≥ (a * c) * c⁻¹ := mul_le_mul_of_nonpos_right this hcinv.le
  rw [add_mul, mul_assoc, mul_assoc, mul_inv_cancel₀ hcneg.ne, mul_one, mul_one] at this
  linarith

theorem riExt12c {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (s : Set V) (z a : V)
    (hz : z ∈ intrinsicInterior ℝ s) (ha : a ∈ s) :
    ∃ ε > (0 : ℝ), ∀ t : ℝ, 0 ≤ t → t ≤ ε → z + t • (z - a) ∈ s := by
  rw [mem_intrinsicInterior] at hz
  obtain ⟨⟨z', hz'⟩, hint, hzz⟩ := hz
  simp only at hzz
  subst hzz
  have hmem : ∀ t : ℝ, z' + t • (z' - a) ∈ affineSpan ℝ s := by
    intro t
    have := AffineMap.lineMap_mem (Q := affineSpan ℝ s) (1 + t) (subset_affineSpan ℝ s ha) hz'
    rw [AffineMap.lineMap_apply] at this
    convert this using 1
    simp only [vsub_eq_sub, vadd_eq_add]
    module
  let f : ℝ → affineSpan ℝ s := fun t => ⟨z' + t • (z' - a), hmem t⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk; fun_prop
  have hf0 : f 0 = ⟨z', hz'⟩ := by
    apply Subtype.ext; simp [f]
  have hn : interior (Subtype.val ⁻¹' s : Set (affineSpan ℝ s)) ∈ nhds (f 0) := by
    rw [hf0]; exact isOpen_interior.mem_nhds hint
  have := Filter.mem_map.mp (hf.tendsto 0 hn)
  rw [Metric.mem_nhds_iff] at this
  obtain ⟨δ, hδ, hball⟩ := this
  refine ⟨δ / 2, by linarith, fun t ht0 ht1 => ?_⟩
  have htb : t ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht0]; linarith
  have := interior_subset (hball htb)
  exact this

theorem KcoreGeom12c {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
    (K : Set E₂) (hK : IsClosedConvexCone K)
    (D : Set E₁) (F : E₁ → E₂) (hF : IsKConvex K D F) (G : Set E₂) (x0 : E₁)
    (hx0 : x0 ∈ intrinsicInterior ℝ D) (hA : F x0 ∈ intrinsicInterior ℝ (G - K))
    (x : E₁) (hx : x ∈ D) (y : E₂) (hy : y ∈ G) (k : E₂) (hk : k ∈ K) :
    ∃ δ > (0 : ℝ), ∃ x'' ∈ D, ∃ y'' ∈ G, ∃ k'' ∈ K, -(δ • (y - k - F x)) = y'' - k'' - F x'' := by
  obtain ⟨hKne, -, hKconv, hKsmul⟩ := hK
  have h0K : (0 : E₂) ∈ K := by
    obtain ⟨k1, hk1⟩ := hKne
    have := hKsmul k1 hk1 0 le_rfl; simpa using this
  have hKadd : ∀ a ∈ K, ∀ b ∈ K, a + b ∈ K := by
    intro a ha b hb
    have := hKsmul _ (hKconv ha hb (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num)) 2 (by norm_num)
    convert this using 1; module
  have hx0D : x0 ∈ D := intrinsicInterior_subset hx0
  have hepi : ∀ z ∈ D, (z, F z) ∈ KEpi K D F := fun z hz => ⟨hz, by simpa using h0K⟩
  obtain ⟨δ0, hδ0, hx'⟩ := riExt12c D x0 x hx0 hx
  set x' := x0 + δ0 • (x0 - x) with hx'def
  have hx'D : x' ∈ D := hx' δ0 hδ0.le le_rfl
  set i := δ0⁻¹ with hidef
  set j := (1 + δ0)⁻¹ with hjdef
  have hi : δ0 * i = 1 := mul_inv_cancel₀ hδ0.ne'
  have hj : (1 + δ0) * j = 1 := mul_inv_cancel₀ (by linarith)
  have hj0 : 0 ≤ j := by positivity
  have hi0 : 0 ≤ i := by positivity
  -- fact 1
  have hc1 := hF (hepi x' hx'D) (hepi x hx) hj0 (mul_nonneg hδ0.le hj0) (by linear_combination hj)
  have hc1' : j • F x' + (δ0 * j) • F x - F x0 ∈ K := by
    have hxx : j • x' + (δ0 * j) • x = x0 := by
      rw [hx'def]; linear_combination (norm := module) hj • x0
    have := hc1.2
    simp only [Prod.smul_mk, Prod.mk_add_mk] at this
    rw [hxx] at this; exact this
  set k' := (i * (1 + δ0)) • (j • F x' + (δ0 * j) • F x - F x0) + k with hk'def
  have hk' : k' ∈ K := hKadd _ (hKsmul _ hc1' _ (by positivity)) _ hk
  have haA : y - k' ∈ G - K := ⟨y, hy, k', hk', rfl⟩
  obtain ⟨ε', hε', hA'⟩ := riExt12c (G - K) (F x0) (y - k') hA haA
  set δ := min δ0 ε' with hδdef
  have hδpos : 0 < δ := lt_min hδ0 hε'
  have hδle : δ ≤ δ0 := min_le_left _ _
  obtain ⟨y'', hy'', k'', hk'', hyk⟩ := hA' δ hδpos.le (min_le_right _ _)
  set θ := δ * i with hθdef
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : 0 ≤ 1 - θ := by
    have : δ * i ≤ δ0 * i := mul_le_mul_of_nonneg_right hδle hi0
    rw [hi] at this; linarith
  have hb := hF (hepi x' hx'D) (hepi x0 hx0D) hθ0 hθ1 (by ring)
  simp only [Prod.smul_mk, Prod.mk_add_mk] at hb
  obtain ⟨hx''D, hkδ⟩ := hb
  refine ⟨δ, hδpos, _, hx''D, y'', hy'', _, hKadd _ hk'' _ hkδ, ?_⟩
  have hyk' : y'' - k'' = F x0 + δ • (F x0 - (y - k')) := hyk
  have hy''eq : y'' = F x0 + δ • (F x0 - (y - k')) + k'' := by rw [← hyk']; abel
  rw [hy''eq, hk'def]
  simp only at hkδ ⊢
  linear_combination (norm := module) hi • (δ • F x0 - δ • F x) + hj • (-(δ*δ0*i) • F x - (δ*i) • F x')

theorem compD12c {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] (g : E₂ → EReal) (D : Set E₁) (F : E₁ → E₂)
    (x : E₁) (hx : x ∈ D) : comp g D F x = g (F x) := by
  simp [comp, hx]

theorem compND12c {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] (g : E₂ → EReal) (D : Set E₁) (F : E₁ → E₂)
    (x : E₁) (hx : x ∉ D) : comp g D F x = ⊤ := by
  simp [comp, hx]

theorem weak12c {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] (g : E₂ → EReal) (D : Set E₁) (F : E₁ → E₂)
    (hgb : ∀ y, g y ≠ ⊥) (p : E₁) (v : E₂) : conj (comp g D F) p ≤ conj g v + conj (scal v D F) p := by
  unfold conj
  refine iSup_le fun x => ?_
  by_cases hx : x ∈ D
  · rw [compD12c g D F x hx]
    by_cases hgt : g (F x) = ⊤
    · rw [hgt, EReal.sub_top]; exact bot_le
    have hgb := hgb (F x)
    · rw [← EReal.coe_toReal hgt hgb]
      have h1 : ((⟪F x, v⟫_ℝ : ℝ) : EReal) - ((g (F x)).toReal : EReal) ≤ ⨆ y, ((⟪y, v⟫_ℝ : ℝ) : EReal) - g y := by
        have := le_iSup (fun y => ((⟪y, v⟫_ℝ : ℝ) : EReal) - g y) (F x)
        rw [← EReal.coe_toReal hgt hgb] at this; exact this
      have h2 : ((⟪x, p⟫_ℝ : ℝ) : EReal) - ((⟪v, F x⟫_ℝ : ℝ) : EReal) ≤ ⨆ z, ((⟪z, p⟫_ℝ : ℝ) : EReal) - scal v D F z := by
        have := le_iSup (fun z => ((⟪z, p⟫_ℝ : ℝ) : EReal) - scal v D F z) x
        rw [scal, compD12c _ D F x hx] at this; exact this
      refine le_trans ?_ (add_le_add h1 h2)
      rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff,
        real_inner_comm v (F x)]
      linarith
  · rw [compND12c g D F x hx, EReal.sub_top]; exact bot_le

theorem exist12c {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (K : Set E₂) (hK : IsClosedConvexCone K)
    (D : Set E₁) (F : E₁ → E₂) (hF : IsKConvex K D F)
    (g : E₂ → EReal) (hg : IsProperConvex g) (h7 : Cond7 K D F g)
    (x0 : E₁) (hx0 : x0 ∈ intrinsicInterior ℝ D) (hA : F x0 ∈ intrinsicInterior ℝ (effDom g - K))
    (p : E₁) (α : ℝ) (hα : conj (comp g D F) p = α) :
    ∃ v : E₂, -v ∈ polarCone K ∧ conj g v + conj (scal v D F) p ≤ α := by
  obtain ⟨hgbot, -, hgconv⟩ := hg
  have hK' := hK
  obtain ⟨hKne, -, hKconv, hKsmul⟩ := hK'
  have h0K : (0 : E₂) ∈ K := by
    obtain ⟨k1, hk1⟩ := hKne
    have := hKsmul k1 hk1 0 le_rfl; simpa using this
  have hx0D : x0 ∈ D := intrinsicInterior_subset hx0
  have hgFx0 : g (F x0) ≠ ⊤ := by
    obtain ⟨y, hy, k, hk, hyk⟩ := Set.mem_sub.mp (intrinsicInterior_subset hA)
    have : g (F x0) ≤ g y := h7 x0 hx0D y (by rw [← hyk]; simpa using hk)
    exact ne_top_of_le_ne_top hy this
  set c0 := (g (F x0)).toReal with hc0
  have hc0' : g (F x0) = c0 := (EReal.coe_toReal hgFx0 (hgbot _)).symm
  have hconjge : ∀ x ∈ D, ((⟪x, p⟫_ℝ : ℝ) : EReal) - g (F x) ≤ α := by
    intro x hx
    rw [← hα]
    have := le_iSup (fun z => ((⟪z, p⟫_ℝ : ℝ) : EReal) - comp g D F z) x
    rw [compD12c g D F x hx] at this; exact this
  set S : Set (E₂ × ℝ) := {q | ∃ x ∈ D, ∃ y k, k ∈ K ∧ q.1 = y - k - F x ∧
      g y ≤ ((q.2 + ⟪x, p⟫_ℝ : ℝ) : EReal)} with hSdef
  have hS : Convex ℝ S := by
    rintro ⟨u1, r1⟩ ⟨x1, hx1, y1, k1, hk1, hu1, hg1⟩ ⟨u2, r2⟩ ⟨x2, hx2, y2, k2, hk2, hu2, hg2⟩
      θ1 θ2 hθ1 hθ2 hsum
    simp only at hu1 hg1 hu2 hg2
    have hm := hF (show (x1, F x1 + k1) ∈ KEpi K D F from ⟨hx1, by simpa using hk1⟩)
      (show (x2, F x2 + k2) ∈ KEpi K D F from ⟨hx2, by simpa using hk2⟩) hθ1 hθ2 hsum
    simp only [Prod.smul_mk, Prod.mk_add_mk] at hm
    obtain ⟨hxD, hk⟩ := hm
    simp only at hxD hk
    have he := hgconv (show (y1, r1 + ⟪x1, p⟫_ℝ) ∈ {q : E₂ × ℝ | g q.1 ≤ (q.2 : EReal)} from hg1)
      (show (y2, r2 + ⟪x2, p⟫_ℝ) ∈ {q : E₂ × ℝ | g q.1 ≤ (q.2 : EReal)} from hg2) hθ1 hθ2 hsum
    simp only [Prod.smul_mk, Prod.mk_add_mk,  smul_eq_mul] at he
    refine ⟨θ1 • x1 + θ2 • x2, hxD, θ1 • y1 + θ2 • y2, _, hk, ?_, ?_⟩
    · simp only [Prod.smul_mk, Prod.mk_add_mk]
      rw [hu1, hu2]; module
    · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
      have he' : g (θ1 • y1 + θ2 • y2) ≤
          ((θ1 * (r1 + ⟪x1, p⟫_ℝ) + θ2 * (r2 + ⟪x2, p⟫_ℝ) : ℝ) : EReal) := he
      refine he'.trans (le_of_eq ?_)
      congr 1
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]; ring
  have hup : ∀ u r r', (u, r) ∈ S → r ≤ r' → (u, r') ∈ S := by
    rintro u r r' ⟨x, hx, y, k, hk, hu, hgy⟩ hrr
    refine ⟨x, hx, y, k, hk, hu, hgy.trans ?_⟩
    simp only [EReal.coe_le_coe_iff]; linarith
  have ha : ∀ r, ((0 : E₂), r) ∈ S → -α ≤ r := by
    rintro r ⟨x, hx, y, k, hk, hu, hgy⟩
    simp only at hu hgy
    have hyk : y - F x ∈ K := by
      have : y - F x = k := by
        have h' : y - k - F x = 0 := hu.symm
        rw [sub_sub, sub_eq_zero] at h'; rw [h']; abel
      rw [this]; exact hk
    have h1 : g (F x) ≤ ((r + ⟪x, p⟫_ℝ : ℝ) : EReal) := (h7 x hx y hyk).trans hgy
    have h2 := hconjge x hx
    have h3 : ((⟪x, p⟫_ℝ : ℝ) : EReal) - ((r + ⟪x, p⟫_ℝ : ℝ) : EReal) ≤
        ((⟪x, p⟫_ℝ : ℝ) : EReal) - g (F x) := EReal.sub_le_sub le_rfl h1
    rw [← EReal.coe_sub] at h3
    have := (h3.trans h2)
    rw [EReal.coe_le_coe_iff] at this
    linarith
  have h0 : ∃ r, ((0 : E₂), r) ∈ S := by
    refine ⟨c0 - ⟪x0, p⟫_ℝ, x0, hx0D, F x0, 0, h0K, by simp, ?_⟩
    rw [hc0']; simp
  have hcore : ∀ u r, (u, r) ∈ S → ∃ ε > (0 : ℝ), ∃ r', (-(ε • u), r') ∈ S := by
    rintro u r ⟨x, hx, y, k, hk, hu, hgy⟩
    simp only at hu hgy
    have hy : y ∈ effDom g := ne_top_of_le_ne_top (EReal.coe_ne_top _) hgy
    obtain ⟨δ, hδ, x'', hx'', y'', hy'', k'', hk'', heq⟩ :=
      KcoreGeom12c K hK D F hF (effDom g) x0 hx0 hA x hx y hy k hk
    refine ⟨δ, hδ, (g y'').toReal - ⟪x'', p⟫_ℝ, x'', hx'', y'', k'', hk'', ?_, ?_⟩
    · simp only; rw [hu]; exact heq
    · simp only [sub_add_cancel]
      rw [EReal.coe_toReal hy'' (hgbot _)]
  obtain ⟨w, hw⟩ := coreSep S hS hup (-α) ha h0 hcore
  refine ⟨w, ?_, ?_⟩
  · intro k hk
    rw [inner_neg_right]
    by_contra hneg
    push Not at hneg
    have hwk : ⟪k, w⟫_ℝ < 0 := by linarith
    set X := c0 - ⟪x0, p⟫_ℝ + α with hX
    set t := (|X| + 1) / (-⟪k, w⟫_ℝ) with ht
    have htpos : 0 ≤ t := by rw [ht]; apply div_nonneg; positivity; linarith
    have hmem : (-(t • k), c0 - ⟪x0, p⟫_ℝ) ∈ S := by
      refine ⟨x0, hx0D, F x0, t • k, hKsmul k hk t htpos, by simp, ?_⟩
      rw [hc0']; simp
    have := hw _ _ hmem
    rw [inner_neg_right, inner_smul_right, real_inner_comm] at this
    have htk : t * ⟪k, w⟫_ℝ = -(|X| + 1) := by
      rw [ht, div_mul_eq_mul_div, div_eq_iff (by linarith)]; ring
    have := le_abs_self X
    linarith
  · unfold conj
    apply EReal.add_le_of_forall_lt
    intro a' ha' b' hb'
    obtain ⟨y, hy⟩ := lt_iSup_iff.mp ha'
    obtain ⟨x, hx⟩ := lt_iSup_iff.mp hb'
    refine (add_le_add hy.le hx.le).trans ?_
    by_cases hgy : g y = ⊤
    · rw [hgy, EReal.sub_top, EReal.bot_add]; exact bot_le
    by_cases hxD : x ∉ D
    · rw [scal, compND12c _ D F x hxD, EReal.sub_top, EReal.add_bot]; exact bot_le
    push Not at hxD
    rw [scal, compD12c _ D F x hxD, ← EReal.coe_toReal hgy (hgbot y)]
    have hmem : (y - 0 - F x, (g y).toReal - ⟪x, p⟫_ℝ) ∈ S := by
      refine ⟨x, hxD, y, 0, h0K, rfl, ?_⟩
      simp only [sub_add_cancel]; rw [EReal.coe_toReal hgy (hgbot y)]
    have := hw _ _ hmem
    rw [sub_zero, inner_sub_right] at this
    rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff,
      real_inner_comm w y]
    linarith


theorem solution {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (K : Set E₂) (hK : IsClosedConvexCone K)
    (D : Set E₁) (hD : D.Nonempty) (F : E₁ → E₂) (hF : IsKConvex K D F)
    (g : E₂ → EReal) (hg : IsProperConvex g) (h7 : Cond7 K D F g)
    (h10 : (F '' intrinsicInterior ℝ D ∩ intrinsicInterior ℝ (effDom g - K)).Nonempty) :
    (∀ p : E₁, conj (comp g D F) p = eta K D F g p ∧
      ∃ v : E₂, -v ∈ polarCone K ∧
        conj (comp g D F) p = conj g v + conj (scal v D F) p) ∧
    effDom (conj (comp g D F)) =
      {p | ∃ v ∈ effDom (conj g), -v ∈ polarCone K ∧
        conj (scal v D F) p < ⊤} := by
  obtain ⟨_, ⟨x0, hx0, rfl⟩, hA⟩ := h10
  have hg' := hg
  obtain ⟨hgbot, ⟨y0, hy0⟩, -⟩ := hg'
  have hx0D : x0 ∈ D := intrinsicInterior_subset hx0
  have hgFx0 : g (F x0) ≠ ⊤ := by
    obtain ⟨y, hy, k, hk, hyk⟩ := Set.mem_sub.mp (intrinsicInterior_subset hA)
    have : g (F x0) ≤ g y := h7 x0 hx0D y (by rw [← hyk]; simpa using hk)
    exact ne_top_of_le_ne_top hy this
  have hweak := weak12c g D F hgbot
  -- lower bounds
  have hconjbot : ∀ p, conj (comp g D F) p ≠ ⊥ := by
    intro p
    have := le_iSup (fun z => ((⟪z, p⟫_ℝ : ℝ) : EReal) - comp g D F z) x0
    rw [compD12c g D F x0 hx0D, ← EReal.coe_toReal hgFx0 (hgbot _), ← EReal.coe_sub] at this
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) this
  have hgvbot : ∀ v, conj g v ≠ ⊥ := by
    intro v
    have := le_iSup (fun z => ((⟪z, v⟫_ℝ : ℝ) : EReal) - g z) y0
    rw [← EReal.coe_toReal hy0 (hgbot _), ← EReal.coe_sub] at this
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) this
  have hscbot : ∀ v p, conj (scal v D F) p ≠ ⊥ := by
    intro v p
    have := le_iSup (fun z => ((⟪z, p⟫_ℝ : ℝ) : EReal) - scal v D F z) x0
    rw [scal, compD12c _ D F x0 hx0D, ← EReal.coe_sub] at this
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) this
  have hex : ∀ p, ∃ v : E₂, -v ∈ polarCone K ∧
      conj g v + conj (scal v D F) p ≤ conj (comp g D F) p := by
    intro p
    by_cases htop : conj (comp g D F) p = ⊤
    · refine ⟨0, ?_, by rw [htop]; exact le_top⟩
      intro x _; simp
    · obtain ⟨v, hv, hle⟩ := exist12c K hK D F hF g hg h7 x0 hx0 hA p
        (conj (comp g D F) p).toReal (EReal.coe_toReal htop (hconjbot p)).symm
      exact ⟨v, hv, hle.trans (EReal.coe_toReal htop (hconjbot p)).le⟩
  have hattain : ∀ p, ∃ v : E₂, -v ∈ polarCone K ∧
      conj (comp g D F) p = conj g v + conj (scal v D F) p := by
    intro p
    obtain ⟨v, hv, hle⟩ := hex p
    exact ⟨v, hv, le_antisymm (hweak p v) hle⟩
  refine ⟨fun p => ⟨?_, hattain p⟩, ?_⟩
  · obtain ⟨v, hv, heq⟩ := hattain p
    apply le_antisymm
    · unfold eta
      exact le_iInf₂ fun v' _ => hweak p v'
    · rw [heq]
      unfold eta
      exact iInf₂_le v hv
  · ext p
    constructor
    · intro hp
      obtain ⟨v, hv, heq⟩ := hattain p
      have hp' : conj g v + conj (scal v D F) p ≠ ⊤ := by rw [← heq]; exact hp
      refine ⟨v, ?_, hv, ?_⟩
      · intro h
        apply hp'
        rw [h, EReal.top_add_of_ne_bot (hscbot v p)]
      · rw [lt_top_iff_ne_top]
        intro h
        apply hp'
        rw [h, EReal.add_top_of_ne_bot (hgvbot v)]
    · rintro ⟨v, hv1, hv2, hv3⟩
      show conj (comp g D F) p ≠ ⊤
      exact ne_top_of_le_ne_top (EReal.add_lt_top hv1 hv3.ne).ne (hweak p v)
