-- Prove2me | solution 1 for FirstOrderOpt.FiniteSum.gradient_variation_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:48:58.044786+00:00
-- url     : https://prove2.me/submissions/2a0dda8a-4503-41ad-a46d-60ac793a1281

import Mathlib



namespace FirstOrderOpt.FiniteSum

open Set Filter Topology

/-- directional derivative nonnegativity -/
lemma dir_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {F' : E →L[ℝ] ℝ} {X : Set E} (hX : Convex ℝ X) {a b : E}
    (ha : a ∈ X) (hb : b ∈ X) (hd : HasFDerivWithinAt F F' X a) {c : ℝ}
    (h : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ s * c + (F (a + s • (b - a)) - F a)) :
    0 ≤ c + F' (b - a) := by
  have h1 : HasDerivWithinAt (fun s : ℝ => a + s • (b - a)) (b - a) (Icc 0 1) 0 := by
    have := (((hasDerivAt_id (0:ℝ)).smul_const (b - a)).const_add a).hasDerivWithinAt (s := Icc (0:ℝ) 1)
    simpa using this
  have hmaps : MapsTo (fun s : ℝ => a + s • (b - a)) (Icc 0 1) X := by
    intro s hs
    exact hX.add_smul_sub_mem ha hb hs
  have h2 : HasDerivWithinAt (F ∘ fun s : ℝ => a + s • (b - a)) (F' (b - a)) (Icc 0 1) 0 := by
    exact HasFDerivWithinAt.comp_hasDerivWithinAt (l := F) (f := fun s : ℝ => a + s • (b - a)) 0
      (by simpa using hd) h1 hmaps
  rw [hasDerivWithinAt_iff_tendsto_slope] at h2
  have hset : Icc (0:ℝ) 1 \ {0} = Ioc 0 1 := by
    ext s; simp only [Set.mem_sdiff, mem_Icc, mem_singleton_iff, mem_Ioc]
    constructor
    · rintro ⟨⟨h0, h1⟩, hne⟩; exact ⟨lt_of_le_of_ne h0 (Ne.symm hne), h1⟩
    · rintro ⟨h0, h1⟩; exact ⟨⟨h0.le, h1⟩, h0.ne'⟩
  rw [hset] at h2
  have h3 : Tendsto (slope (F ∘ fun s : ℝ => a + s • (b - a)) 0) (𝓝[Ioo 0 1] 0) (𝓝 (F' (b - a))) :=
    h2.mono_left (nhdsWithin_mono _ Ioo_subset_Ioc_self)
  have : (𝓝[Ioo (0:ℝ) 1] 0).NeBot := left_nhdsWithin_Ioo_neBot (a := (0:ℝ)) (b := 1) (by norm_num)
  have h4 : -c ≤ F' (b - a) := by
    refine ge_of_tendsto h3 ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : 0 < s := hs.1
    have := h s hs0 hs.2.le
    rw [slope_def_field]
    simp only [Function.comp, sub_zero, zero_smul, add_zero]
    rw [le_div_iff₀ hs0]
    nlinarith
  linarith


lemma line_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {F' : E → E →L[ℝ] ℝ} (hF : ∀ x, HasFDerivAt F (F' x) x) (x d : E) (s : ℝ) :
    HasDerivAt (fun t : ℝ => F (x + t • d)) (F' (x + s • d) d) s := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • d) d s := by
    simpa using ((hasDerivAt_id s).smul_const d).const_add x
  exact (hF (x + s • d)).comp_hasDerivAt s h1

/-- descent lemma -/
lemma descent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (F' : E → E →L[ℝ] ℝ) (hF : ∀ x, HasFDerivAt F (F' x) x) (L : ℝ)
    (hs : ∀ x y, ‖F' x - F' y‖ ≤ L * ‖x - y‖) (x y : E) :
    F y ≤ F x + F' x (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  set d := y - x with hd
  let k : ℝ → ℝ := fun t => F (x + t • d) - F x - t * F' x d - L * t ^ 2 * ‖d‖ ^ 2 / 2
  have hk : ∀ t, HasDerivAt k (F' (x + t • d) d - F' x d - L * t * ‖d‖ ^ 2) t := by
    intro t
    have h1 := line_hasDerivAt hF x d t
    have h2 : HasDerivAt (fun t : ℝ => t * F' x d) (F' x d) t := by
      simpa using (hasDerivAt_id t).mul_const (F' x d)
    have h3 : HasDerivAt (fun t : ℝ => L * t ^ 2 * ‖d‖ ^ 2 / 2) (L * t * ‖d‖ ^ 2) t := by
      have := (((hasDerivAt_id t).pow 2).const_mul L).mul_const (‖d‖ ^ 2) |>.div_const 2
      exact this.congr_deriv (by simp only [id]; push_cast; ring)
    exact ((h1.sub_const (F x)).sub h2).sub h3
  have hanti : AntitoneOn k (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact fun t _ => (hk t).continuousAt.continuousWithinAt
    · exact fun t _ => (hk t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : (0:ℝ) < t := ht
      rw [(hk t).deriv]
      have h1 : F' (x + t • d) d - F' x d ≤ ‖F' (x + t • d) - F' x‖ * ‖d‖ := by
        have := (F' (x + t • d) - F' x).le_opNorm d
        have h' : |F' (x + t • d) d - F' x d| ≤ ‖F' (x + t • d) - F' x‖ * ‖d‖ := by
          simpa [Real.norm_eq_abs] using this
        exact le_trans (le_abs_self _) h'
      have h2 : ‖F' (x + t • d) - F' x‖ ≤ L * (t * ‖d‖) := by
        have := hs (x + t • d) x
        simpa [norm_smul, abs_of_pos ht0] using this
      have h3 : ‖F' (x + t • d) - F' x‖ * ‖d‖ ≤ L * (t * ‖d‖) * ‖d‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      nlinarith
  have := hanti (Set.mem_Ici.2 (le_refl (0:ℝ))) (Set.mem_Ici.2 (zero_le_one' ℝ)) zero_le_one
  simp only [k] at this
  simp at this
  have e : x + d = y := by simp [hd]
  rw [e] at this
  linarith


lemma conv_grad {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {F' : E → E →L[ℝ] ℝ} (hF : ∀ x, HasFDerivAt F (F' x) x)
    (hc : ConvexOn ℝ Set.univ F) (x y : E) : F x + F' x (y - x) ≤ F y := by
  have hd : HasFDerivWithinAt (fun z => - F z) (-(F' x)) Set.univ x :=
    (hF x).neg.hasFDerivWithinAt
  have := dir_nonneg (convex_univ) (Set.mem_univ x) (Set.mem_univ y) hd (c := F y - F x) (by
    intro s hs0 hs1
    have h := hc.2 (Set.mem_univ x) (Set.mem_univ y) (show (0:ℝ) ≤ 1 - s by linarith) hs0.le
      (by ring)
    have e : (1 - s) • x + s • y = x + s • (y - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [e] at h
    simp only [smul_eq_mul] at h
    nlinarith)
  simp only [map_sub, ContinuousLinearMap.neg_apply] at this
  rw [map_sub]
  linarith

lemma cocoerc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {F' : E → E →L[ℝ] ℝ} (hF : ∀ x, HasFDerivAt F (F' x) x)
    (hc : ConvexOn ℝ Set.univ F) {L : ℝ} (hL : 0 < L)
    (hs : ∀ x y, ‖F' x - F' y‖ ≤ L * ‖x - y‖) (x y : E) :
    F x + F' x (y - x) + (1 / (2 * L)) * ‖F' y - F' x‖ ^ 2 ≤ F y := by
  set P := F y - F x - F' x (y - x) with hP
  have hP0 : 0 ≤ P := by have := conv_grad hF hc x y; linarith
  have hφ : ∀ z, F x + F' x (z - x) ≤ F z := conv_grad hF hc x
  have hφd : ∀ z, HasFDerivAt (fun w => F w - F' x w) (F' z - F' x) z := fun z =>
    (hF z).sub (F' x).hasFDerivAt
  have hφs : ∀ z w, ‖(F' z - F' x) - (F' w - F' x)‖ ≤ L * ‖z - w‖ := by
    intro z w
    have : (F' z - F' x) - (F' w - F' x) = F' z - F' w := by abel
    rw [this]; exact hs z w
  have key : ∀ z : E, (( F' y - F' x) z) ^ 2 ≤ 2 * L * P * ‖z‖ ^ 2 := by
    intro z
    by_cases hz : z = 0
    · subst hz; simp
    have hn : 0 < ‖z‖ ^ 2 := by positivity
    have hall : ∀ t : ℝ, 0 ≤ P + t * (F' y - F' x) z + L / 2 * t ^ 2 * ‖z‖ ^ 2 := by
      intro t
      have h1 := descent (fun w => F w - F' x w) (fun z => F' z - F' x) hφd L hφs y (y + t • z)
      have h2 := hφ (y + t • z)
      simp only [add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs,
         map_add, mul_pow, sq_abs] at h1 h2
      simp only [hP,  map_sub, map_add, map_smul, smul_eq_mul] at *
      nlinarith
    set a := (F' y - F' x) z
    have := hall (-a / (L * ‖z‖ ^ 2))
    have e : P + -a / (L * ‖z‖ ^ 2) * a + L / 2 * (-a / (L * ‖z‖ ^ 2)) ^ 2 * ‖z‖ ^ 2
        = P - a ^ 2 / (2 * L * ‖z‖ ^ 2) := by
      field_simp; ring
    rw [e] at this
    have h3 : a ^ 2 / (2 * L * ‖z‖ ^ 2) ≤ P := by linarith
    rw [div_le_iff₀ (by positivity)] at h3
    linarith
  have hB : 0 ≤ 2 * L * P := by positivity
  have hnorm : ‖F' y - F' x‖ ≤ Real.sqrt (2 * L * P) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro z
    rw [Real.norm_eq_abs]
    have := Real.abs_le_sqrt (key z)
    rw [Real.sqrt_mul hB, Real.sqrt_sq (norm_nonneg _)] at this
    exact this
  have hsq : ‖F' y - F' x‖ ^ 2 ≤ 2 * L * P := by
    calc ‖F' y - F' x‖ ^ 2 ≤ (Real.sqrt (2 * L * P)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = 2 * L * P := Real.sq_sqrt hB
  have : (1 / (2 * L)) * ‖F' y - F' x‖ ^ 2 ≤ P := by
    rw [one_div, inv_mul_le_iff₀ (by positivity)]; linarith
  linarith


theorem gvb_core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (hne : (Finset.univ : Finset (Fin m)).Nonempty)
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (f h Ψ : E → ℝ) (hΨ : ∀ x, Ψ x = f x + h x) (hhconv : ConvexOn ℝ X h)
    (fi : Fin m → E → ℝ) (hf : ∀ x, f x = (1 / (m : ℝ)) * ∑ i, fi i x)
    (hfi_conv : ∀ i, ConvexOn ℝ Set.univ (fi i))
    (gradf : Fin m → E → E →L[ℝ] ℝ)
    (hgrad : ∀ i x, HasFDerivAt (fi i) (gradf i x) x)
    (L : Fin m → ℝ) (hL : ∀ i, 0 < L i)
    (hsmooth : ∀ i x y, ‖gradf i x - gradf i y‖ ≤ L i * ‖x - y‖)
    (q : Fin m → ℝ) (hq_pos : ∀ i, 0 < q i) (hq_sum : ∑ i, q i = 1)
    (LQ : ℝ) (hLQ : LQ = (1 / (m : ℝ)) * Finset.univ.sup' hne (fun i => L i / q i))
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, Ψ xstar ≤ Ψ y) :
    ∀ x ∈ X, (1 / (m : ℝ)) * ∑ i, (1 / ((m : ℝ) * q i)) * ‖gradf i x - gradf i xstar‖ ^ 2 ≤
      2 * LQ * (Ψ x - Ψ xstar) := by
  intro x hx
  obtain ⟨i0, _⟩ := hne
  have hm : (0:ℝ) < m := by exact_mod_cast Fin.pos i0
  set d := x - xstar with hd
  -- per-component quantities
  set φ : Fin m → ℝ := fun i => fi i x - fi i xstar - gradf i xstar d with hφ
  have hco : ∀ i, (1 / (2 * L i)) * ‖gradf i x - gradf i xstar‖ ^ 2 ≤ φ i := by
    intro i
    have := cocoerc (hgrad i) (hfi_conv i) (hL i) (hsmooth i) xstar x
    simp only [hφ]; linarith
  have hφ0 : ∀ i, 0 ≤ φ i := fun i =>
    le_trans (by have := hL i; positivity) (hco i)
  have hterm : ∀ i, (1 / ((m : ℝ) * q i)) * ‖gradf i x - gradf i xstar‖ ^ 2 ≤ 2 * LQ * φ i := by
    intro i
    have h1 : ‖gradf i x - gradf i xstar‖ ^ 2 ≤ 2 * L i * φ i := by
      have := hco i
      rw [one_div, inv_mul_le_iff₀ (by have := hL i; positivity)] at this
      linarith
    have h2 : (1 / ((m : ℝ) * q i)) * L i ≤ LQ := by
      have hle : L i / q i ≤ Finset.univ.sup' ⟨i0, Finset.mem_univ _⟩ (fun i => L i / q i) :=
        Finset.le_sup' (fun i => L i / q i) (Finset.mem_univ i)
      rw [hLQ]
      have : (1 / ((m : ℝ) * q i)) * L i = (1 / (m : ℝ)) * (L i / q i) := by
        field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    have hw : 0 ≤ 1 / ((m : ℝ) * q i) := by have := hq_pos i; positivity
    calc (1 / ((m : ℝ) * q i)) * ‖gradf i x - gradf i xstar‖ ^ 2
        ≤ (1 / ((m : ℝ) * q i)) * (2 * L i * φ i) := mul_le_mul_of_nonneg_left h1 hw
      _ = 2 * ((1 / ((m : ℝ) * q i)) * L i) * φ i := by ring
      _ ≤ 2 * LQ * φ i := by
        apply mul_le_mul_of_nonneg_right _ (hφ0 i)
        linarith
  have hsum : (1 / (m : ℝ)) * ∑ i, (1 / ((m : ℝ) * q i)) * ‖gradf i x - gradf i xstar‖ ^ 2 ≤
      2 * LQ * ((1 / (m : ℝ)) * ∑ i, φ i) := by
    calc _ ≤ (1 / (m : ℝ)) * ∑ i, 2 * LQ * φ i :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) (by positivity)
      _ = _ := by rw [← Finset.mul_sum]; ring
  -- derivative of f at xstar
  have hfd : HasFDerivAt f ((1 / (m : ℝ)) • ∑ i, gradf i xstar) xstar := by
    have h1 : HasFDerivAt (fun y => ∑ i, fi i y) (∑ i, gradf i xstar) xstar :=
      HasFDerivAt.fun_sum (fun i _ => hgrad i xstar)
    have h2 := h1.const_mul (1 / (m : ℝ))
    have e : f = fun y => (1 / (m : ℝ)) * ∑ i, fi i y := funext hf
    rw [e]; exact h2
  have hdir := dir_nonneg hXconv hxstar hx hfd.hasFDerivWithinAt (c := h x - h xstar) (by
    intro s hs0 hs1
    have hy : xstar + s • (x - xstar) ∈ X := hXconv.add_smul_sub_mem hxstar hx ⟨hs0.le, hs1⟩
    have h1 := hxstar_opt _ hy
    have h2 := hhconv.2 hxstar hx (show (0:ℝ) ≤ 1 - s by linarith) hs0.le (by ring)
    have e : (1 - s) • xstar + s • x = xstar + s • (x - xstar) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [e] at h2
    simp only [smul_eq_mul] at h2
    rw [hΨ, hΨ] at h1
    nlinarith)
  have hG : ((1 / (m : ℝ)) • ∑ i, gradf i xstar) (x - xstar) = (1 / (m : ℝ)) * ∑ i, gradf i xstar d := by
    simp [hd]
  rw [hG] at hdir
  have hφsum : (1 / (m : ℝ)) * ∑ i, φ i = (f x - f xstar) - (1 / (m : ℝ)) * ∑ i, gradf i xstar d := by
    simp only [hφ, Finset.sum_sub_distrib, hf]; ring
  rw [hφsum] at hsum
  have hLQ0 : 0 ≤ LQ := by
    rw [hLQ]
    have : 0 ≤ L i0 / q i0 := by have := hL i0; have := hq_pos i0; positivity
    exact mul_nonneg (by positivity) (le_trans this (Finset.le_sup' (fun i => L i / q i) (Finset.mem_univ i0)))
  have : (f x - f xstar) - (1 / (m : ℝ)) * ∑ i, gradf i xstar d ≤ Ψ x - Ψ xstar := by
    rw [hΨ, hΨ]; linarith
  calc _ ≤ _ := hsum
    _ ≤ 2 * LQ * (Ψ x - Ψ xstar) := mul_le_mul_of_nonneg_left this (by linarith)

end FirstOrderOpt.FiniteSum

open FirstOrderOpt.FiniteSum


theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (hne : (Finset.univ : Finset (Fin m)).Nonempty)
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (f h Ψ : E → ℝ) (hΨ : ∀ x, Ψ x = f x + h x) (hhconv : ConvexOn ℝ X h)
    (fi : Fin m → E → ℝ) (hf : ∀ x, f x = (1 / (m : ℝ)) * ∑ i, fi i x)
    (hfi_conv : ∀ i, ConvexOn ℝ Set.univ (fi i))
    (gradf : Fin m → E → E →L[ℝ] ℝ)
    (hgrad : ∀ i x, HasFDerivAt (fi i) (gradf i x) x)
    (L : Fin m → ℝ) (hL : ∀ i, 0 < L i)
    (hsmooth : ∀ i x y, ‖gradf i x - gradf i y‖ ≤ L i * ‖x - y‖)
    (q : Fin m → ℝ) (hq_pos : ∀ i, 0 < q i) (hq_sum : ∑ i, q i = 1)
    (LQ : ℝ) (hLQ : LQ = (1 / (m : ℝ)) * Finset.univ.sup' hne (fun i => L i / q i))
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, Ψ xstar ≤ Ψ y) :
    ∀ x ∈ X, (1 / (m : ℝ)) * ∑ i, (1 / ((m : ℝ) * q i)) * ‖gradf i x - gradf i xstar‖ ^ 2 ≤
      2 * LQ * (Ψ x - Ψ xstar) := by
  exact gvb_core hne X hXconv hXclosed f h Ψ hΨ hhconv fi hf hfi_conv gradf hgrad L hL hsmooth q hq_pos hq_sum LQ hLQ xstar hxstar hxstar_opt
