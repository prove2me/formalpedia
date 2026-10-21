-- Prove2me | solution 1 for ChenSimchiLevi.Additive.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:02:31.608905+00:00
-- url     : https://prove2.me/submissions/d79672b6-1454-492a-9d7b-99a38666e610

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_ChenSimchiLevi_Additive_Model

set_option autoImplicit false

open MeasureTheory ChenSimchiLevi.Additive

lemma csl_porteus_to_bertsekas (k : ℝ) (f : ℝ → ℝ)
    (h : ∀ x₀ x₁ lam : ℝ, x₀ ≤ x₁ → lam ∈ Set.Icc (0 : ℝ) 1 →
      f ((1 - lam) * x₀ + lam * x₁) ≤ (1 - lam) * f x₀ + lam * f x₁ + lam * k) :
    BertsekasKConvex k f := by
  intro z b y hz hb
  have hzb : 0 < z + b := by linarith
  have hlam : (b / (z + b)) ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_one hzb]; linarith
  have := h (y - b) (z + y) (b / (z + b)) (by linarith) hlam
  have hy : (1 - b / (z + b)) * (y - b) + b / (z + b) * (z + y) = y := by
    field_simp
    ring
  rw [hy] at this
  have h1 : (1 - b / (z + b)) = z / (z + b) := by field_simp; ring
  rw [h1] at this
  have h2 : f y * (z + b) ≤ z * f (y - b) + b * f (z + y) + b * k := by
    have := mul_le_mul_of_nonneg_right this hzb.le
    have e : (z / (z + b) * f (y - b) + b / (z + b) * f (z + y) + b / (z + b) * k) * (z + b)
        = z * f (y - b) + b * f (z + y) + b * k := by
      field_simp
    linarith
  have : f y + z / b * (f y - f (y - b)) = (f y * (z + b) - z * f (y - b)) / b := by
    field_simp
    ring
  rw [this, div_le_iff₀ hb]
  nlinarith

lemma csl_bertsekas_to_porteus (k : ℝ) (f : ℝ → ℝ) (h : BertsekasKConvex k f) :
    ∀ x₀ x₁ lam : ℝ, x₀ ≤ x₁ → lam ∈ Set.Icc (0 : ℝ) 1 →
      f ((1 - lam) * x₀ + lam * x₁) ≤ (1 - lam) * f x₀ + lam * f x₁ + lam * k := by
  intro x₀ x₁ lam hx hl
  obtain ⟨hl0, hl1⟩ := hl
  have hk : 0 ≤ k := by
    have := h 0 1 0 le_rfl one_pos
    linarith
  rcases hx.eq_or_lt with hx' | hx'
  · subst hx'
    have : (1 - lam) * x₀ + lam * x₀ = x₀ := by ring
    rw [this]
    nlinarith [mul_nonneg hl0 hk]
  rcases hl0.eq_or_lt with hl' | hl'
  · subst hl'
    simp
  set y := (1 - lam) * x₀ + lam * x₁ with hy
  set b := lam * (x₁ - x₀) with hb
  set z := (1 - lam) * (x₁ - x₀) with hz
  have hb0 : 0 < b := mul_pos hl' (by linarith)
  have hz0 : 0 ≤ z := mul_nonneg (by linarith) (by linarith)
  have e1 : y - b = x₀ := by rw [hy, hb]; ring
  have e2 : z + y = x₁ := by rw [hy, hz]; ring
  have := h z b y hz0 hb0
  rw [e1, e2] at this
  have hD : 0 < x₁ - x₀ := by linarith
  have h3 : (f y * b + z * f y - z * f x₀) ≤ b * k + b * f x₁ := by
    have := mul_le_mul_of_nonneg_left this hb0.le
    have e : b * (f y + z / b * (f y - f x₀)) = f y * b + z * f y - z * f x₀ := by
      field_simp
      ring
    nlinarith
  have hbz : b + z = x₁ - x₀ := by rw [hb, hz]; ring
  have h4 : f y * (x₁ - x₀) ≤ z * f x₀ + b * f x₁ + b * k := by nlinarith
  have hzD : z = (1 - lam) * (x₁ - x₀) := rfl
  have hbD : b = lam * (x₁ - x₀) := rfl
  rw [hzD, hbD] at h4
  have : (x₁ - x₀) * f y ≤ (x₁ - x₀) * ((1 - lam) * f x₀ + lam * f x₁ + lam * k) := by nlinarith
  exact le_of_mul_le_mul_left this hD

lemma csl_pow_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (a + b) ^ n ≤ 2 ^ n * (a ^ n + b ^ n) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ n ≤ (2 * b) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2 ^ n * b ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (a ^ n + b ^ n) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : 0 ≤ a ^ n := by positivity
        linarith
  · calc (a + b) ^ n ≤ (2 * a) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2 ^ n * a ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (a ^ n + b ^ n) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : 0 ≤ b ^ n := by positivity
        linarith

lemma csl_select (M : Model) (hA : M.Assumptions) (hadd : M.IsAdditive)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T) (V : ℝ → ℝ)
    (hcont : ContinuousOn (Function.uncurry (M.gWith V t))
      (Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t))) :
    ∃ dsel : ℝ → ℝ,
      (∀ y : ℝ, dsel y ∈ Set.Icc (M.dlo t) (M.dhi t) ∧
        IsMaxOn (M.gWith V t y) (Set.Icc (M.dlo t) (M.dhi t)) (dsel y)) ∧
      Monotone (fun y => y - dsel y) := by
  set I : Set ℝ := Set.Icc (M.dlo t) (M.dhi t) with hI
  have hne : I.Nonempty := Set.nonempty_Icc.mpr (hA.dlo_le_dhi t ht)
  have hRc : ConcaveOn ℝ I (M.R t) := hA.R_concave t ht
  -- structure of g
  have hgform : ∀ y d : ℝ, M.gWith V t y d = M.R t d - M.c t * y +
      ∫ ε, (-M.h t ((y - d) - ε.2) + V ((y - d) - ε.2)) ∂(M.μ t) := by
    intro y d
    unfold Model.gWith
    congr 1
    apply integral_congr_ae
    filter_upwards [hadd t ht] with ε hε
    have : y - (ε.1 * d + ε.2) = (y - d) - ε.2 := by rw [hε]; ring
    simp only [this]
  -- continuity of g y on I
  have hgc : ∀ y, ContinuousOn (M.gWith V t y) I := by
    intro y
    have h1 : ContinuousOn (fun d : ℝ => Function.uncurry (M.gWith V t) (y, d)) I :=
      hcont.comp (Continuous.continuousOn (by fun_prop)) (fun d hd => ⟨Set.mem_univ _, hd⟩)
    exact h1
  -- least maximiser
  have hsel : ∀ y, ∃ d, d ∈ I ∧ IsMaxOn (M.gWith V t y) I d ∧
      ∀ d', d' ∈ I → IsMaxOn (M.gWith V t y) I d' → d ≤ d' := by
    intro y
    obtain ⟨dm, hdm, hdmax⟩ := isCompact_Icc.exists_isMaxOn hne (hgc y)
    set Mset : Set ℝ := I ∩ (M.gWith V t y) ⁻¹' Set.Ici (M.gWith V t y dm) with hMset
    have hMclosed : IsClosed Mset :=
      (hgc y).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hMne : Mset.Nonempty := ⟨dm, hdm, Set.mem_preimage.mpr (Set.mem_Ici.mpr le_rfl)⟩
    have hMbdd : BddBelow Mset := ⟨M.dlo t, fun d hd => hd.1.1⟩
    have hleast := hMclosed.isLeast_csInf hMne hMbdd
    refine ⟨sInf Mset, hleast.1.1, ?_, ?_⟩
    · intro d hd
      have := hdmax hd
      have h2 : M.gWith V t y dm ≤ M.gWith V t y (sInf Mset) := hleast.1.2
      simp only [Set.mem_setOf_eq] at this ⊢
      linarith
    · intro d' hd' hmax'
      apply hleast.2
      refine ⟨hd', ?_⟩
      exact hmax' hdm
  choose dsel hdI hdmax hdleast using hsel
  refine ⟨dsel, fun y => ⟨hdI y, hdmax y⟩, ?_⟩
  intro y1 y2 hy
  simp only
  rcases hy.eq_or_lt with h | h
  · rw [h]
  by_contra hcon
  push_neg at hcon
  -- d2 - d1 > δ
  set δ : ℝ := y2 - y1 with hδ
  set d1 := dsel y1 with hd1
  set d2 := dsel y2 with hd2
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hgap : δ < d2 - d1 := by rw [hδ]; linarith
  have hd1I : d1 ∈ I := hdI y1
  have hd2I : d2 ∈ I := hdI y2
  set d1' := d1 + δ with hd1'
  set d2' := d2 - δ with hd2'
  have hmem : ∀ d, d1 ≤ d → d ≤ d2 → d ∈ I := fun d h1 h2 =>
    ⟨le_trans hd1I.1 h1, le_trans h2 hd2I.2⟩
  have hd1'I : d1' ∈ I := hmem _ (by rw [hd1']; linarith) (by rw [hd1']; linarith)
  have hd2'I : d2' ∈ I := hmem _ (by rw [hd2']; linarith) (by rw [hd2']; linarith)
  -- concavity: R d1 + R d2 ≤ R d1' + R d2'
  have hC : M.R t d1 + M.R t d2 ≤ M.R t d1' + M.R t d2' := by
    set lam : ℝ := δ / (d2 - d1) with hlam
    have hpos : 0 < d2 - d1 := by linarith
    have hl0 : 0 ≤ lam := by rw [hlam]; positivity
    have hl1 : lam ≤ 1 := by rw [hlam, div_le_one hpos]; linarith
    have e1 : d1' = (1 - lam) • d1 + lam • d2 := by
      simp only [smul_eq_mul, hd1', hlam]; field_simp; ring
    have e2 : d2' = lam • d1 + (1 - lam) • d2 := by
      simp only [smul_eq_mul, hd2', hlam]; field_simp; ring
    have c1 := hRc.2 hd1I hd2I (by linarith : 0 ≤ 1 - lam) hl0 (by ring)
    have c2 := hRc.2 hd1I hd2I hl0 (by linarith : 0 ≤ 1 - lam) (by ring)
    rw [← e1] at c1
    rw [← e2] at c2
    simp only [smul_eq_mul] at c1 c2
    nlinarith
  -- optimality comparisons
  have hA1 : M.gWith V t y1 d2' ≤ M.gWith V t y1 d1 := hdmax y1 hd2'I
  have hB1 : M.gWith V t y2 d1' ≤ M.gWith V t y2 d2 := hdmax y2 hd1'I
  have hu1 : y2 - d1' = y1 - d1 := by rw [hd1', hδ]; ring
  have hu2 : y1 - d2' = y2 - d2 := by rw [hd2', hδ]; ring
  rw [hgform, hgform] at hA1 hB1
  rw [hu2] at hA1
  rw [hu1] at hB1
  -- so d1' is a maximiser at y2
  have hEq : M.gWith V t y2 d2 ≤ M.gWith V t y2 d1' := by
    rw [hgform, hgform, hu1]
    have hy : M.c t * y1 = M.c t * y1 := rfl
    nlinarith
  have hmax' : IsMaxOn (M.gWith V t y2) I d1' := by
    intro d hd
    have := hdmax y2 hd
    simp only [Set.mem_setOf_eq] at this ⊢
    linarith
  have := hdleast y2 d1' hd1'I hmax'
  rw [← hd2] at this
  linarith

theorem solution (M : Model) (hA : M.Assumptions) (hadd : M.IsAdditive)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T) (V : ℝ → ℝ)
    (hVcont : Continuous V)
    (hVk : BertsekasKConvex M.k (fun x => -V x))
    (hVgrowth : ∃ C : ℝ, ∀ x : ℝ, |V x| ≤ C * (1 + |x| ^ M.ρ))
    (hcont : ContinuousOn (Function.uncurry (M.gWith V t))
      (Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t))) :
    BertsekasKConvex M.k (fun y => -M.GstarWith V t y) := by
  haveI := hA.prob t ht
  set I : Set ℝ := Set.Icc (M.dlo t) (M.dhi t) with hI
  have hdlo : M.dlo t ∈ I := ⟨le_rfl, hA.dlo_le_dhi t ht⟩
  have hRc : ConcaveOn ℝ I (M.R t) := hA.R_concave t ht
  have hhc : ConvexOn ℝ Set.univ (M.h t) := hA.h_convex t ht
  have hk0 : 0 ≤ M.k := hA.k_nonneg
  -- Φ
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℝ → ℝ, Φ = fun u =>
      ∫ ε, (-M.h t (u - ε.2) + V (u - ε.2)) ∂(M.μ t) := ⟨_, rfl⟩
  have hgform : ∀ y d : ℝ, M.gWith V t y d = M.R t d - M.c t * y + Φ (y - d) := by
    intro y d
    rw [hΦdef]
    unfold Model.gWith
    congr 1
    apply integral_congr_ae
    filter_upwards [hadd t ht] with ε hε
    have : y - (ε.1 * d + ε.2) = (y - d) - ε.2 := by rw [hε]; ring
    simp only [this]
  -- integrability
  have hfint : ∀ u, Integrable (fun ε : ℝ × ℝ => M.h t (u - ε.2)) (M.μ t) := by
    intro u
    have := hA.h_integrable t ht (u + M.dlo t) (M.dlo t) hdlo
    refine this.congr ?_
    filter_upwards [hadd t ht] with ε hε
    have : u + M.dlo t - (ε.1 * M.dlo t + ε.2) = u - ε.2 := by rw [hε]; ring
    simp only [this]
  have hVint : ∀ u, Integrable (fun ε : ℝ × ℝ => V (u - ε.2)) (M.μ t) := by
    intro u
    obtain ⟨C, hC⟩ := hVgrowth
    have hmom := hA.moment t ht (M.dlo t) hdlo
    have hbint : Integrable (fun ε : ℝ × ℝ =>
        |C| * (1 + 2 ^ M.ρ * (|u + M.dlo t| ^ M.ρ + |ε.1 * M.dlo t + ε.2| ^ M.ρ))) (M.μ t) :=
      ((integrable_const (1 : ℝ)).add
        (((integrable_const (|u + M.dlo t| ^ M.ρ)).add hmom).const_mul _)).const_mul _
    refine Integrable.mono' hbint
      (hVcont.comp (continuous_const.sub continuous_snd)).aestronglyMeasurable ?_
    filter_upwards [hadd t ht] with ε hε
    rw [Real.norm_eq_abs]
    have h1 : |V (u - ε.2)| ≤ |C| * (1 + |u - ε.2| ^ M.ρ) :=
      le_trans (hC _) (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    have h2 : |u - ε.2| ^ M.ρ ≤ 2 ^ M.ρ * (|u + M.dlo t| ^ M.ρ + |ε.1 * M.dlo t + ε.2| ^ M.ρ) := by
      have h3 : |u - ε.2| ≤ |u + M.dlo t| + |ε.1 * M.dlo t + ε.2| := by
        rw [hε]
        have : u - ε.2 = (u + M.dlo t) - (1 * M.dlo t + ε.2) := by ring
        rw [this]
        exact abs_sub _ _
      exact le_trans (pow_le_pow_left₀ (abs_nonneg _) h3 _)
        (csl_pow_bound _ _ (abs_nonneg _) (abs_nonneg _) _)
    refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ (abs_nonneg C))
    linarith
  have hfΦint : ∀ u, Integrable (fun ε : ℝ × ℝ => -M.h t (u - ε.2) + V (u - ε.2)) (M.μ t) :=
    fun u => (hfint u).neg.add (hVint u)
  -- Porteus-type concavity of Φ
  have hΦk : ∀ u0 u1 lam : ℝ, u0 ≤ u1 → lam ∈ Set.Icc (0 : ℝ) 1 →
      (1 - lam) * Φ u0 + lam * Φ u1 - lam * M.k ≤ Φ ((1 - lam) * u0 + lam * u1) := by
    intro u0 u1 lam hu hl
    obtain ⟨hl0, hl1⟩ := hl
    have hP := csl_bertsekas_to_porteus M.k _ hVk
    have hB0 : Integrable (fun ε : ℝ × ℝ => (1 - lam) * (-M.h t (u0 - ε.2) + V (u0 - ε.2)))
        (M.μ t) := (hfΦint u0).const_mul _
    have hB1 : Integrable (fun ε : ℝ × ℝ => lam * (-M.h t (u1 - ε.2) + V (u1 - ε.2)))
        (M.μ t) := (hfΦint u1).const_mul _
    have hA' : Integrable (fun ε : ℝ × ℝ => (1 - lam) * (-M.h t (u0 - ε.2) + V (u0 - ε.2)) +
        lam * (-M.h t (u1 - ε.2) + V (u1 - ε.2))) (M.μ t) := hB0.add hB1
    have hint : ∫ ε, ((1 - lam) * (-M.h t (u0 - ε.2) + V (u0 - ε.2)) +
        lam * (-M.h t (u1 - ε.2) + V (u1 - ε.2)) - lam * M.k) ∂(M.μ t) =
        (1 - lam) * Φ u0 + lam * Φ u1 - lam * M.k := by
      rw [integral_sub hA' (integrable_const _), integral_add hB0 hB1,
        integral_const_mul, integral_const_mul, hΦdef]
      simp
    rw [← hint, hΦdef]
    apply integral_mono
    · exact hA'.sub (integrable_const _)
    · exact hfΦint _
    · intro ε
      have hc := hhc.2 (Set.mem_univ (u0 - ε.2)) (Set.mem_univ (u1 - ε.2))
        (by linarith : 0 ≤ 1 - lam) hl0 (by ring)
      have hv := hP (u0 - ε.2) (u1 - ε.2) lam (by linarith) ⟨hl0, hl1⟩
      have e : (1 - lam) * (u0 - ε.2) + lam * (u1 - ε.2) = (1 - lam) * u0 + lam * u1 - ε.2 := by ring
      simp only [smul_eq_mul] at hc
      rw [e] at hc hv
      simp only at hv ⊢
      linarith
  -- the selection
  obtain ⟨dsel, hdsel, hmono⟩ := csl_select M hA hadd t ht V hcont
  have hG : ∀ y, M.GstarWith V t y = M.gWith V t y (dsel y) := by
    intro y
    unfold Model.GstarWith
    apply IsGreatest.csSup_eq
    refine ⟨⟨dsel y, (hdsel y).1, rfl⟩, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    exact (hdsel y).2 hd
  apply csl_porteus_to_bertsekas
  intro y0 y1 lam hy hl
  obtain ⟨hl0, hl1⟩ := hl
  set d0 := dsel y0 with hd0
  set d1 := dsel y1 with hd1
  have hd0I : d0 ∈ I := (hdsel y0).1
  have hd1I : d1 ∈ I := (hdsel y1).1
  set dl : ℝ := (1 - lam) * d0 + lam * d1 with hdl
  set yl : ℝ := (1 - lam) * y0 + lam * y1 with hyl
  have hdlI : dl ∈ I := (convex_Icc _ _) hd0I hd1I (by linarith) hl0 (by ring)
  have hge : M.gWith V t yl dl ≤ M.GstarWith V t yl := by
    rw [hG yl]; exact (hdsel yl).2 hdlI
  have hu : y0 - d0 ≤ y1 - d1 := hmono hy
  have hΦ := hΦk (y0 - d0) (y1 - d1) lam hu ⟨hl0, hl1⟩
  have hRl := hRc.2 hd0I hd1I (by linarith : 0 ≤ 1 - lam) hl0 (by ring)
  simp only [smul_eq_mul] at hRl
  have hul : yl - dl = (1 - lam) * (y0 - d0) + lam * (y1 - d1) := by rw [hyl, hdl]; ring
  have hgl : M.gWith V t yl dl = M.R t dl - M.c t * yl + Φ (yl - dl) := hgform _ _
  rw [hul] at hgl
  have hg0 := hgform y0 d0
  have hg1 := hgform y1 d1
  rw [hG y0, hG y1]
  have hcy : M.c t * yl = (1 - lam) * (M.c t * y0) + lam * (M.c t * y1) := by rw [hyl]; ring
  rw [hgl] at hge
  rw [hg0, hg1]
  nlinarith
