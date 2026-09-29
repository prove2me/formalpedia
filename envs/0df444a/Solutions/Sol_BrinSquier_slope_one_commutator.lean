-- Prove2me | solution 1 for BrinSquier.slope_one_commutator
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-12T22:33:47.962998+00:00
-- url     : https://prove2.me/submissions/c4fd31da-1201-4450-b0da-d4f588cfcebe

import Definitions.Def_BrinSquier
import Mathlib

namespace BS_aux

/-- Two affine maps agreeing at two distinct points are equal. -/
lemma affine_unique {a b a' b' y₁ y₂ : ℝ} (hne : y₁ ≠ y₂)
    (h1 : a * y₁ + b = a' * y₁ + b') (h2 : a * y₂ + b = a' * y₂ + b') :
    a = a' ∧ b = b' := by
  have hsub : (a - a') * (y₁ - y₂) = 0 := by nlinarith [h1, h2]
  have haa : a - a' = 0 := by
    rcases mul_eq_zero.1 hsub with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) hne
  have ha : a = a' := by linarith
  refine ⟨ha, ?_⟩
  rw [ha] at h1
  linarith

/-- Local affineness below `M`, propagated leftwards from a base point. -/
def LocAff (f : ℝ → ℝ) (M : ℝ) : Prop :=
  ∀ x < M, ∃ ε > 0, ∃ a b : ℝ, ∀ y ∈ Set.Ioo (x - ε) (x + ε), f y = a * y + b

/-- Local affineness below `M` gives a single affine map on the ray `(-∞, x₀]`. -/
theorem affine_on_ray {f : ℝ → ℝ} {M : ℝ} (H : LocAff f M) {x₀ : ℝ} (hx₀ : x₀ < M) :
    ∃ a b : ℝ, ∀ y ≤ x₀, f y = a * y + b := by
  obtain ⟨e₀, he₀, a₀, b₀, h₀⟩ := H x₀ hx₀
  set S : Set ℝ := {t : ℝ | t ≤ x₀ ∧ ∀ z ∈ Set.Icc t x₀, f z = a₀ * z + b₀} with hS
  -- the base point's own neighbourhood puts a point strictly below `x₀` into `S`
  have hbase : x₀ - e₀/2 ∈ S := by
    refine ⟨by linarith, fun z hz => h₀ z ⟨by linarith [hz.1], by linarith [hz.2]⟩⟩
  have hne : S.Nonempty := ⟨_, hbase⟩
  refine ⟨a₀, b₀, ?_⟩
  -- it suffices that `S` is unbounded below
  have hunb : ¬ BddBelow S := by
    intro hbdd
    set c := sInf S with hc
    have hcx : c ≤ x₀ - e₀/2 := csInf_le hbdd hbase
    have hcM : c < M := by linarith
    obtain ⟨e, he, a, b, h⟩ := H c hcM
    -- a member of `S` just above the infimum
    obtain ⟨t, htS, htlt⟩ := exists_lt_of_csInf_lt hne
      (show c < c + min e (x₀ - c) by
        have : 0 < min e (x₀ - c) := lt_min he (by linarith)
        linarith)
    have hct : c ≤ t := csInf_le hbdd htS
    have htx : t < x₀ := by
      have := min_le_right e (x₀ - c); linarith
    have hte : t < c + e := by have := min_le_left e (x₀ - c); linarith
    -- two distinct points where both affine formulas hold
    set u := min (c + e) x₀ with hu
    have htu : t < u := lt_min hte htx
    set p := (t + u)/2 with hp
    have htp : t < p := by simp only [hp]; linarith
    have hpu : p < u := by simp only [hp]; linarith
    have hpx : p ≤ x₀ := le_of_lt (lt_of_lt_of_le hpu (min_le_right _ _))
    have hpe : p < c + e := lt_of_lt_of_le hpu (min_le_left _ _)
    have e1 : f t = a₀ * t + b₀ := htS.2 t ⟨le_refl _, le_of_lt htx⟩
    have e2 : f p = a₀ * p + b₀ := htS.2 p ⟨le_of_lt htp, hpx⟩
    have e3 : f t = a * t + b := h t ⟨by linarith, by linarith⟩
    have e4 : f p = a * p + b := h p ⟨by linarith, by linarith⟩
    obtain ⟨haa, hbb⟩ :=
      affine_unique (ne_of_lt htp) (e3.symm.trans e1) (e4.symm.trans e2)
    -- now the affine formula at `c` is the base one, so `S` reaches below `c`
    have : c - e/2 ∈ S := by
      refine ⟨by linarith, fun z hz => ?_⟩
      by_cases hzt : t ≤ z
      · exact htS.2 z ⟨hzt, hz.2⟩
      · replace hzt := not_le.mp hzt
        have := h z ⟨by linarith [hz.1], by linarith⟩
        rw [this, haa, hbb]
    have := csInf_le hbdd this
    linarith
  intro y hy
  rw [not_bddBelow_iff] at hunb
  obtain ⟨t, htS, hty⟩ := hunb y
  exact htS.2 y ⟨le_of_lt hty, hy⟩

/-- Local affineness above `M`. -/
def LocAffTop (f : ℝ → ℝ) (M : ℝ) : Prop :=
  ∀ x > M, ∃ ε > 0, ∃ a b : ℝ, ∀ y ∈ Set.Ioo (x - ε) (x + ε), f y = a * y + b

/-- Local affineness above `M` gives a single affine map on the ray `[x₀, ∞)`. -/
theorem affine_on_ray_top {f : ℝ → ℝ} {M : ℝ} (H : LocAffTop f M) {x₀ : ℝ} (hx₀ : M < x₀) :
    ∃ a b : ℝ, ∀ y, x₀ ≤ y → f y = a * y + b := by
  obtain ⟨e₀, he₀, a₀, b₀, h₀⟩ := H x₀ hx₀
  set S : Set ℝ := {t : ℝ | x₀ ≤ t ∧ ∀ z ∈ Set.Icc x₀ t, f z = a₀ * z + b₀} with hS
  have hbase : x₀ + e₀/2 ∈ S := by
    refine ⟨by linarith, fun z hz => h₀ z ⟨by linarith [hz.1], by linarith [hz.2]⟩⟩
  have hne : S.Nonempty := ⟨_, hbase⟩
  refine ⟨a₀, b₀, ?_⟩
  have hunb : ¬ BddAbove S := by
    intro hbdd
    set c := sSup S with hc
    have hcx : x₀ + e₀/2 ≤ c := le_csSup hbdd hbase
    have hcM : M < c := by linarith
    obtain ⟨e, he, a, b, h⟩ := H c hcM
    obtain ⟨t, htS, htlt⟩ := exists_lt_of_lt_csSup hne
      (show c - min e (c - x₀) < c by
        have : 0 < min e (c - x₀) := lt_min he (by linarith)
        linarith)
    have hct : t ≤ c := le_csSup hbdd htS
    have htx : x₀ < t := by have := min_le_right e (c - x₀); linarith
    have hte : c - e < t := by have := min_le_left e (c - x₀); linarith
    set u := max (c - e) x₀ with hu
    have hut : u < t := max_lt hte htx
    set p := (u + t)/2 with hp
    have hpt : p < t := by simp only [hp]; linarith
    have hup : u < p := by simp only [hp]; linarith
    have hpx : x₀ ≤ p := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hup)
    have hpe : c - e < p := lt_of_le_of_lt (le_max_left _ _) hup
    have e1 : f t = a₀ * t + b₀ := htS.2 t ⟨le_of_lt htx, le_refl _⟩
    have e2 : f p = a₀ * p + b₀ := htS.2 p ⟨hpx, le_of_lt hpt⟩
    have e3 : f t = a * t + b := h t ⟨by linarith, by linarith⟩
    have e4 : f p = a * p + b := h p ⟨by linarith, by linarith⟩
    obtain ⟨haa, hbb⟩ :=
      affine_unique (ne_of_gt hpt) (e3.symm.trans e1) (e4.symm.trans e2)
    have : c + e/2 ∈ S := by
      refine ⟨by linarith, fun z hz => ?_⟩
      by_cases hzt : z ≤ t
      · exact htS.2 z ⟨hz.1, hzt⟩
      · replace hzt := not_le.mp hzt
        have := h z ⟨by linarith, by linarith [hz.2]⟩
        rw [this, haa, hbb]
    have := le_csSup hbdd this
    linarith
  intro y hy
  rw [not_bddAbove_iff] at hunb
  obtain ⟨t, htS, hty⟩ := hunb y
  exact htS.2 y ⟨hy, le_of_lt hty⟩

/-- `IsPLF` gives local affineness on a ray at each end. -/
theorem locAff_of_isPLF {f : ℝ ≃o ℝ} (hf : BrinSquier.IsPLF f) :
    ∃ M : ℝ, LocAff (fun y => f y) M ∧ LocAffTop (fun y => f y) (-M) := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨m, hm⟩ := B.finite_toSet.bddBelow
  obtain ⟨n, hn⟩ := B.finite_toSet.bddAbove
  refine ⟨min (m - 1) (-(n + 1)), fun x hx => ?_, fun x hx => ?_⟩
  · refine hB x (fun hmem => absurd (hm hmem) ?_)
    have := lt_of_lt_of_le hx (min_le_left (m - 1) (-(n+1))); linarith
  · refine hB x (fun hmem => absurd (hn hmem) ?_)
    have h2 := lt_of_le_of_lt (neg_le_neg (min_le_right (m - 1) (-(n+1)))) hx
    simp only [neg_neg] at h2; linarith

open BrinSquier

/-- A slope at an end of an order isomorphism is positive. -/
lemma slopeAtBot_pos {f : ℝ ≃o ℝ} {a : ℝ} (hf : SlopeAtBot f a) : 0 < a := by
  obtain ⟨b, M, h⟩ := hf
  have h1 : f (M - 2) = a * (M - 2) + b := h _ (by linarith)
  have h2 : f (M - 1) = a * (M - 1) + b := h _ (by linarith)
  have : f (M - 2) < f (M - 1) := f.strictMono (by linarith)
  rw [h1, h2] at this; linarith

lemma slopeAtTop_pos {f : ℝ ≃o ℝ} {a : ℝ} (hf : SlopeAtTop f a) : 0 < a := by
  obtain ⟨b, M, h⟩ := hf
  have h1 : f (M + 1) = a * (M + 1) + b := h _ (by linarith)
  have h2 : f (M + 2) = a * (M + 2) + b := h _ (by linarith)
  have : f (M + 1) < f (M + 2) := f.strictMono (by linarith)
  rw [h1, h2] at this; linarith

lemma slopeAtBot_mul {f g : ℝ ≃o ℝ} {a c : ℝ}
    (hf : SlopeAtBot f a) (hg : SlopeAtBot g c) : SlopeAtBot (f * g) (a * c) := by
  have hc : 0 < c := slopeAtBot_pos hg
  obtain ⟨b, M, h⟩ := hf
  obtain ⟨d, N, k⟩ := hg
  refine ⟨a * d + b, min N ((M - d)/c), fun y hy => ?_⟩
  have hyN : y < N := lt_of_lt_of_le hy (min_le_left _ _)
  have hy2 : y < (M - d)/c := lt_of_lt_of_le hy (min_le_right _ _)
  have hlt : c * y + d < M := by
    rw [lt_div_iff₀ hc] at hy2; linarith
  show f (g y) = a * c * y + (a * d + b)
  rw [k y hyN, h _ hlt]; ring

lemma slopeAtTop_mul {f g : ℝ ≃o ℝ} {a c : ℝ}
    (hf : SlopeAtTop f a) (hg : SlopeAtTop g c) : SlopeAtTop (f * g) (a * c) := by
  have hc : 0 < c := slopeAtTop_pos hg
  obtain ⟨b, M, h⟩ := hf
  obtain ⟨d, N, k⟩ := hg
  refine ⟨a * d + b, max N ((M - d)/c), fun y hy => ?_⟩
  have hyN : y > N := lt_of_le_of_lt (le_max_left _ _) hy
  have hy2 : y > (M - d)/c := lt_of_le_of_lt (le_max_right _ _) hy
  have hgt : c * y + d > M := by
    have hy2' : (M - d)/c < y := hy2
    rw [div_lt_iff₀ hc] at hy2'; linarith
  show f (g y) = a * c * y + (a * d + b)
  rw [k y hyN, h _ hgt]; ring

lemma slopeAtBot_inv {f : ℝ ≃o ℝ} {a : ℝ} (hf : SlopeAtBot f a) : SlopeAtBot f⁻¹ (1/a) := by
  have ha : 0 < a := slopeAtBot_pos hf
  obtain ⟨b, M, h⟩ := hf
  refine ⟨-b/a, a * M + b, fun w hw => ?_⟩
  have hy : (w - b)/a < M := by rw [div_lt_iff₀ ha]; linarith
  have hane : a ≠ 0 := ne_of_gt ha
  have hfy : f ((w - b)/a) = w := by
    rw [h _ hy]; field_simp; ring
  show f⁻¹ w = 1/a * w + -b/a
  have : f (f⁻¹ w) = f ((w - b)/a) := by rw [RelIso.apply_inv_self, hfy]
  rw [f.injective this]; field_simp; ring

lemma slopeAtTop_inv {f : ℝ ≃o ℝ} {a : ℝ} (hf : SlopeAtTop f a) : SlopeAtTop f⁻¹ (1/a) := by
  have ha : 0 < a := slopeAtTop_pos hf
  obtain ⟨b, M, h⟩ := hf
  refine ⟨-b/a, a * M + b, fun w hw => ?_⟩
  have hy : (w - b)/a > M := by
    have : M < (w - b)/a := by rw [lt_div_iff₀ ha]; linarith
    exact this
  have hane : a ≠ 0 := ne_of_gt ha
  have hfy : f ((w - b)/a) = w := by
    rw [h _ hy]; field_simp; ring
  show f⁻¹ w = 1/a * w + -b/a
  have : f (f⁻¹ w) = f ((w - b)/a) := by rw [RelIso.apply_inv_self, hfy]
  rw [f.injective this]; field_simp; ring

end BS_aux

open BS_aux

open BrinSquier in
theorem solution {f g : ℝ ≃o ℝ} (hf : IsPLF f) (hg : IsPLF g) :
    SlopeAtBot (f * g * f⁻¹ * g⁻¹) 1 ∧ SlopeAtTop (f * g * f⁻¹ * g⁻¹) 1 := by
  have bot : ∀ {h : ℝ ≃o ℝ}, IsPLF h → ∃ a, SlopeAtBot h a := by
    intro h hh
    obtain ⟨M, hL, _⟩ := locAff_of_isPLF hh
    obtain ⟨a, b, hab⟩ := affine_on_ray hL (show M - 1 < M by linarith)
    exact ⟨a, b, M - 1, fun y hy => hab y (le_of_lt hy)⟩
  have top : ∀ {h : ℝ ≃o ℝ}, IsPLF h → ∃ a, SlopeAtTop h a := by
    intro h hh
    obtain ⟨M, _, hL⟩ := locAff_of_isPLF hh
    obtain ⟨a, b, hab⟩ := affine_on_ray_top hL (show -M < -M + 1 by linarith)
    exact ⟨a, b, -M + 1, fun y hy => hab y (le_of_lt hy)⟩
  obtain ⟨af, hafb⟩ := bot hf
  obtain ⟨ag, hagb⟩ := bot hg
  obtain ⟨cf, hcft⟩ := top hf
  obtain ⟨cg, hcgt⟩ := top hg
  have haf : 0 < af := slopeAtBot_pos hafb
  have hag : 0 < ag := slopeAtBot_pos hagb
  have hcf : 0 < cf := slopeAtTop_pos hcft
  have hcg : 0 < cg := slopeAtTop_pos hcgt
  constructor
  · have h1 : SlopeAtBot (f * g * f⁻¹ * g⁻¹) (af * ag * (1/af) * (1/ag)) :=
      slopeAtBot_mul (slopeAtBot_mul (slopeAtBot_mul hafb hagb) (slopeAtBot_inv hafb))
        (slopeAtBot_inv hagb)
    have hone : af * ag * (1/af) * (1/ag) = 1 := by field_simp
    rwa [hone] at h1
  · have h1 : SlopeAtTop (f * g * f⁻¹ * g⁻¹) (cf * cg * (1/cf) * (1/cg)) :=
      slopeAtTop_mul (slopeAtTop_mul (slopeAtTop_mul hcft hcgt) (slopeAtTop_inv hcft))
        (slopeAtTop_inv hcgt)
    have hone : cf * cg * (1/cf) * (1/cg) = 1 := by field_simp
    rwa [hone] at h1
