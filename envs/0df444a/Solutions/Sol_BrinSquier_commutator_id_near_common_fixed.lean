-- Prove2me | solution 1 for BrinSquier.commutator_id_near_common_fixed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-12T22:45:24.376499+00:00
-- url     : https://prove2.me/submissions/6c0c2773-20e3-497e-97c8-83f536c953b0

import Definitions.Def_BrinSquier
import Mathlib

namespace BS_all
open BrinSquier

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

/-- Local affineness on an open interval makes `f` affine on the whole interval. -/
theorem affine_on_Ioo {f : ℝ → ℝ} {p q : ℝ}
    (H : ∀ x ∈ Set.Ioo p q, ∃ ε > 0, ∃ a b : ℝ, ∀ y ∈ Set.Ioo (x - ε) (x + ε), f y = a * y + b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo p q) :
    ∃ a b : ℝ, ∀ y ∈ Set.Ioo p q, f y = a * y + b := by
  obtain ⟨e₀, he₀, a₀, b₀, h₀⟩ := H x₀ hx₀
  obtain ⟨hpx, hxq⟩ := hx₀
  refine ⟨a₀, b₀, ?_⟩
  -- LEFT: agreement on (p, x₀]
  have left : ∀ y ∈ Set.Ioc p x₀, f y = a₀ * y + b₀ := by
    set S : Set ℝ := {t : ℝ | p < t ∧ t ≤ x₀ ∧ ∀ z ∈ Set.Icc t x₀, f z = a₀ * z + b₀} with hS
    set t₁ := max ((p + x₀)/2) (x₀ - e₀/2) with ht₁
    have ht₁p : p < t₁ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have ht₁x : t₁ < x₀ := max_lt (by linarith) (by linarith)
    have ht₁e : x₀ - e₀/2 ≤ t₁ := le_max_right _ _
    have hbase : t₁ ∈ S :=
      ⟨ht₁p, le_of_lt ht₁x, fun z hz => h₀ z ⟨by linarith [hz.1], by linarith [hz.2]⟩⟩
    have hne : S.Nonempty := ⟨_, hbase⟩
    have hbdd : BddBelow S := ⟨p, fun z hz => le_of_lt hz.1⟩
    have hcp : sInf S = p := by
      by_contra hcne
      have hge : p ≤ sInf S := le_csInf hne (fun z hz => le_of_lt hz.1)
      have hgt : p < sInf S := lt_of_le_of_ne hge (Ne.symm hcne)
      set c := sInf S with hc
      have hcx : c ≤ t₁ := csInf_le hbdd hbase
      have hcq : c < q := by linarith
      obtain ⟨e, he, a, b, h⟩ := H c ⟨hgt, hcq⟩
      obtain ⟨t, htS, htlt⟩ := exists_lt_of_csInf_lt hne
        (show c < c + min e (x₀ - c) by
          have : 0 < min e (x₀ - c) := lt_min he (by linarith)
          linarith)
      have hct : c ≤ t := csInf_le hbdd htS
      have htx : t < x₀ := by have := min_le_right e (x₀ - c); linarith
      have hte : t < c + e := by have := min_le_left e (x₀ - c); linarith
      set u := min (c + e) x₀ with hu
      have htu : t < u := lt_min hte htx
      set pp := (t + u)/2 with hpp
      have htp : t < pp := by simp only [hpp]; linarith
      have hpu : pp < u := by simp only [hpp]; linarith
      have hpx2 : pp ≤ x₀ := le_of_lt (lt_of_lt_of_le hpu (min_le_right _ _))
      have hpe : pp < c + e := lt_of_lt_of_le hpu (min_le_left _ _)
      have e1 : f t = a₀ * t + b₀ := htS.2.2 t ⟨le_refl _, le_of_lt htx⟩
      have e2 : f pp = a₀ * pp + b₀ := htS.2.2 pp ⟨le_of_lt htp, hpx2⟩
      have e3 : f t = a * t + b := h t ⟨by linarith, by linarith⟩
      have e4 : f pp = a * pp + b := h pp ⟨by linarith, by linarith⟩
      obtain ⟨haa, hbb⟩ := affine_unique (ne_of_lt htp) (e3.symm.trans e1) (e4.symm.trans e2)
      set c' := max ((p + c)/2) (c - e/2) with hc'
      have hc'p : p < c' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have hc'c : c' < c := max_lt (by linarith) (by linarith)
      have hc'e : c - e/2 ≤ c' := le_max_right _ _
      have : c' ∈ S := by
        refine ⟨hc'p, by linarith, fun z hz => ?_⟩
        by_cases hzt : t ≤ z
        · exact htS.2.2 z ⟨hzt, hz.2⟩
        · replace hzt := not_le.mp hzt
          have := h z ⟨by linarith [hz.1], by linarith⟩
          rw [this, haa, hbb]
      have := csInf_le hbdd this
      linarith
    intro y hy
    obtain ⟨t, htS, hty⟩ := exists_lt_of_csInf_lt hne (by rw [hcp]; exact hy.1)
    exact htS.2.2 y ⟨le_of_lt hty, hy.2⟩
  -- RIGHT: agreement on [x₀, q)
  have right : ∀ y ∈ Set.Ico x₀ q, f y = a₀ * y + b₀ := by
    set S : Set ℝ := {t : ℝ | t < q ∧ x₀ ≤ t ∧ ∀ z ∈ Set.Icc x₀ t, f z = a₀ * z + b₀} with hS
    set t₁ := min ((q + x₀)/2) (x₀ + e₀/2) with ht₁
    have ht₁q : t₁ < q := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have ht₁x : x₀ < t₁ := lt_min (by linarith) (by linarith)
    have ht₁e : t₁ ≤ x₀ + e₀/2 := min_le_right _ _
    have hbase : t₁ ∈ S :=
      ⟨ht₁q, le_of_lt ht₁x, fun z hz => h₀ z ⟨by linarith [hz.1], by linarith [hz.2]⟩⟩
    have hne : S.Nonempty := ⟨_, hbase⟩
    have hbdd : BddAbove S := ⟨q, fun z hz => le_of_lt hz.1⟩
    have hcq : sSup S = q := by
      by_contra hcne
      have hle : sSup S ≤ q := csSup_le hne (fun z hz => le_of_lt hz.1)
      have hlt : sSup S < q := lt_of_le_of_ne hle hcne
      set c := sSup S with hc
      have hcx : t₁ ≤ c := le_csSup hbdd hbase
      have hcp2 : p < c := by linarith
      obtain ⟨e, he, a, b, h⟩ := H c ⟨hcp2, hlt⟩
      obtain ⟨t, htS, htlt⟩ := exists_lt_of_lt_csSup hne
        (show c - min e (c - x₀) < c by
          have : 0 < min e (c - x₀) := lt_min he (by linarith)
          linarith)
      have hct : t ≤ c := le_csSup hbdd htS
      have htx : x₀ < t := by have := min_le_right e (c - x₀); linarith
      have hte : c - e < t := by have := min_le_left e (c - x₀); linarith
      set u := max (c - e) x₀ with hu
      have hut : u < t := max_lt hte htx
      set pp := (u + t)/2 with hpp
      have hpt : pp < t := by simp only [hpp]; linarith
      have hup : u < pp := by simp only [hpp]; linarith
      have hpx2 : x₀ ≤ pp := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hup)
      have hpe : c - e < pp := lt_of_le_of_lt (le_max_left _ _) hup
      have e1 : f t = a₀ * t + b₀ := htS.2.2 t ⟨le_of_lt htx, le_refl _⟩
      have e2 : f pp = a₀ * pp + b₀ := htS.2.2 pp ⟨hpx2, le_of_lt hpt⟩
      have e3 : f t = a * t + b := h t ⟨by linarith, by linarith⟩
      have e4 : f pp = a * pp + b := h pp ⟨by linarith, by linarith⟩
      obtain ⟨haa, hbb⟩ := affine_unique (ne_of_gt hpt) (e3.symm.trans e1) (e4.symm.trans e2)
      set c' := min ((q + c)/2) (c + e/2) with hc'
      have hc'q : c' < q := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hc'c : c < c' := lt_min (by linarith) (by linarith)
      have hc'e : c' ≤ c + e/2 := min_le_right _ _
      have : c' ∈ S := by
        refine ⟨hc'q, by linarith, fun z hz => ?_⟩
        by_cases hzt : z ≤ t
        · exact htS.2.2 z ⟨hz.1, hzt⟩
        · replace hzt := not_le.mp hzt
          have := h z ⟨by linarith, by linarith [hz.2]⟩
          rw [this, haa, hbb]
      have := le_csSup hbdd this
      linarith
    intro y hy
    obtain ⟨t, htS, hty⟩ := exists_lt_of_lt_csSup hne (by rw [hcq]; exact hy.2)
    exact htS.2.2 y ⟨hy.1, le_of_lt hty⟩
  intro y hy
  by_cases hle : y ≤ x₀
  · exact left y ⟨hy.1, hle⟩
  · exact right y ⟨le_of_lt (not_le.mp hle), hy.2⟩

/-- `f` is linear about `t` with slope `s`, on the right out to radius `r`. -/
def RLin (f : ℝ ≃o ℝ) (t s r : ℝ) : Prop := ∀ y ∈ Set.Ioo t (t + r), f y = s * (y - t) + t

/-- Same, on the left. -/
def LLin (f : ℝ ≃o ℝ) (t s r : ℝ) : Prop := ∀ y ∈ Set.Ioo (t - r) t, f y = s * (y - t) + t

lemma rlin_pos {f : ℝ ≃o ℝ} {t s r : ℝ} (hr : 0 < r) (h : RLin f t s r) : 0 < s := by
  have h1 : f (t + r/3) = s * (r/3) + t := by
    have := h (t + r/3) ⟨by linarith, by linarith⟩; rw [this]; ring
  have h2 : f (t + 2*r/3) = s * (2*r/3) + t := by
    have := h (t + 2*r/3) ⟨by linarith, by linarith⟩; rw [this]; ring
  have : f (t + r/3) < f (t + 2*r/3) := f.strictMono (by linarith)
  rw [h1, h2] at this; nlinarith [this, hr]

lemma llin_pos {f : ℝ ≃o ℝ} {t s r : ℝ} (hr : 0 < r) (h : LLin f t s r) : 0 < s := by
  have h1 : f (t - 2*r/3) = s * (-(2*r/3)) + t := by
    have := h (t - 2*r/3) ⟨by linarith, by linarith⟩; rw [this]; ring
  have h2 : f (t - r/3) = s * (-(r/3)) + t := by
    have := h (t - r/3) ⟨by linarith, by linarith⟩; rw [this]; ring
  have : f (t - 2*r/3) < f (t - r/3) := f.strictMono (by linarith)
  rw [h1, h2] at this; nlinarith [this, hr]

lemma rlin_mul {f g : ℝ ≃o ℝ} {t a c rf rg : ℝ} (hrf : 0 < rf) (hrg : 0 < rg)
    (hf : RLin f t a rf) (hg : RLin g t c rg) :
    RLin (f * g) t (a * c) (min rg (rf / c)) := by
  have hc : 0 < c := rlin_pos hrg hg
  intro y hy
  obtain ⟨hy1, hy2⟩ := hy
  have hm1 : min rg (rf/c) ≤ rg := min_le_left _ _
  have hm2 : min rg (rf/c) ≤ rf/c := min_le_right _ _
  have hpos : 0 < y - t := by linarith
  have hgy : g y = c * (y - t) + t := hg y ⟨hy1, by linarith⟩
  have hlt : y - t < rf / c := by linarith
  rw [lt_div_iff₀ hc] at hlt
  have hlt2 : c * (y - t) < rf := by linarith [mul_comm c (y - t)]
  have hmem : g y ∈ Set.Ioo t (t + rf) := by
    rw [hgy]; exact ⟨by nlinarith, by linarith⟩
  show f (g y) = a * c * (y - t) + t
  rw [hf _ hmem, hgy]; ring

lemma llin_mul {f g : ℝ ≃o ℝ} {t a c rf rg : ℝ} (hrf : 0 < rf) (hrg : 0 < rg)
    (hf : LLin f t a rf) (hg : LLin g t c rg) :
    LLin (f * g) t (a * c) (min rg (rf / c)) := by
  have hc : 0 < c := llin_pos hrg hg
  intro y hy
  obtain ⟨hy1, hy2⟩ := hy
  have hm1 : min rg (rf/c) ≤ rg := min_le_left _ _
  have hm2 : min rg (rf/c) ≤ rf/c := min_le_right _ _
  have hneg : y - t < 0 := by linarith
  have hgy : g y = c * (y - t) + t := hg y ⟨by linarith, hy2⟩
  have hlt : t - y < rf / c := by linarith
  rw [lt_div_iff₀ hc] at hlt
  have hlt2 : -rf < c * (y - t) := by nlinarith [mul_comm c (t - y)]
  have hmem : g y ∈ Set.Ioo (t - rf) t := by
    rw [hgy]; exact ⟨by linarith, by nlinarith⟩
  show f (g y) = a * c * (y - t) + t
  rw [hf _ hmem, hgy]; ring

lemma rlin_inv {f : ℝ ≃o ℝ} {t a r : ℝ} (hr : 0 < r) (hf : RLin f t a r) :
    RLin f⁻¹ t (1/a) (a * r) := by
  have ha : 0 < a := rlin_pos hr hf
  have hane : a ≠ 0 := ne_of_gt ha
  intro w hw
  obtain ⟨hw1, hw2⟩ := hw
  have hq : 0 < (w - t)/a := div_pos (by linarith) ha
  have hq2 : (w - t)/a < r := by rw [div_lt_iff₀ ha]; linarith
  have hy : (w - t)/a + t ∈ Set.Ioo t (t + r) := ⟨by linarith, by linarith⟩
  have hfy : f ((w - t)/a + t) = w := by
    rw [hf _ hy]; field_simp; ring
  have heq : f (f⁻¹ w) = f ((w - t)/a + t) := by rw [RelIso.apply_inv_self, hfy]
  show f⁻¹ w = 1/a * (w - t) + t
  rw [f.injective heq]; field_simp

lemma llin_inv {f : ℝ ≃o ℝ} {t a r : ℝ} (hr : 0 < r) (hf : LLin f t a r) :
    LLin f⁻¹ t (1/a) (a * r) := by
  have ha : 0 < a := llin_pos hr hf
  have hane : a ≠ 0 := ne_of_gt ha
  intro w hw
  obtain ⟨hw1, hw2⟩ := hw
  have hq : (w - t)/a < 0 := div_neg_of_neg_of_pos (by linarith) ha
  have hq2 : -r < (w - t)/a := by
    rw [lt_div_iff₀ ha]; nlinarith
  have hy : (w - t)/a + t ∈ Set.Ioo (t - r) t := ⟨by linarith, by linarith⟩
  have hfy : f ((w - t)/a + t) = w := by
    rw [hf _ hy]; field_simp; ring
  have heq : f (f⁻¹ w) = f ((w - t)/a + t) := by rw [RelIso.apply_inv_self, hfy]
  show f⁻¹ w = 1/a * (w - t) + t
  rw [f.injective heq]; field_simp

/-- Local linearity about `t` with the radius existentially quantified. -/
def RLin' (f : ℝ ≃o ℝ) (t s : ℝ) : Prop := ∃ r > 0, RLin f t s r
def LLin' (f : ℝ ≃o ℝ) (t s : ℝ) : Prop := ∃ r > 0, LLin f t s r

lemma rlin'_pos {f : ℝ ≃o ℝ} {t s : ℝ} (h : RLin' f t s) : 0 < s := by
  obtain ⟨r, hr, h⟩ := h; exact rlin_pos hr h

lemma llin'_pos {f : ℝ ≃o ℝ} {t s : ℝ} (h : LLin' f t s) : 0 < s := by
  obtain ⟨r, hr, h⟩ := h; exact llin_pos hr h

lemma rlin'_mul {f g : ℝ ≃o ℝ} {t a c : ℝ} (hf : RLin' f t a) (hg : RLin' g t c) :
    RLin' (f * g) t (a * c) := by
  obtain ⟨rf, hrf, hf⟩ := hf
  obtain ⟨rg, hrg, hg⟩ := hg
  have hc : 0 < c := rlin_pos hrg hg
  exact ⟨_, lt_min hrg (div_pos hrf hc), rlin_mul hrf hrg hf hg⟩

lemma llin'_mul {f g : ℝ ≃o ℝ} {t a c : ℝ} (hf : LLin' f t a) (hg : LLin' g t c) :
    LLin' (f * g) t (a * c) := by
  obtain ⟨rf, hrf, hf⟩ := hf
  obtain ⟨rg, hrg, hg⟩ := hg
  have hc : 0 < c := llin_pos hrg hg
  exact ⟨_, lt_min hrg (div_pos hrf hc), llin_mul hrf hrg hf hg⟩

lemma rlin'_inv {f : ℝ ≃o ℝ} {t a : ℝ} (hf : RLin' f t a) : RLin' f⁻¹ t (1/a) := by
  obtain ⟨r, hr, hf⟩ := hf
  exact ⟨_, mul_pos (rlin_pos hr hf) hr, rlin_inv hr hf⟩

lemma llin'_inv {f : ℝ ≃o ℝ} {t a : ℝ} (hf : LLin' f t a) : LLin' f⁻¹ t (1/a) := by
  obtain ⟨r, hr, hf⟩ := hf
  exact ⟨_, mul_pos (llin_pos hr hf) hr, llin_inv hr hf⟩

open BrinSquier

/-- A punctured neighbourhood of `t` free of a given finite set. -/
lemma exists_punctured {B : Finset ℝ} (t : ℝ) :
    ∃ δ > 0, ∀ x, x ≠ t → |x - t| < δ → x ∉ (B : Set ℝ) := by
  have hclosed : IsClosed (((B.erase t : Finset ℝ)) : Set ℝ) := (B.erase t).finite_toSet.isClosed
  have hnot : t ∉ (((B.erase t : Finset ℝ)) : Set ℝ) := by simp
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl t hnot
  refine ⟨δ, hδ, fun x hne habs hmem => ?_⟩
  have hb : x ∈ Metric.ball t δ := by
    rw [Metric.mem_ball, Real.dist_eq]; exact habs
  exact (hball hb) (by
    simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]
    exact ⟨hmem, hne⟩)

lemma rlin_of_isPLF{f : ℝ ≃o ℝ} (hf : IsPLF f) {t : ℝ} (htf : f t = t) :
    ∃ a r : ℝ, 0 < r ∧ RLin f t a r := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨δ, hδ, hpunc⟩ := exists_punctured (B := B) t
  have H : ∀ x ∈ Set.Ioo t (t + δ), ∃ ε > 0, ∃ a b : ℝ,
      ∀ y ∈ Set.Ioo (x - ε) (x + ε), f y = a * y + b := by
    intro x hx
    refine hB x (hpunc x (ne_of_gt hx.1) ?_)
    rw [abs_lt]; constructor <;> [linarith [hx.1]; linarith [hx.2]]
  obtain ⟨a, b, hab⟩ := affine_on_Ioo H (x₀ := t + δ/2) ⟨by linarith, by linarith⟩
  have heqon : Set.EqOn (fun y => f y) (fun y => a * y + b) (Set.Ioo t (t + δ)) :=
    fun y hy => hab y hy
  have hclos := heqon.closure (OrderIso.continuous f) (by continuity)
  have htmem : t ∈ closure (Set.Ioo t (t + δ)) := by
    rw [closure_Ioo (by linarith : t ≠ t + δ)]; exact ⟨le_refl _, by linarith⟩
  have hval : f t = a * t + b := hclos htmem
  rw [htf] at hval
  have hb : b = t - a * t := by linarith
  exact ⟨a, δ, hδ, fun y hy => by rw [hab y hy, hb]; ring⟩

lemma llin_of_isPLF {f : ℝ ≃o ℝ} (hf : IsPLF f) {t : ℝ} (htf : f t = t) :
    ∃ a r : ℝ, 0 < r ∧ LLin f t a r := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨δ, hδ, hpunc⟩ := exists_punctured (B := B) t
  have H : ∀ x ∈ Set.Ioo (t - δ) t, ∃ ε > 0, ∃ a b : ℝ,
      ∀ y ∈ Set.Ioo (x - ε) (x + ε), f y = a * y + b := by
    intro x hx
    refine hB x (hpunc x (ne_of_lt hx.2) ?_)
    rw [abs_lt]; constructor <;> [linarith [hx.1]; linarith [hx.2]]
  obtain ⟨a, b, hab⟩ := affine_on_Ioo H (x₀ := t - δ/2) ⟨by linarith, by linarith⟩
  have heqon : Set.EqOn (fun y => f y) (fun y => a * y + b) (Set.Ioo (t - δ) t) :=
    fun y hy => hab y hy
  have hclos := heqon.closure (OrderIso.continuous f) (by continuity)
  have htmem : t ∈ closure (Set.Ioo (t - δ) t) := by
    rw [closure_Ioo (by linarith : t - δ ≠ t)]; exact ⟨by linarith, le_refl _⟩
  have hval : f t = a * t + b := hclos htmem
  rw [htf] at hval
  have hb : b = t - a * t := by linarith
  exact ⟨a, δ, hδ, fun y hy => by rw [hab y hy, hb]; ring⟩

end BS_all

open BS_all BrinSquier in
theorem solution {f g : ℝ ≃o ℝ} (hf : IsPLF f) (hg : IsPLF g)
    {t : ℝ} (htf : f t = t) (htg : g t = t) :
    ∃ ε > 0, ∀ y ∈ Set.Ioo (t - ε) (t + ε), (f * g * f⁻¹ * g⁻¹) y = y := by
  have hfi : f⁻¹ t = t := f.injective (by rw [RelIso.apply_inv_self, htf])
  have hgi : g⁻¹ t = t := g.injective (by rw [RelIso.apply_inv_self, htg])
  obtain ⟨af, rf, hrf, hRf⟩ := rlin_of_isPLF hf htf
  obtain ⟨ag, rg, hrg, hRg⟩ := rlin_of_isPLF hg htg
  obtain ⟨cf, sf, hsf, hLf⟩ := llin_of_isPLF hf htf
  obtain ⟨cg, sg, hsg, hLg⟩ := llin_of_isPLF hg htg
  have Rf : RLin' f t af := ⟨rf, hrf, hRf⟩
  have Rg : RLin' g t ag := ⟨rg, hrg, hRg⟩
  have Lf : LLin' f t cf := ⟨sf, hsf, hLf⟩
  have Lg : LLin' g t cg := ⟨sg, hsg, hLg⟩
  have hafp : 0 < af := rlin'_pos Rf
  have hagp : 0 < ag := rlin'_pos Rg
  have hcfp : 0 < cf := llin'_pos Lf
  have hcgp : 0 < cg := llin'_pos Lg
  have hR : RLin' (f * g * f⁻¹ * g⁻¹) t (af * ag * (1/af) * (1/ag)) :=
    rlin'_mul (rlin'_mul (rlin'_mul Rf Rg) (rlin'_inv Rf)) (rlin'_inv Rg)
  have hL : LLin' (f * g * f⁻¹ * g⁻¹) t (cf * cg * (1/cf) * (1/cg)) :=
    llin'_mul (llin'_mul (llin'_mul Lf Lg) (llin'_inv Lf)) (llin'_inv Lg)
  have hone : af * ag * (1/af) * (1/ag) = 1 := by field_simp
  have hone' : cf * cg * (1/cf) * (1/cg) = 1 := by field_simp
  rw [hone] at hR
  rw [hone'] at hL
  obtain ⟨r, hr, hRr⟩ := hR
  obtain ⟨s, hs, hLs⟩ := hL
  refine ⟨min r s, lt_min hr hs, fun y hy => ?_⟩
  have hmr : min r s ≤ r := min_le_left _ _
  have hms : min r s ≤ s := min_le_right _ _
  rcases lt_trichotomy y t with hlt | heq | hgt
  · have := hLs y ⟨by linarith [hy.1], hlt⟩
    rw [this]; ring
  · subst heq
    show f (g (f⁻¹ (g⁻¹ y))) = y
    rw [hgi, hfi, htg, htf]
  · have := hRr y ⟨hgt, by linarith [hy.2]⟩
    rw [this]; ring
