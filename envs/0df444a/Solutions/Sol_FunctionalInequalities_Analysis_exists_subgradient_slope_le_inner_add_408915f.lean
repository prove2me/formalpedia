-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_subgradient_slope_le_inner_add_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:00:29.456543+00:00
-- url     : https://prove2.me/submissions/81befe1a-d1d1-4729-97df-b90ee10d044f

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section LT5ASubgradientMaxFormula
open scoped RealInnerProductSpace
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Max formula for the one-sided directional derivative of a finite convex function** (weak
Letwin route: "singleton subdifferential ⇒ C¹"): for a convex `u : E → ℝ` on a
finite-dimensional inner product space, every point `x` and every direction `v`, there is a
subgradient `g` of `u` at `x` whose pairing with `v` is the right derivative
`inf_{t>0} (u(x + t v) - u(x))/t`: it is a subgradient and the difference quotients come
arbitrarily close to `⟪g, v⟫` (they are `≥ ⟪g, v⟫` by the subgradient inequality). -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (x v : E) :
    ∃ g : E, (∀ y, u x + ⟪g, y - x⟫ ≤ u y) ∧
      ∀ ε > 0, ∃ t > 0, (u (x + t • v) - u x) / t ≤ ⟪g, v⟫ + ε := by
  let slope : E → ℝ → ℝ := fun w t => (u (x + t • w) - u x) / t
  let p : E → ℝ := fun w =>
    sInf (Set.range (fun t : {t : ℝ // 0 < t} => slope w t))
  have hconvex :
      ∀ {z₁ z₂ : E} {a b : ℝ}, z₁ ∈ Set.univ → z₂ ∈ Set.univ →
        0 ≤ a → 0 ≤ b → a + b = 1 →
          u (a • z₁ + b • z₂) ≤ a * u z₁ + b * u z₂ := by
    intro z₁ z₂ a b hz₁ hz₂ ha hb hab
    exact hconv.2 hz₁ hz₂ ha hb hab
  have hslope_mono :
      ∀ {w : E} {a b : ℝ}, 0 < a → a ≤ b → slope w a ≤ slope w b := by
    intro w a b ha hab
    have hb : 0 < b := lt_of_lt_of_le ha hab
    have hab0 : 0 ≤ a / b := div_nonneg ha.le hb.le
    have hab1 : 0 ≤ 1 - a / b := sub_nonneg.mpr ((div_le_one hb).2 hab)
    have hsum : a / b + (1 - a / b) = 1 := by
      abel
    have hab' : (a / b) * b = a := div_mul_cancel₀ a (ne_of_gt hb)
    have heq :
        (a / b) • (x + b • w) + (1 - a / b) • x = x + a • w := by
      calc
        (a / b) • (x + b • w) + (1 - a / b) • x =
            (a / b + (1 - a / b)) • x + (a / b * b) • w := by
              module
        _ = x + a • w := by rw [hsum, hab', one_smul]
    have hc := hconvex (z₁ := x + b • w) (z₂ := x) (by simp) (by simp)
      hab0 hab1 hsum
    rw [heq] at hc
    have hc' :
        b * (u (x + a • w) - u x) ≤ a * (u (x + b • w) - u x) := by
      field_simp [ne_of_gt hb] at hc
      nlinarith [hc]
    apply (div_le_div_iff₀ ha hb).2
    nlinarith [hc']
  have hslope_lower :
      ∀ {w : E} {t : ℝ}, 0 < t → u x - u (x - w) ≤ slope w t := by
    intro w t ht
    have htp : 0 < t + 1 := by linarith
    have ha : 0 ≤ t / (t + 1) := div_nonneg ht.le htp.le
    have hb : 0 ≤ (1 : ℝ) / (t + 1) := by positivity
    have hsum : t / (t + 1) + (1 : ℝ) / (t + 1) = 1 := by
      calc
        t / (t + 1) + (1 : ℝ) / (t + 1) =
            (t + 1) / (t + 1) := by
              ring
        _ = 1 := div_self (ne_of_gt htp)
    have hcoef : (1 : ℝ) / (t + 1) * t = t / (t + 1) := by
      ring
    have heq :
        (t / (t + 1)) • (x - w) +
            ((1 : ℝ) / (t + 1)) • (x + t • w) = x := by
      calc
        (t / (t + 1)) • (x - w) +
              ((1 : ℝ) / (t + 1)) • (x + t • w) =
            (t / (t + 1) + (1 : ℝ) / (t + 1)) • x +
              (-(t / (t + 1)) + (1 : ℝ) / (t + 1) * t) • w := by
                module
        _ = x := by rw [hsum, hcoef]; simp
    have hc := hconvex (z₁ := x - w) (z₂ := x + t • w) (by simp) (by simp)
      ha hb hsum
    rw [heq] at hc
    have hc' : t * (u x - u (x - w)) ≤ u (x + t • w) - u x := by
      field_simp [ne_of_gt htp] at hc
      nlinarith [hc]
    apply (le_div_iff₀ ht).2
    nlinarith [hc']
  have hnonempty (w : E) :
      (Set.range (fun t : {t : ℝ // 0 < t} => slope w t)).Nonempty := by
    let t : {t : ℝ // 0 < t} := ⟨1, by norm_num⟩
    exact ⟨slope w t, ⟨t, rfl⟩⟩
  have hbdd (w : E) :
      BddBelow (Set.range (fun t : {t : ℝ // 0 < t} => slope w t)) := by
    refine ⟨u x - u (x - w), ?_⟩
    rintro z ⟨t, rfl⟩
    exact hslope_lower t.property
  have hp_lower : ∀ w : E, u x - u (x - w) ≤ p w := by
    intro w
    change u x - u (x - w) ≤
      sInf (Set.range (fun t : {t : ℝ // 0 < t} => slope w t))
    apply le_csInf (hnonempty w)
    rintro z ⟨t, rfl⟩
    exact hslope_lower t.property
  have hp_le : ∀ (w : E) (t : {t : ℝ // 0 < t}), p w ≤ slope w t := by
    intro w t
    change sInf (Set.range (fun t : {t : ℝ // 0 < t} => slope w t)) ≤ slope w t
    exact csInf_le (hbdd w) ⟨t, rfl⟩
  have hp_zero : p 0 = 0 := by
    apply le_antisymm
    · simpa [slope] using hp_le 0 ⟨1, by norm_num⟩
    · simpa [slope] using hp_lower 0
  have hslope_scale :
      ∀ {w : E} {c t : ℝ}, 0 < c → 0 < t →
        slope (c • w) t = c * slope w (c * t) := by
    intro w c t hc ht
    change
      (u (x + t • (c • w)) - u x) / t =
        c * ((u (x + (c * t) • w) - u x) / (c * t))
    rw [smul_smul, mul_comm t c]
    have hct : 0 < c * t := mul_pos hc ht
    field_simp [ne_of_gt hc, ne_of_gt ht, ne_of_gt hct]
  have hp_scale :
      ∀ {w : E} {c : ℝ}, 0 < c → p (c • w) = c * p w := by
    intro w c hc
    have h₁ : p (c • w) / c ≤ p w := by
      change p (c • w) / c ≤
        sInf (Set.range (fun t : {t : ℝ // 0 < t} => slope w t))
      apply le_csInf (hnonempty w)
      rintro z ⟨t, rfl⟩
      let r : {t : ℝ // 0 < t} := ⟨(t : ℝ) / c, div_pos t.property hc⟩
      have harg : c * ((t : ℝ) / c) = (t : ℝ) := by
        field_simp [ne_of_gt hc]
      calc
        p (c • w) / c ≤ slope (c • w) r / c :=
          div_le_div_of_nonneg_right (hp_le (c • w) r) hc.le
        _ = slope w t := by
          rw [hslope_scale hc r.property, harg]
          apply (div_eq_iff (ne_of_gt hc)).2
          ring
    have h₁' : p (c • w) ≤ c * p w := by
      have h := (div_le_iff₀ hc).1 h₁
      simpa [mul_comm] using h
    have h₂ : c * p w ≤ p (c • w) := by
      change c * p w ≤
        sInf (Set.range (fun t : {t : ℝ // 0 < t} => slope (c • w) t))
      apply le_csInf (hnonempty (c • w))
      rintro z ⟨t, rfl⟩
      let r : {t : ℝ // 0 < t} := ⟨c * (t : ℝ), mul_pos hc t.property⟩
      calc
        c * p w ≤ c * slope w r :=
          mul_le_mul_of_nonneg_left (hp_le w r) hc.le
        _ = slope (c • w) t := by
          rw [hslope_scale hc t.property]
    exact le_antisymm h₁' h₂
  have slope_add :
      ∀ {w₁ w₂ : E} {t : ℝ}, 0 < t →
        slope (w₁ + w₂) t ≤
          slope w₁ (2 * t) + slope w₂ (2 * t) := by
    intro w₁ w₂ t ht
    have heq :
        (1 / 2 : ℝ) • (x + (2 * t) • w₁) +
            (1 / 2 : ℝ) • (x + (2 * t) • w₂) =
          x + t • (w₁ + w₂) := by
      module
    have hc := hconvex (z₁ := x + (2 * t) • w₁) (z₂ := x + (2 * t) • w₂)
      (by simp) (by simp)
      (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    rw [heq] at hc
    dsimp [slope]
    apply (div_le_iff₀ ht).2
    have hid :
        ((u (x + (2 * t) • w₁) - u x) / (2 * t) +
            (u (x + (2 * t) • w₂) - u x) / (2 * t)) * t =
          (u (x + (2 * t) • w₁) + u (x + (2 * t) • w₂) - 2 * u x) / 2 := by
      field_simp [ne_of_gt ht]
      ring
    rw [hid]
    linarith [hc]
  have hexists :
      ∀ (w : E) {ε : ℝ}, 0 < ε →
        ∃ t : {t : ℝ // 0 < t}, slope w t < p w + ε := by
    intro w ε hε
    by_contra hnot
    have hforall : ∀ t : {t : ℝ // 0 < t}, p w + ε ≤ slope w t := by
      intro t
      exact le_of_not_gt (fun hlt => hnot ⟨t, hlt⟩)
    have hp' : p w + ε ≤ p w := by
      change p w + ε ≤
        sInf (Set.range (fun t : {t : ℝ // 0 < t} => slope w t))
      apply le_csInf (hnonempty w)
      rintro z ⟨t, rfl⟩
      exact hforall t
    linarith
  have hp_add : ∀ w₁ w₂ : E, p (w₁ + w₂) ≤ p w₁ + p w₂ := by
    intro w₁ w₂
    by_contra h
    have hlt : p w₁ + p w₂ < p (w₁ + w₂) := lt_of_not_ge h
    let ε : ℝ := (p (w₁ + w₂) - p w₁ - p w₂) / 4
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    obtain ⟨t₁, ht₁⟩ := hexists w₁ hε
    obtain ⟨t₂, ht₂⟩ := hexists w₂ hε
    have htmin : 0 < min (t₁ : ℝ) (t₂ : ℝ) :=
      lt_min t₁.property t₂.property
    let t : {t : ℝ // 0 < t} :=
      ⟨min (t₁ : ℝ) t₂ / 2, div_pos htmin (by norm_num)⟩
    have h2t₁ : 2 * (t : ℝ) ≤ (t₁ : ℝ) := by
      dsimp [t]
      linarith [min_le_left (t₁ : ℝ) t₂]
    have h2t₂ : 2 * (t : ℝ) ≤ (t₂ : ℝ) := by
      dsimp [t]
      linarith [min_le_right (t₁ : ℝ) t₂]
    have hpos : 0 < 2 * (t : ℝ) := mul_pos (by norm_num) t.property
    have h₁ := hslope_mono (w := w₁) (a := 2 * (t : ℝ)) (b := t₁)
      hpos h2t₁
    have h₂ := hslope_mono (w := w₂) (a := 2 * (t : ℝ)) (b := t₂)
      hpos h2t₂
    have hsum := slope_add (w₁ := w₁) (w₂ := w₂) t.property
    have hp := hp_le (w₁ + w₂) t
    have hbound :
        p (w₁ + w₂) < p w₁ + p w₂ + 2 * ε := by
      calc
        p (w₁ + w₂) ≤ slope (w₁ + w₂) t := hp
        _ ≤ slope w₁ (2 * (t : ℝ)) + slope w₂ (2 * (t : ℝ)) := hsum
        _ ≤ slope w₁ (t₁ : ℝ) + slope w₂ (t₂ : ℝ) := add_le_add h₁ h₂
        _ < (p w₁ + ε) + (p w₂ + ε) := add_lt_add ht₁ ht₂
        _ = p w₁ + p w₂ + 2 * ε := by ring
    dsimp [ε] at hε hbound ⊢
    linarith
  by_cases hv : v = 0
  · let f : E →ₗ.[ℝ] ℝ := (0 : E →ₗ[ℝ] ℝ).toPMap ⊥
    have hf : ∀ z : f.domain, f z ≤ p z := by
      intro z
      have hz : (z : E) = 0 := by
        have hz' : (z : E) ∈ (⊥ : Submodule ℝ E) := by
          exact z.property
        simpa only [Submodule.mem_bot] using hz'
      have hz'' : z = 0 := Subtype.ext hz
      rw [hz'']
      simp [f, hp_zero]
    obtain ⟨ℓ, hℓf, hℓp⟩ :=
      exists_extension_of_le_sublinear f p
        (fun c hc w => hp_scale (w := w) hc)
        (fun w₁ w₂ => hp_add w₁ w₂) hf
    let L : E →L[ℝ] ℝ :=
      { toLinearMap := ℓ
        cont := LinearMap.continuous_of_finiteDimensional ℓ }
    let g : E := (InnerProductSpace.toDual ℝ E).symm L
    have hpair : ∀ w : E, ⟪g, w⟫ = ℓ w := by
      intro w
      change inner ℝ ((InnerProductSpace.toDual ℝ E).symm L) w = ℓ w
      calc
        inner ℝ ((InnerProductSpace.toDual ℝ E).symm L) w = L w :=
          InnerProductSpace.toDual_symm_apply
        _ = ℓ w := rfl
    refine ⟨g, ?_, ?_⟩
    · intro y
      have hp₁ := hp_le (y - x) ⟨1, by norm_num⟩
      have hq : p (y - x) ≤ u y - u x := by
        have hq' := hp₁
        change p (y - x) ≤
          (u (x + 1 • (y - x)) - u x) / 1 at hq'
        rw [one_smul, div_one] at hq'
        have heq : x + (y - x) = y := by abel
        rw [heq] at hq'
        exact hq'
      have hℓ := hℓp (y - x)
      rw [← hpair] at hℓ
      linarith
    · intro ε hε
      refine ⟨1, by norm_num, ?_⟩
      have hg0 : ⟪g, (0 : E)⟫ = 0 := by
        rw [hpair]
        exact ℓ.map_zero
      simp only [hv, smul_zero, add_zero, sub_self, zero_div, hg0, add_zero]
      linarith
  · let f : E →ₗ.[ℝ] ℝ :=
      LinearPMap.mkSpanSingleton v (p v) hv
    have hf : ∀ z : f.domain, f z ≤ p z := by
      intro z
      have hzdom : (z : E) ∈ ℝ ∙ v := z.property
      rcases Submodule.mem_span_singleton.mp hzdom with ⟨c, hc⟩
      let z₀ : f.domain :=
        ⟨v, Submodule.mem_span_singleton.mpr ⟨1, by simp⟩⟩
      have hz : z = c • z₀ := by
        apply Subtype.ext
        change (z : E) = c • v
        exact hc.symm
      have hf₀ : f z₀ = p v := by
        change (LinearPMap.mkSpanSingleton v (p v) hv) ⟨v, _⟩ = p v
        exact LinearPMap.mkSpanSingleton_apply ℝ ℝ hv (p v)
      rw [hz, f.map_smul, hf₀]
      change c * p v ≤ p (c • v)
      rcases lt_trichotomy c 0 with hcneg | rfl | hcpos
      · have hzero : 0 ≤ p (c • v) + p ((-c) • v) := by
          have h := hp_add (c • v) ((-c) • v)
          have hcv : c • v + (-c) • v = 0 := by module
          rw [hcv, hp_zero] at h
          exact h
        have hpc : p (c • v) = (-c) * p (-v) := by
          have heq : c • v = (-c) • (-v) := by module
          rw [heq, hp_scale (w := -v) (c := -c) (neg_pos.mpr hcneg)]
        have hpneg : p ((-c) • v) = (-c) * p v :=
          hp_scale (w := v) (c := -c) (neg_pos.mpr hcneg)
        rw [hpc, hpneg] at hzero
        calc
          c * p v = -((-c) * p v) := by ring
          _ ≤ (-c) * p (-v) := by linarith
          _ = p (c • v) := hpc.symm
      · simp [hp_zero]
      · rw [hp_scale (w := v) (c := c) hcpos]
    obtain ⟨ℓ, hℓf, hℓp⟩ :=
      exists_extension_of_le_sublinear f p
        (fun c hc w => hp_scale (w := w) hc)
        (fun w₁ w₂ => hp_add w₁ w₂) hf
    let L : E →L[ℝ] ℝ :=
      { toLinearMap := ℓ
        cont := LinearMap.continuous_of_finiteDimensional ℓ }
    let g : E := (InnerProductSpace.toDual ℝ E).symm L
    have hpair : ∀ w : E, ⟪g, w⟫ = ℓ w := by
      intro w
      change inner ℝ ((InnerProductSpace.toDual ℝ E).symm L) w = ℓ w
      calc
        inner ℝ ((InnerProductSpace.toDual ℝ E).symm L) w = L w :=
          InnerProductSpace.toDual_symm_apply
        _ = ℓ w := rfl
    have hℓv : ℓ v = p v := by
      let z₀ : f.domain :=
        ⟨v, Submodule.mem_span_singleton.mpr ⟨1, by simp⟩⟩
      have hf₀ : f z₀ = p v := by
        change (LinearPMap.mkSpanSingleton v (p v) hv) ⟨v, _⟩ = p v
        exact LinearPMap.mkSpanSingleton_apply ℝ ℝ hv (p v)
      change ℓ v = p v
      calc
        ℓ v = ℓ (z₀ : E) := rfl
        _ = f z₀ := hℓf z₀
        _ = p v := hf₀
    refine ⟨g, ?_, ?_⟩
    · intro y
      have hp₁ := hp_le (y - x) ⟨1, by norm_num⟩
      have hq : p (y - x) ≤ u y - u x := by
        have hq' := hp₁
        change p (y - x) ≤
          (u (x + 1 • (y - x)) - u x) / 1 at hq'
        rw [one_smul, div_one] at hq'
        have heq : x + (y - x) = y := by abel
        rw [heq] at hq'
        exact hq'
      have hℓ := hℓp (y - x)
      rw [← hpair] at hℓ
      linarith
    · intro ε hε
      obtain ⟨t, ht⟩ := hexists v hε
      refine ⟨(t : ℝ), t.property, ?_⟩
      have hlt : slope v t < p v + ε := ht
      have heq : p v + ε = ⟪g, v⟫ + ε := by
        rw [← hℓv, hpair]
      dsimp [slope] at hlt
      exact le_of_lt (heq ▸ hlt)
