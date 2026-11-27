-- Prove2me | solution 1 for DriftVarCtrl.FixedLB.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:40:07.055422+00:00
-- url     : https://prove2.me/submissions/abd79533-df8d-4876-81bc-1a94e47c11b3

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_FreeModel
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_Thresholds

open DriftVarCtrl
open DriftVarCtrl.FixedLB
open DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB

/-- Theorem 3, corrected on two boundary segments (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), pp. 19–20, (21)–(24); proof
pp. EC-27–EC-28). With a free lower boundary, it is optimal for the entrepreneur to abandon early
(some optimal stopping interval policy stops at a level `z₀ > 0`) if and only if
(a′) `h₁ > h⁺₁` and `h₂ ≥ hᵀ₂`, or (b′) `h₁ ≥ hᵀ₁` and `h₂ > h⁺₂`, or
(c) `h₁ ∈ (h⁺₁, hᵀ₁)`, `h₂ ∈ (h⁺₂, hᵀ₂)` and `ξ_U(h₁, h₂, w) < M`.

Formalization Note: the page prints (a) with `h₂ > hᵀ₂` and (b) with `h₁ > hᵀ₁`. On the segments
`h₂ = hᵀ₂`, `h₁ ∈ (h⁺₁, hᵀ₁]` and `h₁ = hᵀ₁`, `h₂ ∈ (h⁺₂, hᵀ₂]` none of the printed conditions
holds, yet `ξ_U < M` there (ξ_U decreases in `h₁, h₂` and equals `M` at `(h⁺₁, hᵀ₂)` and
`(hᵀ₁, h⁺₂)`, Lemma 13), so the optimal stopping level is above `0`; at `μ = (1, 2)`,
`σ = (1, 1)`, `M = −20`, `U = 10`, `(h₁, h₂) = (hᵀ₁, hᵀ₂)` a brute force over stopping policies
gives an optimal stopping level above `0`. The weak inequalities repair this. `hᵀᵢ` is (20) read at
the other control's `h⁺` (`hT1`, `hT2`). Policy values are the analytic `IsStopValue`; the
standing `v₁ < v₂` (p. 12) is `hv`. -/
theorem solution (p : Params) (hv : v p .one < v p .two) :
    AbandonsEarly p ↔
      (hplus p .one < p.h₁ ∧ hT2 p ≤ p.h₂) ∨
      (hT1 p ≤ p.h₁ ∧ hplus p .two < p.h₂) ∨
      (p.h₁ ∈ Set.Ioo (hplus p .one) (hT1 p) ∧ p.h₂ ∈ Set.Ioo (hplus p .two) (hT2 p) ∧
        xi p p.U p.h₁ p.h₂ (wFB p p.h₁ p.h₂) < p.M) := by
          have L_glue : ∀ (f g f' g' : ℝ → ℝ) (c : ℝ), (∀ x, HasDerivAt f (f' x) x) →
              (∀ x, HasDerivAt g (g' x) x) → f c = g c → f' c = g' c →
              ∀ x, HasDerivAt (fun t => if t ≤ c then f t else g t) (if x ≤ c then f' x else g' x) x := by
            intro f g f' g' c hf hg h0 h1 x
            rcases lt_trichotomy x c with h | h | h
            · rw [if_pos h.le]
              refine (hf x).congr_of_eventuallyEq ?_
              filter_upwards [Iio_mem_nhds h] with t ht
              rw [if_pos (le_of_lt ht)]
            · subst h
              rw [if_pos le_rfl]
              have hl : HasDerivWithinAt (fun t => if t ≤ x then f t else g t) (f' x) (Set.Iic x) x :=
                (hf x).hasDerivWithinAt.congr (fun t ht => if_pos ht) (if_pos le_rfl)
              have hr : HasDerivWithinAt (fun t => if t ≤ x then f t else g t) (f' x) (Set.Ici x) x := by
                rw [h1]
                refine (hg x).hasDerivWithinAt.congr (fun t ht => ?_) ?_
                · rcases eq_or_lt_of_le (Set.mem_Ici.1 ht) with e | e
                  · subst e; simp [h0]
                  · simp [not_le.2 e]
                · simp [h0]
              have := hl.union hr
              rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
            · rw [if_neg (not_le.2 h)]
              refine (hg x).congr_of_eventuallyEq ?_
              filter_upwards [Ioi_mem_nhds h] with t ht
              rw [if_neg (not_le.2 ht)]
          have L_anti : ∀ (B : Finset ℝ) (f : ℝ → ℝ) (a b : ℝ), a ≤ b → ContinuousOn f (Set.Icc a b) →
              (∀ x ∈ Set.Ioo a b, x ∉ B → ∃ f', HasDerivAt f f' x ∧ f' ≤ 0) → f b ≤ f a := by
            intro B
            induction B using Finset.induction_on with
            | empty =>
              intro f a b hab hc hd
              refine (antitoneOn_of_deriv_nonpos (convex_Icc a b) hc ?_ ?_) (Set.left_mem_Icc.2 hab)
                (Set.right_mem_Icc.2 hab) hab
              · rw [interior_Icc]
                intro x hx
                obtain ⟨f', h, _⟩ := hd x hx (by simp)
                exact h.differentiableAt.differentiableWithinAt
              · rw [interior_Icc]
                intro x hx
                obtain ⟨f', h, h'⟩ := hd x hx (by simp)
                rw [h.deriv]; exact h'
            | insert c B hcB ih =>
              intro f a b hab hc hd
              by_cases hm : c ∈ Set.Ioo a b
              · have h1 : f c ≤ f a := by
                  refine ih f a c hm.1.le (hc.mono (Set.Icc_subset_Icc_right hm.2.le)) ?_
                  intro x hx hxB
                  refine hd x ⟨hx.1, hx.2.trans hm.2⟩ ?_
                  simp [hxB, hx.2.ne]
                have h2 : f b ≤ f c := by
                  refine ih f c b hm.2.le (hc.mono (Set.Icc_subset_Icc_left hm.1.le)) ?_
                  intro x hx hxB
                  refine hd x ⟨hm.1.trans hx.1, hx.2⟩ ?_
                  simp [hxB, hx.1.ne']
                exact h2.trans h1
              · refine ih f a b hab hc ?_
                intro x hx hxB
                refine hd x hx ?_
                have : x ≠ c := by rintro rfl; exact hm hx
                simp [hxB, this]
          have L_neg : ∀ (B : Finset ℝ) (p : ℝ → ℝ) (K a b : ℝ), a ≤ b → ContinuousOn p (Set.Icc a b) →
              p a < 0 →
              (∀ x ∈ Set.Ioo a b, x ∉ B → p x < 0 → ∃ p', HasDerivAt p p' x ∧ p' ≤ -K * p x) → p b < 0 := by
            intro B p K a b hab hc ha hd
            by_contra hb
            push Not at hb
            have hcpt : IsCompact (Set.Icc a b ∩ p ⁻¹' (Set.Ici 0)) :=
              isCompact_Icc.of_isClosed_subset (hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici)
                Set.inter_subset_left
            obtain ⟨c, ⟨hcI, hc0⟩, hleast⟩ := hcpt.exists_isLeast ⟨b, ⟨hab, le_rfl⟩, hb⟩
            have hneg : ∀ x ∈ Set.Ico a c, p x < 0 := by
              intro x hx
              by_contra h
              push Not at h
              have := hleast ⟨⟨hx.1, hx.2.le.trans hcI.2⟩, h⟩
              exact absurd this (not_le.2 hx.2)
            have hsub : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc_right hcI.2
            have key := L_anti B (fun x => Real.exp (K * x) * p x) a c hcI.1
              ((by fun_prop : Continuous fun x : ℝ => Real.exp (K * x)).continuousOn.mul (hc.mono hsub)) (by
                intro x hx hxB
                obtain ⟨p', h1, h2⟩ := hd x ⟨hx.1, hx.2.trans_le hcI.2⟩ hxB (hneg x ⟨hx.1.le, hx.2⟩)
                have he : HasDerivAt (fun x : ℝ => Real.exp (K * x)) (Real.exp (K * x) * K) x := by
                  have := ((hasDerivAt_id x).const_mul K).exp
                  simpa using this
                refine ⟨_, he.mul h1, ?_⟩
                have := Real.exp_pos (K * x)
                nlinarith)
            have h1 : Real.exp (K * a) * p a < 0 := mul_neg_of_pos_of_neg (Real.exp_pos _) ha
            have h2 : 0 ≤ Real.exp (K * c) * p c := mul_nonneg (Real.exp_pos _).le hc0
            try simp only at key
            linarith
          have L_verif : ∀ (B : Finset ℝ) (D d : ℝ → ℝ) (K lo hi : ℝ), lo < hi →
              ContinuousOn D (Set.Icc lo hi) → (∀ x ∈ Set.Ioo lo hi, HasDerivAt D (d x) x) →
              ContinuousOn d (Set.Ioo lo hi) →
              (∀ x ∈ Set.Ioo lo hi, x ∉ B → d x < 0 → ∃ p', HasDerivAt d p' x ∧ p' ≤ -K * d x) →
              0 ≤ D lo → D hi = 0 → ∀ x ∈ Set.Icc lo hi, 0 ≤ D x := by
            intro B D d K lo hi hlh hD hd hdc hode h0 h1 x hx
            by_contra hneg
            push Not at hneg
            have hlx : lo < x := lt_of_le_of_ne hx.1 (by rintro rfl; linarith)
            have hxh : x < hi := lt_of_le_of_ne hx.2 (by rintro rfl; linarith)
            obtain ⟨c, hc, hce⟩ := exists_hasDerivAt_eq_slope D d hlx
              (hD.mono (Set.Icc_subset_Icc_right hx.2)) (fun t ht => hd t ⟨ht.1, ht.2.trans hxh⟩)
            have hcn : d c < 0 := by
              rw [hce]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)
            obtain ⟨e, he, hee⟩ := exists_hasDerivAt_eq_slope D d hxh
              (hD.mono (Set.Icc_subset_Icc_left hx.1)) (fun t ht => hd t ⟨hlx.trans ht.1, ht.2⟩)
            have hen : d e < 0 := by
              refine L_neg B d K c e (hc.2.trans he.1).le (hdc.mono ?_) hcn ?_
              · intro t ht; exact ⟨hc.1.trans_le ht.1, ht.2.trans_lt he.2⟩
              · intro t ht; exact hode t ⟨hc.1.trans ht.1, ht.2.trans he.2⟩
            rw [hee] at hen
            have : 0 < (D hi - D x) / (hi - x) := div_pos (by linarith) (by linarith)
            linarith
          have L_comp : ∀ (y y' g g' J G : ℝ → ℝ) (U : ℝ), 0 < U →
              (∀ x ∈ Set.Icc 0 U, HasDerivAt J (y x) x) → (∀ x ∈ Set.Icc 0 U, HasDerivAt G (g x) x) →
              (∀ x ∈ Set.Icc 0 U, HasDerivAt y (y' x) x) → (∀ x ∈ Set.Icc 0 U, HasDerivAt g (g' x) x) →
              y 0 = g 0 → J 0 = G 0 →
              (∀ x ∈ Set.Ioo 0 U, g x ≤ y x → y' x < g' x) → J U < G U := by
            intro y y' g g' J G U hU hJ hG hy hg h0 hJ0 hcmp
            have hcont : ContinuousOn (fun x => y x - g x) (Set.Icc 0 U) := fun x hx =>
              ((hy x hx).sub (hg x hx)).continuousAt.continuousWithinAt
            have hle : ∀ x ∈ Set.Ioo 0 U, y x - g x ≤ 0 := by
              intro x hx
              by_contra hpos
              push Not at hpos
              have hsub : Set.Icc 0 x ⊆ Set.Icc 0 U := Set.Icc_subset_Icc_right hx.2.le
              have hcpt : IsCompact (Set.Icc 0 x ∩ (fun x => y x - g x) ⁻¹' (Set.Iic 0)) :=
                isCompact_Icc.of_isClosed_subset
                  ((hcont.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic)
                  Set.inter_subset_left
              obtain ⟨c, ⟨hcI, hc0⟩, hgr⟩ := hcpt.exists_isGreatest ⟨0, ⟨le_rfl, hx.1.le⟩, by simp [h0]⟩
              have hc0' : y c - g c ≤ 0 := hc0
              have hcx : c < x := lt_of_le_of_ne hcI.2 (by rintro rfl; linarith)
              obtain ⟨t, ht, hte⟩ := exists_hasDerivAt_eq_slope (fun x => y x - g x)
                (fun x => y' x - g' x) hcx (hcont.mono (fun s hs => ⟨hcI.1.trans hs.1, hs.2.trans hx.2.le⟩))
                (fun s hs => (hy s ⟨hcI.1.trans hs.1.le, hs.2.le.trans hx.2.le⟩).sub
                  (hg s ⟨hcI.1.trans hs.1.le, hs.2.le.trans hx.2.le⟩))
              have htp : 0 ≤ y t - g t := by
                by_contra h
                push Not at h
                have := hgr ⟨⟨hcI.1.trans ht.1.le, ht.2.le⟩, h.le⟩
                exact absurd this (not_le.2 ht.1)
              have h1 := hcmp t ⟨hcI.1.trans_lt ht.1, ht.2.trans hx.2⟩ (by linarith)
              have h2 : 0 < (y x - g x - (y c - g c)) / (x - c) := div_pos (by linarith) (by linarith)
              try simp only at hte
              linarith
            have hlt : ∀ x ∈ Set.Ioo 0 U, y x - g x < 0 := by
              intro x hx
              refine lt_of_le_of_ne (hle x hx) ?_
              intro he
              have hmax : IsLocalMax (fun x => y x - g x) x := by
                filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
                simp only [he]
                exact hle t ht
              have h1 := hmax.hasDerivAt_eq_zero
                ((hy x ⟨hx.1.le, hx.2.le⟩).sub (hg x ⟨hx.1.le, hx.2.le⟩))
              have h2 := hcmp x hx (by linarith)
              linarith
            obtain ⟨t, ht, hte⟩ := exists_hasDerivAt_eq_slope (fun x => J x - G x)
                (fun x => y x - g x) hU (fun s hs => ((hJ s hs).sub (hG s hs)).continuousAt.continuousWithinAt)
                (fun s hs => (hJ s ⟨hs.1.le, hs.2.le⟩).sub (hG s ⟨hs.1.le, hs.2.le⟩))
            have h1 := hlt t ht
            try simp only at hte
            rw [hte] at h1
            have h2 : J U - G U - (J 0 - G 0) < 0 := by
              by_contra h
              push Not at h
              have : 0 ≤ (J U - G U - (J 0 - G 0)) / (U - 0) := div_nonneg h (by linarith)
              linarith
            linarith
          have L_low : ∀ (y y' J : ℝ → ℝ) (v a U : ℝ), 0 < U → 0 < v →
              (∀ x ≥ 0, HasDerivAt J (y x) x) →
              (∀ x ≥ 0, HasDerivAt y (y' x) x) → (∀ x ≥ 0, -(v * (y x + a)) ≤ y' x) → y 0 = 0 → J 0 = 0 →
              -a * U + a / v * (1 - Real.exp (-v * U)) ≤ J U := by
            intro y y' J v a U hU hv hJ hy hode h0 hJ0
            have hexp : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Real.exp (-v * x)) (Real.exp (-v * x) * -v) x := by
              intro x
              have := ((hasDerivAt_id x).const_mul (-v)).exp
              simpa using this
            have hexp2 : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Real.exp (v * x)) (Real.exp (v * x) * v) x := by
              intro x
              have := ((hasDerivAt_id x).const_mul (v)).exp
              simpa using this
            have hyl : ∀ x ≥ 0, -a * (1 - Real.exp (-v * x)) ≤ y x := by
              intro x hx
              have hd : ∀ s ≥ 0, HasDerivAt (fun x => Real.exp (v * x) * (y x + a))
                  (Real.exp (v * s) * v * (y s + a) + Real.exp (v * s) * y' s) s := fun s hs =>
                (hexp2 s).mul ((hy s hs).add_const a)
              have hm : MonotoneOn (fun x => Real.exp (v * x) * (y x + a)) (Set.Ici 0) := by
                refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
                  (fun s hs => (hd s hs).continuousAt.continuousWithinAt) ?_ ?_
                · rw [interior_Ici]
                  exact fun s hs => (hd s (le_of_lt hs)).differentiableAt.differentiableWithinAt
                · rw [interior_Ici]
                  intro s hs
                  rw [(hd s (le_of_lt hs)).deriv]
                  have := hode s (le_of_lt hs)
                  have := Real.exp_pos (v * s)
                  nlinarith
              have h := hm (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
              simp only [mul_zero, Real.exp_zero, h0, zero_add, one_mul] at h
              have hE : Real.exp (-v * x) * Real.exp (v * x) = 1 := by
                rw [← Real.exp_add]; simp
              have hp := Real.exp_pos (-v * x)
              have h3 := mul_le_mul_of_nonneg_left h hp.le
              rw [← mul_assoc, hE] at h3
              linarith
            have hd : ∀ s ≥ 0, HasDerivAt (fun x => J x - (-a * x + a / v * (1 - Real.exp (-v * x))))
                (y s - (-a * (1 - Real.exp (-v * s)))) s := by
              intro s hs
              have h1 := (hJ s hs).sub (((hasDerivAt_id s).const_mul (-a)).add
                (((hexp s).const_sub 1).const_mul (a / v)))
              refine h1.congr_deriv ?_
              field_simp
              ring
            have hm : MonotoneOn (fun x => J x - (-a * x + a / v * (1 - Real.exp (-v * x)))) (Set.Ici 0) := by
              refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
                (fun s hs => (hd s hs).continuousAt.continuousWithinAt) ?_ ?_
              · rw [interior_Ici]
                exact fun s hs => (hd s (le_of_lt hs)).differentiableAt.differentiableWithinAt
              · rw [interior_Ici]
                intro s hs
                rw [(hd s (le_of_lt hs)).deriv]
                have := hyl s (le_of_lt hs)
                linarith
            have h := hm (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hU.le) hU.le
            simp only [hJ0, mul_zero, Real.exp_zero, sub_self, add_zero] at h
            linarith
          have L_exp : ∀ (v c x : ℝ), HasDerivAt (fun x : ℝ => Real.exp (-v * (x - c)))
              (Real.exp (-v * (x - c)) * -v) x := by
            intro v c x
            have := (((hasDerivAt_id x).sub_const c).const_mul (-v)).exp
            simpa using this
          have L_one : ∀ (v a : ℝ), 0 < v → 0 < a →
              (∀ x, HasDerivAt (fun x => -a * x + a / v * (1 - Real.exp (-v * x)))
                (-a * (1 - Real.exp (-v * x))) x) ∧
              (∀ x, HasDerivAt (fun x => -a * (1 - Real.exp (-v * x)))
                (-(v * (-a * (1 - Real.exp (-v * x)) + a))) x) ∧
              (∀ x ≥ 0, -a * (1 - Real.exp (-v * x)) ≤ 0) ∧
              (∀ x > 0, -a * (1 - Real.exp (-v * x)) < 0) ∧
              (∀ x > 0, ∀ z, x ≤ z → -a * (1 - Real.exp (-v * z)) ≤ -a * (1 - Real.exp (-v * x))) := by
            intro v a hv ha
            have hexp : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Real.exp (-v * x)) (Real.exp (-v * x) * -v) x := by
              intro x
              have := ((hasDerivAt_id x).const_mul (-v)).exp
              simpa using this
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · intro x
              refine (((hasDerivAt_id x).const_mul (-a)).add
                (((hexp x).const_sub 1).const_mul (a / v))).congr_deriv ?_
              field_simp
              ring
            · intro x
              refine (((hexp x).const_sub 1).const_mul (-a)).congr_deriv ?_
              ring
            · intro x hx
              have : Real.exp (-v * x) ≤ 1 := by
                rw [Real.exp_le_one_iff]; nlinarith
              nlinarith
            · intro x hx
              have : Real.exp (-v * x) < 1 := by
                rw [Real.exp_lt_one_iff]; nlinarith
              nlinarith
            · intro x hx z hz
              have : Real.exp (-v * z) ≤ Real.exp (-v * x) := by
                rw [Real.exp_le_exp]; nlinarith
              nlinarith
          have L_pkg : ∀ (v1 v2 a1 a2 U : ℝ), 0 < v1 → v1 < v2 → 0 < a1 → 0 < a2 →
              ∃ J y : ℝ → ℝ, J 0 = 0 ∧ y 0 = 0 ∧ (∀ x, HasDerivAt J (y x) x) ∧
                (∀ x ≥ 0, HasDerivAt y (max (-(v1 * (y x + a1))) (-(v2 * (y x + a2)))) x) ∧
                Continuous y ∧ (∀ x > 0, y x < 0) ∧ (∃ X > 0, ∃ ε > 0, ∀ x ≥ X, y x ≤ -ε) ∧
                ((∀ x ≥ 0, v1 * (y x + a1) ≤ v2 * (y x + a2)) ∨
                 (∀ x ≥ 0, v2 * (y x + a2) ≤ v1 * (y x + a1)) ∨
                 (∃ S > 0, (∀ x ∈ Set.Icc 0 S, v1 * (y x + a1) ≤ v2 * (y x + a2)) ∧
                   (∀ x ≥ S, v2 * (y x + a2) ≤ v1 * (y x + a1)))) ∧
                (∀ w, w = v2 * (a1 - a2) / (a1 * (v2 - v1)) → a2 < a1 → v1 * a1 < v2 * a2 →
                  Real.exp (-v1 * U) < w →
                  J U = -(w ^ (-(v2 - v1) / v1) * v1 * Real.exp (-v2 * U) * a1 / v2 ^ 2)
                    + (Real.log w * w * v2 ^ 2 - Real.log w * w * v2 * v1 - w * v2 ^ 2
                      + v1 ^ 2 * w + v2 ^ 2) * a1 / (v1 * v2 ^ 2) - a2 * U) := by
            intro v1 v2 a1 a2 U hv1 hv12 ha1 ha2
            have hv2 : 0 < v2 := hv1.trans hv12
            obtain ⟨A1, A2, A3, A4, A5⟩ := L_one v1 a1 hv1 ha1
            obtain ⟨B1, B2, B3, B4, B5⟩ := L_one v2 a2 hv2 ha2
            have hdv : 0 < v2 - v1 := by linarith
            rcases le_or_gt a1 a2 with hr1 | hr1
            · -- control 1 only
              have hc : ∀ x ≥ 0, v1 * (-a1 * (1 - Real.exp (-v1 * x)) + a1) ≤
                  v2 * (-a1 * (1 - Real.exp (-v1 * x)) + a2) := by
                intro x hx
                have := Real.exp_pos (-v1 * x)
                have h1 : v1 * (a1 * Real.exp (-v1 * x)) ≤ v2 * (a1 * Real.exp (-v1 * x)) :=
                  mul_le_mul_of_nonneg_right hv12.le (by positivity)
                have h2 := mul_le_mul_of_nonneg_left hr1 hv2.le
                linarith
              refine ⟨_, _, ?_, ?_, A1, ?_, ?_, A4, ⟨1, one_pos, -(-a1 * (1 - Real.exp (-v1 * 1))), ?_, ?_⟩,
                Or.inl hc, ?_⟩
              · simp
              · simp
              · intro x hx
                rw [max_eq_left (neg_le_neg (hc x hx))]
                exact A2 x
              · exact continuous_iff_continuousAt.2 fun x => (A2 x).continuousAt
              · have := A4 1 one_pos; linarith
              · intro x hx; have := A5 1 one_pos x hx; linarith
              · intro w _ h; exact absurd h (not_lt.2 hr1)
            rcases le_or_gt (v2 * a2) (v1 * a1) with hr2 | hr2
            · have hc : ∀ x ≥ 0, v2 * (-a2 * (1 - Real.exp (-v2 * x)) + a2) ≤
                  v1 * (-a2 * (1 - Real.exp (-v2 * x)) + a1) := by
                intro x hx
                have := mul_nonpos_of_nonneg_of_nonpos hdv.le (B3 x hx)
                linarith
              refine ⟨_, _, ?_, ?_, B1, ?_, ?_, B4, ⟨1, one_pos, -(-a2 * (1 - Real.exp (-v2 * 1))), ?_, ?_⟩,
                Or.inr (Or.inl hc), ?_⟩
              · simp
              · simp
              · intro x hx
                rw [max_eq_right (neg_le_neg (hc x hx))]
                exact B2 x
              · exact continuous_iff_continuousAt.2 fun x => (B2 x).continuousAt
              · have := B4 1 one_pos; linarith
              · intro x hx; have := B5 1 one_pos x hx; linarith
              · intro w _ _ h; exact absurd h (not_lt.2 hr2)
            -- switching case
            obtain ⟨w, hw⟩ : ∃ w, w = v2 * (a1 - a2) / (a1 * (v2 - v1)) := ⟨_, rfl⟩
            have hwe : w * (a1 * (v2 - v1)) = v2 * (a1 - a2) := by
              rw [hw]; field_simp
            have hw0 : 0 < w := by
              rw [hw]; exact div_pos (mul_pos hv2 (by linarith)) (by positivity)
            have hw1 : w < 1 := by
              rw [hw, div_lt_one (by positivity)]; linarith
            obtain ⟨S, hS⟩ : ∃ S, S = -Real.log w / v1 := ⟨_, rfl⟩
            have hlog : Real.log w = -(v1 * S) := by rw [hS]; field_simp
            have hS0 : 0 < S := by
              rw [hS]; exact div_pos (by linarith [Real.log_neg hw0 hw1]) hv1
            have hwS : Real.exp (-v1 * S) = w := by
              rw [show -v1 * S = Real.log w by rw [hlog]; ring, Real.exp_log hw0]
            obtain ⟨b, hb⟩ : ∃ b, b = a1 * v1 * w / v2 := ⟨_, rfl⟩
            have hb0 : 0 < b := by rw [hb]; positivity
            have hbe : b * v2 = a1 * v1 * w := by rw [hb]; field_simp
            have hbe2 : b - a2 = -a1 * (1 - w) := by
              have : (b - a2) * v2 = (-a1 * (1 - w)) * v2 := by linear_combination hbe - hwe
              exact mul_right_cancel₀ hv2.ne' this
            obtain ⟨C, hC⟩ : ∃ C, C = -a1 * S + a1 / v1 * (1 - w) := ⟨_, rfl⟩
            have e1 := L_glue (fun x => -a1 * (1 - Real.exp (-v1 * x)))
              (fun x => -a2 + b * Real.exp (-v2 * (x - S)))
              (fun x => -(v1 * (-a1 * (1 - Real.exp (-v1 * x)) + a1)))
              (fun x => -(v2 * ((-a2 + b * Real.exp (-v2 * (x - S))) + a2))) S A2
              (fun x => (((L_exp v2 S x).const_mul b).const_add (-a2)).congr_deriv (by ring))
              (by simp only [hwS, sub_self, mul_zero, Real.exp_zero]; linarith)
              (by simp only [hwS, sub_self, mul_zero, Real.exp_zero]; linear_combination hbe)
            have e2 := L_glue (fun x => -a1 * x + a1 / v1 * (1 - Real.exp (-v1 * x)))
              (fun x => C - a2 * (x - S) + b / v2 * (1 - Real.exp (-v2 * (x - S))))
              (fun x => -a1 * (1 - Real.exp (-v1 * x)))
              (fun x => -a2 + b * Real.exp (-v2 * (x - S))) S A1
              (fun x => by
                refine ((((((hasDerivAt_id x).sub_const S).const_mul a2).const_sub C).add
                  (((L_exp v2 S x).const_sub 1).const_mul (b / v2)))).congr_deriv ?_
                field_simp)
              (by simp only [hwS, sub_self, mul_zero, Real.exp_zero]; linarith)
              (by simp only [hwS, sub_self, mul_zero, Real.exp_zero]; linarith)
            have hyS : -a1 * (1 - w) < 0 := by
              have := mul_pos ha1 (show 0 < 1 - w by linarith)
              linarith
            have hy2 : ∀ x, S < x → -a2 + b * Real.exp (-v2 * (x - S)) ≤ -a1 * (1 - w) := by
              intro x hx
              have : Real.exp (-v2 * (x - S)) ≤ 1 := by
                rw [Real.exp_le_one_iff]
                have := mul_pos hv2 (show 0 < x - S by linarith)
                linarith
              have := mul_le_mul_of_nonneg_left this hb0.le
              linarith
            have hc1 : ∀ x ∈ Set.Icc 0 S, v1 * ((if x ≤ S then -a1 * (1 - Real.exp (-v1 * x)) else
                -a2 + b * Real.exp (-v2 * (x - S))) + a1) ≤ v2 * ((if x ≤ S then -a1 * (1 - Real.exp (-v1 * x)) else
                -a2 + b * Real.exp (-v2 * (x - S))) + a2) := by
              intro x hx
              rw [if_pos hx.2]
              have : w ≤ Real.exp (-v1 * x) := by
                rw [← hwS, Real.exp_le_exp]
                have := mul_le_mul_of_nonneg_left hx.2 hv1.le
                linarith
              have : w * (a1 * (v2 - v1)) ≤ Real.exp (-v1 * x) * (a1 * (v2 - v1)) :=
                mul_le_mul_of_nonneg_right this (by positivity)
              linarith
            have hc2 : ∀ x ≥ S, v2 * ((if x ≤ S then -a1 * (1 - Real.exp (-v1 * x)) else
                -a2 + b * Real.exp (-v2 * (x - S))) + a2) ≤ v1 * ((if x ≤ S then -a1 * (1 - Real.exp (-v1 * x)) else
                -a2 + b * Real.exp (-v2 * (x - S))) + a1) := by
              intro x hx
              have hy : (if x ≤ S then -a1 * (1 - Real.exp (-v1 * x)) else
                -a2 + b * Real.exp (-v2 * (x - S))) ≤ -a1 * (1 - w) := by
                rcases eq_or_lt_of_le hx with h | h
                · rw [← h, if_pos le_rfl, hwS]
                · rw [if_neg (not_le.2 h)]; exact hy2 x h
              generalize (if x ≤ S then -a1 * (1 - Real.exp (-v1 * x)) else
                -a2 + b * Real.exp (-v2 * (x - S))) = Y at hy ⊢
              have := mul_le_mul_of_nonneg_left hy hdv.le
              linarith
            refine ⟨_, _, ?_, ?_, e2, ?_, ?_, ?_, ⟨S + 1, by linarith, a1 * (1 - w), by linarith, ?_⟩,
              Or.inr (Or.inr ⟨S, hS0, hc1, hc2⟩), ?_⟩
            · simp [hS0.le]
            · simp [hS0.le]
            · intro x hx
              refine (e1 x).congr_deriv ?_
              by_cases h : x ≤ S
              · rw [max_eq_left (neg_le_neg (hc1 x ⟨hx, h⟩))]
                simp only [if_pos h]
              · rw [max_eq_right (neg_le_neg (hc2 x (le_of_not_ge h)))]
                simp only [if_neg h]
            · exact continuous_iff_continuousAt.2 fun x => (e1 x).continuousAt
            · intro x hx
              by_cases h : x ≤ S
              · simp only [if_pos h]; exact A4 x hx
              · simp only [if_neg h]; exact (hy2 x (not_le.1 h)).trans_lt hyS
            · intro x hx
              rw [if_neg (by linarith)]
              have := hy2 x (by linarith)
              linarith
            · intro w' hw' _ _ hU
              rw [← hw] at hw'
              replace hw' := hw'.symm
              subst hw'
              have hSU : S < U := by
                rw [← hwS, Real.exp_lt_exp] at hU
                exact lt_of_mul_lt_mul_left (show v1 * S < v1 * U by linarith) hv1.le
              simp only [if_neg (not_le.2 hSU)]
              have hE : Real.exp (-v2 * (U - S)) * w = w ^ (-(v2 - v1) / v1) * Real.exp (-v2 * U) := by
                rw [Real.rpow_def_of_pos hw0, hlog]
                nth_rewrite 1 [← hwS]
                rw [← Real.exp_add, ← Real.exp_add]
                congr 1
                field_simp
                ring
              rw [show -(w ^ (-(v2 - v1) / v1) * v1 * Real.exp (-v2 * U) * a1 / v2 ^ 2) =
                -((w ^ (-(v2 - v1) / v1) * Real.exp (-v2 * U)) * v1 * a1 / v2 ^ 2) by ring, ← hE, hlog, hC, hb]
              have ha2e : a2 = a1 - w * (a1 * (v2 - v1)) / v2 := by
                rw [hwe]; field_simp; ring
              rw [ha2e]
              field_simp
              ring
          classical
          have mu_pos : ∀ c, 0 < p.mu c := fun c => by cases c; exacts [p.hμ₁, p.hμ₂]
          have sig_pos : ∀ c, 0 < p.sig c := fun c => by cases c; exacts [p.hσ₁, p.hσ₂]
          have cost_pos : ∀ c, 0 < p.cost c := fun c => by cases c; exacts [p.hh₁, p.hh₂]
          have v_pos : ∀ c, 0 < v p c := fun c => by
            have := mu_pos c; have := sig_pos c; unfold v; positivity
          have hsv : ∀ c, p.sig c ^ 2 / 2 * v p c = p.mu c := fun c => by
            have := (sig_pos c).ne'; unfold v; field_simp
          obtain ⟨a, ha⟩ : ∃ a : Ctrl → ℝ, ∀ c, a c = p.cost c / p.mu c := ⟨_, fun _ => rfl⟩
          have a_pos : ∀ c, 0 < a c := fun c => by rw [ha]; exact div_pos (cost_pos c) (mu_pos c)
          have hma : ∀ c, p.cost c = p.mu c * a c := fun c => by
            have := (mu_pos c).ne'; rw [ha]; field_simp
          obtain ⟨ap, hap⟩ : ∃ ap : Ctrl → ℝ, ∀ c, ap c = -p.M / (p.U - (1 - Real.exp (-v p c * p.U)) / v p c) :=
            ⟨_, fun _ => rfl⟩
          have hU := p.hU
          have hM := p.hM
          have hK : ∀ c, 0 < p.U - (1 - Real.exp (-v p c * p.U)) / v p c := fun c => by
            have h1 := v_pos c
            have h2 := Real.add_one_lt_exp (x := -v p c * p.U) (by
              have : 0 < v p c * p.U := mul_pos h1 hU
              linarith)
            rw [sub_pos, div_lt_iff₀ h1]
            linarith
          have ap_pos : ∀ c, 0 < ap c := fun c => by rw [hap]; exact div_pos (by linarith) (hK c)
          have hapK : ∀ c, ap c * (p.U - (1 - Real.exp (-v p c * p.U)) / v p c) = -p.M := fun c => by
            rw [hap, div_mul_cancel₀ _ (hK c).ne']
          have hapM : ∀ c, -ap c * p.U + ap c / v p c * (1 - Real.exp (-v p c * p.U)) = p.M := fun c => by
            have := hapK c
            linear_combination -this
          have hplus_eq : ∀ c, hplus p c = p.mu c * ap c := fun c => by
            have h1 := (v_pos c).ne'
            have h2 := (hK c).ne'
            unfold hplus hplusU
            rw [show p.U * (1 - (1 - Real.exp (-v p c * p.U)) / (v p c * p.U)) =
              p.U - (1 - Real.exp (-v p c * p.U)) / v p c by field_simp, hap]
            ring
          have hlt : ∀ c, -a c * p.U + a c / v p c * (1 - Real.exp (-v p c * p.U)) < p.M ↔ ap c < a c := by
            intro c
            rw [show -a c * p.U + a c / v p c * (1 - Real.exp (-v p c * p.U)) =
              -(a c * (p.U - (1 - Real.exp (-v p c * p.U)) / v p c)) by ring]
            have h1 := hapK c
            have h2 := hK c
            constructor
            · intro h
              exact lt_of_mul_lt_mul_right (by linarith) h2.le
            · intro h
              have := mul_lt_mul_of_pos_right h h2
              linarith
          have hE : ∀ c, 0 < 1 - Real.exp (-v p c * p.U) := fun c => by
            have : 0 < v p c * p.U := mul_pos (v_pos c) hU
            have : Real.exp (-v p c * p.U) < 1 := by
              rw [Real.exp_lt_one_iff]; linarith
            linarith
          have hs1 : p.σ₁ ^ 2 = 2 * p.μ₁ / v p .one := by
            have h1 := hsv .one; have h2 := (v_pos .one).ne'
            simp only [Params.sig, Params.mu] at h1
            rw [eq_div_iff h2]; linarith
          have hs2 : p.σ₂ ^ 2 = 2 * p.μ₂ / v p .two := by
            have h1 := hsv .two; have h2 := (v_pos .two).ne'
            simp only [Params.sig, Params.mu] at h1
            rw [eq_div_iff h2]; linarith
          have hT2_eq : hT2 p = p.μ₂ * (ap .one * (1 - Real.exp (-v p .one * p.U) * (v p .two - v p .one) / v p .two)) := by
            have h1 := (v_pos .one).ne'
            have h2 := (v_pos .two).ne'
            have h3 := (hE .one).ne'
            have h4 := p.hμ₁.ne'
            have h5 := p.hμ₂.ne'
            have h6 := hU.ne'
            unfold hT2 dU1 hstar
            rw [hplus_eq, hs1, hs2, ← hapK .one]
            simp only [Params.mu]
            generalize Real.exp (-v p .one * p.U) = E at h3 ⊢
            field_simp
            ring
          have hT1_eq : hT1 p = p.μ₁ * (ap .two * v p .two / v p .one) := by
            have h1 := (v_pos .one).ne'
            have h2 := (v_pos .two).ne'
            have h3 := (hE .two).ne'
            have h4 := p.hμ₁.ne'
            have h5 := p.hμ₂.ne'
            have h6 := hU.ne'
            unfold hT1 dL2 hstar
            rw [hplus_eq, hs1, hs2, ← hapK .two, one_div_one_div]
            simp only [Params.mu]
            generalize Real.exp (-v p .two * p.U) = E at h3 ⊢
            field_simp
            ring
          obtain ⟨J, y, J0, y0, hJ, hy, hyc, hyneg, ⟨X, hX, ε, hε, hXε⟩, hpol, hxi⟩ :=
            L_pkg (v p .one) (v p .two) (a .one) (a .two) p.U (v_pos .one) hv (a_pos .one) (a_pos .two)
          have hGle : ∀ c t, -(v p c * (t + a c)) ≤
              max (-(v p .one * (t + a .one))) (-(v p .two * (t + a .two))) := by
            intro c t; cases c
            · exact le_max_left _ _
            · exact le_max_right _ _
          have hJanti : StrictAntiOn J (Set.Ici 0) := by
            refine strictAntiOn_of_deriv_neg (convex_Ici 0)
              (fun x _ => (hJ x).continuousAt.continuousWithinAt) ?_
            rw [interior_Ici]
            intro x hx
            rw [(hJ x).deriv]; exact hyneg x hx
          have hJneg : ∀ x > 0, J x < 0 := fun x hx => by
            have := hJanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx.le) hx
            rwa [J0] at this
          have hJcont : Continuous J := continuous_iff_continuousAt.2 fun x => (hJ x).continuousAt
          -- existence of the length T
          obtain ⟨T, hT0, hTM⟩ : ∃ T > 0, J T = p.M := by
            have hbd : J (X + -p.M / ε) ≤ p.M := by
              have hq : 0 < -p.M / ε := div_pos (by linarith) hε
              obtain ⟨t, ht, hte⟩ := exists_hasDerivAt_eq_slope J y
                (show X < X + -p.M / ε by linarith) hJcont.continuousOn (fun s _ => hJ s)
              have h1 := hXε t ht.1.le
              rw [hte, div_le_iff₀ (by linarith)] at h1
              have h2 : ε * (-p.M / ε) = -p.M := by field_simp
              have h3 := hJneg X hX
              have h4 : -ε * (X + -p.M / ε - X) = p.M := by linear_combination -h2
              linarith
            have hq : 0 < -p.M / ε := div_pos (by linarith) hε
            obtain ⟨T, hT, hTe⟩ := intermediate_value_Icc' (show (0:ℝ) ≤ X + -p.M / ε by linarith)
              hJcont.continuousOn (show p.M ∈ Set.Icc _ _ from ⟨hbd, by rw [J0]; exact hM.le⟩)
            refine ⟨T, lt_of_le_of_ne hT.1 ?_, hTe⟩
            rintro rfl
            linarith
          obtain ⟨z, hz⟩ : ∃ z, z = p.U - T := ⟨_, rfl⟩
          have hzU : z < p.U := by linarith
          -- the policy
          obtain ⟨π, hπz, hπc⟩ : ∃ π : StopPolicy p, π.S 0 = z ∧
              ∀ (j : Fin π.k) (x : ℝ), x ∈ Set.Ioo (π.S j.castSucc) (π.S j.succ) →
                -(v p (π.ctrl j) * (y (x - z) + a (π.ctrl j))) =
                  max (-(v p .one * (y (x - z) + a .one))) (-(v p .two * (y (x - z) + a .two))) := by
            have one_case : (∀ x ∈ Set.Icc 0 T, v p .one * (y x + a .one) ≤ v p .two * (y x + a .two)) →
                ∃ π : StopPolicy p, π.S 0 = z ∧
              ∀ (j : Fin π.k) (x : ℝ), x ∈ Set.Ioo (π.S j.castSucc) (π.S j.succ) →
                -(v p (π.ctrl j) * (y (x - z) + a (π.ctrl j))) =
                  max (-(v p .one * (y (x - z) + a .one))) (-(v p .two * (y (x - z) + a .two))) := by
              intro h
              refine ⟨stopOne p .one z hzU, rfl, ?_⟩
              intro j x hx
              have hj : j = (0 : Fin 1) := Fin.ext (by have := j.2; change j.1 < 1 at this; change j.1 = 0; omega)
              subst hj
              have hx' : x ∈ Set.Ioo z p.U := hx
              have := h (x - z) ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
              rw [max_eq_left (neg_le_neg this)]
              rfl
            rcases hpol with h | h | ⟨S, hS0, h1, h2⟩
            · exact one_case fun x hx => h x hx.1
            · refine ⟨stopOne p .two z hzU, rfl, ?_⟩
              intro j x hx
              have hj : j = (0 : Fin 1) := Fin.ext (by have := j.2; change j.1 < 1 at this; change j.1 = 0; omega)
              subst hj
              have hx' : x ∈ Set.Ioo z p.U := hx
              have := h (x - z) (by linarith [hx'.1])
              rw [max_eq_right (neg_le_neg this)]
              rfl
            · rcases le_or_gt T S with hTS | hTS
              · exact one_case fun x hx => h1 x ⟨hx.1, hx.2.trans hTS⟩
              · refine ⟨stopOneTwo p z (z + S) (by linarith) (by linarith), rfl, ?_⟩
                intro j x hx
                have hj : j = (0 : Fin 2) ∨ j = (1 : Fin 2) := by
                  have := j.2; change j.1 < 2 at this
                  rcases (show j.1 = 0 ∨ j.1 = 1 by omega) with h | h
                  · left; exact Fin.ext h
                  · right; exact Fin.ext h
                rcases hj with rfl | rfl
                · have hx' : x ∈ Set.Ioo z (z + S) := hx
                  have := h1 (x - z) ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
                  rw [max_eq_left (neg_le_neg this)]
                  rfl
                · have hx' : x ∈ Set.Ioo (z + S) p.U := hx
                  have := h2 (x - z) (by linarith [hx'.1])
                  rw [max_eq_right (neg_le_neg this)]
                  rfl
          -- the candidate value
          obtain ⟨V, hVdef⟩ : ∃ V : ℝ → ℝ, V = fun x => if x ≤ z then (fun _ => (0:ℝ)) x else (fun x => J (x - z)) x :=
            ⟨_, rfl⟩
          obtain ⟨Vd, hVddef⟩ : ∃ Vd : ℝ → ℝ, Vd = fun x => if x ≤ z then (fun _ => (0:ℝ)) x else (fun x => y (x - z)) x :=
            ⟨_, rfl⟩
          have hVd : ∀ x, HasDerivAt V (Vd x) x := by
            rw [hVdef, hVddef]
            refine L_glue (fun _ => (0:ℝ)) (fun x => J (x - z)) (fun _ => (0:ℝ)) (fun x => y (x - z)) z
              (fun x => hasDerivAt_const x _) (fun x => ?_) (by simp [J0]) (by simp [y0])
            exact (hJ (x - z)).comp_sub_const x z
          have hVdc : Continuous Vd := by
            rw [hVddef]
            refine Continuous.if_le continuous_const (hyc.comp (continuous_id.sub continuous_const))
              continuous_id continuous_const ?_
            intro x hx
            try simp only [id] at hx
            simp [hx, y0]
          have hVle : ∀ x ≤ z, V x = 0 := fun x hx => by rw [hVdef]; simp [hx]
          have hVgt : ∀ x, z < x → V x = J (x - z) := fun x hx => by rw [hVdef]; simp [not_le.2 hx]
          have hVdle : ∀ x ≤ z, Vd x = 0 := fun x hx => by rw [hVddef]; simp [hx]
          have hVdgt : ∀ x, z < x → Vd x = y (x - z) := fun x hx => by rw [hVddef]; simp [not_le.2 hx]
          have hVdd : ∀ x, z < x → HasDerivAt Vd (max (-(v p .one * (y (x - z) + a .one)))
              (-(v p .two * (y (x - z) + a .two)))) x := by
            intro x hx
            refine ((hy (x - z) (by linarith)).comp_sub_const x z).congr_of_eventuallyEq ?_
            filter_upwards [Ioi_mem_nhds hx] with t ht
            exact hVdgt t ht
          have hVdd0 : ∀ x, x < z → HasDerivAt Vd 0 x := by
            intro x hx
            refine (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq ?_
            filter_upwards [Iio_mem_nhds hx] with t ht
            exact hVdle t (le_of_lt ht)
          have hderivV : deriv V = Vd := funext fun x => (hVd x).deriv
          have hVval : IsStopValue p π V := by
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro x hx; rw [hπz] at hx; exact hVle x hx
            · refine ContDiff.contDiffOn ?_
              rw [contDiff_one_iff_deriv, hderivV]
              exact ⟨fun x => (hVd x).differentiableAt, hVdc⟩
            · rw [hVgt _ hzU, hz]; simpa using hTM
            · intro j x hx
              have hzx : z < x := by
                have h1 : π.S 0 ≤ π.S j.castSucc := π.S_strictMono.monotone (Fin.zero_le _)
                rw [hπz] at h1
                exact h1.trans_lt hx.1
              refine ⟨?_, ?_⟩
              · have hopen : ContDiffOn ℝ 2 V (Set.Ioi z) := by
                  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
                  refine ⟨fun x _ => (hVd x).differentiableAt.differentiableWithinAt, by simp, ?_⟩
                  rw [hderivV, show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
                    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
                  refine ⟨fun x hx => (hVdd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
                  rw [contDiffOn_zero]
                  refine ContinuousOn.congr (f := fun x => max (-(v p .one * (y (x - z) + a .one)))
                    (-(v p .two * (y (x - z) + a .two)))) ?_ (fun x hx => (hVdd x hx).deriv)
                  exact Continuous.continuousOn (by fun_prop)
                exact hopen.contDiffAt (Ioi_mem_nhds hzx)
              · rw [hderivV, (hVdd x hzx).deriv, hVdgt x hzx, ← hπc j x hx, hma, ]
                linear_combination (-(y (x - z) + a (π.ctrl j))) * hsv (π.ctrl j)
          have hVnonpos : ∀ x, V x ≤ 0 := by
            intro x
            rcases le_or_gt x z with h | h
            · exact (hVle x h).le
            · rw [hVgt x h]; exact (hJneg _ (by linarith)).le
          -- verification
          have hverif : ∀ (π' : StopPolicy p) (W : ℝ → ℝ), IsStopValue p π' W → ∀ x ≤ p.U, V x ≤ W x := by
            intro π' W ⟨hW0, hW1, hWU, hWode⟩ x hx
            rcases le_or_gt x (π'.S 0) with hx0 | hx0
            · rw [hW0 x hx0]; exact hVnonpos x
            have hlohi : π'.S 0 < p.U := hx0.trans_le hx
            have hVU : V p.U = p.M := hVval.2.2.1
            have hWo : ContDiffOn ℝ 1 W (Set.Ioo (π'.S 0) p.U) := hW1.mono Set.Ioo_subset_Icc_self
            have hcV : Continuous V := continuous_iff_continuousAt.2 fun x => (hVd x).continuousAt
            have hloc : ∀ t, t ∉ Finset.univ.image π'.S → ∀ i : Fin (π'.k + 1), π'.S 0 < t → t < π'.S i →
                ∃ j : Fin π'.k, t ∈ Set.Ioo (π'.S j.castSucc) (π'.S j.succ) := by
              intro t ht i h0
              induction i using Fin.induction with
              | zero => intro h; exact absurd h0 (not_lt.2 h.le)
              | succ j ih =>
                intro h
                by_cases hlt' : t < π'.S j.castSucc
                · exact ih hlt'
                · refine ⟨j, lt_of_le_of_ne (not_lt.1 hlt') ?_, h⟩
                  intro he
                  exact ht (Finset.mem_image.2 ⟨_, Finset.mem_univ _, he⟩)
            have hmain := L_verif (insert z (Finset.univ.image π'.S)) (fun t => W t - V t)
              (fun t => deriv W t - Vd t) (v p .two) (π'.S 0) p.U hlohi
              (hW1.continuousOn.sub hcV.continuousOn)
              (fun t ht => ((((hWo.differentiableOn one_ne_zero) t ht).differentiableAt
                (Ioo_mem_nhds ht.1 ht.2)).hasDerivAt).sub (hVd t))
              ((hWo.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).sub hVdc.continuousOn)
              (by
                intro t ht htB hdn
                rw [Finset.mem_insert, not_or] at htB
                obtain ⟨j, hj⟩ := hloc t htB.2 (Fin.last _) ht.1 (by rw [π'.S_last]; exact ht.2)
                obtain ⟨hC2, hode⟩ := hWode j t hj
                have hdd : HasDerivAt (deriv W) (deriv (deriv W) t) t := by
                  have h1 : ContDiffAt ℝ 1 (deriv W) t := by
                    exact (hC2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
                  exact (h1.differentiableAt one_ne_zero).hasDerivAt
                have hW2 : deriv (deriv W) t = -(v p (π'.ctrl j) * (deriv W t + a (π'.ctrl j))) := by
                  have h1 := sig_pos (π'.ctrl j)
                  have h2 : 0 < p.sig (π'.ctrl j) ^ 2 / 2 := by positivity
                  apply mul_left_cancel₀ h2.ne'
                  rw [hma] at hode
                  linear_combination hode + (deriv W t + a (π'.ctrl j)) * hsv (π'.ctrl j)
                obtain ⟨q, hq, hqle⟩ : ∃ q, HasDerivAt Vd q t ∧
                    -(v p (π'.ctrl j) * (Vd t + a (π'.ctrl j))) ≤ q := by
                  rcases lt_or_gt_of_ne htB.1 with h | h
                  · refine ⟨0, hVdd0 t h, ?_⟩
                    rw [hVdle t h.le]
                    have := mul_pos (v_pos (π'.ctrl j)) (a_pos (π'.ctrl j))
                    linarith
                  · refine ⟨_, hVdd t h, ?_⟩
                    rw [hVdgt t h]
                    exact hGle _ _
                refine ⟨_, hdd.sub hq, ?_⟩
                have hvle : v p (π'.ctrl j) ≤ v p .two := by
                  cases π'.ctrl j
                  · exact hv.le
                  · exact le_rfl
                have := mul_le_mul_of_nonneg_right hvle (show 0 ≤ -(deriv W t - Vd t) by linarith)
                rw [hW2]
                linarith)
              (by rw [hW0 _ le_rfl]; linarith [hVnonpos (π'.S 0)])
              (by rw [hWU, hVU, sub_self])
            have := hmain x ⟨hx0.le, hx⟩
            linarith
          have hAE : AbandonsEarly p ↔ J p.U < p.M := by
            constructor
            · rintro ⟨π', ⟨V', hV', hopt⟩, hz0⟩
              by_contra hcon
              have hUT : p.U ≤ T := by
                by_contra h
                have := hJanti (Set.mem_Ici.2 hT0.le) (Set.mem_Ici.2 hU.le) (not_le.1 h)
                rw [hTM] at this
                exact hcon this
              have hz0' : 0 < π'.S 0 := hz0
              have hle : π'.S 0 ≤ p.U := by
                rw [← π'.S_last]; exact π'.S_strictMono.monotone (Fin.zero_le _)
              have h1 := hopt π V hVval (π'.S 0) hle
              rw [hV'.1 _ le_rfl, hVgt _ (by linarith)] at h1
              have := hJneg (π'.S 0 - z) (by linarith)
              linarith
            · intro h
              refine ⟨π, ⟨V, hVval, hverif⟩, ?_⟩
              change 0 < π.S 0
              rw [hπz, hz]
              by_contra hcon
              have := hJanti.antitoneOn (Set.mem_Ici.2 hU.le) (Set.mem_Ici.2 hT0.le) (by linarith)
              linarith
          rw [hAE, hT1_eq, hT2_eq, hplus_eq, hplus_eq]
          have hc1 : p.h₁ = p.μ₁ * a .one := hma .one
          have hc2 : p.h₂ = p.μ₂ * a .two := hma .two
          have hμ₁ := p.hμ₁
          have hμ₂ := p.hμ₂
          have hv1 := v_pos .one
          have hv2 := v_pos .two
          have ha1 := a_pos .one
          have ha2 := a_pos .two
          have hwFB : wFB p p.h₁ p.h₂ = v p .two * (a .one - a .two) / (a .one * (v p .two - v p .one)) := by
            have : v p .two - v p .one ≠ 0 := by linarith
            unfold wFB
            rw [hc1, hc2]
            field_simp
          have hxiEq : ∀ w, xi p p.U p.h₁ p.h₂ w =
              -(w ^ (-(v p .two - v p .one) / v p .one) * v p .one * Real.exp (-v p .two * p.U) * a .one / v p .two ^ 2)
                  + (Real.log w * w * v p .two ^ 2 - Real.log w * w * v p .two * v p .one - w * v p .two ^ 2
                    + v p .one ^ 2 * w + v p .two ^ 2) * a .one / (v p .one * v p .two ^ 2) - a .two * p.U := by
            intro w
            unfold xi
            rw [hc1, hc2]
            field_simp
          have hlow : ∀ c, -a c * p.U + a c / v p c * (1 - Real.exp (-v p c * p.U)) ≤ J p.U := fun c =>
            L_low y _ J (v p c) (a c) p.U hU (v_pos c) (fun x _ => hJ x) hy (fun x _ => hGle c (y x)) y0 J0
          have hregion : J p.U < p.M → ap .one < a .one ∧ ap .two < a .two := fun h =>
            ⟨(hlt .one).1 ((hlow .one).trans_lt h), (hlt .two).1 ((hlow .two).trans_lt h)⟩
          have hdv : 0 < v p .two - v p .one := by linarith
          -- region (c): the value is xi
          have hcxi : ap .one < a .one → a .one < ap .two * v p .two / v p .one → ap .two < a .two →
              a .two < ap .one * (1 - Real.exp (-v p .one * p.U) * (v p .two - v p .one) / v p .two) →
              J p.U = xi p p.U p.h₁ p.h₂ (wFB p p.h₁ p.h₂) := by
            intro h1 h2 h3 h4
            have hEp := Real.exp_pos (-v p .one * p.U)
            have hE1 := hE .one
            obtain ⟨κ, hκ⟩ : ∃ κ, κ = 1 - Real.exp (-v p .one * p.U) * (v p .two - v p .one) / v p .two := ⟨_, rfl⟩
            have hκ2 : κ * v p .two = v p .two - Real.exp (-v p .one * p.U) * (v p .two - v p .one) := by
              rw [hκ]; field_simp
            have hκ0 : 0 < κ := by
              have : 0 < κ * v p .two := by rw [hκ2]; have := mul_pos hE1 hdv; linarith
              exact pos_of_mul_pos_left this hv2.le
            rw [← hκ] at h4
            have h5 : a .two < a .one * κ := h4.trans (mul_lt_mul_of_pos_right h1 hκ0)
            have h6 : a .two * v p .two < a .one * (κ * v p .two) := by
              have := mul_lt_mul_of_pos_right h5 hv2
              linarith
            rw [hκ2] at h6
            rw [lt_div_iff₀ hv1] at h2
            rw [hxiEq, hwFB]
            refine hxi _ rfl ?_ ?_ ?_
            · have : 0 < a .one * (Real.exp (-v p .one * p.U) * (v p .two - v p .one)) := by positivity
              exact lt_of_mul_lt_mul_right (by linarith) hv2.le
            · have := mul_lt_mul_of_pos_right h3 hv2
              linarith
            · rw [lt_div_iff₀ (by positivity)]
              linarith
          rw [hc1, hc2] at hcxi ⊢
          simp only [Params.mu, Set.mem_Ioo, mul_lt_mul_iff_right₀ hμ₁, mul_lt_mul_iff_right₀ hμ₂,
            mul_le_mul_iff_right₀ hμ₁, mul_le_mul_iff_right₀ hμ₂]
          constructor
          · intro h
            obtain ⟨h1, h2⟩ := hregion h
            by_cases hA : ap .one * (1 - Real.exp (-v p .one * p.U) * (v p .two - v p .one) / v p .two) ≤ a .two
            · exact Or.inl ⟨h1, hA⟩
            by_cases hB : ap .two * v p .two / v p .one ≤ a .one
            · exact Or.inr (Or.inl ⟨hB, h2⟩)
            push Not at hA hB
            refine Or.inr (Or.inr ⟨⟨h1, hB⟩, ⟨h2, hA⟩, ?_⟩)
            rw [← hcxi h1 hB h2 hA]
            exact h
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩)
            · obtain ⟨A1, A2, A3, A4, A5⟩ := L_one (v p .one) (ap .one) hv1 (ap_pos .one)
              rw [← hapM .one]
              refine L_comp y _ (fun x => -ap .one * (1 - Real.exp (-v p .one * x))) _ J
                (fun x => -ap .one * x + ap .one / v p .one * (1 - Real.exp (-v p .one * x))) p.U hU
                (fun x _ => hJ x) (fun x _ => A1 x) (fun x hx => hy x hx.1) (fun x _ => A2 x)
                (by simp [y0]) (by simp [J0]) ?_
              intro x hx hge
              have hexp : Real.exp (-v p .one * p.U) < Real.exp (-v p .one * x) := by
                rw [Real.exp_lt_exp]
                have := mul_lt_mul_of_pos_left hx.2 hv1
                linarith
              have hap1 := ap_pos .one
              have e1 := mul_lt_mul_of_pos_right hexp (mul_pos hap1 hdv)
              have e2 := mul_le_mul_of_nonneg_right h2 hv2.le
              have e3 : ap .one * (1 - Real.exp (-v p .one * p.U) * (v p .two - v p .one) / v p .two) * v p .two
                = ap .one * (v p .two - Real.exp (-v p .one * p.U) * (v p .two - v p .one)) := by field_simp
              rw [e3] at e2
              rw [max_lt_iff]
              constructor
              · exact neg_lt_neg (mul_lt_mul_of_pos_left (by linarith) hv1)
              · have e4 := mul_le_mul_of_nonneg_left hge hv2.le
                linarith
            · obtain ⟨A1, A2, A3, A4, A5⟩ := L_one (v p .two) (ap .two) hv2 (ap_pos .two)
              rw [← hapM .two]
              refine L_comp y _ (fun x => -ap .two * (1 - Real.exp (-v p .two * x))) _ J
                (fun x => -ap .two * x + ap .two / v p .two * (1 - Real.exp (-v p .two * x))) p.U hU
                (fun x _ => hJ x) (fun x _ => A1 x) (fun x hx => hy x hx.1) (fun x _ => A2 x)
                (by simp [y0]) (by simp [J0]) ?_
              intro x hx hge
              have e1 := A4 x hx.1
              rw [div_le_iff₀ hv1] at h1
              generalize -ap .two * (1 - Real.exp (-v p .two * x)) = Y at hge e1 ⊢
              rw [max_lt_iff]
              constructor
              · have e2 := mul_neg_of_pos_of_neg hdv e1
                have e4 := mul_le_mul_of_nonneg_left hge hv1.le
                linarith
              · exact neg_lt_neg (mul_lt_mul_of_pos_left (by linarith) hv2)
            · rw [hcxi h1 h2 h3 h4]
              exact h5
