-- Prove2me | solution 1 for EthierKurtz.oblique_coefficient_extension_to_closure
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T00:44:45.278573+00:00
-- url     : https://prove2.me/submissions/a7792e87-4222-4a4e-8049-d2660edb580b

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder
import Definitions.Def_EthierKurtz_ComponentHolder

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory Real Set Filter
open scoped Topology

namespace ObliqueLib
/-- Euclidean space of dimension `d`. -/
abbrev Eu (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Normalized Gaussian of "variance parameter" `s`: `G s z = (π s)^(-d/2) exp(-|z|^2/s)`. -/
noncomputable def G (d : ℕ) (s : ℝ) (z : Eu d) : ℝ :=
  (π * s) ^ (-((d : ℝ) / 2)) * rexp (-‖z‖ ^ 2 / s)

section Comp2

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Second derivative of `g ∘ f`: `(v, w) ↦ Dg (D2f v w) + D2g (Df v) (Df w)`. -/
noncomputable def D2comp (Dg : F →L[ℝ] G) (D2g : F →L[ℝ] F →L[ℝ] G) (Df : E →L[ℝ] F)
    (D2f : E →L[ℝ] E →L[ℝ] F) : E →L[ℝ] E →L[ℝ] G :=
  (ContinuousLinearMap.compL ℝ E F G Dg).comp D2f +
    ((ContinuousLinearMap.compL ℝ E F G).flip Df).comp (D2g.comp Df)

lemma D2comp_apply (Dg : F →L[ℝ] G) (D2g : F →L[ℝ] F →L[ℝ] G) (Df : E →L[ℝ] F)
    (D2f : E →L[ℝ] E →L[ℝ] F) (v w : E) :
    D2comp Dg D2g Df D2f v w = Dg (D2f v w) + D2g (Df v) (Df w) := by
  simp [D2comp]

lemma D2comp_norm_le {Dg : F →L[ℝ] G} {D2g : F →L[ℝ] F →L[ℝ] G} {Df : E →L[ℝ] F}
    {D2f : E →L[ℝ] E →L[ℝ] F} {A1 A2 B1 B2 : ℝ} (hA1 : ‖Dg‖ ≤ A1) (hA2 : ‖D2g‖ ≤ A2)
    (hB1 : ‖Df‖ ≤ B1) (hB2 : ‖D2f‖ ≤ B2) :
    ‖D2comp Dg D2g Df D2f‖ ≤ A1 * B2 + A2 * B1 ^ 2 := by
  have hA1' := (norm_nonneg _).trans hA1
  have hA2' := (ContinuousLinearMap.opNorm_nonneg _).trans hA2
  have hB1' := (norm_nonneg _).trans hB1
  have hB2' := (ContinuousLinearMap.opNorm_nonneg _).trans hB2
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun v w => ?_
  rw [D2comp_apply]
  have t1 : ‖Dg (D2f v w)‖ ≤ A1 * B2 * ‖v‖ * ‖w‖ := by
    calc ‖Dg (D2f v w)‖ ≤ ‖Dg‖ * ‖D2f v w‖ := Dg.le_opNorm _
      _ ≤ A1 * (B2 * ‖v‖ * ‖w‖) := by
          refine mul_le_mul hA1 ?_ (norm_nonneg _) hA1'
          exact (D2f.le_opNorm₂ v w).trans (by gcongr)
      _ = _ := by ring
  have t2 : ‖D2g (Df v) (Df w)‖ ≤ A2 * B1 ^ 2 * ‖v‖ * ‖w‖ := by
    calc ‖D2g (Df v) (Df w)‖ ≤ ‖D2g‖ * ‖Df v‖ * ‖Df w‖ := D2g.le_opNorm₂ _ _
      _ ≤ A2 * (B1 * ‖v‖) * (B1 * ‖w‖) := by
          gcongr
          · exact (Df.le_opNorm v).trans (by gcongr)
          · exact (Df.le_opNorm w).trans (by gcongr)
      _ = _ := by ring
  calc ‖Dg (D2f v w) + D2g (Df v) (Df w)‖ ≤ ‖Dg (D2f v w)‖ + ‖D2g (Df v) (Df w)‖ := norm_add_le _ _
    _ ≤ _ := by have := add_le_add t1 t2; linarith

lemma D2comp_sub_le {Dg Dg' : F →L[ℝ] G} {D2g D2g' : F →L[ℝ] F →L[ℝ] G} {Df Df' : E →L[ℝ] F}
    {D2f D2f' : E →L[ℝ] E →L[ℝ] F} {A1 A2 B1 B2 : ℝ} (hA1 : ‖Dg'‖ ≤ A1) (hA2 : ‖D2g'‖ ≤ A2)
    (hB1 : ‖Df‖ ≤ B1) (hB1' : ‖Df'‖ ≤ B1) (hB2 : ‖D2f‖ ≤ B2) :
    ‖D2comp Dg D2g Df D2f - D2comp Dg' D2g' Df' D2f'‖ ≤
      ‖Dg - Dg'‖ * B2 + A1 * ‖D2f - D2f'‖ + ‖D2g - D2g'‖ * B1 ^ 2 + 2 * (A2 * B1 * ‖Df - Df'‖) := by
  have hA1' := (norm_nonneg _).trans hA1
  have hA2' := (ContinuousLinearMap.opNorm_nonneg _).trans hA2
  have hB1n := (norm_nonneg _).trans hB1
  have hB2' := (ContinuousLinearMap.opNorm_nonneg _).trans hB2
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun v w => ?_
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, D2comp_apply, D2comp_apply]
  have e : Dg (D2f v w) + D2g (Df v) (Df w) - (Dg' (D2f' v w) + D2g' (Df' v) (Df' w)) =
      (Dg - Dg') (D2f v w) + Dg' ((D2f - D2f') v w) + (D2g - D2g') (Df v) (Df w) +
      D2g' ((Df - Df') v) (Df w) + D2g' (Df' v) ((Df - Df') w) := by
    simp only [ContinuousLinearMap.sub_apply, map_sub]; abel
  rw [e]
  have nv := norm_nonneg v
  have nw := norm_nonneg w
  have t1 : ‖(Dg - Dg') (D2f v w)‖ ≤ ‖Dg - Dg'‖ * B2 * ‖v‖ * ‖w‖ := by
    calc _ ≤ ‖Dg - Dg'‖ * ‖D2f v w‖ := (Dg - Dg').le_opNorm _
      _ ≤ ‖Dg - Dg'‖ * (B2 * ‖v‖ * ‖w‖) := by
          gcongr; exact (D2f.le_opNorm₂ v w).trans (by gcongr)
      _ = _ := by ring
  have t2 : ‖Dg' ((D2f - D2f') v w)‖ ≤ A1 * ‖D2f - D2f'‖ * ‖v‖ * ‖w‖ := by
    calc _ ≤ ‖Dg'‖ * ‖(D2f - D2f') v w‖ := Dg'.le_opNorm _
      _ ≤ A1 * (‖D2f - D2f'‖ * ‖v‖ * ‖w‖) := mul_le_mul hA1 ((D2f - D2f').le_opNorm₂ v w)
          (norm_nonneg _) hA1'
      _ = _ := by ring
  have t3 : ‖(D2g - D2g') (Df v) (Df w)‖ ≤ ‖D2g - D2g'‖ * B1 ^ 2 * ‖v‖ * ‖w‖ := by
    calc _ ≤ ‖D2g - D2g'‖ * ‖Df v‖ * ‖Df w‖ := (D2g - D2g').le_opNorm₂ _ _
      _ ≤ ‖D2g - D2g'‖ * (B1 * ‖v‖) * (B1 * ‖w‖) := by
          gcongr
          · exact (Df.le_opNorm v).trans (by gcongr)
          · exact (Df.le_opNorm w).trans (by gcongr)
      _ = _ := by ring
  have t4 : ‖D2g' ((Df - Df') v) (Df w)‖ ≤ A2 * B1 * ‖Df - Df'‖ * ‖v‖ * ‖w‖ := by
    calc _ ≤ ‖D2g'‖ * ‖(Df - Df') v‖ * ‖Df w‖ := D2g'.le_opNorm₂ _ _
      _ ≤ A2 * (‖Df - Df'‖ * ‖v‖) * (B1 * ‖w‖) := by
          gcongr
          · exact (Df - Df').le_opNorm v
          · exact (Df.le_opNorm w).trans (by gcongr)
      _ = _ := by ring
  have t5 : ‖D2g' (Df' v) ((Df - Df') w)‖ ≤ A2 * B1 * ‖Df - Df'‖ * ‖v‖ * ‖w‖ := by
    calc _ ≤ ‖D2g'‖ * ‖Df' v‖ * ‖(Df - Df') w‖ := D2g'.le_opNorm₂ _ _
      _ ≤ A2 * (B1 * ‖v‖) * (‖Df - Df'‖ * ‖w‖) := by
          gcongr
          · exact (Df'.le_opNorm v).trans (by gcongr)
          · exact (Df - Df').le_opNorm w
      _ = _ := by ring
  have n1 := norm_add_le ((Dg - Dg') (D2f v w) + Dg' ((D2f - D2f') v w) + (D2g - D2g') (Df v) (Df w) +
      D2g' ((Df - Df') v) (Df w)) (D2g' (Df' v) ((Df - Df') w))
  have n2 := norm_add_le ((Dg - Dg') (D2f v w) + Dg' ((D2f - D2f') v w) + (D2g - D2g') (Df v) (Df w))
      (D2g' ((Df - Df') v) (Df w))
  have n3 := norm_add_le ((Dg - Dg') (D2f v w) + Dg' ((D2f - D2f') v w)) ((D2g - D2g') (Df v) (Df w))
  have n4 := norm_add_le ((Dg - Dg') (D2f v w)) (Dg' ((D2f - D2f') v w))
  have : (‖Dg - Dg'‖ * B2 + A1 * ‖D2f - D2f'‖ + ‖D2g - D2g'‖ * B1 ^ 2 + 2 * (A2 * B1 * ‖Df - Df'‖)) *
      ‖v‖ * ‖w‖ = ‖Dg - Dg'‖ * B2 * ‖v‖ * ‖w‖ + A1 * ‖D2f - D2f'‖ * ‖v‖ * ‖w‖ +
      ‖D2g - D2g'‖ * B1 ^ 2 * ‖v‖ * ‖w‖ + A2 * B1 * ‖Df - Df'‖ * ‖v‖ * ‖w‖ +
      A2 * B1 * ‖Df - Df'‖ * ‖v‖ * ‖w‖ := by ring
  rw [this]; linarith

/-- `ε ≤ R` converts a Lipschitz bound to a `μ`-Hölder one. -/
lemma lip_le_hol {t R μ : ℝ} (ht : 0 ≤ t) (htR : t ≤ R) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    t ≤ R ^ (1 - μ) * t ^ μ := by
  rcases ht.eq_or_lt with h | h
  · subst h; exact mul_nonneg (rpow_nonneg htR _) (rpow_nonneg le_rfl _)
  have : t = t ^ (1 - μ) * t ^ μ := by rw [← rpow_add h]; simp
  calc t = t ^ (1 - μ) * t ^ μ := this
    _ ≤ R ^ (1 - μ) * t ^ μ := by gcongr

/-- Uniform `C^{2,μ}`-type bounds of `(f, Df, D2f)` on a set `T` with one constant `K`. -/
structure C2B (T : Set E) (μ K : ℝ) (f : E → F) (Df : E → E →L[ℝ] F)
    (D2f : E → E →L[ℝ] E →L[ℝ] F) : Prop where
  hK : 0 ≤ K
  lip : ∀ x ∈ T, ∀ y ∈ T, ‖f x - f y‖ ≤ K * ‖x - y‖
  b1 : ∀ x ∈ T, ‖Df x‖ ≤ K
  lip1 : ∀ x ∈ T, ∀ y ∈ T, ‖Df x - Df y‖ ≤ K * ‖x - y‖
  b2 : ∀ x ∈ T, ‖D2f x‖ ≤ K
  hol2 : ∀ x ∈ T, ∀ y ∈ T, ‖D2f x - D2f y‖ ≤ K * ‖x - y‖ ^ μ

/-- Composition of `C2B` data on a bounded set. -/
theorem C2B.comp {T : Set E} {T' : Set F} {μ K K' R : ℝ} {f : E → F} {Df : E → E →L[ℝ] F}
    {D2f : E → E →L[ℝ] E →L[ℝ] F} {g : F → G} {Dg : F → F →L[ℝ] G} {D2g : F → F →L[ℝ] F →L[ℝ] G}
    (hg : C2B T' μ K' g Dg D2g) (hf : C2B T μ K f Df D2f) (hmap : ∀ x ∈ T, f x ∈ T')
    (hR : ∀ x ∈ T, ∀ y ∈ T, ‖x - y‖ ≤ R) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) :
    ∃ K'', C2B T μ K'' (g ∘ f) (fun x => (Dg (f x)).comp (Df x))
      (fun x => D2comp (Dg (f x)) (D2g (f x)) (Df x) (D2f x)) := by
  have hK := hf.hK
  have hK' := hg.hK
  have hR0 : ∀ x ∈ T, ∀ y ∈ T, 0 ≤ R := fun x hx y hy => (norm_nonneg _).trans (hR x hx y hy)
  -- `R⁺ = max R 0` so that the constant is nonnegative even for empty `T`
  set Rp := max R 0 with hRp
  have hRp0 : 0 ≤ Rp := le_max_right _ _
  have hRR : ∀ x ∈ T, ∀ y ∈ T, ‖x - y‖ ≤ Rp := fun x hx y hy => (hR x hx y hy).trans (le_max_left _ _)
  have hRμ : 0 ≤ Rp ^ (1 - μ) := rpow_nonneg hRp0 _
  have hconv : ∀ x ∈ T, ∀ y ∈ T, ‖x - y‖ ≤ Rp ^ (1 - μ) * ‖x - y‖ ^ μ := fun x hx y hy =>
    lip_le_hol (norm_nonneg _) (hRR x hx y hy) hμ0.le hμ1
  have p1 : 0 ≤ K' * K := mul_nonneg hK' hK
  have p2 : 0 ≤ K' * K ^ 2 := mul_nonneg hK' (sq_nonneg K)
  set Ch := K' * K * K * Rp ^ (1 - μ) + K' * K + K' * K ^ μ * K ^ 2 + 2 * (K' * K * K * Rp ^ (1 - μ))
    with hCh
  have pCh : 0 ≤ Ch := by have := rpow_nonneg hK μ; positivity
  refine ⟨K' * K + K' * K ^ 2 + 2 * (K' * K) + Ch, ⟨by positivity, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x hx y hy
    have : ‖g (f x) - g (f y)‖ ≤ K' * K * ‖x - y‖ := by
      calc _ ≤ K' * ‖f x - f y‖ := hg.lip _ (hmap x hx) _ (hmap y hy)
        _ ≤ K' * (K * ‖x - y‖) := by gcongr; exact hf.lip x hx y hy
        _ = _ := by ring
    exact this.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · intro x hx
    have : ‖(Dg (f x)).comp (Df x)‖ ≤ K' * K :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hg.b1 _ (hmap x hx)) (hf.b1 x hx) (norm_nonneg _) hK')
    linarith
  · intro x hx y hy
    have e : (Dg (f x)).comp (Df x) - (Dg (f y)).comp (Df y) =
        (Dg (f x) - Dg (f y)).comp (Df x) + (Dg (f y)).comp (Df x - Df y) := by
      rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]; abel
    rw [e]
    have a1 : ‖(Dg (f x) - Dg (f y)).comp (Df x)‖ ≤ K' * K * ‖x - y‖ * K := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul ?_ (hf.b1 x hx) (norm_nonneg _)
        (by positivity))
      calc _ ≤ K' * ‖f x - f y‖ := hg.lip1 _ (hmap x hx) _ (hmap y hy)
        _ ≤ K' * (K * ‖x - y‖) := by gcongr; exact hf.lip x hx y hy
        _ = _ := by ring
    have a2 : ‖(Dg (f y)).comp (Df x - Df y)‖ ≤ K' * (K * ‖x - y‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hg.b1 _ (hmap y hy)) (hf.lip1 x hx y hy) (norm_nonneg _) hK')
    have h3 : K' * K * ‖x - y‖ * K + K' * (K * ‖x - y‖) = (K' * K * K + K' * K) * ‖x - y‖ := by ring
    have h4 : (K' * K * K + K' * K) * ‖x - y‖ ≤ (K' * K + K' * K ^ 2 + 2 * (K' * K) + Ch) * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
    have := add_le_add a1 a2
    exact (norm_add_le _ _).trans (by linarith)
  · intro x hx
    have := D2comp_norm_le (hg.b1 _ (hmap x hx)) (hg.b2 _ (hmap x hx)) (hf.b1 x hx) (hf.b2 x hx)
    linarith
  · intro x hx y hy
    have hxy := hconv x hx y hy
    have hn := norm_nonneg (x - y)
    have hnμ : 0 ≤ ‖x - y‖ ^ μ := rpow_nonneg hn _
    refine (D2comp_sub_le (hg.b1 _ (hmap y hy)) (hg.b2 _ (hmap y hy)) (hf.b1 x hx) (hf.b1 y hy)
      (hf.b2 x hx)).trans ?_
    have c1 : ‖Dg (f x) - Dg (f y)‖ ≤ K' * K * (Rp ^ (1 - μ) * ‖x - y‖ ^ μ) := by
      calc _ ≤ K' * ‖f x - f y‖ := hg.lip1 _ (hmap x hx) _ (hmap y hy)
        _ ≤ K' * (K * ‖x - y‖) := by gcongr; exact hf.lip x hx y hy
        _ ≤ K' * (K * (Rp ^ (1 - μ) * ‖x - y‖ ^ μ)) := by gcongr
        _ = _ := by ring
    have c2 : ‖D2f x - D2f y‖ ≤ K * ‖x - y‖ ^ μ := hf.hol2 x hx y hy
    have c3 : ‖D2g (f x) - D2g (f y)‖ ≤ K' * (K ^ μ * ‖x - y‖ ^ μ) := by
      calc _ ≤ K' * ‖f x - f y‖ ^ μ := hg.hol2 _ (hmap x hx) _ (hmap y hy)
        _ ≤ K' * (K * ‖x - y‖) ^ μ := by
            gcongr; exact hf.lip x hx y hy
        _ = _ := by rw [mul_rpow hK hn]
    have c4 : ‖Df x - Df y‖ ≤ K * (Rp ^ (1 - μ) * ‖x - y‖ ^ μ) :=
      (hf.lip1 x hx y hy).trans (by gcongr)
    have d1 := mul_le_mul_of_nonneg_right c1 hK
    have d2 := mul_le_mul_of_nonneg_left c2 hK'
    have d3 := mul_le_mul_of_nonneg_right c3 (sq_nonneg K)
    have d4 := mul_le_mul_of_nonneg_left c4 (mul_nonneg hK' hK)
    have e1 : K' * K * (Rp ^ (1 - μ) * ‖x - y‖ ^ μ) * K + K' * (K * ‖x - y‖ ^ μ) +
        K' * (K ^ μ * ‖x - y‖ ^ μ) * K ^ 2 + 2 * (K' * K * (K * (Rp ^ (1 - μ) * ‖x - y‖ ^ μ))) =
        Ch * ‖x - y‖ ^ μ := by rw [hCh]; ring
    have h5 : Ch * ‖x - y‖ ^ μ ≤ (K' * K + K' * K ^ 2 + 2 * (K' * K) + Ch) * ‖x - y‖ ^ μ :=
      mul_le_mul_of_nonneg_right (by linarith) hnμ
    nlinarith

end Comp2

section Glue

variable {n : ℕ}

end Glue

section IFT

variable {d : ℕ}

end IFT

section OpTrans

variable {d : ℕ}

end OpTrans

section CutHelp

variable {d : ℕ}

end CutHelp

structure ObChart {d : ℕ} (Ω : Set (Eu d)) (μ : ℝ) (c : Eu d → Eu d) (x0 : Eu d) (r0 K : ℝ) (e b : Eu d)
    (Θ : Eu d → Eu d) (DΘ : Eu d → Eu d →L[ℝ] Eu d) (D2Θ : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] Eu d) : Prop where
  hr0 : 0 < r0
  he : ‖e‖ = 1
  hb : inner ℝ b e = 0
  strict : ∀ x ∈ Metric.ball x0 r0, HasStrictFDerivAt Θ (DΘ x) x
  hd2 : ∀ x ∈ Metric.ball x0 r0 ∩ Ω, HasFDerivAt DΘ (D2Θ x) x
  h0 : Θ x0 = 0
  hD0 : DΘ x0 = ContinuousLinearMap.id ℝ (Eu d)
  side : ∀ x ∈ Metric.ball x0 r0, (x ∈ Ω ↔ 0 < inner ℝ (Θ x) e) ∧ (x ∈ frontier Ω ↔ inner ℝ (Θ x) e = 0)
  obl : ∀ x ∈ Metric.ball x0 r0 ∩ frontier Ω, ∃ κ : ℝ, 0 < κ ∧ DΘ x (c x) = κ • (b - e)
  c2b : C2B (Metric.ball x0 r0 ∩ closure Ω) μ K Θ DΘ D2Θ

section ObChartS

end ObChartS

section VarDef

end VarDef

section HolA

variable {d : ℕ}

lemma holder_of_paths {Ω S : Set (Eu d)} {μ : ℝ} (hμ : 0 < μ) {f : Eu d → ℝ} {ρ0 M L : ℝ}
    (hL : 0 < L) (hM : 0 ≤ M)
    (hf : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 → ∀ x z : Eu d, z ∈ Ω ∩ Metric.ball x ρ →
      ∀ y ∈ connectedComponentIn (Ω ∩ Metric.ball x ρ) z,
      ∀ w ∈ connectedComponentIn (Ω ∩ Metric.ball x ρ) z, |f y - f w| ≤ M * ρ ^ μ)
    (hpath : ∀ y ∈ S, ∀ w ∈ S, y ≠ w → ∃ T : Set (Eu d), IsPreconnected T ∧ y ∈ T ∧ w ∈ T ∧
      T ⊆ Ω ∩ Metric.ball y (L * ‖y - w‖))
    (hsmall : ∀ y ∈ S, ∀ w ∈ S, L * ‖y - w‖ ≤ ρ0) :
    ∀ y ∈ S, ∀ w ∈ S, |f y - f w| ≤ M * L ^ μ * ‖y - w‖ ^ μ := by
  intro y hy w hw
  by_cases hyw : y = w
  · subst hyw
    simp only [sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg hM (Real.rpow_nonneg hL.le _)) (Real.rpow_nonneg (norm_nonneg _) _)
  obtain ⟨T, hT, hyT, hwT, hTs⟩ := hpath y hy w hw hyw
  have hn : 0 < ‖y - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyw)
  have hρ : 0 < L * ‖y - w‖ := mul_pos hL hn
  have hsub : T ⊆ connectedComponentIn (Ω ∩ Metric.ball y (L * ‖y - w‖)) y :=
    hT.subset_connectedComponentIn hyT hTs
  have := hf (L * ‖y - w‖) hρ (hsmall y hy w hw) y y (hTs hyT) y (hsub hyT) w (hsub hwT)
  rw [Real.mul_rpow hL.le (norm_nonneg _), ← mul_assoc] at this
  exact this

lemma path_interior {Ω : Set (Eu d)} {x0 : Eu d} {R : ℝ} (hball : Metric.ball x0 R ⊆ Ω) :
    ∀ y ∈ Ω ∩ Metric.ball x0 R, ∀ w ∈ Ω ∩ Metric.ball x0 R, y ≠ w →
      ∃ T : Set (Eu d), IsPreconnected T ∧ y ∈ T ∧ w ∈ T ∧ T ⊆ Ω ∩ Metric.ball y (4 * ‖y - w‖) := by
  intro y hy w hw hyw
  have hn : 0 < ‖y - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyw)
  refine ⟨segment ℝ y w, (convex_segment y w).isPreconnected, left_mem_segment ℝ y w,
    right_mem_segment ℝ y w, fun p hp => ⟨hball ((convex_ball x0 R).segment_subset hy.2 hw.2 hp), ?_⟩⟩
  have hw' : w ∈ Metric.closedBall y ‖y - w‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
  have := (convex_closedBall y ‖y - w‖).segment_subset (Metric.mem_closedBall_self hn.le) hw' hp
  exact Metric.closedBall_subset_ball (by linarith) this

lemma vseg_mem {e q : Eu d} {t s : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hs : 0 ≤ s) (he : ‖e‖ = 1) :
    ‖q + t • ((q + s • e) - q) - q‖ = t * s ∧ inner ℝ (q + t • ((q + s • e) - q) - q) e = t * s := by
  have h1 : q + t • ((q + s • e) - q) - q = (t * s) • e := by
    rw [add_sub_cancel_left, add_sub_cancel_left, smul_smul]
  rw [h1, norm_smul, he, Real.norm_of_nonneg (mul_nonneg ht0 hs), real_inner_smul_left,
    real_inner_self_eq_norm_sq, he]
  ring_nf
  simp

theorem path_boundary {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} {x0 : Eu d} {r0 K : ℝ} {e b : Eu d}
    {Θ : Eu d → Eu d} {DΘ : Eu d → Eu d →L[ℝ] Eu d} {D2Θ : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] Eu d}
    (h : ObChart Ω μ c x0 r0 K e b Θ DΘ D2Θ) :
    ∃ r1 : ℝ, 0 < r1 ∧ ∀ y ∈ Ω ∩ Metric.ball x0 r1, ∀ w ∈ Ω ∩ Metric.ball x0 r1, y ≠ w →
      ∃ T : Set (Eu d), IsPreconnected T ∧ y ∈ T ∧ w ∈ T ∧ T ⊆ Ω ∩ Metric.ball y (4 * ‖y - w‖) := by
  obtain ⟨s, hs, hap⟩ := (h.strict x0 (Metric.mem_ball_self h.hr0)).approximates_deriv_on_nhds
    (c := (1 / 4 : NNReal)) (Or.inr (by norm_num))
  rw [h.hD0] at hap
  obtain ⟨r2, hr2, hr2s⟩ := Metric.mem_nhds_iff.mp hs
  have hR : 0 < min r2 r0 := lt_min hr2 h.hr0
  set R := min r2 r0 with hRdef
  have he := h.he
  have key : ∀ p ∈ Metric.ball x0 R, ∀ q ∈ Metric.ball x0 R,
      inner ℝ (Θ q) e + inner ℝ (p - q) e - ‖p - q‖ / 4 ≤ inner ℝ (Θ p) e := by
    intro p hp q hq
    have hp' : p ∈ s := hr2s (Metric.ball_subset_ball (min_le_left _ _) hp)
    have hq' : q ∈ s := hr2s (Metric.ball_subset_ball (min_le_left _ _) hq)
    have h1 := hap p hp' q hq'
    simp only [ContinuousLinearMap.id_apply] at h1
    have h2 : ((1 / 4 : NNReal) : ℝ) = 1 / 4 := by norm_num
    rw [h2] at h1
    have h3 := abs_real_inner_le_norm (Θ p - Θ q - (p - q)) e
    rw [he, mul_one] at h3
    have h4 : inner ℝ (Θ p - Θ q - (p - q)) e = inner ℝ (Θ p) e - inner ℝ (Θ q) e - inner ℝ (p - q) e := by
      rw [inner_sub_left, inner_sub_left]
    have h5 := (abs_le.mp h3).1
    linarith
  have hin : ∀ p ∈ Metric.ball x0 R, p ∈ Ω ↔ 0 < inner ℝ (Θ p) e := fun p hp =>
    (h.side p (Metric.ball_subset_ball (min_le_right _ _) hp)).1
  refine ⟨R / 8, by positivity, fun y hy w hw hyw => ?_⟩
  have hn : 0 < ‖y - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyw)
  set r := ‖y - w‖ with hr
  have hyx : ‖y - x0‖ < R / 8 := by rw [← dist_eq_norm]; exact hy.2
  have hwx : ‖w - x0‖ < R / 8 := by rw [← dist_eq_norm]; exact hw.2
  have hrR : r < R / 4 := by
    have : r ≤ ‖y - x0‖ + ‖w - x0‖ := by
      rw [hr]; calc ‖y - w‖ = ‖(y - x0) - (w - x0)‖ := by congr 1; abel
        _ ≤ ‖y - x0‖ + ‖w - x0‖ := norm_sub_le _ _
    linarith
  have hmem : ∀ p : Eu d, ‖p - y‖ ≤ 3 * r → p ∈ Metric.ball x0 R ∧ p ∈ Metric.ball y (4 * r) := by
    intro p hp
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      calc ‖p - x0‖ = ‖(p - y) + (y - x0)‖ := by congr 1; abel
        _ ≤ ‖p - y‖ + ‖y - x0‖ := norm_add_le _ _
        _ < R := by linarith
    · rw [Metric.mem_ball, dist_eq_norm]; linarith
  have hyR : y ∈ Metric.ball x0 R := hmem y (by simp; positivity) |>.1
  have hwy : ‖w - y‖ = r := by rw [hr, norm_sub_rev]
  have hwR : w ∈ Metric.ball x0 R := hmem w (by rw [hwy]; linarith) |>.1
  have hφy : 0 < inner ℝ (Θ y) e := (hin y hyR).mp hy.1
  have hφw : 0 < inner ℝ (Θ w) e := (hin w hwR).mp hw.1
  have hiwy : -r ≤ inner ℝ (w - y) e := by
    have := abs_real_inner_le_norm (w - y) e
    rw [he, mul_one, hwy] at this
    exact (abs_le.mp this).1
  -- the three segments
  have hT1 : segment ℝ y (y + (2 * r) • e) ⊆ Ω ∩ Metric.ball y (4 * r) := by
    intro p hp
    rw [segment_eq_image'] at hp
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hp
    obtain ⟨hn1, hi1⟩ := vseg_mem (q := y) ht0 ht1 (by positivity : (0 : ℝ) ≤ 2 * r) he
    have hb : ‖y + t • (y + (2 * r) • e - y) - y‖ ≤ 3 * r := by rw [hn1]; nlinarith
    obtain ⟨hpR, hpy⟩ := hmem _ hb
    refine ⟨(hin _ hpR).mpr ?_, hpy⟩
    have := key _ hpR y hyR
    rw [hn1, hi1] at this
    nlinarith
  have hT3 : segment ℝ w (w + (2 * r) • e) ⊆ Ω ∩ Metric.ball y (4 * r) := by
    intro p hp
    rw [segment_eq_image'] at hp
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hp
    obtain ⟨hn1, hi1⟩ := vseg_mem (q := w) ht0 ht1 (by positivity : (0 : ℝ) ≤ 2 * r) he
    have hb : ‖w + t • (w + (2 * r) • e - w) - y‖ ≤ 3 * r := by
      calc ‖w + t • (w + (2 * r) • e - w) - y‖ = ‖(w + t • (w + (2 * r) • e - w) - w) + (w - y)‖ := by
            congr 1; abel
        _ ≤ ‖w + t • (w + (2 * r) • e - w) - w‖ + ‖w - y‖ := norm_add_le _ _
        _ ≤ 3 * r := by rw [hn1, hwy]; nlinarith
    obtain ⟨hpR, hpy⟩ := hmem _ hb
    refine ⟨(hin _ hpR).mpr ?_, hpy⟩
    have := key _ hpR w hwR
    rw [hn1, hi1] at this
    nlinarith
  have hT2 : segment ℝ (y + (2 * r) • e) (w + (2 * r) • e) ⊆ Ω ∩ Metric.ball y (4 * r) := by
    intro p hp
    rw [segment_eq_image'] at hp
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hp
    have hd : y + (2 * r) • e + t • (w + (2 * r) • e - (y + (2 * r) • e)) - y =
        (2 * r) • e + t • (w - y) := by
      have : w + (2 * r) • e - (y + (2 * r) • e) = w - y := by abel
      rw [this]; abel
    have hn2 : ‖y + (2 * r) • e + t • (w + (2 * r) • e - (y + (2 * r) • e)) - y‖ ≤ 3 * r := by
      rw [hd]
      calc ‖(2 * r) • e + t • (w - y)‖ ≤ ‖(2 * r) • e‖ + ‖t • (w - y)‖ := norm_add_le _ _
        _ = 2 * r + t * r := by
            rw [norm_smul, norm_smul, he, hwy, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * r),
              Real.norm_of_nonneg ht0]; ring
        _ ≤ 3 * r := by nlinarith
    have hi2 : inner ℝ (y + (2 * r) • e + t • (w + (2 * r) • e - (y + (2 * r) • e)) - y) e =
        2 * r + t * inner ℝ (w - y) e := by
      rw [hd, inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]
      ring
    obtain ⟨hpR, hpy⟩ := hmem _ hn2
    refine ⟨(hin _ hpR).mpr ?_, hpy⟩
    have := key _ hpR y hyR
    rw [hi2] at this
    have h6 : t * inner ℝ (w - y) e ≥ -(t * r) := by nlinarith
    nlinarith
  refine ⟨segment ℝ y (y + (2 * r) • e) ∪ segment ℝ (y + (2 * r) • e) (w + (2 * r) • e) ∪ segment ℝ w (w + (2 * r) • e), ?_, Or.inl (Or.inl (left_mem_segment ℝ _ _)),
    Or.inr (left_mem_segment ℝ _ _), Set.union_subset (Set.union_subset hT1 hT2) hT3⟩
  have h12 : IsPreconnected (segment ℝ y (y + (2 * r) • e) ∪ segment ℝ (y + (2 * r) • e) (w + (2 * r) • e)) :=
    (convex_segment _ _).isPreconnected.union (y + (2 * r) • e) (right_mem_segment ℝ _ _)
      (left_mem_segment ℝ _ _) (convex_segment _ _).isPreconnected
  exact h12.union (w + (2 * r) • e) (Or.inr (right_mem_segment ℝ _ _)) (right_mem_segment ℝ _ _)
    (convex_segment _ _).isPreconnected

theorem loc_holder {Ω : Set (Eu d)} (hΩ : IsOpen Ω) {μ : ℝ} (hμ : 0 < μ) {c : Eu d → Eu d}
    (hch : ∀ x0 ∈ frontier Ω, ∃ (r0 K : ℝ) (e b : Eu d) (Θ : Eu d → Eu d) (DΘ : Eu d → Eu d →L[ℝ] Eu d)
      (D2Θ : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] Eu d), ObChart Ω μ c x0 r0 K e b Θ DΘ D2Θ)
    {f : Eu d → ℝ} (hf : EthierKurtz.ComponentHolder Ω μ f) :
    ∀ x0 ∈ closure Ω, ∃ r H : ℝ, 0 < r ∧ 0 ≤ H ∧
      ∀ y ∈ Ω ∩ Metric.ball x0 r, ∀ w ∈ Ω ∩ Metric.ball x0 r, |f y - f w| ≤ H * ‖y - w‖ ^ μ := by
  intro x0 hx0
  obtain ⟨-, ρ0, M, hρ0, hM, hfh⟩ := hf
  have hP : ∃ r1 : ℝ, 0 < r1 ∧ ∀ y ∈ Ω ∩ Metric.ball x0 r1, ∀ w ∈ Ω ∩ Metric.ball x0 r1, y ≠ w →
      ∃ T : Set (Eu d), IsPreconnected T ∧ y ∈ T ∧ w ∈ T ∧ T ⊆ Ω ∩ Metric.ball y (4 * ‖y - w‖) := by
    by_cases hxi : x0 ∈ Ω
    · obtain ⟨R0, hR0, hball0⟩ := Metric.isOpen_iff.mp hΩ x0 hxi
      exact ⟨R0, hR0, path_interior hball0⟩
    · have hfr : x0 ∈ frontier Ω := ⟨hx0, by rwa [hΩ.interior_eq]⟩
      obtain ⟨r0, K, e, b, Θ, DΘ, D2Θ, hc0⟩ := hch x0 hfr
      exact path_boundary hc0
  obtain ⟨r1, hr1, hpath⟩ := hP
  have hr : 0 < min r1 (ρ0 / 8) := lt_min hr1 (by positivity)
  have hsub : ∀ y ∈ Ω ∩ Metric.ball x0 (min r1 (ρ0 / 8)), y ∈ Ω ∩ Metric.ball x0 r1 := fun y hy =>
    ⟨hy.1, Metric.ball_subset_ball (min_le_left _ _) hy.2⟩
  refine ⟨min r1 (ρ0 / 8), M * 4 ^ μ, hr, mul_nonneg hM (Real.rpow_nonneg (by norm_num) _), ?_⟩
  refine holder_of_paths hμ (by norm_num : (0 : ℝ) < 4) hM hfh
    (fun y hy w hw hyw => hpath y (hsub y hy) w (hsub w hw) hyw) (fun y hy w hw => ?_)
  have h1 : ‖y - x0‖ < ρ0 / 8 := by
    rw [← dist_eq_norm]; exact lt_of_lt_of_le hy.2 (min_le_right _ _)
  have h2 : ‖w - x0‖ < ρ0 / 8 := by
    rw [← dist_eq_norm]; exact lt_of_lt_of_le hw.2 (min_le_right _ _)
  have : ‖y - w‖ ≤ ‖y - x0‖ + ‖w - x0‖ := by
    calc ‖y - w‖ = ‖(y - x0) - (w - x0)‖ := by congr 1; abel
      _ ≤ ‖y - x0‖ + ‖w - x0‖ := norm_sub_le _ _
  linarith

end HolA

section ExtA

variable {d : ℕ}

lemma ext_tendsto {Ω : Set (Eu d)} {μ : ℝ} (hμ : 0 < μ) {f : Eu d → ℝ} {x0 : Eu d} {r H : ℝ}
    (hH0 : 0 ≤ H)
    (hH : ∀ y ∈ Ω ∩ Metric.ball x0 r, ∀ w ∈ Ω ∩ Metric.ball x0 r, |f y - f w| ≤ H * ‖y - w‖ ^ μ)
    {x : Eu d} (hx : x ∈ closure Ω) (hxr : x ∈ Metric.ball x0 r) :
    Tendsto f (𝓝[Ω] x) (𝓝 (extendFrom Ω f x)) := by
  apply tendsto_extendFrom
  haveI : (𝓝[Ω] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hpos : 0 < r - dist x x0 := by rw [Metric.mem_ball] at hxr; linarith
  have htend : Tendsto (fun δ : ℝ => H * (2 * δ) ^ μ) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun δ : ℝ => H * (2 * δ) ^ μ) 0 :=
      continuousAt_const.mul ((continuousAt_const.mul continuousAt_id).rpow_const (Or.inr hμ.le))
    simpa [Real.zero_rpow hμ.ne'] using hc.tendsto
  have hc : Cauchy (Filter.map f (𝓝[Ω] x)) := by
    rw [Metric.cauchy_iff]
    refine ⟨Filter.map_neBot, fun ε hε => ?_⟩
    have e1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
    have e2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < r - dist x x0 := nhdsWithin_le_nhds (Iio_mem_nhds hpos)
    have e3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), H * (2 * δ) ^ μ < ε :=
      nhdsWithin_le_nhds (htend.eventually (Iio_mem_nhds hε))
    obtain ⟨δ, hδ, hδr, hδε⟩ := (e1.and (e2.and e3)).exists
    have hball : Metric.ball x δ ⊆ Metric.ball x0 r := Metric.ball_subset_ball' (by linarith)
    refine ⟨f '' (Ω ∩ Metric.ball x δ),
      Filter.image_mem_map (inter_mem_nhdsWithin Ω (Metric.ball_mem_nhds x hδ)), ?_⟩
    rintro _ ⟨y, hy, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [Real.dist_eq]
    have hyw : ‖y - w‖ < 2 * δ := by
      rw [← dist_eq_norm]
      have h1 : dist y x < δ := hy.2
      have h2 : dist w x < δ := hw.2
      linarith [dist_triangle_right y w x]
    calc |f y - f w| ≤ H * ‖y - w‖ ^ μ := hH y ⟨hy.1, hball hy.2⟩ w ⟨hw.1, hball hw.2⟩
      _ ≤ H * (2 * δ) ^ μ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hyw.le hμ.le) hH0
      _ < ε := hδε
  obtain ⟨l, hl⟩ := CompleteSpace.complete hc
  exact ⟨l, hl⟩

lemma ext_holder {Ω : Set (Eu d)} {μ : ℝ} (hμ : 0 < μ) {f : Eu d → ℝ} {x0 : Eu d} {r H : ℝ}
    (hH0 : 0 ≤ H)
    (hH : ∀ y ∈ Ω ∩ Metric.ball x0 r, ∀ w ∈ Ω ∩ Metric.ball x0 r, |f y - f w| ≤ H * ‖y - w‖ ^ μ)
    {x x' : Eu d} (hx : x ∈ Metric.ball x0 r ∩ closure Ω) (hx' : x' ∈ Metric.ball x0 r ∩ closure Ω) :
    |extendFrom Ω f x - extendFrom Ω f x'| ≤ H * ‖x - x'‖ ^ μ := by
  haveI : (𝓝[Ω] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx.2
  haveI : (𝓝[Ω] x').NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx'.2
  have t1 := ext_tendsto hμ hH0 hH hx.2 hx.1
  have t2 := ext_tendsto hμ hH0 hH hx'.2 hx'.1
  have hl : Tendsto (fun p : Eu d × Eu d => |f p.1 - f p.2|) (𝓝[Ω] x ×ˢ 𝓝[Ω] x')
      (𝓝 |extendFrom Ω f x - extendFrom Ω f x'|) :=
    ((t1.comp tendsto_fst).sub (t2.comp tendsto_snd)).abs
  have hcont : Continuous (fun p : Eu d × Eu d => H * ‖p.1 - p.2‖ ^ μ) :=
    continuous_const.mul ((continuous_fst.sub continuous_snd).norm.rpow_const (fun _ => Or.inr hμ.le))
  have hr : Tendsto (fun p : Eu d × Eu d => H * ‖p.1 - p.2‖ ^ μ) (𝓝[Ω] x ×ˢ 𝓝[Ω] x')
      (𝓝 (H * ‖x - x'‖ ^ μ)) := by
    have := hcont.tendsto (x, x')
    rw [nhds_prod_eq] at this
    exact this.mono_left (Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds)
  have m1 : Ω ∩ Metric.ball x0 r ∈ 𝓝[Ω] x := inter_mem_nhdsWithin Ω (Metric.isOpen_ball.mem_nhds hx.1)
  have m2 : Ω ∩ Metric.ball x0 r ∈ 𝓝[Ω] x' := inter_mem_nhdsWithin Ω (Metric.isOpen_ball.mem_nhds hx'.1)
  have hev : ∀ᶠ p in 𝓝[Ω] x ×ˢ 𝓝[Ω] x', |f p.1 - f p.2| ≤ H * ‖p.1 - p.2‖ ^ μ := by
    filter_upwards [Filter.prod_mem_prod m1 m2] with p hp
    exact hH p.1 hp.1 p.2 hp.2
  exact le_of_tendsto_of_tendsto hl hr hev

lemma fam_unif {ι : Type*} [Fintype ι] {X : Set (Eu d)} {x0 : Eu d} {μ : ℝ} (E : ι → Eu d → ℝ)
    (h : ∀ k, ∃ r H : ℝ, 0 < r ∧ 0 ≤ H ∧ ∀ x ∈ Metric.ball x0 r ∩ X, ∀ x' ∈ Metric.ball x0 r ∩ X,
      |E k x - E k x'| ≤ H * ‖x - x'‖ ^ μ) :
    ∃ r H : ℝ, 0 < r ∧ 0 ≤ H ∧ ∀ k, ∀ x ∈ Metric.ball x0 r ∩ X, ∀ x' ∈ Metric.ball x0 r ∩ X,
      |E k x - E k x'| ≤ H * ‖x - x'‖ ^ μ := by
  choose r H hr hH hE using h
  have hS : 0 ≤ ∑ k, 1 / r k := Finset.sum_nonneg (fun k _ => (one_div_pos.mpr (hr k)).le)
  refine ⟨1 / (1 + ∑ k, 1 / r k), ∑ k, H k, div_pos one_pos (by linarith),
    Finset.sum_nonneg (fun k _ => hH k), fun k x hx x' hx' => ?_⟩
  have hrk : 1 / (1 + ∑ k, 1 / r k) ≤ r k := by
    have h1 : 1 / r k ≤ 1 + ∑ k, 1 / r k := by
      have := Finset.single_le_sum (f := fun k => 1 / r k) (fun k _ => (one_div_pos.mpr (hr k)).le)
        (Finset.mem_univ k)
      linarith
    rw [div_le_iff₀ (by linarith)]
    rw [div_le_iff₀ (hr k)] at h1
    linarith [mul_comm (r k) (1 + ∑ k, 1 / r k)]
  have hs : ∀ y ∈ Metric.ball x0 (1 / (1 + ∑ k, 1 / r k)) ∩ X, y ∈ Metric.ball x0 (r k) ∩ X :=
    fun y hy => ⟨Metric.ball_subset_ball hrk hy.1, hy.2⟩
  calc |E k x - E k x'| ≤ H k * ‖x - x'‖ ^ μ := hE k x (hs x hx) x' (hs x' hx')
    _ ≤ (∑ k, H k) * ‖x - x'‖ ^ μ :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun k _ => hH k) (Finset.mem_univ k))
          (Real.rpow_nonneg (norm_nonneg _) _)

lemma eu_norm_le_sum (v : Eu d) : ‖v‖ ≤ ∑ i, |v i| := by
  calc ‖v‖ = Real.sqrt (∑ i, ‖v i‖ ^ 2) := EuclideanSpace.norm_eq v
    _ ≤ Real.sqrt ((∑ i, |v i|) ^ 2) := by
        apply Real.sqrt_le_sqrt
        simp only [Real.norm_eq_abs]
        exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)
    _ = ∑ i, |v i| := Real.sqrt_sq (Finset.sum_nonneg fun i _ => abs_nonneg _)

/-- Extension of a matrix field from `Ω` by limits. -/
noncomputable def extM (Ω : Set (Eu d)) (a : Eu d → Matrix (Fin d) (Fin d) ℝ) : Eu d → Matrix (Fin d) (Fin d) ℝ :=
  fun x => Matrix.of fun i j => extendFrom Ω (fun y => a y i j) x

/-- Extension of a vector field from `Ω` by limits. -/
noncomputable def extV (Ω : Set (Eu d)) (b : Eu d → Eu d) : Eu d → Eu d :=
  fun x => WithLp.toLp 2 (fun i => extendFrom Ω (fun y => b y i) x)

lemma extM_apply (Ω : Set (Eu d)) (a : Eu d → Matrix (Fin d) (Fin d) ℝ) (x : Eu d) (i j : Fin d) :
    extM Ω a x i j = extendFrom Ω (fun y => a y i j) x := rfl

lemma extV_apply (Ω : Set (Eu d)) (b : Eu d → Eu d) (x : Eu d) (i : Fin d) :
    extV Ω b x i = extendFrom Ω (fun y => b y i) x := rfl

lemma ext_eq_on {Ω : Set (Eu d)} {f : Eu d → ℝ} (hf : ContinuousOn f Ω) {x : Eu d} (hx : x ∈ Ω) :
    extendFrom Ω f x = f x :=
  extendFrom_eq (subset_closure hx) (hf x hx)

theorem coef_ext_eq {Ω : Set (Eu d)} {μ : ℝ} {a : Eu d → Matrix (Fin d) (Fin d) ℝ} {b : Eu d → Eu d}
    (haH : ∀ i j, EthierKurtz.ComponentHolder Ω μ (fun x => a x i j))
    (hbH : ∀ i, EthierKurtz.ComponentHolder Ω μ (fun x => b x i)) :
    ∀ x ∈ Ω, extM Ω a x = a x ∧ extV Ω b x = b x := by
  intro x hx
  refine ⟨?_, ?_⟩
  · ext i j
    rw [extM_apply]
    exact ext_eq_on (haH i j).1 hx
  · ext i
    rw [extV_apply]
    exact ext_eq_on (hbH i).1 hx

theorem coef_ext_hA {Ω : Set (Eu d)} (hΩ : IsOpen Ω) {μ : ℝ} (hμ : 0 < μ) {c : Eu d → Eu d}
    (hch : ∀ x0 ∈ frontier Ω, ∃ (r0 K : ℝ) (e b : Eu d) (Θ : Eu d → Eu d) (DΘ : Eu d → Eu d →L[ℝ] Eu d)
      (D2Θ : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] Eu d), ObChart Ω μ c x0 r0 K e b Θ DΘ D2Θ)
    {a : Eu d → Matrix (Fin d) (Fin d) ℝ} {b : Eu d → Eu d}
    (haH : ∀ i j, EthierKurtz.ComponentHolder Ω μ (fun x => a x i j))
    (hbH : ∀ i, EthierKurtz.ComponentHolder Ω μ (fun x => b x i)) :
    ∀ x0 ∈ closure Ω, ∃ R Ka : ℝ, 0 < R ∧
      (∀ x ∈ Metric.ball x0 R ∩ closure Ω, ∑ i, ∑ j, |extM Ω a x i j| ≤ Ka ∧ ‖extV Ω b x‖ ≤ Ka) ∧
      (∀ x ∈ Metric.ball x0 R ∩ closure Ω, ∀ x' ∈ Metric.ball x0 R ∩ closure Ω,
        ∑ i, ∑ j, |extM Ω a x i j - extM Ω a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧
        ‖extV Ω b x - extV Ω b x'‖ ≤ Ka * ‖x - x'‖ ^ μ) := by
  intro x0 hx0
  let E : (Fin d × Fin d) ⊕ Fin d → Eu d → ℝ := fun k => match k with
    | Sum.inl ij => extendFrom Ω (fun y => a y ij.1 ij.2)
    | Sum.inr i => extendFrom Ω (fun y => b y i)
  have hEk : ∀ k, ∃ r H : ℝ, 0 < r ∧ 0 ≤ H ∧ ∀ x ∈ Metric.ball x0 r ∩ closure Ω,
      ∀ x' ∈ Metric.ball x0 r ∩ closure Ω, |E k x - E k x'| ≤ H * ‖x - x'‖ ^ μ := by
    intro k
    rcases k with ⟨i, j⟩ | i
    · obtain ⟨r, H, hr, hH0, hH⟩ := loc_holder hΩ hμ hch (haH i j) x0 hx0
      exact ⟨r, H, hr, hH0, fun x hx x' hx' => ext_holder hμ hH0 hH hx hx'⟩
    · obtain ⟨r, H, hr, hH0, hH⟩ := loc_holder hΩ hμ hch (hbH i) x0 hx0
      exact ⟨r, H, hr, hH0, fun x hx x' hx' => ext_holder hμ hH0 hH hx hx'⟩
  obtain ⟨r, H, hr, hH0, hE⟩ := fam_unif E hEk
  have hx0r : x0 ∈ Metric.ball x0 r ∩ closure Ω := ⟨Metric.mem_ball_self hr, hx0⟩
  have hEa : ∀ i j x, E (Sum.inl (i, j)) x = extM Ω a x i j := fun _ _ _ => rfl
  have hEb : ∀ i x, E (Sum.inr i) x = extV Ω b x i := fun _ _ => rfl
  have hrμ : 0 ≤ r ^ μ := Real.rpow_nonneg hr.le _
  have hb1 : ∀ k, ∀ x ∈ Metric.ball x0 r ∩ closure Ω, |E k x| ≤ |E k x0| + H * r ^ μ := by
    intro k x hx
    have h1 := hE k x hx x0 hx0r
    have h2 : ‖x - x0‖ ^ μ ≤ r ^ μ := by
      apply Real.rpow_le_rpow (norm_nonneg _) _ hμ.le
      rw [← dist_eq_norm]; exact hx.1.le
    have h3 : |E k x| ≤ |E k x0| + |E k x - E k x0| := by
      have := abs_add_le (E k x0) (E k x - E k x0)
      rwa [add_sub_cancel] at this
    nlinarith [mul_le_mul_of_nonneg_left h2 hH0]
  set A0 := ∑ i, ∑ j, |extM Ω a x0 i j|
  set B0 := ∑ i, |extV Ω b x0 i|
  have hA0 : 0 ≤ A0 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hB0 : 0 ≤ B0 := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hdd : (0 : ℝ) ≤ (d : ℝ) * d + d := by positivity
  have hHr : 0 ≤ H * r ^ μ := mul_nonneg hH0 hrμ
  refine ⟨r, A0 + B0 + ((d : ℝ) * d + d) * (H * r ^ μ) + ((d : ℝ) * d + d) * H, hr, fun x hx => ?_,
    fun x hx x' hx' => ?_⟩
  · have hsa : ∑ i, ∑ j, |extM Ω a x i j| ≤ A0 + (d : ℝ) * d * (H * r ^ μ) := by
      calc ∑ i, ∑ j, |extM Ω a x i j| ≤ ∑ i : Fin d, ∑ j : Fin d, (|extM Ω a x0 i j| + H * r ^ μ) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
              rw [← hEa, ← hEa]; exact hb1 (Sum.inl (i, j)) x hx
        _ = A0 + (d : ℝ) * d * (H * r ^ μ) := by
            simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            ring
    have hsb : ‖extV Ω b x‖ ≤ B0 + (d : ℝ) * (H * r ^ μ) := by
      calc ‖extV Ω b x‖ ≤ ∑ i, |extV Ω b x i| := eu_norm_le_sum _
        _ ≤ ∑ i : Fin d, (|extV Ω b x0 i| + H * r ^ μ) :=
            Finset.sum_le_sum fun i _ => by rw [← hEb, ← hEb]; exact hb1 (Sum.inr i) x hx
        _ = B0 + (d : ℝ) * (H * r ^ μ) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have h1 : (d : ℝ) * d * (H * r ^ μ) ≤ ((d : ℝ) * d + d) * (H * r ^ μ) := by nlinarith
    have h2 : (d : ℝ) * (H * r ^ μ) ≤ ((d : ℝ) * d + d) * (H * r ^ μ) := by nlinarith
    have h3 : 0 ≤ ((d : ℝ) * d + d) * H := mul_nonneg hdd hH0
    constructor <;> linarith
  · have hp : 0 ≤ ‖x - x'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    have hsa : ∑ i, ∑ j, |extM Ω a x i j - extM Ω a x' i j| ≤ (d : ℝ) * d * H * ‖x - x'‖ ^ μ := by
      calc ∑ i, ∑ j, |extM Ω a x i j - extM Ω a x' i j| ≤ ∑ i : Fin d, ∑ j : Fin d, H * ‖x - x'‖ ^ μ :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
              rw [← hEa, ← hEa]; exact hE (Sum.inl (i, j)) x hx x' hx'
        _ = (d : ℝ) * d * H * ‖x - x'‖ ^ μ := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    have hsb : ‖extV Ω b x - extV Ω b x'‖ ≤ (d : ℝ) * H * ‖x - x'‖ ^ μ := by
      calc ‖extV Ω b x - extV Ω b x'‖ ≤ ∑ i, |(extV Ω b x - extV Ω b x') i| := eu_norm_le_sum _
        _ ≤ ∑ i : Fin d, H * ‖x - x'‖ ^ μ := Finset.sum_le_sum fun i _ => by
            rw [PiLp.sub_apply, ← hEb, ← hEb]; exact hE (Sum.inr i) x hx x' hx'
        _ = (d : ℝ) * H * ‖x - x'‖ ^ μ := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hK : ((d : ℝ) * d + d) * H ≤ A0 + B0 + ((d : ℝ) * d + d) * (H * r ^ μ) + ((d : ℝ) * d + d) * H := by
      nlinarith
    have h1 : (d : ℝ) * d * H * ‖x - x'‖ ^ μ ≤ ((d : ℝ) * d + d) * H * ‖x - x'‖ ^ μ := by
      have : (d : ℝ) * d * H ≤ ((d : ℝ) * d + d) * H := by nlinarith
      exact mul_le_mul_of_nonneg_right this hp
    have h2 : (d : ℝ) * H * ‖x - x'‖ ^ μ ≤ ((d : ℝ) * d + d) * H * ‖x - x'‖ ^ μ := by
      have : (d : ℝ) * H ≤ ((d : ℝ) * d + d) * H := by nlinarith
      exact mul_le_mul_of_nonneg_right this hp
    have h3 := mul_le_mul_of_nonneg_right hK hp
    constructor <;> linarith

theorem coef_ext_pd {Ω : Set (Eu d)} (hΩ : IsOpen Ω) {μ : ℝ} (hμ : 0 < μ) {c : Eu d → Eu d}
    (hch : ∀ x0 ∈ frontier Ω, ∃ (r0 K : ℝ) (e b : Eu d) (Θ : Eu d → Eu d) (DΘ : Eu d → Eu d →L[ℝ] Eu d)
      (D2Θ : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] Eu d), ObChart Ω μ c x0 r0 K e b Θ DΘ D2Θ)
    {a : Eu d → Matrix (Fin d) (Fin d) ℝ}
    (haH : ∀ i j, EthierKurtz.ComponentHolder Ω μ (fun x => a x i j))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (hell : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Ω, ∀ θ : Eu d, ‖θ‖ = 1 → ε ≤ ∑ i, ∑ j, θ i * a x i j * θ j) :
    ∀ x ∈ closure Ω, (extM Ω a x).PosDef := by
  intro x hx
  obtain ⟨ε, hε, hell⟩ := hell
  haveI : (𝓝[Ω] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hT : ∀ i j, Tendsto (fun y => a y i j) (𝓝[Ω] x) (𝓝 (extM Ω a x i j)) := by
    intro i j
    obtain ⟨r, H, hr, hH0, hH⟩ := loc_holder hΩ hμ hch (haH i j) x hx
    exact ext_tendsto hμ hH0 hH hx (Metric.mem_ball_self hr)
  have hsym : ∀ i j, extM Ω a x i j = extM Ω a x j i := by
    intro i j
    refine tendsto_nhds_unique (hT i j) ((hT j i).congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with y hy
    have := (ha y hy).1
    have h2 := congrFun (congrFun this i) j
    simp only [Matrix.conjTranspose_apply, star_trivial] at h2
    exact h2
  have hq : ∀ θ : Eu d, ‖θ‖ = 1 → ε ≤ ∑ i, ∑ j, θ i * extM Ω a x i j * θ j := by
    intro θ hθ
    have hl : Tendsto (fun y => ∑ i, ∑ j, θ i * a y i j * θ j) (𝓝[Ω] x)
        (𝓝 (∑ i, ∑ j, θ i * extM Ω a x i j * θ j)) :=
      tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ =>
        ((hT i j).const_mul (θ i)).mul_const (θ j)
    refine ge_of_tendsto hl ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hell y hy θ hθ
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    rw [star_trivial]
    exact hsym j i
  · set w : Eu d := WithLp.toLp 2 v with hw
    have hw0 : w ≠ 0 := by
      intro h0; apply hv; ext i
      have := congrArg (fun z : Eu d => z i) h0
      simpa [hw] using this
    have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    set θ : Eu d := ‖w‖⁻¹ • w with hθ
    have hθ1 : ‖θ‖ = 1 := by
      rw [hθ, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hθi : ∀ i, θ i = ‖w‖⁻¹ * v i := fun i => by simp [hθ, hw]
    have h1 := hq θ hθ1
    have h2 : ∑ i, ∑ j, θ i * extM Ω a x i j * θ j =
        (‖w‖⁻¹) ^ 2 * ∑ i, ∑ j, v i * extM Ω a x i j * v j := by
      simp only [hθi]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have h3 : dotProduct (star v) (Matrix.mulVec (extM Ω a x) v) = ∑ i, ∑ j, v i * extM Ω a x i j * v j := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h3]
    rw [h2] at h1
    have h4 : 0 < (‖w‖⁻¹) ^ 2 := by positivity
    by_contra hneg
    push_neg at hneg
    have := mul_nonpos_of_nonneg_of_nonpos h4.le hneg
    linarith

end ExtA

end ObliqueLib

theorem solution (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ)
    (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hch : ∀ x0 ∈ frontier Ω, ∃ (r0 K : ℝ) (e b : EuclideanSpace ℝ (Fin d))
        (Θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (DΘ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
        (D2Θ : EuclideanSpace ℝ (Fin d) →
          EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
        0 < r0 ∧ ‖e‖ = 1 ∧ inner ℝ b e = 0 ∧
        (∀ x ∈ Metric.ball x0 r0, HasStrictFDerivAt Θ (DΘ x) x) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ Ω, HasFDerivAt DΘ (D2Θ x) x) ∧
        Θ x0 = 0 ∧ DΘ x0 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) ∧
        (∀ x ∈ Metric.ball x0 r0,
          (x ∈ Ω ↔ 0 < inner ℝ (Θ x) e) ∧ (x ∈ frontier Ω ↔ inner ℝ (Θ x) e = 0)) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ frontier Ω, ∃ κ : ℝ, 0 < κ ∧ DΘ x (c x) = κ • (b - e)) ∧
        0 ≤ K ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ y ∈ Metric.ball x0 r0 ∩ closure Ω,
          ‖Θ x - Θ y‖ ≤ K * ‖x - y‖) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ‖DΘ x‖ ≤ K) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ y ∈ Metric.ball x0 r0 ∩ closure Ω,
          ‖DΘ x - DΘ y‖ ≤ K * ‖x - y‖) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ‖D2Θ x‖ ≤ K) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ y ∈ Metric.ball x0 r0 ∩ closure Ω,
          ‖D2Θ x - D2Θ y‖ ≤ K * ‖x - y‖ ^ μ))
    (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (haH : ∀ i j, EthierKurtz.ComponentHolder Ω μ (fun x => a x i j))
    (hbH : ∀ i, EthierKurtz.ComponentHolder Ω μ (fun x => b x i))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (hell : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Ω, ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ = 1 → ε ≤ ∑ i, ∑ j, θ i * a x i j * θ j) :
    ∃ (abar : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (bbar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      (∀ x ∈ Ω, abar x = a x ∧ bbar x = b x) ∧
      (∀ x0 ∈ closure Ω, ∃ R Ka : ℝ, 0 < R ∧
        (∀ x ∈ Metric.ball x0 R ∩ closure Ω, ∑ i, ∑ j, |abar x i j| ≤ Ka ∧ ‖bbar x‖ ≤ Ka) ∧
        (∀ x ∈ Metric.ball x0 R ∩ closure Ω, ∀ x' ∈ Metric.ball x0 R ∩ closure Ω,
          ∑ i, ∑ j, |abar x i j - abar x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧ ‖bbar x - bbar x'‖ ≤ Ka * ‖x - x'‖ ^ μ)) ∧
      (∀ x ∈ closure Ω, (abar x).PosDef) := by
  have hch' : ∀ x0 ∈ frontier Ω, ∃ (r0 K : ℝ) (e b : ObliqueLib.Eu d) (Θ : ObliqueLib.Eu d → ObliqueLib.Eu d)
      (DΘ : ObliqueLib.Eu d → ObliqueLib.Eu d →L[ℝ] ObliqueLib.Eu d)
      (D2Θ : ObliqueLib.Eu d → ObliqueLib.Eu d →L[ℝ] ObliqueLib.Eu d →L[ℝ] ObliqueLib.Eu d),
      ObliqueLib.ObChart Ω μ c x0 r0 K e b Θ DΘ D2Θ := by
    intro x0 hx0
    obtain ⟨r0, K, e, b, Θ, DΘ, D2Θ, h1, h2, h3, h4, h5, h6, h7, h8, h9, k1, k2, k3, k4, k5, k6⟩ :=
      hch x0 hx0
    exact ⟨r0, K, e, b, Θ, DΘ, D2Θ, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ⟨k1, k2, k3, k4, k5, k6⟩⟩⟩
  exact ⟨ObliqueLib.extM Ω a, ObliqueLib.extV Ω b, ObliqueLib.coef_ext_eq haH hbH,
    ObliqueLib.coef_ext_hA hΩ hμ hch' haH hbH, ObliqueLib.coef_ext_pd hΩ hμ hch' haH ha hell⟩
