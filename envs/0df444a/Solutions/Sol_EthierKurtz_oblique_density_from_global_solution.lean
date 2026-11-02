-- Prove2me | solution 1 for EthierKurtz.oblique_density_from_global_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T00:44:45.570246+00:00
-- url     : https://prove2.me/submissions/62f3175c-5b89-4d64-b003-fab22696b603

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
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

lemma C2B.mono {T : Set E} {μ K K' : ℝ} {f : E → F} {Df : E → E →L[ℝ] F}
    {D2f : E → E →L[ℝ] E →L[ℝ] F} (h : C2B T μ K f Df D2f) (hKK : K ≤ K') : C2B T μ K' f Df D2f where
  hK := h.hK.trans hKK
  lip x hx y hy := (h.lip x hx y hy).trans (by gcongr)
  b1 x hx := (h.b1 x hx).trans hKK
  lip1 x hx y hy := (h.lip1 x hx y hy).trans (by gcongr)
  b2 x hx := (h.b2 x hx).trans hKK
  hol2 x hx y hy := (h.hol2 x hx y hy).trans (by gcongr)

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

section Pull

variable {d : ℕ}

lemma ObChart.mem_closure_iff {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} {x0 : Eu d} {r0 K : ℝ}
    {e b : Eu d} {Θ : Eu d → Eu d} {DΘ : Eu d → Eu d →L[ℝ] Eu d}
    {D2Θ : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] Eu d} (hch : ObChart Ω μ c x0 r0 K e b Θ DΘ D2Θ)
    {x : Eu d} (hx : x ∈ Metric.ball x0 r0) : x ∈ closure Ω ↔ 0 ≤ inner ℝ (Θ x) e := by
  constructor
  · intro h
    by_cases hΩ : x ∈ Ω
    · exact ((hch.side x hx).1.mp hΩ).le
    · have hf : x ∈ frontier Ω := ⟨h, fun hi => hΩ (interior_subset hi)⟩
      exact ((hch.side x hx).2.mp hf).ge
  · intro h
    rcases h.lt_or_eq with h | h
    · exact subset_closure ((hch.side x hx).1.mpr h)
    · exact frontier_subset_closure ((hch.side x hx).2.mpr h.symm)

end Pull

section BumpS

variable {d : ℕ}

end BumpS

section CutDefS

variable {d : ℕ}

end CutDefS

section CutS

variable {d : ℕ}

end CutS

noncomputable local instance instL2NO (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2SO (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

section Series

variable {d : ℕ}

/-- `f` is bounded by `M` and `μ`-Hölder with constant `H` on `X`. -/
def HB (X : Set (Eu d)) (μ M H : ℝ) (f : Eu d → ℝ) : Prop :=
  0 ≤ M ∧ 0 ≤ H ∧ (∀ x ∈ X, |f x| ≤ M) ∧ ∀ x ∈ X, ∀ y ∈ X, |f x - f y| ≤ H * ‖x - y‖ ^ μ

end Series

section ZextS

variable {d : ℕ}

end ZextS

section ProdS

variable {d : ℕ}

end ProdS

section PatchS

variable {d : ℕ}

end PatchS

section LocDefS

variable {d : ℕ}

def LocSol (Ω : Set (Eu d)) (μ : ℝ) (c : Eu d → Eu d) (x0 : Eu d) (ρ lam0 C : ℝ) : Prop :=
  ∀ lam : ℝ, lam0 ≤ lam →
    ∀ (g : Eu d → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ x ∈ closure Ω, |g x| ≤ M) →
    (∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |g x - g y| ≤ H * ‖x - y‖ ^ μ) →
    ∃ (W : Eu d → ℝ) (W1 : Eu d → Eu d →L[ℝ] ℝ) (W2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
      (∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt W (W1 x) x ∧ HasFDerivAt W1 (W2 x) x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        lam * W x - (1 / 2 : ℝ) * ∑ i, W2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = g x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, W1 x (c x) = 0) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W1 x‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W2 x‖ ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H)) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ x' ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x - W x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W1 x - W1 x'‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W2 x - W2 x'‖ ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ)

theorem LocSol.mono {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} {x0 : Eu d} {ρ lam0 C ρ' lam0' C' : ℝ}
    (h : LocSol Ω μ c x0 ρ lam0 C) (hρ : ρ' ≤ ρ) (hl0 : 0 < lam0) (hl : lam0 ≤ lam0') (hC : C ≤ C') :
    LocSol Ω μ c x0 ρ' lam0' C' := by
  intro lam hlam g M H hM hH hgb hgh
  have hlp : 0 < lam := hl0.trans_le (hl.trans hlam)
  obtain ⟨W, W1, W2, h1, h2, h3, h4, h5⟩ := h lam (hl.trans hlam) g M H hM hH hgb hgh
  have hs : Metric.ball x0 ρ' ⊆ Metric.ball x0 ρ := Metric.ball_subset_ball hρ
  have hN : 0 ≤ lam ^ (μ / 2) * M + H := add_nonneg (mul_nonneg (Real.rpow_nonneg hlp.le _) hM) hH
  have hi : 0 ≤ 1 / lam := by positivity
  have e1 : 0 ≤ (1 / lam) ^ (μ / 2) := Real.rpow_nonneg hi _
  have e2 : 0 ≤ (1 / lam) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hi _
  refine ⟨W, W1, W2, fun x hx => h1 x ⟨hs hx.1, hx.2⟩, fun x hx => h2 x ⟨hs hx.1, hx.2⟩,
    fun x hx => h3 x ⟨hs hx.1, hx.2⟩, fun x hx => ?_, fun x hx x' hx' => ?_⟩
  · obtain ⟨b0, b1, b2⟩ := h4 x ⟨hs hx.1, hx.2⟩
    refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_⟩
    · have := mul_nonneg (mul_nonneg hi e1) hN
      linarith [mul_le_mul_of_nonneg_right hC this]
    · have := mul_nonneg (mul_nonneg e2 e1) hN
      linarith [mul_le_mul_of_nonneg_right hC this]
    · have := mul_nonneg e1 hN
      linarith [mul_le_mul_of_nonneg_right hC this]
  · obtain ⟨b0, b1, b2⟩ := h5 x ⟨hs hx.1, hx.2⟩ x' ⟨hs hx'.1, hx'.2⟩
    have hp : 0 ≤ ‖x - x'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_⟩
    · have := mul_nonneg (mul_nonneg hi hN) hp
      linarith [mul_le_mul_of_nonneg_right hC this]
    · have := mul_nonneg (mul_nonneg e2 hN) hp
      linarith [mul_le_mul_of_nonneg_right hC this]
    · have := mul_nonneg hN hp
      linarith [mul_le_mul_of_nonneg_right hC this]

end LocDefS

section CanonS

variable {d : ℕ}

lemma HB.congr {X : Set (Eu d)} {μ M H : ℝ} {f f' : Eu d → ℝ} (h : HB X μ M H f) (he : ∀ x ∈ X, f x = f' x) :
    HB X μ M H f' := by
  obtain ⟨hM, hH, hb, hh⟩ := h
  refine ⟨hM, hH, fun x hx => (he x hx) ▸ hb x hx, fun x hx y hy => ?_⟩
  rw [← he x hx, ← he y hy]; exact hh x hx y hy

end CanonS

section GlobalS

variable {d : ℕ}

end GlobalS

lemma hol_contOn {d : ℕ} {F : Type*} [SeminormedAddCommGroup F] {f : Eu d → F} {X : Set (Eu d)}
    {B μ : ℝ} (hμ : 0 < μ) (h : ∀ x ∈ X, ∀ y ∈ X, ‖f x - f y‖ ≤ B * ‖x - y‖ ^ μ) :
    ContinuousOn f X := by
  intro x hx
  have hg : Tendsto (fun y : Eu d => B * ‖y - x‖ ^ μ) (𝓝[X] x) (𝓝 0) := by
    have hc : Continuous (fun y : Eu d => B * ‖y - x‖ ^ μ) :=
      continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const
        fun _ => Or.inr hμ.le)
    have h0 : Tendsto (fun y : Eu d => B * ‖y - x‖ ^ μ) (𝓝[X] x) (𝓝 (B * ‖x - x‖ ^ μ)) :=
      (hc.tendsto x).mono_left nhdsWithin_le_nhds
    simpa [Real.zero_rpow hμ.ne'] using h0
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hg
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact h y hy x hx

section NormA

variable {d : ℕ}

end NormA

section VarA

variable {d : ℕ}

end VarA

section PullA

variable {d : ℕ}

end PullA

section CoefA

variable {d : ℕ}

end CoefA

section LocalSolveA

variable {d : ℕ}

end LocalSolveA

section InteriorA

variable {d : ℕ}

end InteriorA

section PieceA

variable {d : ℕ}

def LocSolA (Ω : Set (Eu d)) (μ : ℝ) (c : Eu d → Eu d) (a : Eu d → Matrix (Fin d) (Fin d) ℝ) (bb : Eu d → Eu d)
    (x0 : Eu d) (ρ lam0 C : ℝ) : Prop :=
  ∀ lam : ℝ, lam0 ≤ lam →
    ∀ (g : Eu d → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ x ∈ closure Ω, |g x| ≤ M) →
    (∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |g x - g y| ≤ H * ‖x - y‖ ^ μ) →
    ∃ (W : Eu d → ℝ) (W1 : Eu d → Eu d →L[ℝ] ℝ) (W2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
      (∀ x ∈ Metric.ball x0 ρ ∩ Ω, HasFDerivAt W (W1 x) x ∧ HasFDerivAt W1 (W2 x) x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        lam * W x - (1 / 2 : ℝ) * ∑ i, ∑ j, a x i j * W2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - W1 x (bb x) = g x) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ frontier Ω, W1 x (c x) = 0) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W1 x‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        ‖W2 x‖ ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H)) ∧
      (∀ x ∈ Metric.ball x0 ρ ∩ closure Ω, ∀ x' ∈ Metric.ball x0 ρ ∩ closure Ω,
        |W x - W x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W1 x - W1 x'‖ ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        ‖W2 x - W2 x'‖ ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ)

theorem LocSolA.mono {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} {a : Eu d → Matrix (Fin d) (Fin d) ℝ}
    {bb : Eu d → Eu d} {x0 : Eu d} {ρ lam0 C ρ' lam0' C' : ℝ}
    (h : LocSolA Ω μ c a bb x0 ρ lam0 C) (hρ : ρ' ≤ ρ) (hl0 : 0 < lam0) (hl : lam0 ≤ lam0') (hC : C ≤ C') :
    LocSolA Ω μ c a bb x0 ρ' lam0' C' := by
  intro lam hlam g M H hM hH hgb hgh
  have hlp : 0 < lam := hl0.trans_le (hl.trans hlam)
  obtain ⟨W, W1, W2, h1, h2, h3, h4, h5⟩ := h lam (hl.trans hlam) g M H hM hH hgb hgh
  have hs : Metric.ball x0 ρ' ⊆ Metric.ball x0 ρ := Metric.ball_subset_ball hρ
  have hN : 0 ≤ lam ^ (μ / 2) * M + H := add_nonneg (mul_nonneg (Real.rpow_nonneg hlp.le _) hM) hH
  have hi : 0 ≤ 1 / lam := by positivity
  have e1 : 0 ≤ (1 / lam) ^ (μ / 2) := Real.rpow_nonneg hi _
  have e2 : 0 ≤ (1 / lam) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hi _
  refine ⟨W, W1, W2, fun x hx => h1 x ⟨hs hx.1, hx.2⟩, fun x hx => h2 x ⟨hs hx.1, hx.2⟩,
    fun x hx => h3 x ⟨hs hx.1, hx.2⟩, fun x hx => ?_, fun x hx x' hx' => ?_⟩
  · obtain ⟨b0, b1, b2⟩ := h4 x ⟨hs hx.1, hx.2⟩
    refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_⟩
    · have := mul_nonneg (mul_nonneg hi e1) hN
      linarith [mul_le_mul_of_nonneg_right hC this]
    · have := mul_nonneg (mul_nonneg e2 e1) hN
      linarith [mul_le_mul_of_nonneg_right hC this]
    · have := mul_nonneg e1 hN
      linarith [mul_le_mul_of_nonneg_right hC this]
  · obtain ⟨b0, b1, b2⟩ := h5 x ⟨hs hx.1, hx.2⟩ x' ⟨hs hx'.1, hx'.2⟩
    have hp : 0 ≤ ‖x - x'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_⟩
    · have := mul_nonneg (mul_nonneg hi hN) hp
      linarith [mul_le_mul_of_nonneg_right hC this]
    · have := mul_nonneg (mul_nonneg e2 hN) hp
      linarith [mul_le_mul_of_nonneg_right hC this]
    · have := mul_nonneg hN hp
      linarith [mul_le_mul_of_nonneg_right hC this]

end PieceA

section ProdA

variable {d : ℕ}

end ProdA

section PatchA

variable {d : ℕ}

end PatchA

section LinA

variable {d : ℕ}

end LinA

section GlobalA

variable {d : ℕ}

end GlobalA

section GSolA

variable {d : ℕ}

/-- Global solvability of the oblique problem for `lam u - ½ a:D²u - Du·bb = g` with Hölder estimates. -/
def GSolA (Ω : Set (Eu d)) (μ : ℝ) (c : Eu d → Eu d) (a : Eu d → Matrix (Fin d) (Fin d) ℝ)
    (bb : Eu d → Eu d) : Prop :=
  ∃ lam1 : ℝ, 1 ≤ lam1 ∧ ∀ lam : ℝ, lam1 ≤ lam → ∀ (g : Eu d → ℝ) (M H : ℝ), HB (closure Ω) μ M H g →
    ∃ (u : Eu d → ℝ) (u1 : Eu d → Eu d →L[ℝ] ℝ) (u2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
      (∀ x ∈ Ω, HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
      (∀ x ∈ frontier Ω, u1 x (c x) = 0) ∧
      (∀ x ∈ closure Ω, lam * u x -
        (1 / 2 : ℝ) * ∑ i, ∑ j, a x i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - u1 x (bb x) = g x) ∧
      (∃ B : ℝ, ∀ x ∈ closure Ω, |u x| ≤ B ∧ ‖u1 x‖ ≤ B ∧ ‖u2 x‖ ≤ B) ∧
      (∃ B : ℝ, ∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |u x - u y| ≤ B * ‖x - y‖ ^ μ ∧
        ‖u1 x - u1 y‖ ≤ B * ‖x - y‖ ^ μ ∧ ‖u2 x - u2 y‖ ≤ B * ‖x - y‖ ^ μ)

end GSolA

section HolA

variable {d : ℕ}

end HolA

section ExtA

variable {d : ℕ}

end ExtA

section GlueA

variable {d : ℕ}

theorem glue_defA {Ω : Set (Eu d)} (hΩ : IsOpen Ω) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    {c : Eu d → Eu d} {a abar : Eu d → Matrix (Fin d) (Fin d) ℝ} {b bbar : Eu d → Eu d}
    (hG : GSolA Ω μ c abar bbar) (heqab : ∀ x ∈ Ω, abar x = a x ∧ bbar x = b x) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (h : BoundedContinuousFunction (closure Ω) ℝ) (C : ℝ), 0 ≤ C →
      (∀ x y : closure Ω, |h x - h y| ≤ C * ‖(x : Eu d) - y‖ ^ μ) →
        ∃ fg ∈ EthierKurtz.obliqueDiffusionGraph Ω μ a b c, lam₀ • fg.1 - fg.2 = h := by
  obtain ⟨lam1, hl1, hsol⟩ := hG
  refine ⟨lam1, by linarith, fun h C hC0 hC => ?_⟩
  obtain ⟨g, hgdef⟩ : ∃ g : Eu d → ℝ, g = EthierKurtz.closedRegionRestriction h := ⟨_, rfl⟩
  have hgx : ∀ x (hx : x ∈ closure Ω), g x = h ⟨x, hx⟩ := fun x hx => by
    rw [hgdef, EthierKurtz.closedRegionRestriction, dif_pos hx]
  have hHB : HB (closure Ω) μ ‖h‖ C g := by
    refine ⟨norm_nonneg _, hC0, fun x hx => ?_, fun x hx y hy => ?_⟩
    · rw [hgx x hx, ← Real.norm_eq_abs]; exact h.norm_coe_le_norm _
    · rw [hgx x hx, hgx y hy]
      exact hC ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨u, u1, u2, hder, hbc, heq, ⟨B0, hB0⟩, ⟨B, hB⟩⟩ := hsol lam1 le_rfl g ‖h‖ C hHB
  have hcu : ContinuousOn u (closure Ω) :=
    hol_contOn hμ0 (fun x hx y hy => by rw [Real.norm_eq_abs]; exact (hB x hx y hy).1)
  have hcu1 : ContinuousOn u1 (closure Ω) := hol_contOn hμ0 (fun x hx y hy => (hB x hx y hy).2.1)
  have hcu2 : ContinuousOn u2 (closure Ω) := hol_contOn hμ0 (fun x hx y hy => (hB x hx y hy).2.2)
  obtain ⟨f, hf⟩ : ∃ f : BoundedContinuousFunction (closure Ω) ℝ, ∀ x : closure Ω, f x = u x :=
    ⟨BoundedContinuousFunction.mkOfBound ⟨fun x => u x, hcu.restrict⟩ (2 * B0) (fun x y => by
      have h1 := abs_le.1 (hB0 x x.2).1
      have h2 := abs_le.1 (hB0 y y.2).1
      show dist (u x) (u y) ≤ 2 * B0
      rw [Real.dist_eq]; exact abs_le.2 ⟨by linarith, by linarith⟩), fun x => rfl⟩
  have hF : ∀ x ∈ closure Ω, EthierKurtz.closedRegionRestriction f x = u x := fun x hx => by
    rw [EthierKurtz.closedRegionRestriction, dif_pos hx, hf]
  have hFev : ∀ x ∈ Ω, EthierKurtz.closedRegionRestriction f =ᶠ[𝓝 x] u := fun x hx =>
    Filter.eventually_of_mem (hΩ.mem_nhds hx) (fun y hy => hF y (subset_closure hy))
  have hD1 : ∀ x ∈ Ω, HasFDerivAt (EthierKurtz.closedRegionRestriction f) (u1 x) x := fun x hx =>
    (hder x hx).1.congr_of_eventuallyEq (hFev x hx)
  have hfd : ∀ x ∈ Ω, fderiv ℝ (EthierKurtz.closedRegionRestriction f) x = u1 x := fun x hx =>
    (hD1 x hx).fderiv
  have hD2 : ∀ x ∈ Ω, HasFDerivAt (fderiv ℝ (EthierKurtz.closedRegionRestriction f)) (u2 x) x :=
    fun x hx => (hder x hx).2.congr_of_eventuallyEq
      (Filter.eventually_of_mem (hΩ.mem_nhds hx) hfd)
  have hD2j : ∀ x ∈ Ω, ∀ v w : Eu d,
      fderiv ℝ (fun y => fderiv ℝ (EthierKurtz.closedRegionRestriction f) y w) x v = u2 x v w := by
    intro x hx v w
    have hh : HasFDerivAt (fun y => fderiv ℝ (EthierKurtz.closedRegionRestriction f) y w)
        ((ContinuousLinearMap.apply ℝ ℝ w).comp (u2 x)) x :=
      (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp x (hD2 x hx)
    rw [hh.fderiv]; rfl
  have hcont2 : ContDiffOn ℝ 2 (EthierKurtz.closedRegionRestriction f) Ω := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from one_add_one_eq_two.symm,
      contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨fun x hx => (hD1 x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [← zero_add (1 : WithTop ℕ∞), contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨fun x hx => (hD2 x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact (hcu2.mono subset_closure).congr (fun x hx => (hD2 x hx).fderiv)
  have hCH : ∀ i j : Fin d, EthierKurtz.ComponentHolder Ω μ (fun x =>
      fderiv ℝ (fun y => fderiv ℝ (EthierKurtz.closedRegionRestriction f) y
        (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) := by
    intro i j
    have hval := fun x hx => hD2j x hx (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j 1)
    refine ⟨?_, 1, 2 * max B 0, one_pos, by positivity, fun ρ hρ _ x z _ y hy w hw => ?_⟩
    · have hc := hcu2.mono (subset_closure (s := Ω))
      exact ((hc.clm_apply continuousOn_const).clm_apply continuousOn_const).congr hval
    · dsimp only
      have hy' := connectedComponentIn_subset _ _ hy
      have hw' := connectedComponentIn_subset _ _ hw
      rw [hval y hy'.1, hval w hw'.1]
      have e : u2 y (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j 1) -
          u2 w (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
          (u2 y - u2 w) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by simp
      rw [e, ← Real.norm_eq_abs]
      have hyw : ‖y - w‖ ≤ 2 * ρ := by
        have a1 : dist y x < ρ := hy'.2
        have a2 : dist w x < ρ := hw'.2
        rw [← dist_eq_norm]; linarith [dist_triangle_right y w x]
      have hpow : ‖y - w‖ ^ μ ≤ 2 * ρ ^ μ := by
        calc ‖y - w‖ ^ μ ≤ (2 * ρ) ^ μ := Real.rpow_le_rpow (norm_nonneg _) hyw hμ0.le
          _ = 2 ^ μ * ρ ^ μ := Real.mul_rpow (by norm_num) hρ.le
          _ ≤ 2 * ρ ^ μ := by
            gcongr
            calc (2 : ℝ) ^ μ ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) hμ1
              _ = 2 := Real.rpow_one 2
      have hB' := (hB y (subset_closure hy'.1) w (subset_closure hw'.1)).2.2
      calc ‖(u2 y - u2 w) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)‖
          ≤ ‖u2 y - u2 w‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ :=
            ContinuousLinearMap.le_opNorm₂ _ _ _
        _ = ‖u2 y - u2 w‖ := by simp [EuclideanSpace.norm_single]
        _ ≤ B * ‖y - w‖ ^ μ := hB'
        _ ≤ max B 0 * ‖y - w‖ ^ μ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _)
        _ ≤ max B 0 * (2 * ρ ^ μ) := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
        _ = 2 * max B 0 * ρ ^ μ := by ring
  refine ⟨(f, lam1 • f - h), ?_, sub_sub_cancel _ _⟩
  simp only [EthierKurtz.obliqueDiffusionGraph, Set.mem_setOf_eq]
  refine ⟨⟨hcont2, hCH⟩, fun x hx => ?_, fun x => u1 x, hcu1.restrict, fun x hx => (hfd x hx).symm,
    fun x hx => hbc x hx⟩
  have hxc : x ∈ closure Ω := subset_closure hx
  have h1 : EthierKurtz.closedRegionRestriction (lam1 • f - h) x = lam1 * u x - g x := by
    rw [EthierKurtz.closedRegionRestriction, dif_pos hxc, hgx x hxc]
    simp [hf]
  have hs : ∑ i : Fin d, ∑ j : Fin d, a x i j *
      fderiv ℝ (fun y => fderiv ℝ (EthierKurtz.closedRegionRestriction f) y
        (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) =
      ∑ i : Fin d, ∑ j : Fin d, a x i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hD2j x hx]
  have hb1 : fderiv ℝ (EthierKurtz.closedRegionRestriction f) x (b x) = u1 x (b x) := by rw [hfd x hx]
  rw [h1, hs, hb1]
  have := heq x hxc
  rw [(heqab x hx).1, (heqab x hx).2] at this
  linarith

theorem holder_dense {Ω : Set (Eu d)} (hbdd : Bornology.IsBounded Ω) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (h : BoundedContinuousFunction (closure Ω) ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (h' : BoundedContinuousFunction (closure Ω) ℝ) (C : ℝ), 0 ≤ C ∧
      (∀ x y : closure Ω, |h' x - h' y| ≤ C * ‖(x : Eu d) - y‖ ^ μ) ∧ ‖h' - h‖ < δ := by
  have hcpt : IsCompact (closure Ω) := hbdd.isCompact_closure
  haveI : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp hcpt
  let A : Subalgebra ℝ C(closure Ω, ℝ) :=
    { carrier := {f | ∃ F : Eu d → ℝ, ContDiff ℝ 1 F ∧ ∀ x : closure Ω, f x = F x}
      mul_mem' := by
        rintro f g ⟨F, hF, hf⟩ ⟨G, hG, hg⟩
        exact ⟨fun z => F z * G z, hF.mul hG, fun x => by simp [hf, hg]⟩
      one_mem' := ⟨fun _ => 1, contDiff_const, fun x => by simp⟩
      add_mem' := by
        rintro f g ⟨F, hF, hf⟩ ⟨G, hG, hg⟩
        exact ⟨fun z => F z + G z, hF.add hG, fun x => by simp [hf, hg]⟩
      zero_mem' := ⟨fun _ => 0, contDiff_const, fun x => by simp⟩
      algebraMap_mem' := fun r => ⟨fun _ => r, contDiff_const, fun x => by simp⟩ }
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    let F : Eu d → ℝ := fun z => inner ℝ z ((x : Eu d) - y)
    have hF : ContDiff ℝ 1 F := contDiff_id.inner ℝ contDiff_const
    let f : C(closure Ω, ℝ) := ⟨fun p => F p, hF.continuous.comp continuous_subtype_val⟩
    refine ⟨f, ⟨f, ⟨F, hF, fun p => rfl⟩, rfl⟩, ?_⟩
    intro hfe
    have hne : (x : Eu d) - y ≠ 0 := sub_ne_zero.mpr (fun h0 => hxy (Subtype.ext h0))
    have h1 : F x - F y = ‖(x : Eu d) - y‖ ^ 2 := by
      simp only [F]
      rw [← inner_sub_left, real_inner_self_eq_norm_sq]
    have h2 : F x = F y := hfe
    have h3 : 0 < ‖(x : Eu d) - y‖ := norm_pos_iff.mpr hne
    nlinarith
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hmem : h.toContinuousMap ∈ closure (A : Set C(closure Ω, ℝ)) := by
    rw [← Subalgebra.topologicalClosure_coe, htop]; trivial
  obtain ⟨f, ⟨F, hF, hfF⟩, hdist⟩ := Metric.mem_closure_iff.mp hmem δ hδ
  obtain ⟨K, hK⟩ := (hF.locallyLipschitz.locallyLipschitzOn (s := closure Ω)).exists_lipschitzOnWith_of_compact hcpt
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp hbdd.closure
  set D0 := max D 0
  refine ⟨BoundedContinuousFunction.mkOfCompact f, K * D0 ^ (1 - μ),
    mul_nonneg K.2 (Real.rpow_nonneg (le_max_right _ _) _), fun x y => ?_, ?_⟩
  · simp only [BoundedContinuousFunction.mkOfCompact_apply, hfF]
    by_cases hxy : (x : Eu d) = y
    · rw [hxy, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg K.2 (Real.rpow_nonneg (le_max_right _ _) _))
        (Real.rpow_nonneg (norm_nonneg _) _)
    have hn : 0 < ‖(x : Eu d) - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have h1 : |F x - F y| ≤ K * ‖(x : Eu d) - y‖ := by
      have := hK.dist_le_mul x x.2 y y.2
      rwa [Real.dist_eq, dist_eq_norm] at this
    have h2 : ‖(x : Eu d) - y‖ = ‖(x : Eu d) - y‖ ^ (1 - μ) * ‖(x : Eu d) - y‖ ^ μ := by
      rw [← Real.rpow_add hn, sub_add_cancel, Real.rpow_one]
    have h3 : ‖(x : Eu d) - y‖ ^ (1 - μ) ≤ D0 ^ (1 - μ) := by
      apply Real.rpow_le_rpow (norm_nonneg _) _ (by linarith)
      rw [← dist_eq_norm]; exact (hD x.2 y.2).trans (le_max_left _ _)
    have h4 : 0 ≤ ‖(x : Eu d) - y‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    calc |F x - F y| ≤ K * ‖(x : Eu d) - y‖ := h1
      _ = K * (‖(x : Eu d) - y‖ ^ (1 - μ) * ‖(x : Eu d) - y‖ ^ μ) := by rw [← h2]
      _ ≤ K * (D0 ^ (1 - μ) * ‖(x : Eu d) - y‖ ^ μ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 h4) K.2
      _ = K * D0 ^ (1 - μ) * ‖(x : Eu d) - y‖ ^ μ := by ring
  · rw [BoundedContinuousFunction.norm_lt_iff_of_compact hδ]
    intro x
    rw [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.mkOfCompact_apply, Real.norm_eq_abs,
      ← Real.dist_eq, dist_comm]
    exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist (f := h.toContinuousMap) (g := f) x) hdist

theorem dense_from_gsol {Ω : Set (Eu d)} (hΩ : IsOpen Ω) (hbdd : Bornology.IsBounded Ω) {μ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {c : Eu d → Eu d} {a abar : Eu d → Matrix (Fin d) (Fin d) ℝ} {b bbar : Eu d → Eu d}
    (hG : GSolA Ω μ c abar bbar) (heqab : ∀ x ∈ Ω, abar x = a x ∧ bbar x = b x) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ h : BoundedContinuousFunction (closure Ω) ℝ, ∀ delta : ℝ, 0 < delta →
      ∃ fg ∈ closure (EthierKurtz.obliqueDiffusionGraph Ω μ a b c),
        ‖(lam₀ • fg.1 - fg.2) - h‖ < delta := by
  obtain ⟨lam₀, hl, hsol⟩ := glue_defA hΩ hμ0 hμ1 hG heqab
  refine ⟨lam₀, hl, fun h delta hdelta => ?_⟩
  obtain ⟨h', C, hC0, hC, hlt⟩ := holder_dense hbdd hμ0 hμ1 h hdelta
  obtain ⟨fg, hfg, hfe⟩ := hsol h' C hC0 hC
  exact ⟨fg, subset_closure hfg, by rw [hfe]; exact hlt⟩

end GlueA

section D1A

end D1A

end ObliqueLib

theorem solution (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : IsOpen Ω) (hbdd : Bornology.IsBounded Ω)
    (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (a abar : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (b bbar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hG : (∃ lam1 : ℝ, 1 ≤ lam1 ∧ ∀ lam : ℝ, lam1 ≤ lam → ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ) (M H : ℝ),
      (0 ≤ M ∧ 0 ≤ H ∧ (∀ x ∈ closure Ω, |g x| ≤ M) ∧
        ∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |g x - g y| ≤ H * ‖x - y‖ ^ μ) →
      ∃ (u : EuclideanSpace ℝ (Fin d) → ℝ) (u1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (u2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
        (∀ x ∈ Ω, HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
        (∀ x ∈ frontier Ω, u1 x (c x) = 0) ∧
        (∀ x ∈ closure Ω, lam * u x -
          (1 / 2 : ℝ) * ∑ i, ∑ j, abar x i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
            - u1 x (bbar x) = g x) ∧
        (∃ B : ℝ, ∀ x ∈ closure Ω, |u x| ≤ B ∧ ‖u1 x‖ ≤ B ∧ ‖u2 x‖ ≤ B) ∧
        (∃ B : ℝ, ∀ x ∈ closure Ω, ∀ y ∈ closure Ω, |u x - u y| ≤ B * ‖x - y‖ ^ μ ∧
          ‖u1 x - u1 y‖ ≤ B * ‖x - y‖ ^ μ ∧ ‖u2 x - u2 y‖ ≤ B * ‖x - y‖ ^ μ)))
    (heqab : ∀ x ∈ Ω, abar x = a x ∧ bbar x = b x) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ h : BoundedContinuousFunction (closure Ω) ℝ, ∀ delta : ℝ, 0 < delta →
      ∃ fg ∈ closure (EthierKurtz.obliqueDiffusionGraph Ω μ a b c),
        ‖(lam₀ • fg.1 - fg.2) - h‖ < delta := by
  have hG' : ObliqueLib.GSolA Ω μ c abar bbar := hG
  exact ObliqueLib.dense_from_gsol hΩ hbdd hμ0 hμ1 hG' heqab
