-- Prove2me | solution 1 for EthierKurtz.oblique_chart_from_core
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T00:02:18.43124+00:00
-- url     : https://prove2.me/submissions/a722ea8c-76bf-4e0f-bb4c-116fb0e992d9

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_COnceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder

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
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
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
    linarith

end Comp2

section HalfLip

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

end HalfLip

section Flat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

end Flat

section PkgDef

end PkgDef

section Shear

variable {d : ℕ}

end Shear

section Glue

variable {n : ℕ}

lemma coord_le (v : Eu n) (i : Fin n) : |v i| ≤ ‖v‖ := by
  have h := abs_real_inner_le_norm v (EuclideanSpace.single i (1 : ℝ))
  rw [EuclideanSpace.inner_single_right, EuclideanSpace.norm_single, norm_one, mul_one] at h
  simpa using h

lemma eu_expand (v : Eu n) : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
  have h := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] at h
  exact h.symm

/-- Operator norm of a bilinear form on `ℝ^n` is at most the sum of the absolute values of its entries. -/
lemma entries_le (A : Eu n →L[ℝ] Eu n →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ i, ∑ j, |A (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun v w => ?_
  have hA : A v w = ∑ i, ∑ j, v i * w j * A (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    conv_lhs => rw [eu_expand v, eu_expand w]
    simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    first
    | (refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring1)
    | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring1)
  rw [Real.norm_eq_abs, hA, Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  set a := A (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  rw [abs_mul, abs_mul]
  have h1 := mul_le_mul (coord_le v i) (coord_le w j) (abs_nonneg _) (norm_nonneg _)
  linarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg a)]

/-- `ComponentHolder` gives a local Hölder bound along segments inside the set. -/
lemma CH_local {D : Set (Eu n)} {μ : ℝ} {f : Eu n → ℝ} (hf : EthierKurtz.ComponentHolder D μ f)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    ∃ ρ₀ M : ℝ, 0 < ρ₀ ∧ 0 ≤ M ∧ ∀ x y : Eu n, segment ℝ x y ⊆ D → ‖x - y‖ ≤ ρ₀ / 2 →
      |f x - f y| ≤ 2 * M * ‖x - y‖ ^ μ := by
  obtain ⟨-, ρ₀, M, hρ₀, hM, h⟩ := hf
  refine ⟨ρ₀, M, hρ₀, hM, fun x y hseg hxy => ?_⟩
  rcases eq_or_ne x y with rfl | hne
  · simp only [sub_self, abs_zero]; positivity
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  set ρ := 2 * ‖x - y‖
  have hρ : 0 < ρ := by positivity
  have hsub : segment ℝ x y ⊆ D ∩ Metric.ball x ρ := by
    intro p hp
    refine ⟨hseg hp, ?_⟩
    have hcb : segment ℝ x y ⊆ Metric.closedBall x ‖x - y‖ :=
      (convex_closedBall x _).segment_subset (Metric.mem_closedBall_self hpos.le)
        (by rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev])
    have := hcb hp
    rw [Metric.mem_closedBall] at this
    rw [Metric.mem_ball]; linarith
  have hxD : x ∈ D ∩ Metric.ball x ρ := hsub (left_mem_segment ℝ x y)
  have hcomp := (convex_segment x y).isPreconnected.subset_connectedComponentIn (left_mem_segment ℝ x y) hsub
  have key := h ρ hρ (by linarith) x x hxD x (hcomp (left_mem_segment ℝ x y)) y (hcomp (right_mem_segment ℝ x y))
  have h2 : ρ ^ μ ≤ 2 * ‖x - y‖ ^ μ := by
    rw [Real.mul_rpow (by norm_num) hpos.le]
    gcongr
    calc (2 : ℝ) ^ μ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hμ1
      _ = 2 := Real.rpow_one 2
  calc |f x - f y| ≤ M * ρ ^ μ := key
    _ ≤ M * (2 * ‖x - y‖ ^ μ) := by gcongr
    _ = 2 * M * ‖x - y‖ ^ μ := by ring

/-- Main glue: `CTwiceHolder` on an open set gives derivative facts and `C2B` on a small closed ball. -/
theorem ctwice_C2B {D : Set (Eu n)} {μ : ℝ} {u : Eu n → ℝ} (hD : IsOpen D)
    (hu : EthierKurtz.CTwiceHolder D μ u) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) :
    (∀ z ∈ D, HasFDerivAt u (fderiv ℝ u z) z ∧
      HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) z) z) ∧
    ∀ z0 ∈ D, ∃ r > 0, Metric.closedBall z0 r ⊆ D ∧
      ∃ K, C2B (Metric.closedBall z0 r) μ K u (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u)) := by
  obtain ⟨hcd, hent⟩ := hu
  have hder : ∀ z ∈ D, HasFDerivAt u (fderiv ℝ u z) z ∧
      HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) z) z := by
    intro z hz
    have hc := hcd.contDiffAt (hD.mem_nhds hz)
    refine ⟨(hc.differentiableAt (by norm_num)).hasFDerivAt, ?_⟩
    have hc1 : ContDiffAt ℝ 1 (fderiv ℝ u) z := hc.fderiv_right (by norm_num)
    exact (hc1.differentiableAt (by norm_num)).hasFDerivAt
  refine ⟨hder, fun z0 hz0 => ?_⟩
  set Du := fderiv ℝ u
  set D2u := fderiv ℝ Du
  -- entries of D2u are the CTwiceHolder second partials
  have hentry : ∀ x ∈ D, ∀ i j : Fin n,
      fderiv ℝ (fun y => Du y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) =
        D2u x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    intro x hx i j
    have h := ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))).hasFDerivAt.comp x
      (hder x hx).2).fderiv
    simp only [Function.comp_def, ContinuousLinearMap.apply_apply] at h
    rw [h]; rfl
  have hloc := fun i j => CH_local (hent i j) hμ0.le hμ1
  choose ρ M hρ hM hH using hloc
  -- choose the radius
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.1 hD z0 hz0
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), (∀ i j, 4 * r < ρ i j) ∧ r < ε := by
    refine nhdsWithin_le_nhds ?_
    refine Filter.Eventually.and ?_ (gt_mem_nhds hε)
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    have h := ((continuous_const.mul continuous_id : Continuous fun r : ℝ => 4 * r).tendsto 0)
    exact h.eventually (gt_mem_nhds (by simp [hρ i j]))
  obtain ⟨r, ⟨hrρ, hrε⟩, hr0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hr0' : (0 : ℝ) < r := hr0
  have hball : Metric.closedBall z0 r ⊆ D :=
    (Metric.closedBall_subset_ball hrε).trans hεD
  refine ⟨r, hr0', hball, ?_⟩
  set S := Metric.closedBall z0 r
  have hconv : Convex ℝ S := convex_closedBall z0 r
  have hdist : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ 2 * r := by
    intro x hx y hy
    rw [← dist_eq_norm]
    calc dist x y ≤ dist x z0 + dist y z0 := dist_triangle_right _ _ _
      _ ≤ r + r := add_le_add hx hy
      _ = 2 * r := by ring
  -- Hölder of D2u
  set Mh := ∑ i, ∑ j, 2 * M i j
  have hMh : 0 ≤ Mh := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by linarith [hM i j]
  have hhol : ∀ x ∈ S, ∀ y ∈ S, ‖D2u x - D2u y‖ ≤ Mh * ‖x - y‖ ^ μ := by
    intro x hx y hy
    refine (entries_le _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have := hH i j x y ((hconv.segment_subset hx hy).trans hball) (by linarith [hdist x hx y hy, hrρ i j])
    rw [hentry x (hball hx), hentry y (hball hy)] at this
    exact this
  have hz0S : z0 ∈ S := Metric.mem_closedBall_self hr0'.le
  set B2 := ‖D2u z0‖ + Mh * r ^ μ
  have hb2 : ∀ x ∈ S, ‖D2u x‖ ≤ B2 := by
    intro x hx
    have h1 := hhol x hx z0 hz0S
    have h2 : ‖x - z0‖ ^ μ ≤ r ^ μ := by
      gcongr; rw [← dist_eq_norm]; exact hx
    have h3 : ‖D2u x‖ ≤ ‖D2u z0‖ + ‖D2u x - D2u z0‖ := by
      have := norm_add_le (D2u z0) (D2u x - D2u z0); simpa using this
    linarith [mul_le_mul_of_nonneg_left h2 hMh]
  have hB2 : 0 ≤ B2 := (norm_nonneg (D2u z0)).trans (hb2 z0 hz0S)
  have hlip1 : ∀ x ∈ S, ∀ y ∈ S, ‖Du x - Du y‖ ≤ B2 * ‖x - y‖ := by
    intro x hx y hy
    exact hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun p hp => ((hder p (hball hp)).2).hasFDerivWithinAt) hb2 hy hx
  set B1 := ‖Du z0‖ + B2 * (2 * r)
  have hb1 : ∀ x ∈ S, ‖Du x‖ ≤ B1 := by
    intro x hx
    have h1 := hlip1 x hx z0 hz0S
    have h3 : ‖Du x‖ ≤ ‖Du z0‖ + ‖Du x - Du z0‖ := by
      have := norm_add_le (Du z0) (Du x - Du z0); simpa using this
    linarith [mul_le_mul_of_nonneg_left (hdist x hx z0 hz0S) hB2]
  have hB1 : 0 ≤ B1 := (norm_nonneg (Du z0)).trans (hb1 z0 hz0S)
  have hlip : ∀ x ∈ S, ∀ y ∈ S, ‖u x - u y‖ ≤ B1 * ‖x - y‖ := by
    intro x hx y hy
    exact hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun p hp => ((hder p (hball hp)).1).hasFDerivWithinAt) hb1 hy hx
  refine ⟨Mh + B2 + B1, ⟨by positivity, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x hx y hy
    exact (hlip x hx y hy).trans (by gcongr; linarith)
  · intro x hx; exact (hb1 x hx).trans (by linarith)
  · intro x hx y hy
    exact (hlip1 x hx y hy).trans (by gcongr; linarith)
  · intro x hx; exact (hb2 x hx).trans (by linarith)
  · intro x hx y hy
    exact (hhol x hx y hy).trans (by gcongr; linarith)

end Glue

section Cutoff

variable {d : ℕ}

end Cutoff

section Graph

variable {n : ℕ}

noncomputable def eL (n : ℕ) : Eu (n + 1) := EuclideanSpace.single (Fin.last n) 1

noncomputable def piL (n : ℕ) : Eu (n + 1) →L[ℝ] Eu n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ξ => WithLp.toLp 2 (fun i => ξ (Fin.castSucc i))
      map_add' := fun a b => by refine PiLp.ext fun i => ?_; simp
      map_smul' := fun c a => by refine PiLp.ext fun i => ?_; simp }

noncomputable def iL (n : ℕ) : Eu n →L[ℝ] Eu (n + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (Fin.lastCases (0 : ℝ) (fun i => z i))
      map_add' := fun a b => by
        refine PiLp.ext fun j => ?_
        cases j using Fin.lastCases <;> simp
      map_smul' := fun c a => by
        refine PiLp.ext fun j => ?_
        cases j using Fin.lastCases <;> simp }

/-- The graph map of the Definitions' boundary charts. -/
noncomputable def gr (u : Eu n → ℝ) (z : Eu n) : Eu (n + 1) :=
  (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)) : EuclideanSpace ℝ (Fin (n + 1)))

lemma piL_apply (ξ : Eu (n + 1)) (i : Fin n) : piL n ξ i = ξ (Fin.castSucc i) := rfl

lemma iL_castSucc (z : Eu n) (i : Fin n) : iL n z (Fin.castSucc i) = z i := by simp [iL]

lemma iL_last (z : Eu n) : iL n z (Fin.last n) = 0 := by simp [iL]

lemma eL_castSucc (i : Fin n) : eL n (Fin.castSucc i) = 0 := by
  simp [eL, EuclideanSpace.single_apply, Fin.castSucc_ne_last]

lemma eL_last : eL n (Fin.last n) = 1 := by simp [eL]

lemma norm_eL : ‖eL n‖ = 1 := by simp [eL]

lemma gr_castSucc (u : Eu n → ℝ) (z : Eu n) (i : Fin n) : gr u z (Fin.castSucc i) = z i := by simp [gr]

lemma gr_last (u : Eu n → ℝ) (z : Eu n) : gr u z (Fin.last n) = u z := by simp [gr]

lemma piL_iL (z : Eu n) : piL n (iL n z) = z := PiLp.ext fun i => by rw [piL_apply, iL_castSucc]

lemma piL_eL : piL n (eL n) = 0 := PiLp.ext fun i => by rw [piL_apply, eL_castSucc]; rfl

lemma piL_gr (u : Eu n → ℝ) (z : Eu n) : piL n (gr u z) = z :=
  PiLp.ext fun i => by rw [piL_apply, gr_castSucc]

lemma inner_eL (ξ : Eu (n + 1)) : inner ℝ ξ (eL n) = ξ (Fin.last n) := by
  simp [eL, EuclideanSpace.inner_single_right]

lemma decomp (ξ : Eu (n + 1)) : ξ = iL n (piL n ξ) + ξ (Fin.last n) • eL n := by
  refine PiLp.ext fun j => ?_
  cases j using Fin.lastCases with
  | last => simp [iL_last, eL_last]
  | cast i => simp [iL_castSucc, eL_castSucc, piL_apply]

lemma gr_eq (u : Eu n → ℝ) (z : Eu n) : gr u z = iL n z + u z • eL n := by
  refine PiLp.ext fun j => ?_
  cases j using Fin.lastCases with
  | last => simp [iL_last, eL_last, gr_last]
  | cast i => simp [iL_castSucc, eL_castSucc, gr_castSucc]

lemma norm_sq_split (ξ : Eu (n + 1)) : ‖ξ‖ ^ 2 = ‖piL n ξ‖ ^ 2 + ξ (Fin.last n) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp only [piL_apply, Real.norm_eq_abs, sq_abs]

lemma norm_piL_apply_le (ξ : Eu (n + 1)) : ‖piL n ξ‖ ≤ ‖ξ‖ := by
  have h := norm_sq_split ξ
  have h2 : ‖piL n ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by linarith [sq_nonneg (ξ (Fin.last n))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

lemma norm_piL_le : ‖piL n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => by rw [one_mul]; exact norm_piL_apply_le ξ

lemma norm_iL_apply (z : Eu n) : ‖iL n z‖ = ‖z‖ := by
  have h := norm_sq_split (iL n z)
  rw [piL_iL, iL_last] at h
  have h2 : ‖iL n z‖ ^ 2 = ‖z‖ ^ 2 := by rw [h]; ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

/-- Flattening map and its global inverse. -/
noncomputable def Fl (u : Eu n → ℝ) (ξ : Eu (n + 1)) : Eu (n + 1) := ξ - u (piL n ξ) • eL n

noncomputable def Flinv (u : Eu n → ℝ) (ξ : Eu (n + 1)) : Eu (n + 1) := ξ + u (piL n ξ) • eL n

lemma piL_Fl (u : Eu n → ℝ) (ξ : Eu (n + 1)) : piL n (Fl u ξ) = piL n ξ := by
  simp [Fl, map_sub, map_smul, piL_eL]

lemma piL_Flinv (u : Eu n → ℝ) (ξ : Eu (n + 1)) : piL n (Flinv u ξ) = piL n ξ := by
  simp [Flinv, map_add, map_smul, piL_eL]

lemma Fl_Flinv (u : Eu n → ℝ) (ξ : Eu (n + 1)) : Fl u (Flinv u ξ) = ξ := by
  rw [Fl, piL_Flinv, Flinv, add_sub_cancel_right]

lemma Flinv_Fl (u : Eu n → ℝ) (ξ : Eu (n + 1)) : Flinv u (Fl u ξ) = ξ := by
  rw [Flinv, piL_Fl, Fl, sub_add_cancel]

lemma Fl_gr (u : Eu n → ℝ) (z : Eu n) : Fl u (gr u z) = iL n z := by
  rw [Fl, piL_gr, gr_eq, add_sub_cancel_right]

lemma Flinv_iL (u : Eu n → ℝ) (z : Eu n) : Flinv u (iL n z) = gr u z := by
  rw [Flinv, piL_iL, gr_eq]

lemma inner_Fl (u : Eu n → ℝ) (ξ : Eu (n + 1)) :
    inner ℝ (Fl u ξ) (eL n) = ξ (Fin.last n) - u (piL n ξ) := by
  rw [Fl, inner_sub_left, real_inner_smul_left, inner_eL, inner_eL, eL_last, mul_one]

end Graph

section Side

variable {n : ℕ}

lemma r_zero_of_frontier {Ω V : Set (Eu (n + 1))} {r : Eu (n + 1) → ℝ} (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hr : ContinuousOn r V) (hside : ∀ y ∈ V, y ∈ Ω ↔ r y < 0) {y : Eu (n + 1)} (hyV : y ∈ V)
    (hy : y ∈ frontier Ω) : r y = 0 := by
  rw [hΩ.frontier_eq] at hy
  have h1 : 0 ≤ r y := not_lt.1 fun h => hy.2 ((hside y hyV).2 h)
  refine le_antisymm (not_lt.1 fun h => ?_) h1
  have hc : ContinuousAt r y := hr.continuousAt (hV.mem_nhds hyV)
  have hev : ∀ᶠ z in 𝓝 y, 0 < r z ∧ z ∈ V := (hc.eventually (lt_mem_nhds h)).and (hV.mem_nhds hyV)
  obtain ⟨z, hz, hzΩ⟩ := mem_closure_iff_nhds.1 hy.1 _ hev
  exact absurd ((hside z hz.2).1 hzΩ) (not_lt.2 hz.1.le)

lemma graph_mem_frontier {Ω : Set (Eu (n + 1))} {x0 : Eu (n + 1)} {ρ : ℝ}
    {U : Eu (n + 1) ≃ₗᵢ[ℝ] Eu (n + 1)} {D : Set (Eu n)} {u : Eu n → ℝ}
    (himg : (fun x => U (x - x0)) '' (frontier Ω ∩ Metric.ball x0 ρ) = gr u '' D) {z : Eu n} (hz : z ∈ D) :
    x0 + U.symm (gr u z) ∈ frontier Ω := by
  have hm : gr u z ∈ (fun x => U (x - x0)) '' (frontier Ω ∩ Metric.ball x0 ρ) := himg ▸ ⟨z, hz, rfl⟩
  obtain ⟨x, hx, hxe⟩ := hm
  have hx' : x = x0 + U.symm (gr u z) := by
    rw [← hxe]; simp
  exact hx' ▸ hx.1

lemma frontier_graph {Ω : Set (Eu (n + 1))} {x0 : Eu (n + 1)} {ρ : ℝ}
    {U : Eu (n + 1) ≃ₗᵢ[ℝ] Eu (n + 1)} {D : Set (Eu n)} {u : Eu n → ℝ}
    (himg : (fun x => U (x - x0)) '' (frontier Ω ∩ Metric.ball x0 ρ) = gr u '' D) {x : Eu (n + 1)}
    (hx : x ∈ frontier Ω) (hxb : x ∈ Metric.ball x0 ρ) : ∃ z ∈ D, U (x - x0) = gr u z := by
  have hm : U (x - x0) ∈ gr u '' D := himg ▸ ⟨x, ⟨hx, hxb⟩, rfl⟩
  obtain ⟨z, hz, h⟩ := hm
  exact ⟨z, hz, h.symm⟩

lemma inner_iL (w : Eu (n + 1)) (h : Eu n) : inner ℝ w (iL n h) = inner ℝ (piL n w) h := by
  simp [PiLp.inner_apply, Fin.sum_univ_castSucc, iL_castSucc, iL_last, piL_apply]

lemma hasFDerivAt_gr {u : Eu n → ℝ} (hu : HasFDerivAt u (0 : Eu n →L[ℝ] ℝ) 0) :
    HasFDerivAt (gr u) (iL n) 0 := by
  have h1 : HasFDerivAt (fun z => iL n z + u z • eL n)
      (iL n + (0 : Eu n →L[ℝ] ℝ).smulRight (eL n)) 0 :=
    (iL n).hasFDerivAt.add (hu.smul_const (eL n))
  have h2 : (fun z => iL n z + u z • eL n) = gr u := funext fun z => (gr_eq u z).symm
  rw [h2] at h1
  simpa using h1

lemma hasFDerivAt_chart {x0 : Eu (n + 1)} {U : Eu (n + 1) ≃ₗᵢ[ℝ] Eu (n + 1)} {u : Eu n → ℝ}
    (hu : HasFDerivAt u (0 : Eu n →L[ℝ] ℝ) 0) :
    HasFDerivAt (fun z => x0 + U.symm (gr u z))
      ((U.symm.toLinearIsometry.toContinuousLinearMap).comp (iL n)) 0 :=
  ((U.symm.toLinearIsometry.toContinuousLinearMap).hasFDerivAt.comp 0 (hasFDerivAt_gr hu)).const_add x0

lemma chart_zero {x0 : Eu (n + 1)} {U : Eu (n + 1) ≃ₗᵢ[ℝ] Eu (n + 1)} {u : Eu n → ℝ} (hu0 : u 0 = 0) :
    x0 + U.symm (gr u 0) = x0 := by
  simp [gr_eq, hu0]

lemma normal_along_eL {r : Eu (n + 1) → ℝ} {L : Eu (n + 1) →L[ℝ] ℝ} {x0 ν : Eu (n + 1)} {scale : ℝ}
    {U : Eu (n + 1) ≃ₗᵢ[ℝ] Eu (n + 1)} {u : Eu n → ℝ}
    (hr : HasFDerivAt r L x0) (hL : ∀ h, L h = scale * inner ℝ ν h) (hscale : scale ≠ 0)
    (hu : HasFDerivAt u (0 : Eu n →L[ℝ] ℝ) 0) (hu0 : u 0 = 0)
    (hzero : ∀ᶠ z in 𝓝 (0 : Eu n), r (x0 + U.symm (gr u z)) = 0) :
    U ν = U ν (Fin.last n) • eL n := by
  have hr' : HasFDerivAt r L (x0 + U.symm (gr u 0)) := by rw [chart_zero hu0]; exact hr
  have hφ := hr'.comp (0 : Eu n) (hasFDerivAt_chart (x0 := x0) (U := U) hu)
  have hφ0 : HasFDerivAt (fun z => r (x0 + U.symm (gr u z))) (0 : Eu n →L[ℝ] ℝ) 0 :=
    (hasFDerivAt_const (0 : ℝ) (0 : Eu n)).congr_of_eventuallyEq hzero
  have huniq := hφ.unique hφ0
  have hperp : ∀ h : Eu n, inner ℝ (piL n (U ν)) h = 0 := by
    intro h
    have h3 := congrArg (fun T : Eu n →L[ℝ] ℝ => T h) huniq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry] at h3
    rw [hL] at h3
    have h4 : inner ℝ ν (U.symm (iL n h)) = 0 := (mul_eq_zero.1 h3).resolve_left hscale
    rw [← U.inner_map_map, U.apply_symm_apply, inner_iL] at h4
    exact h4
  have hpi : piL n (U ν) = 0 := inner_self_eq_zero.1 (hperp _)
  have hd := decomp (U ν)
  rw [hpi, map_zero, zero_add] at hd
  exact hd

lemma sign_along {r : Eu (n + 1) → ℝ} {L : Eu (n + 1) →L[ℝ] ℝ} {x0 w : Eu (n + 1)}
    (hr : HasFDerivAt r L x0) (hr0 : r x0 = 0) {c : ℝ} (hc : 0 < c * L w) :
    ∃ δ > 0, ∀ t : ℝ, t ≠ 0 → |t| < δ → 0 < t * (c * r (x0 + t • w)) := by
  have hg : HasDerivAt (fun t : ℝ => r (x0 + t • w)) (L w) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x0 + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x0
    have hr' : HasFDerivAt r L (x0 + (0 : ℝ) • w) := by simpa using hr
    exact hr'.comp_hasDerivAt (0 : ℝ) h1
  have hev := ((hg.tendsto_slope_zero).const_mul c).eventually (lt_mem_nhds hc)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hδ'⟩ := hev
  refine ⟨δ, hδ, fun t ht0 ht => ?_⟩
  have h1 := hδ' (show dist t 0 < δ by rw [Real.dist_eq, sub_zero]; exact ht) ht0
  simp only [zero_add, zero_smul, add_zero, hr0, sub_zero, smul_eq_mul] at h1
  have h2 : t * (c * r (x0 + t • w)) = t ^ 2 * (c * (t⁻¹ * r (x0 + t • w))) := by
    field_simp
  rw [h2]
  have : 0 < t ^ 2 := by positivity
  exact mul_pos this h1

lemma mem_iff_of_preconnected {X : Type*} [TopologicalSpace X] {Ω W : Set X} (hΩ : IsOpen Ω)
    (hW : IsPreconnected W) (hfr : ∀ y ∈ W, y ∉ frontier Ω) {x p : X} (hx : x ∈ W) (hp : p ∈ W) :
    x ∈ Ω ↔ p ∈ Ω := by
  have hsub : W ⊆ Ω ∪ (closure Ω)ᶜ := by
    intro y hy
    by_cases h : y ∈ Ω
    · exact Or.inl h
    · right; intro hc; exact hfr y hy ⟨hc, by rwa [hΩ.interior_eq]⟩
  rcases hW.subset_or_subset hΩ isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure)) hsub with h | h
  · exact iff_of_true (h hx) (h hp)
  · exact iff_of_false (fun hx' => h hx (subset_closure hx')) (fun hp' => h hp (subset_closure hp'))

lemma not_frontier_of_last_ne {Ω : Set (Eu (n + 1))} {x0 : Eu (n + 1)} {ρ : ℝ}
    {U : Eu (n + 1) ≃ₗᵢ[ℝ] Eu (n + 1)} {D : Set (Eu n)} {u : Eu n → ℝ}
    (himg : (fun x => U (x - x0)) '' (frontier Ω ∩ Metric.ball x0 ρ) = gr u '' D) {η : Eu (n + 1)}
    (hlast : η (Fin.last n) ≠ 0) (hρη : ‖Flinv u η‖ < ρ) : x0 + U.symm (Flinv u η) ∉ frontier Ω := by
  intro hf
  have hb : x0 + U.symm (Flinv u η) ∈ Metric.ball x0 ρ := by
    rw [mem_ball_iff_norm, add_sub_cancel_left, LinearIsometryEquiv.norm_map]; exact hρη
  obtain ⟨z, -, hz⟩ := frontier_graph himg hf hb
  rw [add_sub_cancel_left, U.apply_symm_apply] at hz
  have h2 := congrArg (Fl u) hz
  rw [Fl_Flinv, Fl_gr] at h2
  exact hlast (by rw [h2, iL_last])

lemma region_iff {Ω : Set (Eu (n + 1))} {x0 : Eu (n + 1)} {ρ a lo hi : ℝ}
    {U : Eu (n + 1) ≃ₗᵢ[ℝ] Eu (n + 1)} {D : Set (Eu n)} {u : Eu n → ℝ} (hΩ : IsOpen Ω)
    (himg : (fun x => U (x - x0)) '' (frontier Ω ∩ Metric.ball x0 ρ) = gr u '' D)
    (hcont : ContinuousOn u D) (haD : Metric.ball (0 : Eu n) a ⊆ D)
    (hbd : ∀ η : Eu (n + 1), ‖piL n η‖ < a → η (Fin.last n) ∈ Ioo lo hi → ‖Flinv u η‖ < ρ)
    (h0 : (0 : ℝ) ∉ Ioo lo hi) {η p : Eu (n + 1)}
    (hη : ‖piL n η‖ < a ∧ η (Fin.last n) ∈ Ioo lo hi) (hp : ‖piL n p‖ < a ∧ p (Fin.last n) ∈ Ioo lo hi) :
    x0 + U.symm (Flinv u η) ∈ Ω ↔ x0 + U.symm (Flinv u p) ∈ Ω := by
  set S : Set (Eu (n + 1)) := {η | ‖piL n η‖ < a ∧ η (Fin.last n) ∈ Ioo lo hi} with hS
  have hconv : Convex ℝ S := by
    have h1 := (convex_ball (0 : Eu n) a).linear_preimage (piL n).toLinearMap
    have h2 := (convex_Ioo lo hi).linear_preimage (EuclideanSpace.projₗ (𝕜 := ℝ) (Fin.last n))
    have hSe : S = ⇑(piL n).toLinearMap ⁻¹' Metric.ball 0 a ∩
        ⇑(EuclideanSpace.projₗ (𝕜 := ℝ) (Fin.last n)) ⁻¹' Ioo lo hi := by
      ext ξ
      simp only [hS, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, mem_ball_zero_iff]
      rfl
    rw [hSe]; exact h1.inter h2
  have hFl : ContinuousOn (Flinv u) S := by
    have hm : MapsTo (piL n) S D := fun η hη => haD (mem_ball_zero_iff.2 hη.1)
    have h3 := (hcont.comp (piL n).continuous.continuousOn hm).smul (continuousOn_const (c := eL n))
    exact continuousOn_id.add h3
  have hP : ContinuousOn (fun η => x0 + U.symm (Flinv u η)) S :=
    continuousOn_const.add (U.symm.continuous.comp_continuousOn hFl)
  have hW := hconv.isPreconnected.image _ hP
  refine mem_iff_of_preconnected hΩ hW ?_ ⟨η, hη, rfl⟩ ⟨p, hp, rfl⟩
  rintro y ⟨ξ, hξ, rfl⟩
  exact not_frontier_of_last_ne himg (fun h => h0 (h ▸ hξ.2)) (hbd ξ hξ.1 hξ.2)

lemma norm_le_split (ξ : Eu (n + 1)) : ‖ξ‖ ≤ ‖piL n ξ‖ + |ξ (Fin.last n)| := by
  have h := norm_sq_split ξ
  rw [← sq_abs (ξ (Fin.last n))] at h
  nlinarith [norm_nonneg ξ, norm_nonneg (piL n ξ), abs_nonneg (ξ (Fin.last n))]

lemma abs_last_le (ξ : Eu (n + 1)) : |ξ (Fin.last n)| ≤ ‖ξ‖ := by
  have h := norm_sq_split ξ
  rw [← sq_abs (ξ (Fin.last n))] at h
  nlinarith [norm_nonneg ξ, norm_nonneg (piL n ξ), abs_nonneg (ξ (Fin.last n))]

lemma probe_mem_iff {Ω V : Set (Eu (n + 1))} {x0 ν : Eu (n + 1)} {scale s t δ εV τ : ℝ}
    {U : Eu (n + 1) ≃ₗᵢ[ℝ] Eu (n + 1)} {u : Eu n → ℝ} {r : Eu (n + 1) → ℝ}
    (hu0 : u 0 = 0) (hside : ∀ y ∈ V, y ∈ Ω ↔ r y < 0) (hεVs : Metric.ball x0 εV ⊆ V)
    (hsign : ∀ t : ℝ, t ≠ 0 → |t| < δ → 0 < t * (s * r (x0 + t • U.symm (eL n))))
    (ht : 0 < t) (htδ : t < δ) (htε : t < εV) (hτ : τ = 1 ∨ τ = -1) :
    x0 + U.symm (Flinv u ((τ * t) • eL n)) ∈ Ω ↔ τ * s < 0 := by
  have hτt : |τ * t| = t := by
    rcases hτ with h | h <;> rw [h] <;> simp [abs_of_pos ht]
  have hpt : x0 + U.symm (Flinv u ((τ * t) • eL n)) = x0 + (τ * t) • U.symm (eL n) := by
    rw [Flinv, map_smul, piL_eL, smul_zero, hu0, zero_smul, add_zero, map_smul]
  rw [hpt]
  have hin : x0 + (τ * t) • U.symm (eL n) ∈ V := hεVs (by
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul, LinearIsometryEquiv.norm_map, norm_eL, mul_one,
      Real.norm_eq_abs, hτt]; exact htε)
  rw [hside _ hin]
  have hne : τ * t ≠ 0 := by
    rcases hτ with h | h <;> rw [h] <;> [exact (one_mul t).symm ▸ ht.ne'; (rw [neg_one_mul]; exact neg_ne_zero.2 ht.ne')]
  have hpos := hsign (τ * t) hne (by rw [hτt]; exact htδ)
  set R := r (x0 + (τ * t) • U.symm (eL n))
  have h2 : 0 < (τ * s) * R := by
    have h3 : τ * t * (s * R) = t * ((τ * s) * R) := by ring
    rw [h3] at hpos
    exact (mul_pos_iff_of_pos_left ht).1 hpos
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **O8b7b main**: near a boundary point the domain is one side of the flattened chart. -/
lemma sign_iff_neg {s e : ℝ} (he : e < 0) : (-1 * s < 0) ↔ (0 < -s * e) := by
  constructor <;> intro h <;> nlinarith

lemma sign_iff_pos {s e : ℝ} (he : 0 < e) : (1 * s < 0) ↔ (0 < -s * e) := by
  constructor <;> intro h <;> nlinarith

theorem side_chart {Ω V : Set (Eu (n + 1))} {x0 ν : Eu (n + 1)} {ρ scale : ℝ}
    {U : Eu (n + 1) ≃ₗᵢ[ℝ] Eu (n + 1)} {D : Set (Eu n)} {u : Eu n → ℝ}
    {r : Eu (n + 1) → ℝ} {L : Eu (n + 1) →L[ℝ] ℝ}
    (hΩ : IsOpen Ω) (hρ : 0 < ρ) (hD : IsOpen D) (h0D : (0 : Eu n) ∈ D) (hu0 : u 0 = 0)
    (hcont : ContinuousOn u D) (hdu : HasFDerivAt u (0 : Eu n →L[ℝ] ℝ) 0)
    (himg : (fun x => U (x - x0)) '' (frontier Ω ∩ Metric.ball x0 ρ) = gr u '' D)
    (hV : IsOpen V) (hx0V : x0 ∈ V) (hrc : ContinuousOn r V) (hside : ∀ y ∈ V, y ∈ Ω ↔ r y < 0)
    (hr : HasFDerivAt r L x0) (hL : ∀ h, L h = scale * inner ℝ ν h) (hscale : 0 < scale)
    (hν : ‖ν‖ = 1) :
    ∃ s : ℝ, U ν = s • eL n ∧ (s = 1 ∨ s = -1) ∧ ∃ r1 > 0, ∀ x ∈ Metric.ball x0 r1,
      (x ∈ Ω ↔ 0 < -s * inner ℝ (Fl u (U (x - x0))) (eL n)) ∧
      (x ∈ frontier Ω ↔ inner ℝ (Fl u (U (x - x0))) (eL n) = 0) := by
  have hx0f : x0 ∈ frontier Ω := by
    have h := graph_mem_frontier himg h0D; rwa [chart_zero hu0] at h
  have hr0 : r x0 = 0 := r_zero_of_frontier hΩ hV hrc hside hx0V hx0f
  have hcg : ContinuousAt (fun z => x0 + U.symm (gr u z)) 0 :=
    (hasFDerivAt_chart (x0 := x0) (U := U) hdu).continuousAt
  have hzero : ∀ᶠ z in 𝓝 (0 : Eu n), r (x0 + U.symm (gr u z)) = 0 := by
    have hVn : V ∈ 𝓝 (x0 + U.symm (gr u 0)) := by rw [chart_zero hu0]; exact hV.mem_nhds hx0V
    filter_upwards [hD.mem_nhds h0D, hcg.preimage_mem_nhds hVn] with z hz hzV
    exact r_zero_of_frontier hΩ hV hrc hside hzV (graph_mem_frontier himg hz)
  set s := U ν (Fin.last n) with hs_def
  have hUν : U ν = s • eL n := normal_along_eL hr hL hscale.ne' hdu hu0 hzero
  have hs1 : s = 1 ∨ s = -1 := by
    have h1 : ‖U ν‖ = 1 := by rw [U.norm_map, hν]
    rw [hUν, norm_smul, norm_eL, mul_one, Real.norm_eq_abs] at h1
    exact (abs_eq zero_le_one).1 h1
  have hs2 : s * s = 1 := by rcases hs1 with h | h <;> rw [h] <;> norm_num
  have hLw : L (U.symm (eL n)) = scale * s := by
    rw [hL, ← U.inner_map_map, U.apply_symm_apply, hUν, real_inner_smul_left, real_inner_self_eq_norm_sq,
      norm_eL]; ring
  have hc : 0 < s * L (U.symm (eL n)) := by
    rw [hLw, show s * (scale * s) = scale * (s * s) by ring, hs2, mul_one]; exact hscale
  obtain ⟨δ, hδ, hsign⟩ := sign_along hr hr0 hc
  obtain ⟨εV, hεV, hεVs⟩ := Metric.isOpen_iff.1 hV x0 hx0V
  have hUev : ∀ᶠ z in 𝓝 (0 : Eu n), z ∈ D ∧ |u z| < ρ / 8 := by
    have h8 : 0 < ρ / 8 := by positivity
    filter_upwards [hD.mem_nhds h0D, hdu.continuousAt.eventually (Metric.ball_mem_nhds (u 0) h8)] with z hz hz2
    rw [Real.dist_eq, hu0, sub_zero] at hz2
    exact ⟨hz, hz2⟩
  obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff.1 hUev
  set a := min ε (ρ / 4) with ha_def
  have ha0 : 0 < a := lt_min hε (by positivity)
  have haε : a ≤ ε := min_le_left _ _
  have haρ : a ≤ ρ / 4 := min_le_right _ _
  have haD : Metric.ball (0 : Eu n) a ⊆ D := fun z hz =>
    (hεs (lt_of_lt_of_le (Metric.mem_ball.1 hz) haε)).1
  have hua : ∀ z : Eu n, ‖z‖ < a → |u z| < ρ / 8 := fun z hz =>
    (hεs (by rw [dist_zero_right]; exact lt_of_lt_of_le hz haε)).2
  have hbd : ∀ lo hi : ℝ, -(ρ / 4) ≤ lo → hi ≤ ρ / 4 → ∀ η : Eu (n + 1), ‖piL n η‖ < a →
      η (Fin.last n) ∈ Ioo lo hi → ‖Flinv u η‖ < ρ := by
    intro lo hi hlo hhi η h1 h2
    have h3 : ‖Flinv u η‖ ≤ ‖η‖ + |u (piL n η)| := by
      rw [Flinv]; refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_eL, mul_one, Real.norm_eq_abs]
    have h4 := norm_le_split η
    have h5 := hua _ h1
    have h6 : |η (Fin.last n)| < ρ / 4 := abs_lt.2 ⟨by linarith [h2.1], by linarith [h2.2]⟩
    linarith
  set t := min δ (min εV (ρ / 4)) / 2 with ht_def
  have hm0 : 0 < min δ (min εV (ρ / 4)) := lt_min hδ (lt_min hεV (by positivity))
  have ht : 0 < t := by positivity
  have htδ : t < δ := by
    have := min_le_left δ (min εV (ρ / 4)); linarith
  have htε : t < εV := by
    have := (min_le_right δ (min εV (ρ / 4))).trans (min_le_left _ _); linarith
  have htb : t < ρ / 4 := by
    have := (min_le_right δ (min εV (ρ / 4))).trans (min_le_right _ _); linarith
  have hprobe := fun τ (hτ : τ = 1 ∨ τ = -1) =>
    probe_mem_iff (Ω := Ω) (ν := ν) (scale := scale) hu0 hside hεVs hsign ht htδ htε hτ
  have hpe : ∀ τ : ℝ, ‖piL n ((τ * t) • eL n)‖ < a := fun τ => by
    rw [map_smul, piL_eL, smul_zero, norm_zero]; exact ha0
  have hle : ∀ τ : ℝ, ((τ * t) • eL n) (Fin.last n) = τ * t := fun τ => by
    simp [eL_last]
  refine ⟨s, hUν, hs1, min a (ρ / 8), lt_min ha0 (by positivity), fun x hx => ?_⟩
  have hξ : ‖U (x - x0)‖ < min a (ρ / 8) := by rw [U.norm_map]; exact mem_ball_iff_norm.1 hx
  have hxη : x = x0 + U.symm (Flinv u (Fl u (U (x - x0)))) := by rw [Flinv_Fl]; simp
  have hpη : ‖piL n (Fl u (U (x - x0)))‖ < a := by
    rw [piL_Fl]; exact lt_of_le_of_lt (norm_piL_apply_le _) (lt_of_lt_of_le hξ (min_le_left _ _))
  rw [inner_eL]
  have hηlast : (Fl u (U (x - x0))) (Fin.last n) = (U (x - x0)) (Fin.last n) - u (piL n (U (x - x0))) := by
    rw [← inner_eL, inner_Fl]
  have hηb : |(Fl u (U (x - x0))) (Fin.last n)| < ρ / 4 := by
    rw [hηlast]
    have h1 := abs_last_le (U (x - x0))
    have h2 := hua _ (lt_of_le_of_lt (norm_piL_apply_le _) (lt_of_lt_of_le hξ (min_le_left _ _)))
    have h3 : ‖U (x - x0)‖ < ρ / 8 := lt_of_lt_of_le hξ (min_le_right _ _)
    have h4 := abs_sub (U (x - x0) (Fin.last n)) (u (piL n (U (x - x0))))
    linarith
  set η := Fl u (U (x - x0)) with hη_def
  rcases lt_trichotomy (η (Fin.last n)) 0 with hneg | hz | hpos
  · have hI : η (Fin.last n) ∈ Ioo (-(ρ / 4)) 0 := ⟨by linarith [(abs_lt.1 hηb).1], hneg⟩
    have hbd' := hbd (-(ρ / 4)) 0 le_rfl (by positivity)
    have hreg := region_iff (Ω := Ω) (x0 := x0) hΩ himg hcont haD hbd' (fun h => lt_irrefl _ h.2)
      ⟨hpη, hI⟩ (p := ((-1) * t) • eL n) ⟨hpe _, by rw [hle]; exact ⟨by linarith, by linarith⟩⟩
    rw [← hxη, hprobe (-1) (Or.inr rfl)] at hreg
    refine ⟨hreg.trans (sign_iff_neg hneg), ?_⟩
    refine iff_of_false ?_ hneg.ne
    rw [hxη]; exact not_frontier_of_last_ne himg hneg.ne (hbd' η hpη hI)
  · have hηe : η = iL n (piL n η) := by
      have hd := decomp η; rw [hz, zero_smul, add_zero] at hd; exact hd
    have hxf : x ∈ frontier Ω := by
      rw [hxη, hηe, Flinv_iL]
      exact graph_mem_frontier himg (haD (mem_ball_zero_iff.2 hpη))
    have hxΩ : x ∉ Ω := by
      have h := hxf; rw [hΩ.frontier_eq] at h; exact h.2
    rw [hz, mul_zero]
    exact ⟨iff_of_false hxΩ (lt_irrefl _), iff_of_true hxf rfl⟩
  · have hI : η (Fin.last n) ∈ Ioo 0 (ρ / 4) := ⟨hpos, by linarith [(abs_lt.1 hηb).2]⟩
    have hbd' := hbd 0 (ρ / 4) (by linarith) le_rfl
    have hreg := region_iff (Ω := Ω) (x0 := x0) hΩ himg hcont haD hbd' (fun h => lt_irrefl _ h.1)
      ⟨hpη, hI⟩ (p := (1 * t) • eL n) ⟨hpe _, by rw [hle]; exact ⟨by linarith, by linarith⟩⟩
    rw [← hxη, hprobe 1 (Or.inl rfl)] at hreg
    refine ⟨hreg.trans (sign_iff_pos hpos), ?_⟩
    refine iff_of_false ?_ hpos.ne'
    rw [hxη]; exact not_frontier_of_last_ne himg hpos.ne' (hbd' η hpη hI)

end Side

section SideDef

variable {n : ℕ}

lemma sum_mul_eq_inner {m : ℕ} (v h : Eu m) : ∑ i, v i * h i = inner ℝ v h := by
  simp [PiLp.inner_apply, mul_comm]

theorem side_chart_def {Ω : Set (Eu (n + 1))} {μ ρ : ℝ} {x0 ν : Eu (n + 1)}
    {U : Eu (n + 1) ≃ₗᵢ[ℝ] Eu (n + 1)} {D : Set (Eu n)} {u : Eu n → ℝ}
    (hΩ : IsOpen Ω) (hnormal : EthierKurtz.IsOutwardUnitNormal Ω x0 ν) (hρ : 0 < ρ)
    (hD : IsOpen D) (h0D : (0 : Eu n) ∈ D) (hu : EthierKurtz.CTwiceHolder D μ u) (hu0 : u 0 = 0)
    (hdu : fderiv ℝ u 0 = 0)
    (himg : (fun x => U (x - x0)) '' (frontier Ω ∩ Metric.ball x0 ρ) =
      (fun z : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)) :
            EuclideanSpace ℝ (Fin (n + 1)))) '' D) :
    ∃ s : ℝ, U ν = s • eL n ∧ (s = 1 ∨ s = -1) ∧ ∃ r1 > 0, ∀ x ∈ Metric.ball x0 r1,
      (x ∈ Ω ↔ 0 < -s * inner ℝ (Fl u (U (x - x0))) (eL n)) ∧
      (x ∈ frontier Ω ↔ inner ℝ (Fl u (U (x - x0))) (eL n) = 0) := by
  obtain ⟨-, hν, V, hV, hx0V, r, scale, hscale, hrC, -, hside, hder⟩ := hnormal
  have hrd : DifferentiableAt ℝ r x0 :=
    (hrC.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hx0V)
  have hud : DifferentiableAt ℝ u 0 :=
    (hu.1.differentiableOn (by norm_num)).differentiableAt (hD.mem_nhds h0D)
  have hdu' : HasFDerivAt u (0 : Eu n →L[ℝ] ℝ) 0 := hdu ▸ hud.hasFDerivAt
  exact side_chart hΩ hρ hD h0D hu0 hu.1.continuousOn hdu' himg hV hx0V hrC.continuousOn hside
    hrd.hasFDerivAt (fun h => by rw [hder, sum_mul_eq_inner]) hscale hν

end SideDef

section C1Hb

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `f` is `C^{1,μ}` on `T` with bounds `M0` (value), `M1` (derivative), `H` (Hölder constant of the derivative). -/
structure C1Hb (T : Set E) (μ M0 M1 H : ℝ) (f : E → ℝ) (f1 : E → E →L[ℝ] ℝ) : Prop where
  hd : ∀ y ∈ T, HasFDerivAt f (f1 y) y
  b0 : ∀ y ∈ T, |f y| ≤ M0
  b1 : ∀ y ∈ T, ‖f1 y‖ ≤ M1
  hol : ∀ y ∈ T, ∀ z ∈ T, ‖f1 y - f1 z‖ ≤ H * ‖y - z‖ ^ μ
  hH : 0 ≤ H

lemma C1Hb.mono {T S : Set E} {μ M0 M1 H : ℝ} {f : E → ℝ} {f1 : E → E →L[ℝ] ℝ}
    (h : C1Hb T μ M0 M1 H f f1) (hST : S ⊆ T) : C1Hb S μ M0 M1 H f f1 :=
  ⟨fun y hy => h.hd y (hST hy), fun y hy => h.b0 y (hST hy), fun y hy => h.b1 y (hST hy),
    fun y hy z hz => h.hol y (hST hy) z (hST hz), h.hH⟩

lemma C1Hb.lip {T : Set E} {μ M0 M1 H : ℝ} {f : E → ℝ} {f1 : E → E →L[ℝ] ℝ}
    (h : C1Hb T μ M0 M1 H f f1) (hT : Convex ℝ T) {y z : E} (hy : y ∈ T) (hz : z ∈ T) :
    |f y - f z| ≤ M1 * ‖y - z‖ := by
  have := hT.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x hx => (h.hd x hx).hasFDerivWithinAt) h.b1 hz hy
  simpa [Real.norm_eq_abs] using this

lemma C1Hb_const (T : Set E) (μ c : ℝ) : C1Hb T μ |c| 0 0 (fun _ => c) (fun _ => 0) :=
  ⟨fun y _ => hasFDerivAt_const c y, fun _ _ => le_rfl, fun _ _ => by simp, fun _ _ _ _ => by simp, le_rfl⟩

lemma C1Hb.add {T : Set E} {μ M0 M1 H N0 N1 H' : ℝ} {f g : E → ℝ} {f1 g1 : E → E →L[ℝ] ℝ}
    (hf : C1Hb T μ M0 M1 H f f1) (hg : C1Hb T μ N0 N1 H' g g1) :
    C1Hb T μ (M0 + N0) (M1 + N1) (H + H') (fun y => f y + g y) (fun y => f1 y + g1 y) := by
  refine ⟨fun y hy => (hf.hd y hy).add (hg.hd y hy), fun y hy => ?_, fun y hy => ?_,
    fun y hy z hz => ?_, add_nonneg hf.hH hg.hH⟩
  · exact (abs_add_le _ _).trans (add_le_add (hf.b0 y hy) (hg.b0 y hy))
  · exact (norm_add_le _ _).trans (add_le_add (hf.b1 y hy) (hg.b1 y hy))
  · have h1 : f1 y + g1 y - (f1 z + g1 z) = (f1 y - f1 z) + (g1 y - g1 z) := by abel
    rw [h1, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hf.hol y hy z hz) (hg.hol y hy z hz))

lemma C1Hb.const_mul {T : Set E} {μ M0 M1 H : ℝ} {f : E → ℝ} {f1 : E → E →L[ℝ] ℝ}
    (hf : C1Hb T μ M0 M1 H f f1) (a : ℝ) :
    C1Hb T μ (|a| * M0) (|a| * M1) (|a| * H) (fun y => a * f y) (fun y => a • f1 y) := by
  refine ⟨fun y hy => (hf.hd y hy).const_mul a, fun y hy => ?_, fun y hy => ?_,
    fun y hy z hz => ?_, mul_nonneg (abs_nonneg a) hf.hH⟩
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hf.b0 y hy) (abs_nonneg a)
  · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hf.b1 y hy) (abs_nonneg a)
  · have hs : a • f1 y - a • f1 z = a • (f1 y - f1 z) := by
      ext v; simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
    rw [hs, norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hf.hol y hy z hz) (abs_nonneg a)

lemma C1Hb.sum {T : Set E} {μ : ℝ} {ι : Type*} (s : Finset ι) {M0 M1 H : ι → ℝ} {f : ι → E → ℝ}
    {f1 : ι → E → E →L[ℝ] ℝ} (hf : ∀ i ∈ s, C1Hb T μ (M0 i) (M1 i) (H i) (f i) (f1 i)) :
    C1Hb T μ (∑ i ∈ s, M0 i) (∑ i ∈ s, M1 i) (∑ i ∈ s, H i) (fun y => ∑ i ∈ s, f i y)
      (fun y => ∑ i ∈ s, f1 i y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using C1Hb_const T μ 0
  | insert a s ha ih =>
    have h1 := (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h1

lemma C1Hb.mul {T : Set E} {μ M0 M1 H N0 N1 H' R : ℝ} {f g : E → ℝ} {f1 g1 : E → E →L[ℝ] ℝ}
    (hf : C1Hb T μ M0 M1 H f f1) (hg : C1Hb T μ N0 N1 H' g g1) (hT : Convex ℝ T)
    (hR : ∀ y ∈ T, ∀ z ∈ T, ‖y - z‖ ≤ R) (hR0 : 0 ≤ R) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hM0' : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hN0 : 0 ≤ N0) (hN1' : 0 ≤ N1) :
    C1Hb T μ (M0 * N0) (M0 * N1 + N0 * M1) (M0 * H' + N0 * H + 2 * (M1 * N1) * R ^ (1 - μ))
      (fun y => f y * g y) (fun y => f y • g1 y + g y • f1 y) := by
  have hM0 : ∀ y ∈ T, 0 ≤ M0 := fun y hy => (abs_nonneg _).trans (hf.b0 y hy)
  have hN1 : ∀ y ∈ T, 0 ≤ N1 := fun y hy => (norm_nonneg _).trans (hg.b1 y hy)
  refine ⟨fun y hy => (hf.hd y hy).mul (hg.hd y hy), fun y hy => ?_, fun y hy => ?_,
    fun y hy z hz => ?_, ?_⟩
  · rw [abs_mul]; exact mul_le_mul (hf.b0 y hy) (hg.b0 y hy) (abs_nonneg _) (hM0 y hy)
  · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul (hf.b0 y hy) (hg.b1 y hy) (norm_nonneg _) (hM0 y hy)
    · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul (hg.b0 y hy) (hf.b1 y hy) (norm_nonneg _) hN0
  · have hd : f y • g1 y + g y • f1 y - (f z • g1 z + g z • f1 z) =
        f y • (g1 y - g1 z) + (f y - f z) • g1 z + g y • (f1 y - f1 z) + (g y - g z) • f1 z := by
      ext v; simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
    have hyz : ‖y - z‖ ≤ R ^ (1 - μ) * ‖y - z‖ ^ μ := lip_le_hol (norm_nonneg _) (hR y hy z hz) hμ0 hμ1
    have hp : 0 ≤ ‖y - z‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    have e1 : ‖f y • (g1 y - g1 z)‖ ≤ M0 * (H' * ‖y - z‖ ^ μ) := by
      rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul (hf.b0 y hy) (hg.hol y hy z hz) (norm_nonneg _) (hM0 y hy)
    have e2 : ‖(f y - f z) • g1 z‖ ≤ (M1 * ‖y - z‖) * N1 := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hf.lip hT hy hz) (hg.b1 z hz) (norm_nonneg _) (mul_nonneg hM1 (norm_nonneg _))
    have e3 : ‖g y • (f1 y - f1 z)‖ ≤ N0 * (H * ‖y - z‖ ^ μ) := by
      rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul (hg.b0 y hy) (hf.hol y hy z hz) (norm_nonneg _) hN0
    have e4 : ‖(g y - g z) • f1 z‖ ≤ (N1 * ‖y - z‖) * M1 := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hg.lip hT hy hz) (hf.b1 z hz) (norm_nonneg _) (mul_nonneg (hN1 y hy) (norm_nonneg _))
    rw [hd]
    have e5 : (M1 * ‖y - z‖) * N1 + (N1 * ‖y - z‖) * M1 ≤ 2 * (M1 * N1) * (R ^ (1 - μ) * ‖y - z‖ ^ μ) := by
      have := mul_le_mul_of_nonneg_left hyz (mul_nonneg hM1 (hN1 y hy)); linarith
    calc _ ≤ ‖f y • (g1 y - g1 z)‖ + ‖(f y - f z) • g1 z‖ + ‖g y • (f1 y - f1 z)‖ + ‖(g y - g z) • f1 z‖ :=
          norm_add₄_le
      _ ≤ M0 * (H' * ‖y - z‖ ^ μ) + (M1 * ‖y - z‖) * N1 + N0 * (H * ‖y - z‖ ^ μ) + (N1 * ‖y - z‖) * M1 := by
          linarith
      _ ≤ (M0 * H' + N0 * H + 2 * (M1 * N1) * R ^ (1 - μ)) * ‖y - z‖ ^ μ := by linarith
      _ ≤ _ := le_rfl
  · have := Real.rpow_nonneg hR0 (1 - μ)
    have := hf.hH; have := hg.hH
    positivity

lemma C1Hb.comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set F} {T : Set E}
    {μ M0 M1 H K R : ℝ} {f : E → ℝ} {f1 : E → E →L[ℝ] ℝ} (hf : C1Hb T μ M0 M1 H f f1)
    {τ : F → E} {Dτ : F → F →L[ℝ] E} {D2τ : F → F →L[ℝ] F →L[ℝ] E}
    (hτ : C2B S μ K τ Dτ D2τ) (hτd : ∀ y ∈ S, HasFDerivAt τ (Dτ y) y) (hmap : ∀ y ∈ S, τ y ∈ T)
    (hR : ∀ y ∈ S, ∀ z ∈ S, ‖y - z‖ ≤ R) (hR0 : 0 ≤ R) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hM1 : 0 ≤ M1) :
    C1Hb S μ M0 (M1 * K) (H * K ^ μ * K + M1 * K * R ^ (1 - μ)) (fun y => f (τ y))
      (fun y => (f1 (τ y)).comp (Dτ y)) := by
  have hK := hτ.hK
  refine ⟨fun y hy => (hf.hd (τ y) (hmap y hy)).comp y (hτd y hy), fun y hy => hf.b0 _ (hmap y hy),
    fun y hy => ?_, fun y hy z hz => ?_, ?_⟩
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hf.b1 _ (hmap y hy)) (hτ.b1 y hy) (norm_nonneg _) hM1)
  · have hd : (f1 (τ y)).comp (Dτ y) - (f1 (τ z)).comp (Dτ z) =
        (f1 (τ y) - f1 (τ z)).comp (Dτ y) + (f1 (τ z)).comp (Dτ y - Dτ z) := by
      ext v; simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.comp_apply, map_sub]; ring
    have hyz : ‖y - z‖ ≤ R ^ (1 - μ) * ‖y - z‖ ^ μ := lip_le_hol (norm_nonneg _) (hR y hy z hz) hμ0 hμ1
    have hτl : ‖τ y - τ z‖ ^ μ ≤ K ^ μ * ‖y - z‖ ^ μ := by
      rw [← Real.mul_rpow hK (norm_nonneg _)]
      exact Real.rpow_le_rpow (norm_nonneg _) (hτ.lip y hy z hz) hμ0
    have e1 : ‖(f1 (τ y) - f1 (τ z)).comp (Dτ y)‖ ≤ H * (K ^ μ * ‖y - z‖ ^ μ) * K :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul
        ((hf.hol _ (hmap y hy) _ (hmap z hz)).trans (mul_le_mul_of_nonneg_left hτl hf.hH))
        (hτ.b1 y hy) (norm_nonneg _) (mul_nonneg hf.hH (mul_nonneg (Real.rpow_nonneg hK _)
          (Real.rpow_nonneg (norm_nonneg _) _))))
    have e2 : ‖(f1 (τ z)).comp (Dτ y - Dτ z)‖ ≤ M1 * (K * (R ^ (1 - μ) * ‖y - z‖ ^ μ)) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hf.b1 _ (hmap z hz))
        ((hτ.lip1 y hy z hz).trans (mul_le_mul_of_nonneg_left hyz hK)) (norm_nonneg _) hM1)
    rw [hd]
    have h8 : (H * K ^ μ * K + M1 * K * R ^ (1 - μ)) * ‖y - z‖ ^ μ =
        H * (K ^ μ * ‖y - z‖ ^ μ) * K + M1 * (K * (R ^ (1 - μ) * ‖y - z‖ ^ μ)) := by ring
    rw [h8]
    exact (norm_add_le _ _).trans (add_le_add e1 e2)
  · have := Real.rpow_nonneg hR0 (1 - μ); have := Real.rpow_nonneg hK μ; have := hf.hH; positivity

end C1Hb

section Transfer

variable {n : ℕ}

lemma entries_le1 (A : Eu n →L[ℝ] ℝ) : ‖A‖ ≤ ∑ i, |A (EuclideanSpace.single i 1)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ => abs_nonneg _) fun v => ?_
  conv_lhs => rw [eu_expand v]
  rw [map_sum, Finset.sum_mul, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_smul, smul_eq_mul, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (coord_le v i) (abs_nonneg _)

/-- `COnceHolder` on an open set gives derivative facts and `C1Hb` on a small closed ball. -/
theorem once_C1Hb {D : Set (Eu n)} {μ : ℝ} {f : Eu n → ℝ} (hD : IsOpen D)
    (hf : EthierKurtz.COnceHolder D μ f) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) :
    (∀ z ∈ D, HasFDerivAt f (fderiv ℝ f z) z) ∧
    ∀ z0 ∈ D, ∃ r > 0, Metric.closedBall z0 r ⊆ D ∧
      ∃ M0 M1 H, C1Hb (Metric.closedBall z0 r) μ M0 M1 H f (fderiv ℝ f) := by
  obtain ⟨hcd, hent⟩ := hf
  have hder : ∀ z ∈ D, HasFDerivAt f (fderiv ℝ f z) z := fun z hz =>
    ((hcd.contDiffAt (hD.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
  refine ⟨hder, fun z0 hz0 => ?_⟩
  have hloc := fun i => CH_local (hent i) hμ0.le hμ1
  choose ρ M hρ hM hH using hloc
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.1 hD z0 hz0
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), (∀ i, 4 * r < ρ i) ∧ r < ε := by
    refine nhdsWithin_le_nhds ?_
    refine Filter.Eventually.and ?_ (gt_mem_nhds hε)
    refine Filter.eventually_all.2 fun i => ?_
    have h := ((continuous_const.mul continuous_id : Continuous fun r : ℝ => 4 * r).tendsto 0)
    exact h.eventually (gt_mem_nhds (by simp [hρ i]))
  obtain ⟨r, ⟨hrρ, hrε⟩, hr0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hr0' : (0 : ℝ) < r := hr0
  have hball : Metric.closedBall z0 r ⊆ D := (Metric.closedBall_subset_ball hrε).trans hεD
  refine ⟨r, hr0', hball, ?_⟩
  set S := Metric.closedBall z0 r
  have hconv : Convex ℝ S := convex_closedBall z0 r
  have hdist : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ 2 * r := by
    intro x hx y hy
    rw [← dist_eq_norm]
    calc dist x y ≤ dist x z0 + dist y z0 := dist_triangle_right _ _ _
      _ ≤ r + r := add_le_add hx hy
      _ = 2 * r := by ring
  set Mh := ∑ i, 2 * M i
  have hMh : 0 ≤ Mh := Finset.sum_nonneg fun i _ => by linarith [hM i]
  have hhol : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ Mh * ‖x - y‖ ^ μ := by
    intro x hx y hy
    refine (entries_le1 _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have := hH i x y ((hconv.segment_subset hx hy).trans hball) (by linarith [hdist x hx y hy, hrρ i])
    simpa only [ContinuousLinearMap.sub_apply] using this
  have hz0S : z0 ∈ S := Metric.mem_closedBall_self hr0'.le
  set B1 := ‖fderiv ℝ f z0‖ + Mh * r ^ μ
  have hb1 : ∀ x ∈ S, ‖fderiv ℝ f x‖ ≤ B1 := by
    intro x hx
    have h1 := hhol x hx z0 hz0S
    have h2 : ‖x - z0‖ ^ μ ≤ r ^ μ := by
      gcongr; rw [← dist_eq_norm]; exact hx
    have h3 : ‖fderiv ℝ f x‖ ≤ ‖fderiv ℝ f z0‖ + ‖fderiv ℝ f x - fderiv ℝ f z0‖ := by
      have := norm_add_le (fderiv ℝ f z0) (fderiv ℝ f x - fderiv ℝ f z0); simpa using this
    linarith [mul_le_mul_of_nonneg_left h2 hMh]
  have hB1 : 0 ≤ B1 := (norm_nonneg _).trans (hb1 z0 hz0S)
  have hb0 : ∀ x ∈ S, |f x| ≤ |f z0| + B1 * (2 * r) := by
    intro x hx
    have h1 : ‖f x - f z0‖ ≤ B1 * ‖x - z0‖ :=
      hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun p hp => (hder p (hball hp)).hasFDerivWithinAt) hb1 hz0S hx
    rw [Real.norm_eq_abs] at h1
    have h2 := abs_sub_abs_le_abs_sub (f x) (f z0)
    linarith [mul_le_mul_of_nonneg_left (hdist x hx z0 hz0S) hB1]
  exact ⟨_, _, _, ⟨fun z hz => hder z (hball hz), hb0, hb1, hhol, hMh⟩⟩

lemma C1Hb.congr_open {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T O : Set E} {μ M0 M1 H : ℝ}
    {f g : E → ℝ} {f1 : E → E →L[ℝ] ℝ} (hf : C1Hb T μ M0 M1 H f f1) (hO : IsOpen O) (hTO : T ⊆ O)
    (heq : ∀ y ∈ O, f y = g y) : C1Hb T μ M0 M1 H g f1 :=
  ⟨fun y hy => (hf.hd y hy).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hO.mem_nhds (hTO hy)) fun z hz => (heq z hz).symm),
    fun y hy => heq y (hTO hy) ▸ hf.b0 y hy, hf.b1, hf.hol, hf.hH⟩

/-- Transition map between two boundary charts at the same point (linear part). -/
noncomputable def trL (U U' : Eu (n + 1) ≃ₗᵢ[ℝ] Eu (n + 1)) : Eu (n + 1) →L[ℝ] Eu n :=
  (piL n).comp ((U'.toLinearIsometry.toContinuousLinearMap).comp
    (U.symm.toLinearIsometry.toContinuousLinearMap))

lemma trL_apply (U U' : Eu (n + 1) ≃ₗᵢ[ℝ] Eu (n + 1)) (ξ : Eu (n + 1)) :
    trL U U' ξ = piL n (U' (U.symm ξ)) := rfl

lemma norm_trL_le (U U' : Eu (n + 1) ≃ₗᵢ[ℝ] Eu (n + 1)) : ‖trL U U'‖ ≤ 1 := by
  unfold trL
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine mul_le_one₀ norm_piL_le (norm_nonneg _) ?_
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_one₀ (LinearIsometry.norm_toContinuousLinearMap_le _) (norm_nonneg _)
    (LinearIsometry.norm_toContinuousLinearMap_le _)

lemma norm_iL_le : ‖iL n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by rw [norm_iL_apply, one_mul]

lemma hasFDerivAt_gr' {u : Eu n → ℝ} {Du : Eu n →L[ℝ] ℝ} {z : Eu n} (hu : HasFDerivAt u Du z) :
    HasFDerivAt (gr u) (iL n + Du.smulRight (eL n)) z := by
  have h1 : HasFDerivAt (fun z => iL n z + u z • eL n) (iL n + Du.smulRight (eL n)) z :=
    (iL n).hasFDerivAt.add (hu.smul_const (eL n))
  have h2 : (fun z => iL n z + u z • eL n) = gr u := funext fun z => (gr_eq u z).symm
  rwa [h2] at h1

lemma norm_gr_le (u : Eu n → ℝ) (z : Eu n) : ‖gr u z‖ ≤ ‖z‖ + |u z| := by
  rw [gr_eq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_iL_apply, norm_smul, norm_eL, mul_one, Real.norm_eq_abs]

/-- **O8b7c2 main**: a function on `∂Ω` that is `C^{1,μ}` in a second chart at `x0` is `C^{1,μ}` on a small ball
in the main chart (main chart `u` is `CTwiceHolder`). -/
theorem transfer_C1Hb {Ω : Set (Eu (n + 1))} {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {x0 : Eu (n + 1)}
    {φ : Eu (n + 1) → ℝ} {ρ : ℝ} {U : Eu (n + 1) ≃ₗᵢ[ℝ] Eu (n + 1)} {D : Set (Eu n)} {u : Eu n → ℝ}
    (hD : IsOpen D) (h0D : (0 : Eu n) ∈ D) (hu : EthierKurtz.CTwiceHolder D μ u) (hu0 : u 0 = 0)
    (himg : (fun x => U (x - x0)) '' (frontier Ω ∩ Metric.ball x0 ρ) = gr u '' D)
    {ρ' : ℝ} (hρ' : 0 < ρ') {U' : Eu (n + 1) ≃ₗᵢ[ℝ] Eu (n + 1)} {D' : Set (Eu n)} {u' : Eu n → ℝ}
    (hD' : IsOpen D') (h0D' : (0 : Eu n) ∈ D')
    (himg' : (fun x => U' (x - x0)) '' (frontier Ω ∩ Metric.ball x0 ρ') = gr u' '' D')
    (hφ : EthierKurtz.COnceHolder D' μ (fun z => φ (x0 + U'.symm (gr u' z)))) :
    ∃ R > 0, ∃ M0 M1 H : ℝ, ∃ g1 : Eu n → Eu n →L[ℝ] ℝ,
      C1Hb (Metric.closedBall 0 R) μ M0 M1 H (fun z => φ (x0 + U.symm (gr u z))) g1 := by
  obtain ⟨hder, hC2⟩ := ctwice_C2B hD hu hμ0 hμ1
  obtain ⟨r, hr, hrD, K, hK⟩ := hC2 0 h0D
  obtain ⟨-, hCφ⟩ := once_C1Hb hD' hφ hμ0 hμ1
  obtain ⟨r', hr', hr'D, M0, M1, H, hf'⟩ := hCφ 0 h0D'
  have hK0 := hK.hK
  have hK1 : 0 < 1 + K := by linarith
  have hM1 : 0 ≤ M1 := (norm_nonneg _).trans (hf'.b1 0 (Metric.mem_closedBall_self hr'.le))
  set R := min (r / 2) (min (ρ' / (4 * (1 + K))) (r' / (1 + K))) with hRdef
  have hR : 0 < R := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hRr : R ≤ r / 2 := min_le_left _ _
  have hRρ : R * (4 * (1 + K)) ≤ ρ' :=
    (le_div_iff₀ (by positivity)).1 ((min_le_right _ _).trans (min_le_left _ _))
  have hRr' : R * (1 + K) ≤ r' :=
    (le_div_iff₀ hK1).1 ((min_le_right _ _).trans (min_le_right _ _))
  set L := trL U U'
  set τ : Eu n → Eu n := fun z => L (gr u z) with hτdef
  set Dτ : Eu n → Eu n →L[ℝ] Eu n := fun z => L.comp (iL n + (fderiv ℝ u z).smulRight (eL n))
  have hτd : ∀ z ∈ D, HasFDerivAt τ (Dτ z) z := fun z hz =>
    L.hasFDerivAt.comp z (hasFDerivAt_gr' (hder z hz).1)
  set B := Metric.closedBall (0 : Eu n) r
  have hDτb : ∀ z ∈ B, ‖Dτ z‖ ≤ 1 + K := by
    intro z hz
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 : ‖iL n + (fderiv ℝ u z).smulRight (eL n)‖ ≤ 1 + K := by
      refine (norm_add_le _ _).trans (add_le_add norm_iL_le ?_)
      rw [ContinuousLinearMap.norm_smulRight_apply, norm_eL, mul_one]; exact hK.b1 z hz
    calc ‖L‖ * ‖iL n + (fderiv ℝ u z).smulRight (eL n)‖ ≤ 1 * (1 + K) :=
          mul_le_mul (norm_trL_le U U') h1 (norm_nonneg _) zero_le_one
      _ = 1 + K := one_mul _
  have hDτl : ∀ z ∈ B, ∀ w ∈ B, ‖Dτ z - Dτ w‖ ≤ K * ‖z - w‖ := by
    intro z hz w hw
    have hA : (iL n + (fderiv ℝ u z).smulRight (eL n)) - (iL n + (fderiv ℝ u w).smulRight (eL n)) =
        (fderiv ℝ u z - fderiv ℝ u w).smulRight (eL n) := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp [sub_smul]
    have h2 : Dτ z - Dτ w = L.comp ((fderiv ℝ u z - fderiv ℝ u w).smulRight (eL n)) := by
      simp only [Dτ, ← ContinuousLinearMap.comp_sub, hA]
    rw [h2]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_eL, mul_one]
    calc ‖L‖ * ‖fderiv ℝ u z - fderiv ℝ u w‖ ≤ 1 * (K * ‖z - w‖) :=
          mul_le_mul (norm_trL_le U U') (hK.lip1 z hz w hw) (norm_nonneg _) zero_le_one
      _ = K * ‖z - w‖ := one_mul _
  have hτl : ∀ z ∈ B, ∀ w ∈ B, ‖τ z - τ w‖ ≤ (1 + K) * ‖z - w‖ := fun z hz w hw =>
    (convex_closedBall 0 r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun p hp => (hτd p (hrD hp)).hasFDerivWithinAt) hDτb hw hz
  have hτ0 : τ 0 = 0 := by
    simp only [hτdef, gr_eq, map_zero, hu0, zero_smul, add_zero]
  set S := Metric.closedBall (0 : Eu n) R
  have hSB : S ⊆ B := Metric.closedBall_subset_closedBall (by linarith)
  have hτC : C2B S μ (1 + K) τ Dτ (fun _ => 0) := by
    refine ⟨hK1.le, fun x hx y hy => hτl x (hSB hx) y (hSB hy), fun x hx => hDτb x (hSB hx),
      fun x hx y hy => (hDτl x (hSB hx) y (hSB hy)).trans (by gcongr; linarith), fun _ _ => ?_,
      fun _ _ _ _ => ?_⟩
    · exact ContinuousLinearMap.opNorm_zero.le.trans hK1.le
    · simp only [sub_self]
      exact ContinuousLinearMap.opNorm_zero.le.trans (by positivity)
  have hmap : ∀ z ∈ S, τ z ∈ Metric.closedBall (0 : Eu n) r' := by
    intro z hz
    have h1 := hτl z (hSB hz) 0 (Metric.mem_closedBall_self hr.le)
    rw [hτ0, sub_zero, sub_zero] at h1
    rw [mem_closedBall_zero_iff] at hz ⊢
    nlinarith
  have hdiam : ∀ y ∈ S, ∀ z ∈ S, ‖y - z‖ ≤ 2 * R := by
    intro y hy z hz
    rw [← dist_eq_norm]
    calc dist y z ≤ dist y 0 + dist z 0 := dist_triangle_right _ _ _
      _ ≤ R + R := add_le_add hy hz
      _ = 2 * R := by ring
  have hcomp := hf'.comp hτC (fun z hz => hτd z (hrD (hSB hz))) hmap hdiam (by positivity) hμ0.le hμ1 hM1
  refine ⟨R, hR, _, _, _, _, hcomp.congr_open (O := Metric.ball 0 (2 * R)) Metric.isOpen_ball
    (Metric.closedBall_subset_ball (by linarith)) fun z hz => ?_⟩
  -- the two charts agree on the boundary near x0
  have hzB : z ∈ B := by
    rw [mem_ball_zero_iff] at hz; rw [mem_closedBall_zero_iff]; linarith
  have hzD : z ∈ D := hrD hzB
  have hxf := graph_mem_frontier himg hzD
  have hun : |u z| ≤ K * ‖z‖ := by
    have := hK.lip z hzB 0 (Metric.mem_closedBall_self hr.le)
    rwa [hu0, sub_zero, sub_zero, Real.norm_eq_abs] at this
  have hxb : x0 + U.symm (gr u z) ∈ Metric.ball x0 ρ' := by
    rw [mem_ball_iff_norm, add_sub_cancel_left, LinearIsometryEquiv.norm_map]
    have h1 := norm_gr_le u z
    rw [mem_ball_zero_iff] at hz
    nlinarith
  obtain ⟨z', -, hz'⟩ := frontier_graph himg' hxf hxb
  rw [add_sub_cancel_left] at hz'
  have hτz : τ z = z' := by
    simp only [hτdef, trL_apply, L]; rw [hz', piL_gr]
  have hx : x0 + U.symm (gr u z) = x0 + U'.symm (gr u' z') := by
    rw [← hz', LinearIsometryEquiv.symm_apply_apply]
  show φ (x0 + U'.symm (gr u' (τ z))) = φ (x0 + U.symm (gr u z))
  rw [hτz, hx]

end Transfer

section Coef

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma C1Hb.weaken {T : Set E} {μ M0 M1 H M0' M1' H' : ℝ} {f : E → ℝ} {f1 : E → E →L[ℝ] ℝ}
    (h : C1Hb T μ M0 M1 H f f1) (h0 : M0 ≤ M0') (h1 : M1 ≤ M1') (h2 : H ≤ H') :
    C1Hb T μ M0' M1' H' f f1 :=
  ⟨h.hd, fun y hy => (h.b0 y hy).trans h0, fun y hy => (h.b1 y hy).trans h1,
    fun y hy z hz => (h.hol y hy z hz).trans
      (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (norm_nonneg _) _)), h.hH.trans h2⟩

/-- `f` is `C^{1,μ}` on `T` with some bounds. -/
def C1ex (T : Set E) (μ : ℝ) (f : E → ℝ) : Prop :=
  ∃ M0 M1 H : ℝ, ∃ f1 : E → E →L[ℝ] ℝ, C1Hb T μ M0 M1 H f f1

lemma C1ex.mono {T S : Set E} {μ : ℝ} {f : E → ℝ} (h : C1ex T μ f) (hST : S ⊆ T) : C1ex S μ f := by
  obtain ⟨M0, M1, H, f1, h⟩ := h
  exact ⟨M0, M1, H, f1, h.mono hST⟩

lemma C1ex_const (T : Set E) (μ c : ℝ) : C1ex T μ (fun _ => c) := ⟨_, _, _, _, C1Hb_const T μ c⟩

lemma C1ex.add {T : Set E} {μ : ℝ} {f g : E → ℝ} (hf : C1ex T μ f) (hg : C1ex T μ g) :
    C1ex T μ (fun y => f y + g y) := by
  obtain ⟨M0, M1, H, f1, hf⟩ := hf
  obtain ⟨N0, N1, H', g1, hg⟩ := hg
  exact ⟨_, _, _, _, hf.add hg⟩

lemma C1ex.const_mul {T : Set E} {μ : ℝ} {f : E → ℝ} (hf : C1ex T μ f) (a : ℝ) :
    C1ex T μ (fun y => a * f y) := by
  obtain ⟨M0, M1, H, f1, hf⟩ := hf
  exact ⟨_, _, _, _, hf.const_mul a⟩

lemma C1ex.sum {T : Set E} {μ : ℝ} {ι : Type*} (s : Finset ι) {f : ι → E → ℝ}
    (hf : ∀ i ∈ s, C1ex T μ (f i)) : C1ex T μ (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using C1ex_const T μ 0
  | insert a s ha ih =>
    have h1 := (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h1

lemma C1ex.mul {T : Set E} {μ : ℝ} {f g : E → ℝ} (hf : C1ex T μ f) (hg : C1ex T μ g) (hT : Convex ℝ T)
    {R : ℝ} (hR : ∀ y ∈ T, ∀ z ∈ T, ‖y - z‖ ≤ R) (hR0 : 0 ≤ R) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    C1ex T μ (fun y => f y * g y) := by
  obtain ⟨M0, M1, H, f1, hf⟩ := hf
  obtain ⟨N0, N1, H', g1, hg⟩ := hg
  exact ⟨_, _, _, _, (hf.weaken (le_max_left M0 0) (le_max_left M1 0) le_rfl).mul
    (hg.weaken (le_max_left N0 0) (le_max_left N1 0) le_rfl) hT hR hR0 hμ0 hμ1 (le_max_right _ _)
    (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)⟩

lemma C1ex.lip {T : Set E} {μ : ℝ} {f : E → ℝ} (hf : C1ex T μ f) (hT : Convex ℝ T) :
    ∃ L, 0 ≤ L ∧ ∀ y ∈ T, ∀ z ∈ T, |f y - f z| ≤ L * ‖y - z‖ := by
  obtain ⟨M0, M1, H, f1, hf⟩ := hf
  exact ⟨max M1 0, le_max_right _ _, fun y hy z hz =>
    (hf.lip hT hy hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩

end Coef

section CoefEu

variable {n : ℕ}

lemma C1ex_lin_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ} {T : Set E} {μ : ℝ}
    {V : E → Eu m} (hV : ∀ j, C1ex T μ (fun z => V z j)) (L : Eu m →L[ℝ] Eu n) (k : Fin n) :
    C1ex T μ (fun z => L (V z) k) := by
  have he : ∀ z, L (V z) k = ∑ j, L (EuclideanSpace.single j (1 : ℝ)) k * V z j := by
    intro z
    have h := congrArg ((EuclideanSpace.proj k : Eu n →L[ℝ] ℝ).comp L) (eu_expand (V z))
    rw [map_sum] at h
    have hp : ∀ v : Eu n, (EuclideanSpace.proj k : Eu n →L[ℝ] ℝ) v = v k := fun v => rfl
    simp only [map_smul, smul_eq_mul, ContinuousLinearMap.comp_apply, hp] at h
    rw [h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp only [he]
  exact C1ex.sum _ fun j _ => (hV j).const_mul _

end CoefEu

section ObCoef

variable {n : ℕ}

end ObCoef

section ObDir

variable {n : ℕ}

end ObDir

section ChartV

lemma C2B.restrict {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {T S : Set E} {μ K : ℝ} {f : E → F} {Df : E → E →L[ℝ] F}
    {D2f : E → E →L[ℝ] E →L[ℝ] F} (h : C2B T μ K f Df D2f) (hST : S ⊆ T) : C2B S μ K f Df D2f where
  hK := h.hK
  lip x hx y hy := h.lip x (hST hx) y (hST hy)
  b1 x hx := h.b1 x (hST hx)
  lip1 x hx y hy := h.lip1 x (hST hx) y (hST hy)
  b2 x hx := h.b2 x (hST hx)
  hol2 x hx y hy := h.hol2 x (hST hx) y (hST hy)

variable {n : ℕ}

theorem chart_V {Ω : Set (Eu (n + 1))} {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {x0 : Eu (n + 1)}
    (hx0 : x0 ∈ frontier Ω) {ρ : ℝ} {U : Eu (n + 1) ≃ₗᵢ[ℝ] Eu (n + 1)} {D : Set (Eu n)} {u : Eu n → ℝ}
    (hD : IsOpen D) (h0D : (0 : Eu n) ∈ D) (hu : EthierKurtz.CTwiceHolder D μ u) (hu0 : u 0 = 0)
    (himg : (fun x => U (x - x0)) '' (frontier Ω ∩ Metric.ball x0 ρ) = gr u '' D)
    {c : Eu (n + 1) → Eu (n + 1)} (hc : ∀ j, EthierKurtz.BoundaryCOnceHolder Ω μ (fun x => c x j)) :
    ∃ R > 0, Metric.closedBall 0 R ⊆ D ∧
      (∃ K, C2B (Metric.closedBall 0 R) μ K u (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u))) ∧
      (∀ z ∈ D, HasFDerivAt u (fderiv ℝ u z) z ∧
        HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) z) z) ∧
      ∀ k, C1ex (Metric.closedBall 0 R) μ (fun z => U (c (x0 + U.symm (gr u z))) k) := by
  obtain ⟨hder, hC2⟩ := ctwice_C2B hD hu hμ0 hμ1
  obtain ⟨r, hr, hrD, K, hK⟩ := hC2 0 h0D
  have hj : ∀ j, ∃ R > 0,
      C1ex (Metric.closedBall (0 : Eu n) R) μ (fun z => c (x0 + U.symm (gr u z)) j) := by
    intro j
    obtain ⟨ρ', hρ', U', D', u', hD', h0D', -, -, -, -, himg', hφ⟩ := hc j x0 hx0
    obtain ⟨R, hR, M0, M1, H, g1, h⟩ :=
      transfer_C1Hb (φ := fun x => c x j) hμ0 hμ1 hD h0D hu hu0 himg hρ' hD' h0D' himg' hφ
    exact ⟨R, hR, M0, M1, H, g1, h⟩
  choose Rj hRj hCj using hj
  set R := min r (Finset.univ.inf' Finset.univ_nonempty Rj) with hRdef
  have hR : 0 < R := lt_min hr ((Finset.lt_inf'_iff _).2 fun j _ => hRj j)
  have hRr : R ≤ r := min_le_left _ _
  have hRj' : ∀ j, R ≤ Rj j := fun j =>
    (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ j))
  refine ⟨R, hR, (Metric.closedBall_subset_closedBall hRr).trans hrD,
    ⟨K, hK.restrict (Metric.closedBall_subset_closedBall hRr)⟩, hder, fun k => ?_⟩
  have h := C1ex_lin_comp (V := fun z => c (x0 + U.symm (gr u z)))
    (fun j => (hCj j).mono (Metric.closedBall_subset_closedBall (hRj' j)))
    (U.toLinearIsometry.toContinuousLinearMap) k
  exact h

end ChartV

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

section ObDef

/-- plain core of O8: chart data (C2B graph function, C^{1,μ} transported field, side description) ⇒ `ObChart`. -/
def ObCore (n : ℕ) (μ : ℝ) : Prop :=
  ∀ (Ω : Set (Eu (n + 1))), IsOpen Ω → ∀ (x0 : Eu (n + 1)) (U : Eu (n + 1) ≃ₗᵢ[ℝ] Eu (n + 1))
    (u : Eu n → ℝ) (Du : Eu n → Eu n →L[ℝ] ℝ) (D2u : Eu n → Eu n →L[ℝ] Eu n →L[ℝ] ℝ) (R K : ℝ), 0 < R →
    C2B (Metric.closedBall 0 R) μ K u Du D2u →
    (∀ z ∈ Metric.closedBall (0 : Eu n) R, HasFDerivAt u (Du z) z ∧ HasFDerivAt Du (D2u z) z) →
    u 0 = 0 → Du 0 = 0 → ∀ (c : Eu (n + 1) → Eu (n + 1)),
    (∀ k, C1ex (Metric.closedBall 0 R) μ (fun z => U (c (x0 + U.symm (gr u z))) k)) →
    ∀ (s r1 : ℝ), (s = 1 ∨ s = -1) → 0 < r1 →
    (∀ x ∈ Metric.ball x0 r1, (x ∈ Ω ↔ 0 < -s * inner ℝ (Fl u (U (x - x0))) (eL n)) ∧
      (x ∈ frontier Ω ↔ inner ℝ (Fl u (U (x - x0))) (eL n) = 0)) →
    0 < s * U (c x0) (Fin.last n) →
    ∃ (r0 K' : ℝ) (e b : Eu (n + 1)) (Θ : Eu (n + 1) → Eu (n + 1)) (DΘ : Eu (n + 1) → Eu (n + 1) →L[ℝ] Eu (n + 1))
      (D2Θ : Eu (n + 1) → Eu (n + 1) →L[ℝ] Eu (n + 1) →L[ℝ] Eu (n + 1)), ObChart Ω μ c x0 r0 K' e b Θ DΘ D2Θ

end ObDef

section ObChartDef

variable {n : ℕ}

theorem ob_chart_def {μ : ℝ} (hcore : ObCore n μ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {Ω : Set (Eu (n + 1))}
    (hΩ : IsOpen Ω) (hboundary : EthierKurtz.BoundaryCTwiceHolder Ω μ) {c ν : Eu (n + 1) → Eu (n + 1)}
    (hc : ∀ i, EthierKurtz.BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, EthierKurtz.IsOutwardUnitNormal Ω x (ν x))
    {ε : ℝ} (hε : 0 < ε) (hobl : ∀ x ∈ frontier Ω, ε ≤ ∑ i, c x i * ν x i)
    {x0 : Eu (n + 1)} (hx0 : x0 ∈ frontier Ω) :
    ∃ (r0 K : ℝ) (e b : Eu (n + 1)) (Θ : Eu (n + 1) → Eu (n + 1))
      (DΘ : Eu (n + 1) → Eu (n + 1) →L[ℝ] Eu (n + 1))
      (D2Θ : Eu (n + 1) → Eu (n + 1) →L[ℝ] Eu (n + 1) →L[ℝ] Eu (n + 1)),
      ObChart Ω μ c x0 r0 K e b Θ DΘ D2Θ := by
  obtain ⟨ρ, hρ, hch⟩ := hboundary
  obtain ⟨U, D, u, hD, h0D, hu, hu0, hdu, -, himg⟩ := hch x0 hx0
  obtain ⟨R, hR, hRD, ⟨K, hK⟩, hder, hV⟩ := chart_V hμ0 hμ1 hx0 hD h0D hu hu0 himg hc
  obtain ⟨s, hUν, hs, r1, hr1, hside⟩ := side_chart_def hΩ (hnormal x0 hx0) hρ hD h0D hu hu0 hdu himg
  have hs2 : s * s = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hUe : U.symm (eL n) = s • ν x0 := by
    have h1 : ν x0 = U.symm (s • eL n) := by rw [← hUν, U.symm_apply_apply]
    rw [h1, map_smul, smul_smul, hs2, one_smul]
  have hlast : U (c x0) (Fin.last n) = s * inner ℝ (c x0) (ν x0) := by
    rw [← inner_eL, ← U.apply_symm_apply (eL n), LinearIsometryEquiv.inner_map_map, hUe,
      real_inner_smul_right]
  have hpos : 0 < s * U (c x0) (Fin.last n) := by
    rw [hlast, ← mul_assoc, hs2, one_mul, ← sum_mul_eq_inner]
    exact hε.trans_le (hobl x0 hx0)
  exact hcore Ω hΩ x0 U u (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u)) R K hR hK
    (fun z hz => hder z (hRD hz)) hu0 hdu c hV s r1 hs hr1 hside hpos

end ObChartDef

section Plain

theorem obcore_of_plain {n : ℕ} {μ : ℝ} (h : let eL : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single (Fin.last n) 1
    let gr : (EuclideanSpace ℝ (Fin n) → ℝ) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1)) := fun u z => WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i))
    let Fl : (EuclideanSpace ℝ (Fin n) → ℝ) → EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := fun u ξ => ξ - u (WithLp.toLp 2 (fun i => ξ (Fin.castSucc i))) • eL
    ∀ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), IsOpen Ω → ∀ (x0 : EuclideanSpace ℝ (Fin (n + 1))) (U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (Du : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (D2u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (R K : ℝ), 0 < R →
    (0 ≤ K ∧ (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖u x - u y‖ ≤ K * ‖x - y‖) ∧
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖Du x‖ ≤ K) ∧ (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖Du x - Du y‖ ≤ K * ‖x - y‖) ∧
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖D2u x‖ ≤ K) ∧ (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖D2u x - D2u y‖ ≤ K * ‖x - y‖ ^ μ)) →
    (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, HasFDerivAt u (Du z) z ∧ HasFDerivAt Du (D2u z) z) →
    u 0 = 0 → Du 0 = 0 → ∀ (c : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))),
    (∀ k, ∃ (M0 M1 H : ℝ) (f1 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
      (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, HasFDerivAt (fun z => U (c (x0 + U.symm (gr u z))) k) (f1 y) y) ∧
      (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, |U (c (x0 + U.symm (gr u y))) k| ≤ M0) ∧ (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖f1 y‖ ≤ M1) ∧
      (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖f1 y - f1 z‖ ≤ H * ‖y - z‖ ^ μ) ∧ 0 ≤ H) →
    ∀ (s r1 : ℝ), (s = 1 ∨ s = -1) → 0 < r1 →
    (∀ x ∈ Metric.ball x0 r1, (x ∈ Ω ↔ 0 < -s * inner ℝ (Fl u (U (x - x0))) eL) ∧
      (x ∈ frontier Ω ↔ inner ℝ (Fl u (U (x - x0))) eL = 0)) →
    0 < s * U (c x0) (Fin.last n) →
    ∃ (r0 K : ℝ) (e b : EuclideanSpace ℝ (Fin (n + 1)))
        (Θ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
        (DΘ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
        (D2Θ : EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))),
        0 < r0 ∧ ‖e‖ = 1 ∧ inner ℝ b e = 0 ∧
        (∀ x ∈ Metric.ball x0 r0, HasStrictFDerivAt Θ (DΘ x) x) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ Ω, HasFDerivAt DΘ (D2Θ x) x) ∧
        Θ x0 = 0 ∧ DΘ x0 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1))) ∧
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
          ‖D2Θ x - D2Θ y‖ ≤ K * ‖x - y‖ ^ μ)) : ObCore n μ := by
  intro Ω hΩ x0 U u Du D2u R K hR hu hd hu0 hDu0 c hV s r1 hs hr1 hside hpos
  obtain ⟨r0, K', e, b, Θ, DΘ, D2Θ, hr0, he, hb, hst, hd2, h0, hD0, hsd, hobl', hK, hlip, hb1, hlip1, hb2, hhol2⟩ :=
    h Ω hΩ x0 U u Du D2u R K hR ⟨hu.hK, hu.lip, hu.b1, hu.lip1, hu.b2, hu.hol2⟩ hd hu0 hDu0 c
      (fun k => by
        obtain ⟨M0, M1, H, f1, hC⟩ := hV k
        exact ⟨M0, M1, H, f1, hC.hd, hC.b0, hC.b1, hC.hol, hC.hH⟩) s r1 hs hr1 hside hpos
  exact ⟨r0, K', e, b, Θ, DΘ, D2Θ, ⟨hr0, he, hb, hst, hd2, h0, hD0, hsd, hobl', ⟨hK, hlip, hb1, hlip1, hb2, hhol2⟩⟩⟩

end Plain

end ObliqueLib

theorem solution (n : ℕ) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hcore : let eL : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single (Fin.last n) 1
    let gr : (EuclideanSpace ℝ (Fin n) → ℝ) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1)) := fun u z => WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i))
    let Fl : (EuclideanSpace ℝ (Fin n) → ℝ) → EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := fun u ξ => ξ - u (WithLp.toLp 2 (fun i => ξ (Fin.castSucc i))) • eL
    ∀ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), IsOpen Ω → ∀ (x0 : EuclideanSpace ℝ (Fin (n + 1))) (U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (Du : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (D2u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (R K : ℝ), 0 < R →
    (0 ≤ K ∧ (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖u x - u y‖ ≤ K * ‖x - y‖) ∧
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖Du x‖ ≤ K) ∧ (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖Du x - Du y‖ ≤ K * ‖x - y‖) ∧
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖D2u x‖ ≤ K) ∧ (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖D2u x - D2u y‖ ≤ K * ‖x - y‖ ^ μ)) →
    (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, HasFDerivAt u (Du z) z ∧ HasFDerivAt Du (D2u z) z) →
    u 0 = 0 → Du 0 = 0 → ∀ (c : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))),
    (∀ k, ∃ (M0 M1 H : ℝ) (f1 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
      (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, HasFDerivAt (fun z => U (c (x0 + U.symm (gr u z))) k) (f1 y) y) ∧
      (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, |U (c (x0 + U.symm (gr u y))) k| ≤ M0) ∧ (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖f1 y‖ ≤ M1) ∧
      (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖f1 y - f1 z‖ ≤ H * ‖y - z‖ ^ μ) ∧ 0 ≤ H) →
    ∀ (s r1 : ℝ), (s = 1 ∨ s = -1) → 0 < r1 →
    (∀ x ∈ Metric.ball x0 r1, (x ∈ Ω ↔ 0 < -s * inner ℝ (Fl u (U (x - x0))) eL) ∧
      (x ∈ frontier Ω ↔ inner ℝ (Fl u (U (x - x0))) eL = 0)) →
    0 < s * U (c x0) (Fin.last n) →
    ∃ (r0 K : ℝ) (e b : EuclideanSpace ℝ (Fin (n + 1)))
        (Θ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
        (DΘ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
        (D2Θ : EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))),
        0 < r0 ∧ ‖e‖ = 1 ∧ inner ℝ b e = 0 ∧
        (∀ x ∈ Metric.ball x0 r0, HasStrictFDerivAt Θ (DΘ x) x) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ Ω, HasFDerivAt DΘ (D2Θ x) x) ∧
        Θ x0 = 0 ∧ DΘ x0 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1))) ∧
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
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hΩ : IsOpen Ω) (hboundary : EthierKurtz.BoundaryCTwiceHolder Ω μ)
    (c ν : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hc : ∀ i, EthierKurtz.BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, EthierKurtz.IsOutwardUnitNormal Ω x (ν x))
    (hobl : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω, ε ≤ ∑ i, c x i * ν x i) :
    ∀ x0 ∈ frontier Ω, ∃ (r0 K : ℝ) (e b : EuclideanSpace ℝ (Fin (n + 1)))
            (Θ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
            (DΘ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
            (D2Θ : EuclideanSpace ℝ (Fin (n + 1)) →
              EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))),
            0 < r0 ∧ ‖e‖ = 1 ∧ inner ℝ b e = 0 ∧
            (∀ x ∈ Metric.ball x0 r0, HasStrictFDerivAt Θ (DΘ x) x) ∧
            (∀ x ∈ Metric.ball x0 r0 ∩ Ω, HasFDerivAt DΘ (D2Θ x) x) ∧
            Θ x0 = 0 ∧ DΘ x0 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1))) ∧
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
              ‖D2Θ x - D2Θ y‖ ≤ K * ‖x - y‖ ^ μ) := by
  obtain ⟨ε, hε, hob⟩ := hobl
  intro x0 hx0
  obtain ⟨r0, K, e, b, Θ, DΘ, D2Θ, hO⟩ := ObliqueLib.ob_chart_def (ObliqueLib.obcore_of_plain hcore) hμ0 hμ1.le hΩ
    hboundary hc hnormal hε hob hx0
  obtain ⟨hr0, he, hb, hst, hd2, h0, hD0, hside, hobl', hc2⟩ := hO
  obtain ⟨hK, hlip, hb1, hlip1, hb2, hhol2⟩ := hc2
  exact ⟨r0, K, e, b, Θ, DΘ, D2Θ, hr0, he, hb, hst, hd2, h0, hD0, hside, hobl', hK, hlip, hb1, hlip1, hb2, hhol2⟩
