-- Prove2me | solution 1 for EthierKurtz.oblique_shear_extension
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T23:46:43.657082+00:00
-- url     : https://prove2.me/submissions/62ee89fa-7979-4ae3-8121-ebe1aa042459

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

lemma convex_openHalf (e : Eu d) : Convex ℝ {z : Eu d | 0 < inner ℝ z e} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  rcases ha.eq_or_lt with h | h
  · subst h; simp at hab; subst hab; simpa using hy
  · linarith [mul_pos h hx, mul_nonneg hb hy.le]

lemma half_lip {f : Eu d → F} {Df : Eu d → (Eu d →L[ℝ] F)} {e c : Eu d} {r K : ℝ} (he : ‖e‖ = 1)
    (hf : Continuous f) (hd : ∀ x, 0 < inner ℝ x e → HasFDerivAt f (Df x) x)
    (hb : ∀ x, 0 < inner ℝ x e → dist x c ≤ r + 1 → ‖Df x‖ ≤ K) :
    ∀ x y : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ y e → dist x c ≤ r → dist y c ≤ r →
      ‖f x - f y‖ ≤ K * ‖x - y‖ := by
  intro x y hx hy hxc hyc
  set s : Set (Eu d) := {z | 0 < inner ℝ z e} ∩ Metric.closedBall c (r + 1) with hs
  have hsc : Convex ℝ s := (convex_openHalf e).inter (convex_closedBall c (r + 1))
  have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hmem : ∀ z : Eu d, 0 ≤ inner ℝ z e → dist z c ≤ r → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → z + ε • e ∈ s := by
    intro z hz hzc ε hε hε1
    refine ⟨?_, ?_⟩
    · show 0 < inner ℝ (z + ε • e) e
      rw [inner_add_left, real_inner_smul_left, hee]; linarith
    · rw [Metric.mem_closedBall]
      calc dist (z + ε • e) c ≤ dist (z + ε • e) z + dist z c := dist_triangle _ _ _
        _ = ε + dist z c := by
            rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he, Real.norm_eq_abs, abs_of_pos hε, mul_one]
        _ ≤ r + 1 := by linarith
  have hK : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ‖f (x + ε • e) - f (y + ε • e)‖ ≤ K * ‖x - y‖ := by
    intro ε hε hε1
    have h := hsc.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := f) (f' := Df) (C := K) (fun z hz => (hd z hz.1).hasFDerivWithinAt)
      (fun z hz => hb z hz.1 hz.2) (hmem y hy hyc ε hε hε1) (hmem x hx hxc ε hε hε1)
    have : x + ε • e - (y + ε • e) = x - y := by abel
    rwa [this] at h
  have hT : Filter.Tendsto (fun ε : ℝ => ‖f (x + ε • e) - f (y + ε • e)‖) (𝓝[>] 0)
      (𝓝 ‖f x - f y‖) := by
    have hc : Continuous (fun ε : ℝ => ‖f (x + ε • e) - f (y + ε • e)‖) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  refine le_of_tendsto hT ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  exact hK ε hε.1 hε.2.le

/-- `C2B` bounds on `half ∩ closedBall c r` for data that is `C¹` on the open half-space with continuous `Df`,
twice differentiable there, and whose second derivative is `μ`-Hölder on the closed half-space. -/
theorem half_C2B {f : Eu d → F} {Df : Eu d → (Eu d →L[ℝ] F)} {D2f : Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] F)}
    {e c : Eu d} {r μ C : ℝ} (he : ‖e‖ = 1) (hr : 0 ≤ r) (hμ0 : 0 ≤ μ)
    (hf : Continuous f) (hDf : Continuous Df)
    (hd : ∀ x, 0 < inner ℝ x e → HasFDerivAt f (Df x) x)
    (hd2 : ∀ x, 0 < inner ℝ x e → HasFDerivAt Df (D2f x) x)
    (hhol : ∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e → ‖D2f x' - D2f x‖ ≤ C * ‖x' - x‖ ^ μ)
    (hC : 0 ≤ C) :
    ∃ K, C2B {x : Eu d | 0 ≤ inner ℝ x e ∧ dist x c ≤ r} μ K f Df D2f := by
  by_cases hex : ∃ x0 : Eu d, 0 ≤ inner ℝ x0 e ∧ dist x0 c ≤ r
  swap
  · push_neg at hex
    refine ⟨0, ⟨le_rfl, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
      first
      | (intro x hx; exact absurd hx.2 (not_le.mpr (hex x hx.1)))
  obtain ⟨x0, hx0, hx0c⟩ := hex
  set B2 := ‖D2f x0‖ + C * (2 * r + 2) ^ μ with hB2
  have hB2n : 0 ≤ B2 := by
    have := ContinuousLinearMap.opNorm_nonneg (D2f x0)
    have := rpow_nonneg (show (0 : ℝ) ≤ 2 * r + 2 by linarith) μ
    positivity
  have hD2b : ∀ x, 0 ≤ inner ℝ x e → dist x c ≤ r + 2 → ‖D2f x‖ ≤ B2 := by
    intro x hx hxc
    have h1 := hhol x0 x hx0 hx
    have hxx : ‖x - x0‖ ≤ 2 * r + 2 := by
      rw [← dist_eq_norm]; have := dist_triangle x c x0; rw [dist_comm c x0] at this; linarith
    have h2 : ‖x - x0‖ ^ μ ≤ (2 * r + 2) ^ μ := rpow_le_rpow (norm_nonneg _) hxx hμ0
    have h3 : ‖D2f x‖ ≤ ‖D2f x0‖ + ‖D2f x - D2f x0‖ := by
      have := norm_add_le (D2f x0) (D2f x - D2f x0); simpa using this
    have := mul_le_mul_of_nonneg_left h2 hC
    rw [hB2]; linarith
  have hDlip : ∀ x y : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ y e → dist x c ≤ r + 1 → dist y c ≤ r + 1 →
      ‖Df x - Df y‖ ≤ B2 * ‖x - y‖ :=
    half_lip (r := r + 1) he hDf hd2 (fun x hx hxc => hD2b x hx.le (by linarith))
  set B1 := ‖Df x0‖ + B2 * (2 * r + 1) with hB1
  have hB1n : 0 ≤ B1 := by
    have := norm_nonneg (Df x0); have : 0 ≤ B2 * (2 * r + 1) := mul_nonneg hB2n (by linarith)
    linarith
  have hD1b : ∀ x, 0 ≤ inner ℝ x e → dist x c ≤ r + 1 → ‖Df x‖ ≤ B1 := by
    intro x hx hxc
    have h1 := hDlip x x0 hx hx0 hxc (by linarith)
    have hxx : ‖x - x0‖ ≤ 2 * r + 1 := by
      rw [← dist_eq_norm]; have := dist_triangle x c x0; rw [dist_comm c x0] at this; linarith
    have h3 : ‖Df x‖ ≤ ‖Df x0‖ + ‖Df x - Df x0‖ := by
      have := norm_add_le (Df x0) (Df x - Df x0); simpa using this
    have := mul_le_mul_of_nonneg_left hxx hB2n
    rw [hB1]; linarith
  have hflip : ∀ x y : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ y e → dist x c ≤ r → dist y c ≤ r →
      ‖f x - f y‖ ≤ B1 * ‖x - y‖ :=
    half_lip (r := r) he hf hd (fun x hx hxc => hD1b x hx.le hxc)
  refine ⟨B1 + B2 + C, ⟨by positivity, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x hx y hy
    exact (hflip x y hx.1 hy.1 hx.2 hy.2).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · intro x hx; have := hD1b x hx.1 (by linarith [hx.2]); linarith
  · intro x hx y hy
    exact (hDlip x y hx.1 hy.1 (by linarith [hx.2]) (by linarith [hy.2])).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · intro x hx; have := hD2b x hx.1 (by linarith [hx.2]); linarith
  · intro x hx y hy
    have := hhol y x hy.1 hx.1
    exact this.trans (mul_le_mul_of_nonneg_right (by linarith) (rpow_nonneg (norm_nonneg _) _))

end HalfLip

section Flat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `φ ↦ φ.smulRight e` as a continuous linear map. -/
noncomputable def sRL (e : F) : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] F) :=
  (ContinuousLinearMap.smulRightL ℝ E F).flip e

lemma sRL_apply (e : F) (φ : E →L[ℝ] ℝ) : sRL e φ = φ.smulRight e := rfl

noncomputable def DFl (e : F) (Dg : E → E →L[ℝ] ℝ) (x : E) : E →L[ℝ] F := sRL e (Dg x)

noncomputable def D2Fl (e : F) (D2g : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) : E →L[ℝ] E →L[ℝ] F :=
  (sRL e).comp (D2g x)

lemma hasFDerivAt_Dfl {Dg : E → E →L[ℝ] ℝ} {D2g : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (e : F)
    (hg : HasFDerivAt Dg (D2g x) x) : HasFDerivAt (DFl e Dg) (D2Fl e D2g x) x :=
  (sRL e).hasFDerivAt.comp x hg

end Flat

section PkgDef

/-- For every bounded `C^{1,μ}` function `ψ` on `ℝ^d` and unit `e`, there is a `C¹` function `E` vanishing on the
plane `⟪x,e⟫ = 0` with normal derivative `ψ` there (`DE x = ψ x • ⟪·,e⟫`), `C²` on the open half-space, whose second
derivative extends `μ`-Hölder continuously to the closed half-space. -/
def ExtPackage (d : ℕ) (μ : ℝ) : Prop :=
  ∀ (M0 M1 H : ℝ) (ψ : Eu d → ℝ) (ψ1 : Eu d → (Eu d →L[ℝ] ℝ)) (e : Eu d),
    (∀ y, HasFDerivAt ψ (ψ1 y) y) → Continuous ψ1 → (∀ y, |ψ y| ≤ M0) → (∀ y, ‖ψ1 y‖ ≤ M1) →
    (∀ y z, ‖ψ1 y - ψ1 z‖ ≤ H * ‖y - z‖ ^ μ) → 0 ≤ H → ‖e‖ = 1 →
    ∃ (E : Eu d → ℝ) (DE : Eu d → (Eu d →L[ℝ] ℝ)) (D2E : Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ)),
      (∀ x, HasStrictFDerivAt E (DE x) x) ∧ Continuous DE ∧
      (∀ x, inner ℝ x e = 0 → E x = 0 ∧ DE x = ψ x • innerSL ℝ e) ∧
      (∀ x, 0 < inner ℝ x e → HasFDerivAt DE (D2E x) x) ∧
      ∃ C, 0 ≤ C ∧ ∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
        ‖D2E x' - D2E x‖ ≤ C * ‖x' - x‖ ^ μ

end PkgDef

section Shear

variable {d : ℕ}

lemma norm_sRL_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (w : F) : ‖(sRL w : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] F))‖ ≤ ‖w‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun φ => ?_
  rw [sRL_apply, ContinuousLinearMap.norm_smulRight_apply, mul_comm]

/-- Vector version of `ExtPackage`: `T = Σ_i E_i • w_i` with `DT = ⟪·,e⟫ • Σ ψ_i w_i` on the plane. -/
theorem ext_vec {μ : ℝ} (hP : ExtPackage d μ) {m : ℕ} (w : Fin m → Eu d) (e : Eu d) (he : ‖e‖ = 1)
    (M0 M1 H : Fin m → ℝ) (ψ : Fin m → Eu d → ℝ) (ψ1 : Fin m → Eu d → (Eu d →L[ℝ] ℝ))
    (hd : ∀ i y, HasFDerivAt (ψ i) (ψ1 i y) y) (hc : ∀ i, Continuous (ψ1 i))
    (hb0 : ∀ i y, |ψ i y| ≤ M0 i) (hb1 : ∀ i y, ‖ψ1 i y‖ ≤ M1 i)
    (hhol : ∀ i y z, ‖ψ1 i y - ψ1 i z‖ ≤ H i * ‖y - z‖ ^ μ) (hH : ∀ i, 0 ≤ H i) :
    ∃ (T : Eu d → Eu d) (DT : Eu d → (Eu d →L[ℝ] Eu d)) (D2T : Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d)),
      (∀ x, ∃ c : Fin m → ℝ, T x = ∑ i, c i • w i) ∧
      (∀ x, HasStrictFDerivAt T (DT x) x) ∧ Continuous DT ∧
      (∀ x, inner ℝ x e = 0 → T x = 0 ∧ DT x = (innerSL ℝ e).smulRight (∑ i, ψ i x • w i)) ∧
      (∀ x, 0 < inner ℝ x e → HasFDerivAt DT (D2T x) x) ∧
      ∃ C, 0 ≤ C ∧ ∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
        ‖D2T x' - D2T x‖ ≤ C * ‖x' - x‖ ^ μ := by
  have hall := fun i => hP (M0 i) (M1 i) (H i) (ψ i) (ψ1 i) e (hd i) (hc i) (hb0 i) (hb1 i) (hhol i) (hH i) he
  choose E DE D2E hs hcont hpl hd2 C hC0 hCh using hall
  refine ⟨fun x => ∑ i, E i x • w i, fun x => ∑ i, (DE i x).smulRight (w i),
    fun x => ∑ i, (sRL (w i)).comp (D2E i x), fun x => ⟨fun i => E i x, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have h := HasStrictFDerivAt.sum (u := Finset.univ) (A := fun i y => E i y • w i)
      (A' := fun i => (DE i x).smulRight (w i)) fun i _ => (hs i x).smul_const (w i)
    convert h using 1
    all_goals first | rfl | (funext y; simp [Finset.sum_apply])
  · refine continuous_finsetSum _ fun i _ => ?_
    exact (sRL (w i)).continuous.comp (hcont i)
  · intro x hx
    refine ⟨by simp [(hpl _ x hx).1], ?_⟩
    refine ContinuousLinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.smulRight_apply, fun i => (hpl i x hx).2, ContinuousLinearMap.smul_apply,
      Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, smul_eq_mul]
  · intro x hx
    have h := HasFDerivAt.sum (u := Finset.univ) (A := fun i => DFl (w i) (DE i))
      (A' := fun i => D2Fl (w i) (D2E i) x) fun i _ => hasFDerivAt_Dfl (w i) (hd2 i x hx)
    convert h using 1
    all_goals first | rfl | (funext y; simp [Finset.sum_apply, DFl, sRL_apply])
  · refine ⟨∑ i, ‖w i‖ * C i, Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (hC0 i), ?_⟩
    intro x x' hx hx'
    dsimp only
    calc ‖(∑ i, (sRL (w i)).comp (D2E i x')) - ∑ i, (sRL (w i)).comp (D2E i x)‖
        = ‖∑ i, (sRL (w i)).comp (D2E i x' - D2E i x)‖ := by
          congr 1
          refine ((Finset.sum_sub_distrib _ _).symm).trans (Finset.sum_congr rfl fun i _ => ?_)
          exact (ContinuousLinearMap.comp_sub _ _ _).symm
      _ ≤ ∑ i, ‖sRL (E := Eu d) (w i)‖ * ‖D2E i x' - D2E i x‖ := by
          refine (norm_sum_le Finset.univ fun i => (sRL (E := Eu d) (w i)).comp (D2E i x' - D2E i x)).trans
            (Finset.sum_le_sum fun i _ => ?_)
          exact ContinuousLinearMap.opNorm_comp_le (sRL (E := Eu d) (w i)) (D2E i x' - D2E i x)
      _ ≤ ∑ i, ‖w i‖ * (C i * ‖x' - x‖ ^ μ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul (norm_sRL_le (E := Eu d) (w i)) (hCh i x x' hx hx') (by positivity) (by positivity)
      _ = (∑ i, ‖w i‖ * C i) * ‖x' - x‖ ^ μ := by rw [Finset.sum_mul]; simp only [mul_assoc]

/-- The shear `G = id - T` built from `ext_vec`: `C¹`, `C²` on the open half-space, `C2B` on every
`half ∩ closedBall`, `G = id` on the plane with `DG = id - ⟪·,e⟫ • Σ ψ_i w_i` there, and `G` preserves
`⟪·,v⟫` for every `v ⟂ w_i`. -/
theorem shear {μ : ℝ} (hP : ExtPackage d μ) (hμ0 : 0 ≤ μ) {m : ℕ} (w : Fin m → Eu d) (e : Eu d) (he : ‖e‖ = 1)
    (M0 M1 H : Fin m → ℝ) (ψ : Fin m → Eu d → ℝ) (ψ1 : Fin m → Eu d → (Eu d →L[ℝ] ℝ))
    (hd : ∀ i y, HasFDerivAt (ψ i) (ψ1 i y) y) (hc : ∀ i, Continuous (ψ1 i))
    (hb0 : ∀ i y, |ψ i y| ≤ M0 i) (hb1 : ∀ i y, ‖ψ1 i y‖ ≤ M1 i)
    (hhol : ∀ i y z, ‖ψ1 i y - ψ1 i z‖ ≤ H i * ‖y - z‖ ^ μ) (hH : ∀ i, 0 ≤ H i) :
    ∃ (Gm : Eu d → Eu d) (DG : Eu d → (Eu d →L[ℝ] Eu d)) (D2G : Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] Eu d)),
      (∀ x v, (∀ i, inner ℝ (w i) v = 0) → inner ℝ (Gm x) v = inner ℝ x v) ∧
      (∀ x, HasStrictFDerivAt Gm (DG x) x) ∧ Continuous DG ∧
      (∀ x, inner ℝ x e = 0 → Gm x = x ∧
        DG x = ContinuousLinearMap.id ℝ (Eu d) - (innerSL ℝ e).smulRight (∑ i, ψ i x • w i)) ∧
      (∀ x, 0 < inner ℝ x e → HasFDerivAt DG (D2G x) x) ∧
      (∀ (c : Eu d) (r : ℝ), 0 ≤ r → ∃ K, C2B {x : Eu d | 0 ≤ inner ℝ x e ∧ dist x c ≤ r} μ K Gm DG D2G) := by
  obtain ⟨T, DT, D2T, hT, hs, hcont, hpl, hd2, C, hC0, hCh⟩ :=
    ext_vec hP w e he M0 M1 H ψ ψ1 hd hc hb0 hb1 hhol hH
  refine ⟨fun x => x - T x, fun x => ContinuousLinearMap.id ℝ (Eu d) - DT x, fun x => -D2T x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x v hv
    obtain ⟨c, hcx⟩ := hT x
    rw [inner_sub_left, hcx, sum_inner]
    simp [real_inner_smul_left, hv]
  · intro x
    exact (hasStrictFDerivAt_id x).sub (hs x)
  · exact continuous_const.sub hcont
  · intro x hx
    obtain ⟨h1, h2⟩ := hpl x hx
    exact ⟨by simp [h1], by dsimp only; rw [h2]⟩
  · intro x hx
    simpa using (hd2 x hx).const_sub (ContinuousLinearMap.id ℝ (Eu d))
  · intro c r hr
    refine half_C2B he hr hμ0 (continuous_id.sub (continuous_iff_continuousAt.2 fun x => (hs x).continuousAt))
      (continuous_const.sub hcont) (fun x _ => (hasFDerivAt_id x).sub (hs x).hasFDerivAt)
      (fun x hx => (hd2 x hx).const_sub (ContinuousLinearMap.id ℝ (Eu d))) (fun x x' hx hx' => ?_) hC0
    rw [neg_sub_neg]
    exact (norm_sub_rev (D2T x) (D2T x')).trans_le (hCh x x' hx hx')

end Shear

end ObliqueLib

theorem solution (n : ℕ) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hP : ∀ (M0 M1 H : ℝ) (ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (ψ1 : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)) (e : EuclideanSpace ℝ (Fin (n + 1))),
        (∀ y, HasFDerivAt ψ (ψ1 y) y) → Continuous ψ1 → (∀ y, |ψ y| ≤ M0) → (∀ y, ‖ψ1 y‖ ≤ M1) →
        (∀ y z, ‖ψ1 y - ψ1 z‖ ≤ H * ‖y - z‖ ^ μ) → 0 ≤ H → ‖e‖ = 1 →
        ∃ (E : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (DE : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)) (D2E : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)),
          (∀ x, HasStrictFDerivAt E (DE x) x) ∧ Continuous DE ∧
          (∀ x, inner ℝ x e = 0 → E x = 0 ∧ DE x = ψ x • innerSL ℝ e) ∧
          (∀ x, 0 < inner ℝ x e → HasFDerivAt DE (D2E x) x) ∧
          ∃ C, 0 ≤ C ∧ ∀ x x' : EuclideanSpace ℝ (Fin (n + 1)), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
            ‖D2E x' - D2E x‖ ≤ C * ‖x' - x‖ ^ μ) :
    ∀ {m : ℕ} (w : Fin m → EuclideanSpace ℝ (Fin (n + 1))) (e : EuclideanSpace ℝ (Fin (n + 1))) (he : ‖e‖ = 1)
    (M0 M1 H : Fin m → ℝ) (ψ : Fin m → EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (ψ1 : Fin m → EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ))
    (hd : ∀ i y, HasFDerivAt (ψ i) (ψ1 i y) y) (hc : ∀ i, Continuous (ψ1 i))
    (hb0 : ∀ i y, |ψ i y| ≤ M0 i) (hb1 : ∀ i y, ‖ψ1 i y‖ ≤ M1 i)
    (hhol : ∀ i y z, ‖ψ1 i y - ψ1 i z‖ ≤ H i * ‖y - z‖ ^ μ) (hH : ∀ i, 0 ≤ H i),
    ∃ (Gm : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) (DG : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) (D2G : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))),
      (∀ x v, (∀ i, inner ℝ (w i) v = 0) → inner ℝ (Gm x) v = inner ℝ x v) ∧
      (∀ x, HasStrictFDerivAt Gm (DG x) x) ∧ Continuous DG ∧
      (∀ x, inner ℝ x e = 0 → Gm x = x ∧
        DG x = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1))) - (innerSL ℝ e).smulRight (∑ i, ψ i x • w i)) ∧
      (∀ x, 0 < inner ℝ x e → HasFDerivAt DG (D2G x) x) ∧
      (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 ≤ r → ∃ K, let S : Set (EuclideanSpace ℝ (Fin (n + 1))) := {x : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ inner ℝ x e ∧ dist x c ≤ r}
        0 ≤ K ∧ (∀ x ∈ S, ∀ y ∈ S, ‖Gm x - Gm y‖ ≤ K * ‖x - y‖) ∧ (∀ x ∈ S, ‖DG x‖ ≤ K) ∧ (∀ x ∈ S, ∀ y ∈ S, ‖DG x - DG y‖ ≤ K * ‖x - y‖) ∧ (∀ x ∈ S, ‖D2G x‖ ≤ K) ∧ (∀ x ∈ S, ∀ y ∈ S, ‖D2G x - D2G y‖ ≤ K * ‖x - y‖ ^ μ)) := by
  intro m w e he M0 M1 H ψ ψ1 hd hc hb0 hb1 hhol hH
  obtain ⟨Gm, DG, D2G, h1, h2, h3, h4, h5, h6⟩ := ObliqueLib.shear hP hμ0.le w e he M0 M1 H ψ ψ1 hd hc hb0 hb1 hhol hH
  refine ⟨Gm, DG, D2G, h1, h2, h3, h4, h5, fun c r hr => ?_⟩
  obtain ⟨K, hK⟩ := h6 c r hr
  exact ⟨K, hK.hK, hK.lip, hK.b1, hK.lip1, hK.b2, hK.hol2⟩
