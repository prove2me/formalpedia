-- Prove2me | solution 1 for EthierKurtz.oblique_halfspace_model_general_principal_part
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T00:27:33.734709+00:00
-- url     : https://prove2.me/submissions/85d73845-025a-43e5-b8f2-59260db55ec8

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder

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

lemma eu_expand (v : Eu n) : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
  have h := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] at h
  exact h.symm

end Glue

section OpTrans

variable {d : ℕ}

lemma lin_expand (A : Eu d →L[ℝ] ℝ) (w : Eu d) : A w = ∑ k, w k * A (EuclideanSpace.single k (1 : ℝ)) := by
  conv_lhs => rw [eu_expand w]
  simp only [map_sum, map_smul, smul_eq_mul]

lemma bil_expand (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) (v w : Eu d) :
    B v w = ∑ k, ∑ l, v k * w l * B (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ)) := by
  rw [lin_expand (B v) w]
  conv_lhs => rw [eu_expand v]
  simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

end OpTrans

section VarDef

/-- Variable-coefficient half-space solvability with Schauder bounds. -/
def VarModel (d : ℕ) (μ : ℝ) : Prop :=
  ∀ e b : Eu d, ‖e‖ = 1 → inner ℝ b e = 0 → ∃ δ : ℝ, 0 < δ ∧ ∀ K : ℝ, 0 ≤ K →
  ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧ ∀ lam : ℝ, lam0 ≤ lam →
  ∀ (α : Eu d → Fin d → Fin d → ℝ) (β : Eu d → Fin d → ℝ),
    (∀ x : Eu d, 0 ≤ inner ℝ x e → ∑ i, ∑ j, |α x i j| ≤ δ) →
    (∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, ∑ j, |α x i j - α x' i j| ≤ K * ‖x - x'‖ ^ μ) →
    (∀ x : Eu d, 0 ≤ inner ℝ x e → ∑ i, |β x i| ≤ K) →
    (∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, |β x i - β x' i| ≤ K * ‖x - x'‖ ^ μ) →
    ∀ (g : Eu d → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ y : Eu d, 0 ≤ inner ℝ y e → |g y| ≤ M) →
    (∀ y z : Eu d, 0 ≤ inner ℝ y e → 0 ≤ inner ℝ z e → |g y - g z| ≤ H * ‖y - z‖ ^ μ) →
    ∃ (u : Eu d → ℝ) (u1 : Eu d → Eu d →L[ℝ] ℝ) (u2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
      (∀ x : Eu d, 0 < inner ℝ x e → HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
      (∀ x : Eu d, 0 ≤ inner ℝ x e →
        lam * u x - (1 / 2 : ℝ) * ∑ i, u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
          - ∑ i, ∑ j, α x i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - ∑ i, β x i * u1 x (EuclideanSpace.single i 1) = g x) ∧
      (∀ x : Eu d, inner ℝ x e = 0 → u1 x (b - e) = 0) ∧
      (∀ x : Eu d, 0 ≤ inner ℝ x e → ∀ v w : Eu d,
        |u x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        |u1 x v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ ∧
        |u2 x v w| ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ * ‖w‖) ∧
      (∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e → ∀ v w : Eu d,
        |u x - u x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        |u1 x v - u1 x' v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ ∧
        |u2 x v w - u2 x' v w| ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ * ‖w‖)

end VarDef

section NormA

variable {d : ℕ}

theorem exists_normalizer (A0 : Matrix (Fin d) (Fin d) ℝ) (hA : A0.PosDef) :
    ∃ S Si : Eu d →L[ℝ] Eu d, (∀ y, S (Si y) = y) ∧ (∀ z, Si (S z) = z) ∧
      ∀ k l : Fin d, ∑ i, ∑ j, A0 i j * S (EuclideanSpace.single i 1) k * S (EuclideanSpace.single j 1) l =
        if k = l then 1 else 0 := by
  classical
  set v := hA.1.eigenvectorBasis with hv
  set ev := hA.1.eigenvalues with hev
  have hpos : ∀ k, 0 < ev k := fun k => hA.eigenvalues_pos k
  set s : Fin d → ℝ := fun k => Real.sqrt (ev k) with hs
  have hs0 : ∀ k, 0 < s k := fun k => Real.sqrt_pos.mpr (hpos k)
  have hss : ∀ k, s k * s k = ev k := fun k => Real.mul_self_sqrt (hpos k).le
  let S : Eu d →L[ℝ] Eu d :=
    ∑ k, ((s k)⁻¹ • innerSL ℝ (v k)).smulRight (EuclideanSpace.single k (1 : ℝ))
  let Si : Eu d →L[ℝ] Eu d :=
    ∑ k, (s k • (EuclideanSpace.proj k : Eu d →L[ℝ] ℝ)).smulRight (v k)
  have hS : ∀ z m, S z m = (s m)⁻¹ * inner ℝ (v m) z := by
    intro z m
    simp [S, Pi.single_apply]
  have hSi : ∀ y, Si y = ∑ k, (s k * y k) • v k := by
    intro y
    simp [Si]
  have hon := v.orthonormal
  refine ⟨S, Si, fun y => ?_, fun z => ?_, fun k l => ?_⟩
  · ext m
    rw [hS, hSi, hon.inner_right_fintype]
    field_simp [(hs0 m).ne']
  · rw [hSi]
    have h1 : ∀ k, (s k * S z k) • v k = inner ℝ (v k) z • v k := by
      intro k
      rw [hS]
      congr 1
      field_simp [(hs0 k).ne']
    simp_rw [h1]
    exact v.sum_repr' z
  · have hSe : ∀ i m, S (EuclideanSpace.single i 1) m = (s m)⁻¹ * v m i := by
      intro i m
      rw [hS, EuclideanSpace.inner_single_right]
      simp
    have hmul : ∀ i, ∑ j, A0 i j * v l j = ev l * v l i := by
      intro i
      have := congrFun (hA.1.mulVec_eigenvectorBasis l) i
      simpa [Matrix.mulVec, dotProduct] using this
    have hinner : ∑ i, v k i * v l i = if k = l then 1 else 0 := by
      have := orthonormal_iff_ite.mp hon k l
      rw [← this, PiLp.inner_apply]
      simp [mul_comm]
    calc ∑ i, ∑ j, A0 i j * S (EuclideanSpace.single i 1) k * S (EuclideanSpace.single j 1) l
        = ∑ i, ((s k)⁻¹ * (s l)⁻¹) * (v k i * ∑ j, A0 i j * v l j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hSe, hSe]; ring
      _ = ((s k)⁻¹ * (s l)⁻¹ * ev l) * ∑ i, v k i * v l i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hmul]; ring
      _ = if k = l then 1 else 0 := by
          rw [hinner]
          split_ifs with hkl
          · subst hkl
            rw [← hss k]
            field_simp [(hs0 k).ne']
          · simp

end NormA

section VarA

variable {d : ℕ}

/-- Variable-coefficient half-space solvability with principal part `½ Σ A0_ij ∂_ij`, `A0` positive definite. -/
def VarModelA (d : ℕ) (μ : ℝ) : Prop :=
  ∀ A0 : Matrix (Fin d) (Fin d) ℝ, A0.PosDef →
  ∀ e b : Eu d, ‖e‖ = 1 → inner ℝ b e = 0 → ∃ δ : ℝ, 0 < δ ∧ ∀ K : ℝ, 0 ≤ K →
  ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧ ∀ lam : ℝ, lam0 ≤ lam →
  ∀ (α : Eu d → Fin d → Fin d → ℝ) (β : Eu d → Fin d → ℝ),
    (∀ x : Eu d, 0 ≤ inner ℝ x e → ∑ i, ∑ j, |α x i j| ≤ δ) →
    (∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, ∑ j, |α x i j - α x' i j| ≤ K * ‖x - x'‖ ^ μ) →
    (∀ x : Eu d, 0 ≤ inner ℝ x e → ∑ i, |β x i| ≤ K) →
    (∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, |β x i - β x' i| ≤ K * ‖x - x'‖ ^ μ) →
    ∀ (g : Eu d → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ y : Eu d, 0 ≤ inner ℝ y e → |g y| ≤ M) →
    (∀ y z : Eu d, 0 ≤ inner ℝ y e → 0 ≤ inner ℝ z e → |g y - g z| ≤ H * ‖y - z‖ ^ μ) →
    ∃ (u : Eu d → ℝ) (u1 : Eu d → Eu d →L[ℝ] ℝ) (u2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
      (∀ x : Eu d, 0 < inner ℝ x e → HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
      (∀ x : Eu d, 0 ≤ inner ℝ x e →
        lam * u x - (1 / 2 : ℝ) * ∑ i, ∑ j, A0 i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - ∑ i, ∑ j, α x i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - ∑ i, β x i * u1 x (EuclideanSpace.single i 1) = g x) ∧
      (∀ x : Eu d, inner ℝ x e = 0 → u1 x (b - e) = 0) ∧
      (∀ x : Eu d, 0 ≤ inner ℝ x e → ∀ v w : Eu d,
        |u x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        |u1 x v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ ∧
        |u2 x v w| ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ * ‖w‖) ∧
      (∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e → ∀ v w : Eu d,
        |u x - u x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        |u1 x v - u1 x' v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ ∧
        |u2 x v w - u2 x' v w| ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ * ‖w‖)

lemma sum4_comm (f : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  calc ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, ∑ l, f i j k l := Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm

lemma lin_sum_le (s : Fin d → Fin d → ℝ) {c : ℝ} (hc : ∀ i, ∑ k, |s i k| ≤ c) (y : Fin d → ℝ) :
    ∑ k, |∑ i, y i * s i k| ≤ c * ∑ i, |y i| := by
  calc ∑ k, |∑ i, y i * s i k| ≤ ∑ k, ∑ i, |y i| * |s i k| :=
        Finset.sum_le_sum fun k _ => (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (by simp [abs_mul]))
    _ = ∑ i, |y i| * ∑ k, |s i k| := by rw [Finset.sum_comm]; simp [Finset.mul_sum]
    _ ≤ ∑ i, |y i| * c := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hc i) (abs_nonneg _)
    _ = c * ∑ i, |y i| := by rw [Finset.mul_sum]; simp [mul_comm]

lemma quad_sum_le (s : Fin d → Fin d → ℝ) {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ i, ∑ k, |s i k| ≤ c)
    (x : Fin d → Fin d → ℝ) :
    ∑ k, ∑ l, |∑ i, ∑ j, x i j * s i k * s j l| ≤ c ^ 2 * ∑ i, ∑ j, |x i j| := by
  have h1 : ∀ k l, |∑ i, ∑ j, x i j * s i k * s j l| ≤ ∑ i, ∑ j, |x i j| * |s i k| * |s j l| := by
    intro k l
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    simp [abs_mul]
  calc ∑ k, ∑ l, |∑ i, ∑ j, x i j * s i k * s j l|
      ≤ ∑ k, ∑ l, ∑ i, ∑ j, |x i j| * |s i k| * |s j l| :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => h1 k l
    _ = ∑ i, ∑ j, |x i j| * ((∑ k, |s i k|) * ∑ l, |s j l|) := by
        rw [← sum4_comm (fun i j k l => |x i j| * |s i k| * |s j l|)]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
    _ ≤ ∑ i, ∑ j, |x i j| * (c * c) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact mul_le_mul (hc i) (hc j) (Finset.sum_nonneg fun _ _ => abs_nonneg _) hc0
    _ = c ^ 2 * ∑ i, ∑ j, |x i j| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

lemma chg_le {X Ct F Nt N G G' a b Cq : ℝ} (hX : X ≤ Ct * F * Nt * G) (hCt : 0 ≤ Ct) (hF : 0 ≤ F)
    (hG0 : 0 ≤ G) (hNt : Nt ≤ a * N) (hG : G ≤ b * G') (ha : 0 ≤ a) (hN : 0 ≤ N)
    (hG'0 : 0 ≤ G') (hab : a * b ≤ Cq) (hb : 0 ≤ b) : X ≤ Ct * Cq * F * N * G' := by
  have hCF : 0 ≤ Ct * F := mul_nonneg hCt hF
  have h1 : Ct * F * Nt * G ≤ Ct * F * (a * N) * G :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNt hCF) hG0
  have h2 : Ct * F * (a * N) * G ≤ Ct * F * (a * N) * (b * G') :=
    mul_le_mul_of_nonneg_left hG (mul_nonneg hCF (mul_nonneg ha hN))
  have h3 : Ct * F * (a * N) * (b * G') = (Ct * F * N * G') * (a * b) := by ring
  have h4 : (Ct * F * N * G') * (a * b) ≤ (Ct * F * N * G') * Cq :=
    mul_le_mul_of_nonneg_left hab (mul_nonneg (mul_nonneg hCF hN) hG'0)
  have h5 : (Ct * F * N * G') * Cq = Ct * Cq * F * N * G' := by ring
  linarith

lemma clm_rpow_le {μ : ℝ} (hμ0 : 0 ≤ μ) (T : Eu d →L[ℝ] Eu d) (x x' : Eu d) :
    ‖T x - T x'‖ ^ μ ≤ ‖T‖ ^ μ * ‖x - x'‖ ^ μ := by
  rw [← Real.mul_rpow (norm_nonneg _) (norm_nonneg _), ← map_sub]
  exact Real.rpow_le_rpow (norm_nonneg _) (T.le_opNorm _) hμ0

set_option maxHeartbeats 1000000 in
theorem varModelA {μ : ℝ} (hμ0 : 0 ≤ μ) (hV : VarModel d μ) : VarModelA d μ := by
  intro A0 hA e b he hb
  obtain ⟨S, Si, hSSi, hSiS, hnorm⟩ := exists_normalizer A0 hA
  set w : Eu d := (ContinuousLinearMap.adjoint Si) e with hwdef
  have hw : ∀ y, inner ℝ (Si y) e = inner ℝ y w := fun y =>
    (ContinuousLinearMap.adjoint_inner_right Si y e).symm
  have hwz : ∀ z, inner ℝ z e = inner ℝ (S z) w := by
    intro z; rw [← hw, hSiS]
  have hw0 : 0 < ‖w‖ := by
    rcases (norm_nonneg w).lt_or_eq with h | h
    · exact h
    · exfalso
      have hw00 : w = 0 := norm_eq_zero.mp h.symm
      have h1 := hwz e
      rw [hw00, inner_zero_right, real_inner_self_eq_norm_sq, he] at h1
      norm_num at h1
  set e' : Eu d := ‖w‖⁻¹ • w with he'def
  have he' : ‖e'‖ = 1 := by
    rw [he'def, norm_smul, norm_inv, norm_norm]; field_simp
  have hy : ∀ y, inner ℝ (Si y) e = ‖w‖ * inner ℝ y e' := by
    intro y; rw [hw, he'def, inner_smul_right]; field_simp
  have hz : ∀ z, inner ℝ z e = ‖w‖ * inner ℝ (S z) e' := by
    intro z; rw [← hy, hSiS]
  have hTz : ∀ z, 0 ≤ inner ℝ z e ↔ 0 ≤ inner ℝ (S z) e' := by
    intro z; rw [hz]; exact mul_nonneg_iff_of_pos_left hw0
  have hTy : ∀ y, 0 ≤ inner ℝ y e' → 0 ≤ inner ℝ (Si y) e := by
    intro y h; rw [hy]; exact mul_nonneg hw0.le h
  have hPz : ∀ z, 0 < inner ℝ z e → 0 < inner ℝ (S z) e' := by
    intro z h; rw [hz] at h; exact (mul_pos_iff_of_pos_left hw0).mp h
  have hZz : ∀ z, inner ℝ z e = 0 → inner ℝ (S z) e' = 0 := by
    intro z h; rw [hz] at h; exact (mul_eq_zero.mp h).resolve_left hw0.ne'
  set q : Eu d := S (b - e) with hqdef
  have hq : inner ℝ q e' = -‖w‖⁻¹ := by
    have h1 := hz (b - e)
    rw [inner_sub_left, hb, real_inner_self_eq_norm_sq, he] at h1
    rw [← hqdef] at h1
    field_simp
    linarith
  set b' : Eu d := ‖w‖ • q + e' with hb'def
  have hb' : inner ℝ b' e' = 0 := by
    rw [hb'def, inner_add_left, inner_smul_left, hq, real_inner_self_eq_norm_sq, he']
    simp only [conj_trivial]
    field_simp
    ring
  have hqb : q = ‖w‖⁻¹ • (b' - e') := by
    rw [hb'def, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hw0.ne', one_smul]
  obtain ⟨δ, hδ, hVδ⟩ := hV e' b' he' hb'
  set s : Fin d → Fin d → ℝ := fun i k => S (EuclideanSpace.single i 1) k with hsdef
  set cS : ℝ := ∑ i, ∑ k, |s i k| with hcS
  have hcS0 : 0 ≤ cS := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => abs_nonneg _
  have hcSi : ∀ i, ∑ k, |s i k| ≤ cS := fun i =>
    Finset.single_le_sum (f := fun i => ∑ k, |s i k|) (fun i _ => Finset.sum_nonneg fun k _ => abs_nonneg _)
      (Finset.mem_univ i)
  refine ⟨δ / (cS ^ 2 + 1), by positivity, fun K hK => ?_⟩
  set nS : ℝ := ‖S‖ with hnS
  set nSi : ℝ := ‖Si‖ with hnSi
  have hnS0 : 0 ≤ nS := norm_nonneg _
  have hnSi0 : 0 ≤ nSi := norm_nonneg _
  have hpSi : 0 ≤ nSi ^ μ := Real.rpow_nonneg hnSi0 _
  have hpS : 0 ≤ nS ^ μ := Real.rpow_nonneg hnS0 _
  set Kt : ℝ := (cS ^ 2 + cS + 1) * K * (nSi ^ μ + 1) with hKt
  have hKt0 : 0 ≤ Kt := by positivity
  obtain ⟨lam0, Ct, hlam0, hCt, hsol⟩ := hVδ Kt hKt0
  set Cq : ℝ := (nSi ^ μ + 1) * ((nS + 1) ^ 2 * (nS ^ μ + 1)) with hCq
  have hCq0 : 0 ≤ Cq := by positivity
  refine ⟨lam0, Ct * Cq, hlam0, mul_nonneg hCt hCq0,
    fun lam hlam α β hα1 hα2 hβ1 hβ2 g M H hM hH hg1 hg2 => ?_⟩
  have hlam1 : 1 ≤ lam := hlam0.trans hlam
  -- transformed data
  set αt : Eu d → Fin d → Fin d → ℝ := fun y k l => ∑ i, ∑ j, α (Si y) i j * s i k * s j l with hαt
  set βt : Eu d → Fin d → ℝ := fun y k => ∑ i, β (Si y) i * s i k with hβt
  set gt : Eu d → ℝ := fun y => g (Si y) with hgt
  set Ht : ℝ := H * (nSi ^ μ + 1) with hHt
  have hKa : cS ^ 2 * K * nSi ^ μ ≤ Kt := by
    have h1 : 0 ≤ (cS + 1) * K * nSi ^ μ := by positivity
    have h2 : 0 ≤ (cS ^ 2 + cS + 1) * K := by positivity
    have h3 : Kt = cS ^ 2 * K * nSi ^ μ + ((cS + 1) * K * nSi ^ μ + (cS ^ 2 + cS + 1) * K) := by
      rw [hKt]; ring
    linarith
  have hKb : cS * K * nSi ^ μ ≤ Kt := by
    have h1 : 0 ≤ (cS ^ 2 + 1) * K * nSi ^ μ := by positivity
    have h2 : 0 ≤ (cS ^ 2 + cS + 1) * K := by positivity
    have h3 : Kt = cS * K * nSi ^ μ + ((cS ^ 2 + 1) * K * nSi ^ μ + (cS ^ 2 + cS + 1) * K) := by
      rw [hKt]; ring
    linarith
  have hKc : cS * K ≤ Kt := by
    have h1 : 0 ≤ (cS ^ 2 + 1) * K := by positivity
    have h2 : 0 ≤ (cS ^ 2 + cS + 1) * K * nSi ^ μ := by positivity
    have h3 : Kt = cS * K + ((cS ^ 2 + 1) * K + (cS ^ 2 + cS + 1) * K * nSi ^ μ) := by
      rw [hKt]; ring
    linarith
  have hαt1 : ∀ y : Eu d, 0 ≤ inner ℝ y e' → ∑ k, ∑ l, |αt y k l| ≤ δ := by
    intro y hy0
    have h1 := quad_sum_le s hcS0 hcSi (α (Si y))
    have h2 := hα1 (Si y) (hTy y hy0)
    have h3 : cS ^ 2 * (δ / (cS ^ 2 + 1)) ≤ δ := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      have h4 : δ * (cS ^ 2 + 1) = cS ^ 2 * δ + δ := by ring
      linarith
    calc ∑ k, ∑ l, |αt y k l| ≤ cS ^ 2 * ∑ i, ∑ j, |α (Si y) i j| := h1
      _ ≤ cS ^ 2 * (δ / (cS ^ 2 + 1)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ δ := h3
  have hαt2 : ∀ y y' : Eu d, 0 ≤ inner ℝ y e' → 0 ≤ inner ℝ y' e' →
      ∑ k, ∑ l, |αt y k l - αt y' k l| ≤ Kt * ‖y - y'‖ ^ μ := by
    intro y y' hy0 hy0'
    have hsub : ∀ k l, αt y k l - αt y' k l =
        ∑ i, ∑ j, (α (Si y) i j - α (Si y') i j) * s i k * s j l := by
      intro k l
      simp only [hαt, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [hsub]
    have h1 := quad_sum_le s hcS0 hcSi (fun i j => α (Si y) i j - α (Si y') i j)
    have h2 := hα2 (Si y) (Si y') (hTy y hy0) (hTy y' hy0')
    have h3 := clm_rpow_le hμ0 Si y y'
    have hp : 0 ≤ ‖y - y'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    calc _ ≤ cS ^ 2 * ∑ i, ∑ j, |α (Si y) i j - α (Si y') i j| := h1
      _ ≤ cS ^ 2 * (K * ‖Si y - Si y'‖ ^ μ) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ cS ^ 2 * (K * (nSi ^ μ * ‖y - y'‖ ^ μ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hK) (by positivity)
      _ = (cS ^ 2 * K * nSi ^ μ) * ‖y - y'‖ ^ μ := by ring
      _ ≤ Kt * ‖y - y'‖ ^ μ := mul_le_mul_of_nonneg_right hKa hp
  have hβt1 : ∀ y : Eu d, 0 ≤ inner ℝ y e' → ∑ k, |βt y k| ≤ Kt := by
    intro y hy0
    have h1 := lin_sum_le s hcSi (β (Si y))
    have h2 := hβ1 (Si y) (hTy y hy0)
    calc ∑ k, |βt y k| ≤ cS * ∑ i, |β (Si y) i| := h1
      _ ≤ cS * K := mul_le_mul_of_nonneg_left h2 hcS0
      _ ≤ Kt := hKc
  have hβt2 : ∀ y y' : Eu d, 0 ≤ inner ℝ y e' → 0 ≤ inner ℝ y' e' →
      ∑ k, |βt y k - βt y' k| ≤ Kt * ‖y - y'‖ ^ μ := by
    intro y y' hy0 hy0'
    have hsub : ∀ k, βt y k - βt y' k = ∑ i, (β (Si y) i - β (Si y') i) * s i k := by
      intro k
      simp only [hβt, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    simp_rw [hsub]
    have h1 := lin_sum_le s hcSi (fun i => β (Si y) i - β (Si y') i)
    have h2 := hβ2 (Si y) (Si y') (hTy y hy0) (hTy y' hy0')
    have h3 := clm_rpow_le hμ0 Si y y'
    have hp : 0 ≤ ‖y - y'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    calc _ ≤ cS * ∑ i, |β (Si y) i - β (Si y') i| := h1
      _ ≤ cS * (K * ‖Si y - Si y'‖ ^ μ) := mul_le_mul_of_nonneg_left h2 hcS0
      _ ≤ cS * (K * (nSi ^ μ * ‖y - y'‖ ^ μ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hK) hcS0
      _ = (cS * K * nSi ^ μ) * ‖y - y'‖ ^ μ := by ring
      _ ≤ Kt * ‖y - y'‖ ^ μ := mul_le_mul_of_nonneg_right hKb hp
  have hgt1 : ∀ y : Eu d, 0 ≤ inner ℝ y e' → |gt y| ≤ M := fun y hy0 => hg1 (Si y) (hTy y hy0)
  have hgt2 : ∀ y z : Eu d, 0 ≤ inner ℝ y e' → 0 ≤ inner ℝ z e' → |gt y - gt z| ≤ Ht * ‖y - z‖ ^ μ := by
    intro y z hy0 hz0
    have h2 := hg2 (Si y) (Si z) (hTy y hy0) (hTy z hz0)
    have h3 := clm_rpow_le hμ0 Si y z
    have hp : 0 ≤ ‖y - z‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    calc |gt y - gt z| ≤ H * ‖Si y - Si z‖ ^ μ := h2
      _ ≤ H * (nSi ^ μ * ‖y - z‖ ^ μ) := mul_le_mul_of_nonneg_left h3 hH
      _ ≤ Ht * ‖y - z‖ ^ μ := by
          have : H * (nSi ^ μ * ‖y - z‖ ^ μ) + H * ‖y - z‖ ^ μ = Ht * ‖y - z‖ ^ μ := by ring
          linarith [mul_nonneg hH hp]
  obtain ⟨v, v1, v2, hvd, hve, hvb, hvs, hvt⟩ :=
    hsol lam hlam αt βt hαt1 hαt2 hβt1 hβt2 gt M Ht hM (by positivity) hgt1 hgt2
  set P : (Eu d →L[ℝ] ℝ) →L[ℝ] (Eu d →L[ℝ] ℝ) := (ContinuousLinearMap.compL ℝ (Eu d) (Eu d) ℝ).flip S with hP
  have hPa : ∀ φ : Eu d →L[ℝ] ℝ, P φ = φ.comp S := fun φ => rfl
  have hu2 : ∀ z v' w' : Eu d, (P.comp ((v2 (S z)).comp S)) v' w' = v2 (S z) (S v') (S w') := by
    intro z v' w'; rfl
  -- weights
  set N : ℝ := lam ^ (μ / 2) * M + H with hN
  set Nt : ℝ := lam ^ (μ / 2) * M + Ht with hNt
  have hlp : 0 ≤ lam ^ (μ / 2) := Real.rpow_nonneg (by linarith) _
  have hN0 : 0 ≤ N := by positivity
  have hNtN : Nt ≤ (nSi ^ μ + 1) * N := by
    have h1 : 0 ≤ nSi ^ μ * (lam ^ (μ / 2) * M) := by positivity
    have h2 : (nSi ^ μ + 1) * N = nSi ^ μ * (lam ^ (μ / 2) * M) + Nt := by ring
    linarith
  have hT : (nS + 1) ^ 2 * (nS ^ μ + 1) =
      nS ^ μ * (nS * nS) + 2 * (nS ^ μ * nS) + nS ^ μ + (nS * nS + 2 * nS + 1) := by ring
  have hq1 : 0 ≤ nS ^ μ * (nS * nS) := by positivity
  have hq2 : 0 ≤ nS ^ μ * nS := by positivity
  have hq3 : 0 ≤ nS * nS := by positivity
  have hS1 : nS ≤ (nS + 1) ^ 2 * (nS ^ μ + 1) := by linarith
  have hS2 : nS * nS ≤ (nS + 1) ^ 2 * (nS ^ μ + 1) := by linarith
  have hS0 : (1 : ℝ) ≤ (nS + 1) ^ 2 * (nS ^ μ + 1) := by linarith
  have hS3 : nS ^ μ ≤ (nS + 1) ^ 2 * (nS ^ μ + 1) := by linarith
  have hS4 : nS ^ μ * nS ≤ (nS + 1) ^ 2 * (nS ^ μ + 1) := by linarith
  have hS5 : nS ^ μ * (nS * nS) ≤ (nS + 1) ^ 2 * (nS ^ μ + 1) := by linarith
  have hab : ∀ t : ℝ, 0 ≤ t → t ≤ (nS + 1) ^ 2 * (nS ^ μ + 1) → (nSi ^ μ + 1) * t ≤ Cq := by
    intro t _ ht
    exact mul_le_mul_of_nonneg_left ht (by positivity)
  have hSv : ∀ v' : Eu d, ‖S v'‖ ≤ nS * ‖v'‖ := fun v' => S.le_opNorm v'
  refine ⟨fun z => v (S z), fun z => (v1 (S z)).comp S, fun z => P.comp ((v2 (S z)).comp S),
    fun z hz0 => ?_, fun z hz0 => ?_, fun z hz0 => ?_, fun z hz0 v' w' => ?_, fun z z' hz0 hz0' v' w' => ?_⟩
  · obtain ⟨h1, h2⟩ := hvd (S z) (hPz z hz0)
    refine ⟨h1.comp z S.hasFDerivAt, ?_⟩
    exact P.hasFDerivAt.comp z (h2.comp z S.hasFDerivAt)
  · have he0 := hve (S z) ((hTz z).mp hz0)
    set V : Fin d → Fin d → ℝ := fun k l =>
      v2 (S z) (EuclideanSpace.single k 1) (EuclideanSpace.single l 1) with hV
    have hexp : ∀ i j, (P.comp ((v2 (S z)).comp S)) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
        ∑ k, ∑ l, s i k * s j l * V k l := by
      intro i j
      rw [hu2]
      exact bil_expand (v2 (S z)) _ _
    have hexp1 : ∀ i, ((v1 (S z)).comp S) (EuclideanSpace.single i 1) =
        ∑ k, s i k * v1 (S z) (EuclideanSpace.single k 1) := by
      intro i
      exact lin_expand (v1 (S z)) _
    have k1 : ∑ i, ∑ j, A0 i j * (P.comp ((v2 (S z)).comp S)) (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) = ∑ k, V k k := by
      simp_rw [hexp, Finset.mul_sum]
      rw [sum4_comm (fun i j k l => A0 i j * (s i k * s j l * V k l))]
      have : ∀ k l, ∑ i, ∑ j, A0 i j * (s i k * s j l * V k l) = (if k = l then 1 else 0) * V k l := by
        intro k l
        rw [← hnorm k l, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hsdef]
        ring
      simp_rw [this]
      simp
    have k2 : ∑ i, ∑ j, α z i j * (P.comp ((v2 (S z)).comp S)) (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) = ∑ k, ∑ l, αt (S z) k l * V k l := by
      simp_rw [hexp, Finset.mul_sum]
      rw [sum4_comm (fun i j k l => α z i j * (s i k * s j l * V k l))]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [hαt, hSiS, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have k3 : ∑ i, β z i * ((v1 (S z)).comp S) (EuclideanSpace.single i 1) =
        ∑ k, βt (S z) k * v1 (S z) (EuclideanSpace.single k 1) := by
      simp_rw [hexp1, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hβt, hSiS, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hg' : gt (S z) = g z := by simp only [hgt, hSiS]
    rw [k1, k2, k3, ← hg']
    exact he0
  · have h1 := hvb (S z) (hZz z hz0)
    show v1 (S z) (S (b - e)) = 0
    rw [← hqdef, hqb, map_smul, h1, smul_zero]
  · obtain ⟨b0, b1, b2⟩ := hvs (S z) ((hTz z).mp hz0) (S v') (S w')
    have hv0 := norm_nonneg v'
    have hw0' := norm_nonneg w'
    have hF0 : 0 ≤ (1 / lam) * (1 / lam) ^ (μ / 2) := by positivity
    have hF1 : 0 ≤ (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) := by positivity
    have hF2 : 0 ≤ (1 / lam) ^ (μ / 2) := by positivity
    refine ⟨?_, ?_, ?_⟩
    · have := chg_le (X := |v (S z)|) (G := 1) (G' := 1) (b := 1)
        (by simpa [mul_assoc] using b0) hCt hF0 zero_le_one hNtN (by norm_num) (by positivity) hN0 zero_le_one
        (by have := hab 1 zero_le_one hS0; simpa using this) zero_le_one
      simpa [mul_assoc] using this
    · have := chg_le (X := |v1 (S z) (S v')|) (b := nS) (G' := ‖v'‖)
        (by simpa [mul_assoc] using b1) hCt hF1 (norm_nonneg _) hNtN (hSv v') (by positivity) hN0 hv0
        (hab nS hnS0 hS1) hnS0
      simpa [mul_assoc] using this
    · have hSS : ‖S v'‖ * ‖S w'‖ ≤ (nS * nS) * (‖v'‖ * ‖w'‖) := by
        have := mul_le_mul (hSv v') (hSv w') (norm_nonneg _) (by positivity)
        linarith [this]
      have := chg_le (X := |v2 (S z) (S v') (S w')|) (G := ‖S v'‖ * ‖S w'‖) (b := nS * nS)
        (G' := ‖v'‖ * ‖w'‖)
        (by simpa [mul_assoc] using b2) hCt hF2 (by positivity) hNtN hSS (by positivity) hN0
        (by positivity) (hab (nS * nS) (by positivity) hS2) (by positivity)
      rw [hu2]
      simpa [mul_assoc] using this
  · obtain ⟨t0, t1, t2⟩ := hvt (S z) (S z') ((hTz z).mp hz0) ((hTz z').mp hz0') (S v') (S w')
    have hr := clm_rpow_le hμ0 S z z'
    have hv0 := norm_nonneg v'
    have hw0' := norm_nonneg w'
    have hp : 0 ≤ ‖z - z'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    have hp' : 0 ≤ ‖S z - S z'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) _
    have hF0 : 0 ≤ (1 / lam) := by positivity
    have hF1 : 0 ≤ (1 / lam) ^ (1 / 2 : ℝ) := by positivity
    refine ⟨?_, ?_, ?_⟩
    · have := chg_le (X := |v (S z) - v (S z')|) (F := 1 / lam) (b := nS ^ μ)
        (G' := ‖z - z'‖ ^ μ)
        (by simpa [mul_assoc] using t0) hCt hF0 hp' hNtN hr (by positivity) hN0 hp
        (hab (nS ^ μ) hpS hS3) hpS
      simpa [mul_assoc] using this
    · have hG : ‖S z - S z'‖ ^ μ * ‖S v'‖ ≤ (nS ^ μ * nS) * (‖z - z'‖ ^ μ * ‖v'‖) := by
        have := mul_le_mul hr (hSv v') (norm_nonneg _) (by positivity)
        linarith [this]
      have := chg_le (X := |v1 (S z) (S v') - v1 (S z') (S v')|) (F := (1 / lam) ^ (1 / 2 : ℝ))
        (G := ‖S z - S z'‖ ^ μ * ‖S v'‖) (b := nS ^ μ * nS) (G' := ‖z - z'‖ ^ μ * ‖v'‖)
        (by simpa [mul_assoc] using t1) hCt hF1 (by positivity) hNtN hG (by positivity) hN0
        (by positivity) (hab (nS ^ μ * nS) (by positivity) hS4) (by positivity)
      simpa [mul_assoc] using this
    · have hSS : ‖S v'‖ * ‖S w'‖ ≤ (nS * nS) * (‖v'‖ * ‖w'‖) := by
        have := mul_le_mul (hSv v') (hSv w') (norm_nonneg _) (by positivity)
        linarith [this]
      have hG : ‖S z - S z'‖ ^ μ * (‖S v'‖ * ‖S w'‖) ≤
          (nS ^ μ * (nS * nS)) * (‖z - z'‖ ^ μ * (‖v'‖ * ‖w'‖)) := by
        have := mul_le_mul hr hSS (by positivity) (by positivity)
        linarith [this]
      have := chg_le (X := |v2 (S z) (S v') (S w') - v2 (S z') (S v') (S w')|) (F := 1)
        (G := ‖S z - S z'‖ ^ μ * (‖S v'‖ * ‖S w'‖)) (b := nS ^ μ * (nS * nS))
        (G' := ‖z - z'‖ ^ μ * (‖v'‖ * ‖w'‖))
        (by simpa [mul_assoc] using t2) hCt zero_le_one (by positivity) hNtN hG (by positivity) hN0
        (by positivity) (hab (nS ^ μ * (nS * nS)) (by positivity) hS5) (by positivity)
      rw [hu2, hu2]
      simpa [mul_assoc] using this

end VarA

end ObliqueLib

theorem solution (d : ℕ) (μ : ℝ) (hμ0 : 0 ≤ μ)
    (hV : ∀ e b : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 → inner ℝ b e = 0 → ∃ δ : ℝ, 0 < δ ∧ ∀ K : ℝ, 0 ≤ K →
  ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧ ∀ lam : ℝ, lam0 ≤ lam →
  ∀ (α : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ) (β : EuclideanSpace ℝ (Fin d) → Fin d → ℝ),
    (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∑ i, ∑ j, |α x i j| ≤ δ) →
    (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, ∑ j, |α x i j - α x' i j| ≤ K * ‖x - x'‖ ^ μ) →
    (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∑ i, |β x i| ≤ K) →
    (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, |β x i - β x' i| ≤ K * ‖x - x'‖ ^ μ) →
    ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ y : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → |g y| ≤ M) →
    (∀ y z : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → 0 ≤ inner ℝ z e → |g y - g z| ≤ H * ‖y - z‖ ^ μ) →
    ∃ (u : EuclideanSpace ℝ (Fin d) → ℝ) (u1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (u2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      (∀ x : EuclideanSpace ℝ (Fin d), 0 < inner ℝ x e → HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e →
        lam * u x - (1 / 2 : ℝ) * ∑ i, u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
          - ∑ i, ∑ j, α x i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - ∑ i, β x i * u1 x (EuclideanSpace.single i 1) = g x) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), inner ℝ x e = 0 → u1 x (b - e) = 0) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∀ v w : EuclideanSpace ℝ (Fin d),
        |u x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        |u1 x v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ ∧
        |u2 x v w| ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ * ‖w‖) ∧
      (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e → ∀ v w : EuclideanSpace ℝ (Fin d),
        |u x - u x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        |u1 x v - u1 x' v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ ∧
        |u2 x v w - u2 x' v w| ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ * ‖w‖)) :
    ∀ A0 : Matrix (Fin d) (Fin d) ℝ, A0.PosDef →
  ∀ e b : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 → inner ℝ b e = 0 → ∃ δ : ℝ, 0 < δ ∧ ∀ K : ℝ, 0 ≤ K →
  ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧ ∀ lam : ℝ, lam0 ≤ lam →
  ∀ (α : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ) (β : EuclideanSpace ℝ (Fin d) → Fin d → ℝ),
    (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∑ i, ∑ j, |α x i j| ≤ δ) →
    (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, ∑ j, |α x i j - α x' i j| ≤ K * ‖x - x'‖ ^ μ) →
    (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∑ i, |β x i| ≤ K) →
    (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, |β x i - β x' i| ≤ K * ‖x - x'‖ ^ μ) →
    ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ y : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → |g y| ≤ M) →
    (∀ y z : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → 0 ≤ inner ℝ z e → |g y - g z| ≤ H * ‖y - z‖ ^ μ) →
    ∃ (u : EuclideanSpace ℝ (Fin d) → ℝ) (u1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (u2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      (∀ x : EuclideanSpace ℝ (Fin d), 0 < inner ℝ x e → HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e →
        lam * u x - (1 / 2 : ℝ) * ∑ i, ∑ j, A0 i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - ∑ i, ∑ j, α x i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - ∑ i, β x i * u1 x (EuclideanSpace.single i 1) = g x) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), inner ℝ x e = 0 → u1 x (b - e) = 0) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∀ v w : EuclideanSpace ℝ (Fin d),
        |u x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        |u1 x v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ ∧
        |u2 x v w| ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ * ‖w‖) ∧
      (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e → ∀ v w : EuclideanSpace ℝ (Fin d),
        |u x - u x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        |u1 x v - u1 x' v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ ∧
        |u2 x v w - u2 x' v w| ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ * ‖w‖) := by
  exact ObliqueLib.varModelA hμ0 hV
