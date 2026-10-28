-- Prove2me | solution 1 for EthierKurtz.oblique_local_corrector
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T05:35:32.367121+00:00
-- url     : https://prove2.me/submissions/cc777dee-06cb-4960-a980-9ad6c048c9f0

import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_CTwiceHolder

set_option autoImplicit false

/-! C2e Hoelder calculus on a set: bounded and `μ`-Hoelder on `S`. -/

namespace Pd67abb68C2h

/-- bounded and `μ`-Hoelder on `S` -/
def HBon {X F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup F] (μ : ℝ) (S : Set X)
    (f : X → F) : Prop :=
  ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ (∀ p ∈ S, ‖f p‖ ≤ B) ∧
    ∀ p ∈ S, ∀ p' ∈ S, ‖f p - f p'‖ ≤ K * ‖p - p'‖ ^ μ

variable {X Y F G H : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedAddCommGroup H]
  {μ : ℝ} {S T : Set X}

lemma HBon.mono {f : X → F} (hf : HBon μ S f) (h : T ⊆ S) : HBon μ T f := by
  obtain ⟨B, K, hB, hK, h1, h2⟩ := hf
  exact ⟨B, K, hB, hK, fun p hp => h1 p (h hp), fun p hp p' hp' => h2 p (h hp) p' (h hp')⟩

lemma HBon.congr {f g : X → F} (hf : HBon μ S f) (h : ∀ p ∈ S, f p = g p) : HBon μ S g := by
  obtain ⟨B, K, hB, hK, h1, h2⟩ := hf
  refine ⟨B, K, hB, hK, fun p hp => ?_, fun p hp p' hp' => ?_⟩
  · rw [← h p hp]; exact h1 p hp
  · rw [← h p hp, ← h p' hp']; exact h2 p hp p' hp'

lemma HBon.const (c : F) : HBon μ S (fun _ : X => c) :=
  ⟨‖c‖, 0, norm_nonneg _, le_rfl, fun _ _ => le_rfl, fun p _ p' _ => by simp⟩

lemma HBon.add {f g : X → F} (hf : HBon μ S f) (hg : HBon μ S g) :
    HBon μ S (fun p => f p + g p) := by
  obtain ⟨B1, K1, hB1, hK1, hf1, hf2⟩ := hf
  obtain ⟨B2, K2, hB2, hK2, hg1, hg2⟩ := hg
  refine ⟨B1 + B2, K1 + K2, by positivity, by positivity, fun p hp => ?_, fun p hp p' hp' => ?_⟩
  · exact (norm_add_le _ _).trans (add_le_add (hf1 p hp) (hg1 p hp))
  · calc ‖f p + g p - (f p' + g p')‖ = ‖(f p - f p') + (g p - g p')‖ := by congr 1; abel
      _ ≤ ‖f p - f p'‖ + ‖g p - g p'‖ := norm_add_le _ _
      _ ≤ K1 * ‖p - p'‖ ^ μ + K2 * ‖p - p'‖ ^ μ := add_le_add (hf2 p hp p' hp') (hg2 p hp p' hp')
      _ = _ := by ring

lemma HBon.neg {f : X → F} (hf : HBon μ S f) : HBon μ S (fun p => -f p) := by
  obtain ⟨B, K, hB, hK, h1, h2⟩ := hf
  refine ⟨B, K, hB, hK, fun p hp => by rw [norm_neg]; exact h1 p hp, fun p hp p' hp' => ?_⟩
  have e : -f p - -f p' = -(f p - f p') := by abel
  rw [e, norm_neg]; exact h2 p hp p' hp'

lemma HBon.sub {f g : X → F} (hf : HBon μ S f) (hg : HBon μ S g) :
    HBon μ S (fun p => f p - g p) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- the general product rule: through a bounded bilinear map -/
lemma HBon.bilin [NormedSpace ℝ F] [NormedSpace ℝ G] [NormedSpace ℝ H]
    (β : F →L[ℝ] G →L[ℝ] H) {f : X → F} {g : X → G} (hf : HBon μ S f) (hg : HBon μ S g) :
    HBon μ S (fun p => β (f p) (g p)) := by
  obtain ⟨B1, K1, hB1, hK1, hf1, hf2⟩ := hf
  obtain ⟨B2, K2, hB2, hK2, hg1, hg2⟩ := hg
  have hβ := norm_nonneg β
  refine ⟨‖β‖ * B1 * B2, ‖β‖ * (K1 * B2 + B1 * K2), by positivity, by positivity,
    fun p hp => ?_, fun p hp p' hp' => ?_⟩
  · calc ‖β (f p) (g p)‖ ≤ ‖β‖ * ‖f p‖ * ‖g p‖ := β.le_opNorm₂ _ _
      _ ≤ ‖β‖ * B1 * B2 := by
          have := hf1 p hp; have := hg1 p hp
          have : 0 ≤ ‖f p‖ := norm_nonneg _
          gcongr
  · have hr : 0 ≤ ‖p - p'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) μ
    have he : β (f p) (g p) - β (f p') (g p') = β (f p - f p') (g p) + β (f p') (g p - g p') := by
      simp [map_sub]
    rw [he]
    have e1 := β.le_opNorm₂ (f p - f p') (g p)
    have e2 := β.le_opNorm₂ (f p') (g p - g p')
    have a1 := hf2 p hp p' hp'; have a2 := hg1 p hp; have a3 := hf1 p' hp'; have a4 := hg2 p hp p' hp'
    have n1 : 0 ≤ ‖f p - f p'‖ := norm_nonneg _
    have n2 : 0 ≤ ‖g p - g p'‖ := norm_nonneg _
    have n3 : 0 ≤ ‖f p'‖ := norm_nonneg _
    have n4 : 0 ≤ ‖g p‖ := norm_nonneg _
    calc _ ≤ ‖β (f p - f p') (g p)‖ + ‖β (f p') (g p - g p')‖ := norm_add_le _ _
      _ ≤ ‖β‖ * ‖f p - f p'‖ * ‖g p‖ + ‖β‖ * ‖f p'‖ * ‖g p - g p'‖ := add_le_add e1 e2
      _ ≤ ‖β‖ * (K1 * ‖p - p'‖ ^ μ) * B2 + ‖β‖ * B1 * (K2 * ‖p - p'‖ ^ μ) := by gcongr
      _ = _ := by ring

/-- linear image -/
lemma HBon.clm [NormedSpace ℝ F] [NormedSpace ℝ G] (L : F →L[ℝ] G) {f : X → F}
    (hf : HBon μ S f) : HBon μ S (fun p => L (f p)) := by
  obtain ⟨B, K, hB, hK, h1, h2⟩ := hf
  have hL := norm_nonneg L
  refine ⟨‖L‖ * B, ‖L‖ * K, by positivity, by positivity, fun p hp => ?_, fun p hp p' hp' => ?_⟩
  · exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h1 p hp) hL)
  · rw [← map_sub]
    calc _ ≤ ‖L‖ * ‖f p - f p'‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (K * ‖p - p'‖ ^ μ) := mul_le_mul_of_nonneg_left (h2 p hp p' hp') hL
      _ = _ := by ring

/-- composition with a Lipschitz map -/
lemma HBon.comp {f : Y → F} {T' : Set Y} (hf : HBon μ T' f) (hμ : 0 ≤ μ) (φ : X → Y)
    (hφ : Set.MapsTo φ S T') (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ p ∈ S, ∀ p' ∈ S, ‖φ p - φ p'‖ ≤ L * ‖p - p'‖) :
    HBon μ S (fun p => f (φ p)) := by
  obtain ⟨B, K, hB, hK, h1, h2⟩ := hf
  refine ⟨B, K * L ^ μ, hB, by positivity, fun p hp => h1 _ (hφ hp), fun p hp p' hp' => ?_⟩
  calc ‖f (φ p) - f (φ p')‖ ≤ K * ‖φ p - φ p'‖ ^ μ := h2 _ (hφ hp) _ (hφ hp')
    _ ≤ K * (L * ‖p - p'‖) ^ μ := by
        gcongr; exact hL p hp p' hp'
    _ = _ := by rw [Real.mul_rpow hL0 (norm_nonneg _)]; ring

/-- bounded + Lipschitz on `S` gives Hoelder for `μ ≤ 1` -/
lemma HBon.of_lip (hμ : 0 < μ) (hμ1 : μ ≤ 1) (f : X → F) (B L : ℝ)
    (hB : ∀ p ∈ S, ‖f p‖ ≤ B) (hL : ∀ p ∈ S, ∀ p' ∈ S, ‖f p - f p'‖ ≤ L * ‖p - p'‖) :
    HBon μ S f := by
  refine ⟨max B 0, max L 0 + 2 * max B 0, le_max_right _ _, by positivity,
    fun p hp => (hB p hp).trans (le_max_left _ _), fun p hp p' hp' => ?_⟩
  have hB0 := le_max_right B 0
  have hL0 := le_max_right L 0
  have hr : 0 ≤ ‖p - p'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) μ
  rcases le_or_gt ‖p - p'‖ 1 with h | h
  · have h1 : ‖p - p'‖ ≤ ‖p - p'‖ ^ μ := Real.self_le_rpow_of_le_one (norm_nonneg _) h hμ1
    calc ‖f p - f p'‖ ≤ L * ‖p - p'‖ := hL p hp p' hp'
      _ ≤ max L 0 * ‖p - p'‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max L 0 * ‖p - p'‖ ^ μ := mul_le_mul_of_nonneg_left h1 hL0
      _ ≤ _ := by nlinarith
  · have h1 : 1 ≤ ‖p - p'‖ ^ μ := Real.one_le_rpow h.le hμ.le
    calc ‖f p - f p'‖ ≤ ‖f p‖ + ‖f p'‖ := norm_sub_le _ _
      _ ≤ 2 * max B 0 := by linarith [hB p hp, hB p' hp', le_max_left B 0]
      _ ≤ _ := by nlinarith

/-- Lipschitz on a convex set from a derivative bound -/
lemma lip_of_fderiv_bound [NormedSpace ℝ X] [NormedSpace ℝ F] {f : X → F} {C : ℝ}
    (hS : Convex ℝ S) (hd : ∀ p ∈ S, DifferentiableAt ℝ f p) (hC : ∀ p ∈ S, ‖fderiv ℝ f p‖ ≤ C) :
    ∀ p ∈ S, ∀ p' ∈ S, ‖f p - f p'‖ ≤ C * ‖p - p'‖ := fun p hp p' hp' =>
  hS.norm_image_sub_le_of_norm_fderiv_le hd hC hp' hp

/-- a `C^1` function on an open convex set with bounded derivative and bounded values is Hoelder -/
lemma HBon.of_fderiv [NormedSpace ℝ X] [NormedSpace ℝ F] (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    {f : X → F} {B C : ℝ} (hS : Convex ℝ S) (hd : ∀ p ∈ S, DifferentiableAt ℝ f p)
    (hB : ∀ p ∈ S, ‖f p‖ ≤ B) (hC : ∀ p ∈ S, ‖fderiv ℝ f p‖ ≤ C) : HBon μ S f :=
  HBon.of_lip hμ hμ1 f B C hB (lip_of_fderiv_bound hS hd hC)

lemma eq_zero_of_not_mem_tsupport' {X' F' : Type*} [TopologicalSpace X'] [Zero F'] {f : X' → F'} {p : X'} (hp : p ∉ tsupport f) : f p = 0 := by
  by_contra h; exact hp (subset_tsupport _ (Function.mem_support.mpr h))

set_option synthInstance.maxHeartbeats 400000 in
/-- side bounds: a `C^1` compactly supported function, `C^2` on an open convex unbounded set `S`
with `D^2` Hoelder there, is `HBon` on `S` together with its first two derivatives. -/
lemma side_bounds [NormedSpace ℝ X] (hμ : 0 < μ) (hμ1 : μ ≤ 1) (V : X → ℝ)
    (hSo : IsOpen S) (hSc : Convex ℝ S) (hfar : ∀ R : ℝ, ∃ p ∈ S, R < ‖p‖)
    (hV : ContDiff ℝ 1 V) (hVs : HasCompactSupport V) (hV2 : ContDiffOn ℝ 2 V S) (K : ℝ)
    (hK : ∀ p ∈ S, ∀ p' ∈ S,
      ‖fderiv ℝ (fderiv ℝ V) p - fderiv ℝ (fderiv ℝ V) p'‖ ≤ K * ‖p - p'‖ ^ μ) :
    HBon μ S V ∧ HBon μ S (fderiv ℝ V) ∧ HBon μ S (fderiv ℝ (fderiv ℝ V)) := by
  have hd : Differentiable ℝ V := hV.differentiable one_ne_zero
  have hs1 : HasCompactSupport (fderiv ℝ V) := hVs.fderiv (𝕜 := ℝ)
  have hs2 : HasCompactSupport (fderiv ℝ (fderiv ℝ V)) := hs1.fderiv (𝕜 := ℝ)
  have hdd : ∀ p ∈ S, DifferentiableAt ℝ (fderiv ℝ V) p := fun p hp => by
    have h3 : ContDiffAt ℝ 2 V p := hV2.contDiffAt (hSo.mem_nhds hp)
    exact (h3.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  -- bound on D^2 over S
  obtain ⟨R, hR⟩ := hs2.isCompact.isBounded.subset_closedBall 0
  obtain ⟨p', hp'S, hp'R⟩ := hfar (max R 0)
  have hp'0 : fderiv ℝ (fderiv ℝ V) p' = 0 := by
    apply eq_zero_of_not_mem_tsupport'
    intro h; have := hR h; rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith [le_max_left R 0]
  have hB2 : ∀ p ∈ S, ‖fderiv ℝ (fderiv ℝ V) p‖ ≤ max K 0 * (max R 0 + ‖p'‖) ^ μ := by
    intro p hp
    by_cases hpt : p ∈ tsupport (fderiv ℝ (fderiv ℝ V))
    · have h1 := hR hpt; rw [Metric.mem_closedBall, dist_zero_right] at h1
      have h2 := hK p hp p' hp'S
      rw [hp'0, sub_zero] at h2
      refine h2.trans ?_
      have : ‖p - p'‖ ≤ max R 0 + ‖p'‖ :=
        (norm_sub_le _ _).trans (by linarith [le_max_left R 0])
      have h0 : 0 ≤ ‖p - p'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) μ
      calc K * ‖p - p'‖ ^ μ ≤ max K 0 * ‖p - p'‖ ^ μ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) h0
        _ ≤ _ := by gcongr
    · rw [eq_zero_of_not_mem_tsupport' hpt, ContinuousLinearMap.opNorm_zero]
      have : 0 ≤ max R 0 + ‖p'‖ := by positivity
      exact mul_nonneg (le_max_right _ _) (Real.rpow_nonneg this μ)
  obtain ⟨C1, hC1⟩ := hs1.exists_bound_of_continuous (hV.continuous_fderiv one_ne_zero)
  obtain ⟨C0, hC0⟩ := hVs.exists_bound_of_continuous hV.continuous
  refine ⟨HBon.of_fderiv hμ hμ1 hSc (fun p _ => hd p) (fun p _ => hC0 p) (fun p _ => hC1 p),
    HBon.of_fderiv hμ hμ1 hSc hdd (fun p _ => hC1 p) hB2, ?_⟩
  refine ⟨max K 0 * (max R 0 + ‖p'‖) ^ μ, max K 0, ?_, le_max_right _ _, hB2,
    fun p hp q hq => (hK p hp q hq).trans ?_⟩
  · exact mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by positivity) μ)
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) μ)

lemma convex_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Convex ℝ {p : E × ℝ | 0 < p.2} :=
  (convex_Ioi (0:ℝ)).linear_preimage (LinearMap.snd ℝ E ℝ)

lemma convex_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Convex ℝ {p : E × ℝ | p.2 < 0} :=
  (convex_Iio (0:ℝ)).linear_preimage (LinearMap.snd ℝ E ℝ)

lemma far_pos {E : Type*} [NormedAddCommGroup E] (R : ℝ) :
    ∃ p ∈ {p : E × ℝ | 0 < p.2}, R < ‖p‖ :=
  ⟨(0, |R| + 1), by simp only [Set.mem_setOf_eq]; positivity, by
    rw [Prod.norm_def]; simp only [norm_zero, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity : (0:ℝ) < |R| + 1)]
    exact (le_abs_self R).trans_lt (by simp)⟩

lemma far_neg {E : Type*} [NormedAddCommGroup E] (R : ℝ) :
    ∃ p ∈ {p : E × ℝ | p.2 < 0}, R < ‖p‖ :=
  ⟨(0, -(|R| + 1)), by simp only [Set.mem_setOf_eq]; linarith [abs_nonneg R], by
    rw [Prod.norm_def]; simp only [norm_zero, Real.norm_eq_abs, abs_neg]
    rw [abs_of_pos (by positivity : (0:ℝ) < |R| + 1)]
    exact (le_abs_self R).trans_lt (by simp)⟩


/-! ### evaluated second derivatives (avoids iterated-CLM instance unification, see pitfalls) -/

lemma HBon.mul {f g : X → ℝ} (hf : HBon μ S f) (hg : HBon μ S g) :
    HBon μ S (fun p => f p * g p) := by
  have := HBon.bilin (ContinuousLinearMap.mul ℝ ℝ) hf hg
  simpa using this

lemma HBon.eval [NormedSpace ℝ Y] [NormedSpace ℝ F] {A : X → (Y →L[ℝ] F)} {a : X → Y}
    (hA : HBon μ S A) (ha : HBon μ S a) : HBon μ S (fun p => A p (a p)) := by
  obtain ⟨B1, K1, hB1, hK1, hf1, hf2⟩ := hA
  obtain ⟨B2, K2, hB2, hK2, hg1, hg2⟩ := ha
  refine ⟨B1 * B2, K1 * B2 + B1 * K2, by positivity, by positivity, fun p hp => ?_, fun p hp p' hp' => ?_⟩
  · calc ‖A p (a p)‖ ≤ ‖A p‖ * ‖a p‖ := (A p).le_opNorm _
      _ ≤ B1 * B2 := mul_le_mul (hf1 p hp) (hg1 p hp) (norm_nonneg _) hB1
  · have hr : 0 ≤ ‖p - p'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) μ
    have he : A p (a p) - A p' (a p') = (A p - A p') (a p) + A p' (a p - a p') := by
      simp [map_sub]
    rw [he]
    calc _ ≤ ‖(A p - A p') (a p)‖ + ‖A p' (a p - a p')‖ := norm_add_le _ _
      _ ≤ ‖A p - A p'‖ * ‖a p‖ + ‖A p'‖ * ‖a p - a p'‖ :=
          add_le_add ((A p - A p').le_opNorm _) ((A p').le_opNorm _)
      _ ≤ (K1 * ‖p - p'‖ ^ μ) * B2 + B1 * (K2 * ‖p - p'‖ ^ μ) :=
          add_le_add (mul_le_mul (hf2 p hp p' hp') (hg1 p hp) (norm_nonneg _) (by positivity))
            (mul_le_mul (hf1 p' hp') (hg2 p hp p' hp') (norm_nonneg _) hB1)
      _ = _ := by ring

lemma HBon.sum {ι : Type*} (s : Finset ι) {f : ι → X → F} (hf : ∀ i ∈ s, HBon μ S (f i)) :
    HBon μ S (fun p => ∑ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (HBon.const (μ := μ) (S := S) (0 : F))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- second partial of `ξ * (g ∘ Φ)` in evaluated form -/
lemma partial2_formula [NormedSpace ℝ X] [NormedSpace ℝ Y] (ξ : X → ℝ) (g : Y → ℝ) (Φ : X → Y)
    (x : X) (hξ : ContDiff ℝ 2 ξ) (hg : ContDiffAt ℝ 2 g (Φ x)) (hΦ : ContDiffAt ℝ 2 Φ x)
    (v w : X) :
    fderiv ℝ (fun y => fderiv ℝ (fun y => ξ y * g (Φ y)) y w) x v =
      ξ x * (fderiv ℝ (fderiv ℝ g) (Φ x) (fderiv ℝ Φ x v) (fderiv ℝ Φ x w) +
        fderiv ℝ g (Φ x) (fderiv ℝ (fderiv ℝ Φ) x v w)) +
      fderiv ℝ ξ x v * fderiv ℝ g (Φ x) (fderiv ℝ Φ x w) +
      fderiv ℝ ξ x w * fderiv ℝ g (Φ x) (fderiv ℝ Φ x v) +
      g (Φ x) * fderiv ℝ (fderiv ℝ ξ) x v w := by
  have two : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hΦev : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 Φ y := hΦ.eventually (by simp)
  have hgev : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 g (Φ y) :=
    hΦ.continuousAt.eventually (hg.eventually (by simp))
  -- first derivative near x
  have hev : (fun y => fderiv ℝ (fun y => ξ y * g (Φ y)) y w) =ᶠ[nhds x]
      fun y => ξ y * fderiv ℝ g (Φ y) (fderiv ℝ Φ y w) + fderiv ℝ ξ y w * g (Φ y) := by
    filter_upwards [hΦev, hgev] with y hy1 hy2
    have d1 : HasFDerivAt (fun y => g (Φ y)) ((fderiv ℝ g (Φ y)).comp (fderiv ℝ Φ y)) y :=
      (hy2.differentiableAt (by norm_num)).hasFDerivAt.comp y
        (hy1.differentiableAt (by norm_num)).hasFDerivAt
    have d2 := ((hξ.differentiable (by norm_num)) y).hasFDerivAt.mul d1
    have d2' : HasFDerivAt (fun y => ξ y * g (Φ y)) _ y := d2
    rw [d2'.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul]
    ring
  rw [hev.fderiv_eq]
  have hDΦ : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) x) x :=
    ((hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hDg : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) (Φ x)) (Φ x) :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hDξ : HasFDerivAt (fderiv ℝ ξ) (fderiv ℝ (fderiv ℝ ξ) x) x :=
    (((hξ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) x).hasFDerivAt
  have hΦ1 : HasFDerivAt Φ (fderiv ℝ Φ x) x := (hΦ.differentiableAt (by norm_num)).hasFDerivAt
  have hg1 : HasFDerivAt g (fderiv ℝ g (Φ x)) (Φ x) := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hξ1 : HasFDerivAt ξ (fderiv ℝ ξ x) x := ((hξ.differentiable (by norm_num)) x).hasFDerivAt
  have ha := hDg.comp x hΦ1
  have hb := hDΦ.clm_apply (hasFDerivAt_const w x)
  have hab := ha.clm_apply hb
  have hc := hDξ.clm_apply (hasFDerivAt_const w x)
  have hgΦ := hg1.comp x hΦ1
  have htot := (hξ1.mul hab).add (hc.mul hgΦ)
  have htot' : HasFDerivAt (fun y => ξ y * fderiv ℝ g (Φ y) (fderiv ℝ Φ y w) +
      fderiv ℝ ξ y w * g (Φ y)) _ x := htot
  rw [htot'.fderiv]
  simp only [Function.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, smul_eq_mul,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_zero, zero_add, map_zero]
  ring

end Pd67abb68C2h

/-! C2e2 composition: `ξ * (g ∘ Φ)` is `CTwiceHolder` on `Ω` when `Ω` avoids the flat interface. -/

namespace Pd67abb68C2g

open Pd67abb68C2h

lemma hbon_of_cpt {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) {f : X → F} (hf : ContDiff ℝ 1 f)
    (hs : HasCompactSupport f) : HBon μ Set.univ f := by
  obtain ⟨B, hB⟩ := hf.continuous.bounded_above_of_compact_support hs
  obtain ⟨C, hC⟩ := (hf.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hs.fderiv (𝕜 := ℝ))
  exact HBon.of_fderiv hμ hμ1 convex_univ (fun p _ => hf.differentiable one_ne_zero p)
    (fun p _ => hB p) (fun p _ => hC p)

section
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

set_option maxHeartbeats 1000000 in
lemma partial2_hbon {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) (ξ : X → ℝ) (hξ : ContDiff ℝ 3 ξ)
    (hξs : HasCompactSupport ξ) (g : Y → ℝ) (Φ : X → Y) (O : Set X) (hO : IsOpen O)
    (hΦ : ContDiffOn ℝ 2 Φ O) (P : Set Y) (hP : IsOpen P) (hg2 : ContDiffOn ℝ 2 g P)
    (hg0 : HBon μ P g) (hg1 : HBon μ P (fderiv ℝ g)) (hg2' : HBon μ P (fderiv ℝ (fderiv ℝ g)))
    (hΦ1 : ∀ v, HBon μ O (fun x => fderiv ℝ Φ x v))
    (hΦ2 : ∀ v w, HBon μ O (fun x => fderiv ℝ (fderiv ℝ Φ) x v w))
    (L : ℝ) (hL0 : 0 ≤ L) (hL : ∀ p ∈ O, ∀ p' ∈ O, ‖Φ p - Φ p'‖ ≤ L * ‖p - p'‖) (v w : X) :
    HBon μ (O ∩ Φ ⁻¹' P)
      (fun x => fderiv ℝ (fun y => fderiv ℝ (fun y => ξ y * g (Φ y)) y w) x v) := by
  have hmaps : Set.MapsTo Φ (O ∩ Φ ⁻¹' P) P := fun x hx => hx.2
  have hLS : ∀ p ∈ O ∩ Φ ⁻¹' P, ∀ p' ∈ O ∩ Φ ⁻¹' P, ‖Φ p - Φ p'‖ ≤ L * ‖p - p'‖ :=
    fun p hp p' hp' => hL p hp.1 p' hp'.1
  have cg0 : HBon μ (O ∩ Φ ⁻¹' P) (fun p => g (Φ p)) := hg0.comp hμ.le Φ hmaps L hL0 hLS
  have cg1 : HBon μ (O ∩ Φ ⁻¹' P) (fun p => fderiv ℝ g (Φ p)) := hg1.comp hμ.le Φ hmaps L hL0 hLS
  have cg2 : HBon μ (O ∩ Φ ⁻¹' P) (fun p => fderiv ℝ (fderiv ℝ g) (Φ p)) :=
    hg2'.comp hμ.le Φ hmaps L hL0 hLS
  have dv : HBon μ (O ∩ Φ ⁻¹' P) (fun x => fderiv ℝ Φ x v) := (hΦ1 v).mono Set.inter_subset_left
  have dw : HBon μ (O ∩ Φ ⁻¹' P) (fun x => fderiv ℝ Φ x w) := (hΦ1 w).mono Set.inter_subset_left
  have dvw : HBon μ (O ∩ Φ ⁻¹' P) (fun x => fderiv ℝ (fderiv ℝ Φ) x v w) :=
    (hΦ2 v w).mono Set.inter_subset_left
  have hsub : O ∩ Φ ⁻¹' P ⊆ Set.univ := Set.subset_univ _
  have hξ0 : HBon μ (O ∩ Φ ⁻¹' P) ξ :=
    (hbon_of_cpt hμ hμ1 (hξ.of_le (by norm_num)) hξs).mono hsub
  have hD1 : ContDiff ℝ 2 (fderiv ℝ ξ) := hξ.fderiv_right (m := 2) (by norm_num)
  have hD2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ ξ)) := hD1.fderiv_right (m := 1) (by norm_num)
  have hξ1' : HBon μ (O ∩ Φ ⁻¹' P) (fderiv ℝ ξ) :=
    (hbon_of_cpt hμ hμ1 (hD1.of_le (by norm_num)) (hξs.fderiv (𝕜 := ℝ))).mono hsub
  have hξ2' : HBon μ (O ∩ Φ ⁻¹' P) (fderiv ℝ (fderiv ℝ ξ)) :=
    (hbon_of_cpt hμ hμ1 hD2 ((hξs.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ))).mono hsub
  have hξv : HBon μ (O ∩ Φ ⁻¹' P) (fun x => fderiv ℝ ξ x v) := hξ1'.eval (HBon.const v)
  have hξw : HBon μ (O ∩ Φ ⁻¹' P) (fun x => fderiv ℝ ξ x w) := hξ1'.eval (HBon.const w)
  have hξvw : HBon μ (O ∩ Φ ⁻¹' P) (fun x => fderiv ℝ (fderiv ℝ ξ) x v w) :=
    (hξ2'.eval (HBon.const v)).eval (HBon.const w)
  have t1 : HBon μ (O ∩ Φ ⁻¹' P)
      (fun x => fderiv ℝ (fderiv ℝ g) (Φ x) (fderiv ℝ Φ x v) (fderiv ℝ Φ x w)) :=
    (cg2.eval dv).eval dw
  have t2 : HBon μ (O ∩ Φ ⁻¹' P) (fun x => fderiv ℝ g (Φ x) (fderiv ℝ (fderiv ℝ Φ) x v w)) :=
    cg1.eval dvw
  have t3 : HBon μ (O ∩ Φ ⁻¹' P) (fun x => fderiv ℝ g (Φ x) (fderiv ℝ Φ x w)) := cg1.eval dw
  have t4 : HBon μ (O ∩ Φ ⁻¹' P) (fun x => fderiv ℝ g (Φ x) (fderiv ℝ Φ x v)) := cg1.eval dv
  have key := (((hξ0.mul (t1.add t2)).add (hξv.mul t3)).add (hξw.mul t4)).add (cg0.mul hξvw)
  refine key.congr (fun x hx => ?_)
  exact (partial2_formula ξ g Φ x (hξ.of_le (by norm_num)) (hg2.contDiffAt (hP.mem_nhds hx.2))
    (hΦ.contDiffAt (hO.mem_nhds hx.1)) v w).symm

end

lemma componentHolder_of_sides {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d))) (μ : ℝ)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (f s : EuclideanSpace ℝ (Fin d) → ℝ) (hfc : ContinuousOn f Ω)
    (O K : Set (EuclideanSpace ℝ (Fin d))) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (h0 : ∀ x ∈ Ω, x ∉ K → f x = 0) (hs : ContinuousOn s O) (hsΩ : ∀ x ∈ Ω ∩ O, s x ≠ 0)
    (hpos : HBon μ (O ∩ {x | 0 < s x}) f) (hneg : HBon μ (O ∩ {x | s x < 0}) f) :
    EthierKurtz.ComponentHolder Ω μ f := by
  obtain ⟨ε, hε, hεO⟩ := hK.exists_thickening_subset_open hO hKO
  obtain ⟨B1, K1, -, hK1, -, hp⟩ := hpos
  obtain ⟨B2, K2, -, hK2, -, hn⟩ := hneg
  refine ⟨hfc, ε / 2, 2 * (K1 + K2), by positivity, by positivity, ?_⟩
  intro ρ hρ hρε x z _ y hy w hw
  have hCsub : connectedComponentIn (Ω ∩ Metric.ball x ρ) z ⊆ Ω ∩ Metric.ball x ρ :=
    connectedComponentIn_subset _ _
  have hρμ : (0:ℝ) ≤ ρ ^ μ := Real.rpow_nonneg hρ.le μ
  by_cases hCK : ∃ p ∈ connectedComponentIn (Ω ∩ Metric.ball x ρ) z, p ∈ K
  · obtain ⟨p, hpC, hpK⟩ := hCK
    have hCO : connectedComponentIn (Ω ∩ Metric.ball x ρ) z ⊆ O := by
      intro c hc
      apply hεO
      rw [Metric.mem_thickening_iff]
      refine ⟨p, hpK, ?_⟩
      have h1 := (hCsub hc).2
      have h2 := (hCsub hpC).2
      rw [Metric.mem_ball] at h1 h2
      calc dist c p ≤ dist c x + dist p x := dist_triangle_right _ _ _
        _ < ρ + ρ := add_lt_add h1 h2
        _ ≤ ε := by linarith
    have hyw : ‖y - w‖ ≤ 2 * ρ := by
      have h1 := (hCsub hy).2
      have h2 := (hCsub hw).2
      rw [Metric.mem_ball] at h1 h2
      rw [← dist_eq_norm]
      linarith [dist_triangle_right y w x]
    have hpow : ‖y - w‖ ^ μ ≤ 2 * ρ ^ μ := by
      calc ‖y - w‖ ^ μ ≤ (2 * ρ) ^ μ := Real.rpow_le_rpow (norm_nonneg _) hyw hμ.le
        _ = 2 ^ μ * ρ ^ μ := Real.mul_rpow (by norm_num) hρ.le
        _ ≤ 2 * ρ ^ μ := by
            apply mul_le_mul_of_nonneg_right _ hρμ
            calc (2:ℝ) ^ μ ≤ 2 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hμ1
              _ = 2 := Real.rpow_one 2
    have hpre : IsPreconnected (s '' connectedComponentIn (Ω ∩ Metric.ball x ρ) z) :=
      isPreconnected_connectedComponentIn.image s (hs.mono hCO)
    have hne : ∀ c ∈ connectedComponentIn (Ω ∩ Metric.ball x ρ) z, s c ≠ 0 :=
      fun c hc => hsΩ c ⟨(hCsub hc).1, hCO hc⟩
    have side : ∀ a ∈ connectedComponentIn (Ω ∩ Metric.ball x ρ) z,
        ∀ b ∈ connectedComponentIn (Ω ∩ Metric.ball x ρ) z, 0 < s a → ¬ s b < 0 := by
      intro a ha b hb ha' hb'
      obtain ⟨c, hc, hc0⟩ := hpre.Icc_subset (Set.mem_image_of_mem s hb)
        (Set.mem_image_of_mem s ha) (show (0:ℝ) ∈ Set.Icc (s b) (s a) from ⟨hb'.le, ha'.le⟩)
      exact hne c hc hc0
    rcases (hne y hy).lt_or_gt with hy' | hy'
    · have hw' : s w < 0 := by
        rcases (hne w hw).lt_or_gt with h | h
        · exact h
        · exact absurd hy' (side w hw y hy h)
      have := hn y ⟨hCO hy, hy'⟩ w ⟨hCO hw, hw'⟩
      rw [Real.norm_eq_abs] at this
      calc |f y - f w| ≤ K2 * ‖y - w‖ ^ μ := this
        _ ≤ K2 * (2 * ρ ^ μ) := mul_le_mul_of_nonneg_left hpow hK2
        _ ≤ _ := by nlinarith
    · have hw' : 0 < s w := by
        rcases (hne w hw).lt_or_gt with h | h
        · exact absurd h (side y hy w hw hy')
        · exact h
      have := hp y ⟨hCO hy, hy'⟩ w ⟨hCO hw, hw'⟩
      rw [Real.norm_eq_abs] at this
      calc |f y - f w| ≤ K1 * ‖y - w‖ ^ μ := this
        _ ≤ K1 * (2 * ρ ^ μ) := mul_le_mul_of_nonneg_left hpow hK1
        _ ≤ _ := by nlinarith
  · push Not at hCK
    rw [h0 y (hCsub hy).1 (hCK y hy), h0 w (hCsub hw).1 (hCK w hw)]
    simp only [sub_self, abs_zero]
    positivity

lemma ctwice_of_chart {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (ξ : EuclideanSpace ℝ (Fin d) → ℝ) (hξ : ContDiff ℝ 3 ξ) (hξs : HasCompactSupport ξ)
    (g : E × ℝ → ℝ) (hg2 : ContDiffOn ℝ 2 g {p | p.2 ≠ 0})
    (hgp : HBon μ {p : E × ℝ | 0 < p.2} g ∧ HBon μ {p : E × ℝ | 0 < p.2} (fderiv ℝ g) ∧
      HBon μ {p : E × ℝ | 0 < p.2} (fderiv ℝ (fderiv ℝ g)))
    (hgn : HBon μ {p : E × ℝ | p.2 < 0} g ∧ HBon μ {p : E × ℝ | p.2 < 0} (fderiv ℝ g) ∧
      HBon μ {p : E × ℝ | p.2 < 0} (fderiv ℝ (fderiv ℝ g)))
    (Φ : EuclideanSpace ℝ (Fin d) → E × ℝ) (O : Set (EuclideanSpace ℝ (Fin d))) (hO : IsOpen O)
    (hΦ : ContDiffOn ℝ 2 Φ O)
    (hΦ1 : ∀ v, HBon μ O (fun x => fderiv ℝ Φ x v))
    (hΦ2 : ∀ v w, HBon μ O (fun x => fderiv ℝ (fderiv ℝ Φ) x v w))
    (L : ℝ) (hL0 : 0 ≤ L) (hL : ∀ p ∈ O, ∀ p' ∈ O, ‖Φ p - Φ p'‖ ≤ L * ‖p - p'‖)
    (htO : tsupport ξ ⊆ O) (hside : ∀ x ∈ Ω ∩ O, (Φ x).2 ≠ 0) :
    EthierKurtz.CTwiceHolder Ω μ (fun x => ξ x * g (Φ x)) := by
  have hgo : IsOpen {p : E × ℝ | p.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
  have hzero : ∀ x, x ∉ tsupport ξ → (fun x => ξ x * g (Φ x)) =ᶠ[nhds x] fun _ => (0:ℝ) := by
    intro x hxK
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxK] with y hy
    simp [hy]
  have hat : ∀ x ∈ Ω, ContDiffAt ℝ 2 (fun x => ξ x * g (Φ x)) x := by
    intro x hx
    by_cases hxK : x ∈ tsupport ξ
    · have hxO := htO hxK
      have h1 : ContDiffAt ℝ 2 g (Φ x) := hg2.contDiffAt (hgo.mem_nhds (hside x ⟨hx, hxO⟩))
      have h2 : ContDiffAt ℝ 2 Φ x := hΦ.contDiffAt (hO.mem_nhds hxO)
      exact (hξ.of_le (by norm_num)).contDiffAt.mul (h1.comp x h2)
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero x hxK)
  refine ⟨fun x hx => (hat x hx).contDiffWithinAt, fun i j => ?_⟩
  refine componentHolder_of_sides Ω μ hμ hμ1 _ (fun x => (Φ x).2) ?_ O (tsupport ξ) hO
    hξs.isCompact htO ?_ (continuous_snd.comp_continuousOn hΦ.continuousOn) hside ?_ ?_
  · intro x hx
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ (fun x => ξ x * g (Φ x))) x :=
      (hat x hx).fderiv_right (m := 1) (by norm_num)
    have h2 : ContDiffAt ℝ 1
        (fun y => fderiv ℝ (fun x => ξ x * g (Φ x)) y (EuclideanSpace.single j 1)) x :=
      h1.clm_apply contDiffAt_const
    have h3 := (h2.fderiv_right (m := 0) (by norm_num)).continuousAt
    exact (h3.clm_apply continuousAt_const).continuousWithinAt
  · intro x _ hxK
    have hev2 : (fun y => fderiv ℝ (fun x => ξ x * g (Φ x)) y (EuclideanSpace.single j 1))
        =ᶠ[nhds x] fun _ => (0:ℝ) := by
      filter_upwards [(hzero x hxK).eventuallyEq_nhds] with y hy
      rw [hy.fderiv_eq]
      simp
    show fderiv ℝ _ x _ = 0
    rw [hev2.fderiv_eq]
    simp
  · exact partial2_hbon hμ hμ1 ξ hξ hξs g Φ O hO hΦ {p | 0 < p.2}
      (continuous_snd.isOpen_preimage _ isOpen_Ioi) (hg2.mono fun p hp => ne_of_gt hp)
      hgp.1 hgp.2.1 hgp.2.2 hΦ1 hΦ2 L hL0 hL _ _
  · exact partial2_hbon hμ hμ1 ξ hξ hξs g Φ O hO hΦ {p | p.2 < 0}
      (continuous_snd.isOpen_preimage _ isOpen_Iio) (hg2.mono fun p hp => ne_of_lt hp)
      hgn.1 hgn.2.1 hgn.2.2 hΦ1 hΦ2 L hL0 hL _ _

end Pd67abb68C2g

/-! C2e chart library: from `ComponentHolder` to `HBon` on balls, basis expansions. -/

namespace Pd67abb68C2j

open Pd67abb68C2h

/-- `ComponentHolder` on `D` gives bounded + Hoelder on any ball whose closure lies in `D`. -/
lemma hbon_of_componentHolder {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} {μ : ℝ}
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : EthierKurtz.ComponentHolder D μ f)
    {c : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : Metric.closedBall c r ⊆ D) :
    HBon μ (Metric.ball c r) f := by
  obtain ⟨hfc, ρ₀, M, hρ₀, hM, hH⟩ := hf
  obtain ⟨C, hC⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn (hfc.mono hr)
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hq : (0:ℝ) ≤ (2 / ρ₀) ^ μ := Real.rpow_nonneg (by positivity) μ
  refine ⟨max C 0, M * 2 + 2 * max C 0 * (2 / ρ₀) ^ μ, hC0, by positivity,
    fun p hp => (hC p (Metric.ball_subset_closedBall hp)).trans (le_max_left _ _), ?_⟩
  intro p hp p' hp'
  have hb : ∀ x ∈ Metric.ball c r, ‖f x‖ ≤ max C 0 :=
    fun x hx => (hC x (Metric.ball_subset_closedBall hx)).trans (le_max_left _ _)
  have hr0 : 0 ≤ ‖p - p'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) μ
  rcases eq_or_lt_of_le (norm_nonneg (p - p')) with h0 | hpos
  · have : p = p' := sub_eq_zero.mp (norm_eq_zero.mp h0.symm)
    subst this
    simp only [sub_self, norm_zero]
    positivity
  by_cases hsmall : ‖p - p'‖ ≤ ρ₀ / 2
  · have hρ : 0 < 2 * ‖p - p'‖ := by positivity
    have hmem : p' ∈ connectedComponentIn (D ∩ Metric.ball p (2 * ‖p - p'‖)) p := by
      have hseg : segment ℝ p p' ⊆ D ∩ Metric.ball p (2 * ‖p - p'‖) := by
        refine Set.subset_inter
          (((convex_ball c r).segment_subset hp hp').trans
            (Metric.ball_subset_closedBall.trans hr)) ?_
        refine (convex_ball p _).segment_subset (Metric.mem_ball_self hρ) ?_
        rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
        linarith
      exact (convex_segment p p').isPreconnected.subset_connectedComponentIn
        (left_mem_segment ℝ p p') hseg (right_mem_segment ℝ p p')
    have hpm : p ∈ D ∩ Metric.ball p (2 * ‖p - p'‖) :=
      ⟨hr (Metric.ball_subset_closedBall hp), Metric.mem_ball_self hρ⟩
    have := hH (2 * ‖p - p'‖) hρ (by linarith) p p hpm p (mem_connectedComponentIn hpm) p' hmem
    rw [Real.norm_eq_abs]
    have h2 : (2 * ‖p - p'‖) ^ μ ≤ 2 * ‖p - p'‖ ^ μ := by
      rw [Real.mul_rpow (by norm_num) (norm_nonneg _)]
      apply mul_le_mul_of_nonneg_right _ hr0
      calc (2:ℝ) ^ μ ≤ 2 ^ (1:ℝ) := by
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hμ1
        _ = 2 := Real.rpow_one 2
    have h3 : 0 ≤ 2 * max C 0 * (2 / ρ₀) ^ μ * ‖p - p'‖ ^ μ := by positivity
    calc |f p - f p'| ≤ M * (2 * ‖p - p'‖) ^ μ := this
      _ ≤ M * (2 * ‖p - p'‖ ^ μ) := mul_le_mul_of_nonneg_left h2 hM
      _ ≤ _ := by nlinarith
  · push Not at hsmall
    have h1 : 1 ≤ ((2 / ρ₀) * ‖p - p'‖) ^ μ := by
      apply Real.one_le_rpow _ hμ.le
      rw [div_mul_eq_mul_div, le_div_iff₀ hρ₀]
      linarith
    rw [Real.mul_rpow (by positivity) (norm_nonneg _)] at h1
    calc ‖f p - f p'‖ ≤ ‖f p‖ + ‖f p'‖ := norm_sub_le _ _
      _ ≤ 2 * max C 0 := by linarith [hb p hp, hb p' hp']
      _ ≤ 2 * max C 0 * ((2 / ρ₀) ^ μ * ‖p - p'‖ ^ μ) := by nlinarith
      _ ≤ _ := by nlinarith [mul_nonneg hM hr0]


section basis
variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma clm_expand (L : EuclideanSpace ℝ (Fin d) →L[ℝ] F) (a : EuclideanSpace ℝ (Fin d)) :
    L a = ∑ i, a i • L (EuclideanSpace.single i 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr a]
  simp [map_sum, map_smul]

lemma opNorm_le_sum_basis (L : EuclideanSpace ℝ (Fin d) →L[ℝ] F) :
    ‖L‖ ≤ ∑ i, ‖L (EuclideanSpace.single i 1)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun i _ => norm_nonneg _) fun a => ?_
  rw [clm_expand L a, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact PiLp.norm_apply_le a i

lemma hbon_clm_of_basis {X : Type*} [NormedAddCommGroup X] {μ : ℝ} {S : Set X}
    (L : X → (EuclideanSpace ℝ (Fin d) →L[ℝ] F))
    (h : ∀ i, HBon μ S (fun x => L x (EuclideanSpace.single i 1))) : HBon μ S L := by
  choose B K hB hK h1 h2 using h
  refine ⟨∑ i, B i, ∑ i, K i, Finset.sum_nonneg fun i _ => hB i,
    Finset.sum_nonneg fun i _ => hK i, fun p hp => ?_, fun p hp p' hp' => ?_⟩
  · exact (opNorm_le_sum_basis _).trans (Finset.sum_le_sum fun i _ => h1 i p hp)
  · refine (opNorm_le_sum_basis _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    simpa only [ContinuousLinearMap.sub_apply] using h2 i p hp p' hp'

end basis


section ufacts
variable {d : ℕ}

lemma hess_eval_eq {u : EuclideanSpace ℝ (Fin d) → ℝ} {z : EuclideanSpace ℝ (Fin d)}
    (h : DifferentiableAt ℝ (fderiv ℝ u) z) (a b : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun y => fderiv ℝ u y b) z a = fderiv ℝ (fderiv ℝ u) z a b := by
  have h' : HasFDerivAt (fun y => fderiv ℝ u y b) _ z :=
    h.hasFDerivAt.clm_apply (hasFDerivAt_const b z)
  rw [h'.fderiv]
  simp

lemma lip_of_basis {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : EuclideanSpace ℝ (Fin d) → F} {S : Set (EuclideanSpace ℝ (Fin d))} (hS : Convex ℝ S)
    (hd : ∀ p ∈ S, DifferentiableAt ℝ f p)
    (hb : ∀ i, ∃ B, ∀ p ∈ S, ‖fderiv ℝ f p (EuclideanSpace.single i 1)‖ ≤ B) :
    ∃ L, 0 ≤ L ∧ ∀ p ∈ S, ∀ p' ∈ S, ‖f p - f p'‖ ≤ L * ‖p - p'‖ := by
  choose B hB using hb
  exact ⟨∑ i, max (B i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _,
    lip_of_fderiv_bound hS hd fun p hp => (opNorm_le_sum_basis _).trans
      (Finset.sum_le_sum fun i _ => (hB i p hp).trans (le_max_left _ _))⟩

variable {D : Set (EuclideanSpace ℝ (Fin d))} {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
  {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : EthierKurtz.CTwiceHolder D μ u) (hD : IsOpen D)
  {c : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : Metric.closedBall c r ⊆ D)
include hμ hμ1 hu hD hr

lemma u_hess_hbon (a b : EuclideanSpace ℝ (Fin d)) :
    HBon μ (Metric.ball c r) (fun z => fderiv ℝ (fderiv ℝ u) z a b) := by
  have hH : ∀ i j, HBon μ (Metric.ball c r) (fun z => fderiv ℝ (fun y => fderiv ℝ u y
      (EuclideanSpace.single j 1)) z (EuclideanSpace.single i 1)) :=
    fun i j => hbon_of_componentHolder hμ hμ1 (hu.2 i j) hr
  have hdiff : ∀ z ∈ D, DifferentiableAt ℝ (fderiv ℝ u) z := fun z hz =>
    ((hu.1.contDiffAt (hD.mem_nhds hz)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      one_ne_zero
  have key : HBon μ (Metric.ball c r) (fun z => ∑ i, a i * ∑ j, b j *
      fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) z
        (EuclideanSpace.single i 1)) :=
    HBon.sum _ fun i _ => (HBon.const (a i)).mul
      (HBon.sum _ fun j _ => (HBon.const (b j)).mul (hH i j))
  refine key.congr fun z hz => ?_
  have hzD := hr (Metric.ball_subset_closedBall hz)
  simp only [hess_eval_eq (hdiff z hzD)]
  symm
  rw [clm_expand (fderiv ℝ (fderiv ℝ u) z) a, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.smul_apply, clm_expand (fderiv ℝ (fderiv ℝ u) z
    (EuclideanSpace.single i 1)) b, smul_eq_mul]
  simp only [smul_eq_mul]

lemma u_d1_hbon : HBon μ (Metric.ball c r) (fderiv ℝ u) := by
  have hdiff : ∀ z ∈ D, DifferentiableAt ℝ (fderiv ℝ u) z := fun z hz =>
    ((hu.1.contDiffAt (hD.mem_nhds hz)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      one_ne_zero
  apply hbon_clm_of_basis
  intro k
  have hH : ∀ i, HBon μ (Metric.ball c r) (fun z => fderiv ℝ (fun y => fderiv ℝ u y
      (EuclideanSpace.single k 1)) z (EuclideanSpace.single i 1)) :=
    fun i => hbon_of_componentHolder hμ hμ1 (hu.2 i k) hr
  choose B K hB hK h1 h2 using hH
  have hcont : ContinuousOn (fun z => fderiv ℝ u z (EuclideanSpace.single k 1)) D :=
    (hu.1.continuousOn_fderiv_of_isOpen hD (by norm_num)).clm_apply continuousOn_const
  obtain ⟨C, hC⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn (hcont.mono hr)
  exact HBon.of_fderiv hμ hμ1 (convex_ball c r)
    (fun z hz => (hdiff z (hr (Metric.ball_subset_closedBall hz))).clm_apply
      (differentiableAt_const _))
    (fun z hz => hC z (Metric.ball_subset_closedBall hz))
    (fun z hz => (opNorm_le_sum_basis _).trans (Finset.sum_le_sum fun i _ => h1 i z hz))

end ufacts

end Pd67abb68C2j

/-! C2e flat chart `Φ y = (π U (y - x₀), last U (y - x₀) - u (π U (y - x₀)))`. -/

namespace Pd67abb68Ch

open Pd67abb68C2h Pd67abb68C2j

section chart
variable {n : ℕ}

/-- drop the last coordinate -/
noncomputable def projL (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun i => v (Fin.castSucc i))
      map_add' := fun v w => by ext i; simp
      map_smul' := fun a v => by ext i; simp }

lemma projL_apply (v : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    projL n v i = v (Fin.castSucc i) := rfl

/-- the last coordinate -/
noncomputable def lastL (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ :=
  EuclideanSpace.proj (Fin.last n)

lemma lastL_apply (v : EuclideanSpace ℝ (Fin (n + 1))) : lastL n v = v (Fin.last n) := rfl

lemma norm_projL_le (v : EuclideanSpace ℝ (Fin (n + 1))) : ‖projL n v‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_castSucc]
  simp only [projL_apply]
  exact le_add_of_nonneg_right (sq_nonneg _)

lemma recon (v : EuclideanSpace ℝ (Fin (n + 1))) :
    (WithLp.toLp 2 (Fin.lastCases (v (Fin.last n)) (fun i => v (Fin.castSucc i))) :
      EuclideanSpace ℝ (Fin (n + 1))) = v := by
  ext i
  induction i using Fin.lastCases <;> simp

lemma projL_mk (a : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    projL n (WithLp.toLp 2 (Fin.lastCases a (fun i => z i))) = z := by
  ext i
  simp [projL_apply]

lemma lastL_mk (a : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    lastL n (WithLp.toLp 2 (Fin.lastCases a (fun i => z i))) = a := by
  simp [lastL_apply]

/-- the flat chart -/
noncomputable def chartΦ (U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (y : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin n) × ℝ :=
  (projL n (U (y - x₀)), lastL n (U (y - x₀)) - u (projL n (U (y - x₀))))

variable (U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
  (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (u : EuclideanSpace ℝ (Fin n) → ℝ)

lemma chartΦ_of_graph (x : EuclideanSpace ℝ (Fin (n + 1))) (z : EuclideanSpace ℝ (Fin n))
    (h : U (x - x₀) = WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i))) :
    chartΦ U x₀ u x = (z, 0) := by
  simp only [chartΦ, h, projL_mk, lastL_mk, sub_self]

lemma graph_of_chartΦ (x : EuclideanSpace ℝ (Fin (n + 1))) (h : (chartΦ U x₀ u x).2 = 0) :
    U (x - x₀) = WithLp.toLp 2 (Fin.lastCases (u (chartΦ U x₀ u x).1)
      (fun i => (chartΦ U x₀ u x).1 i)) := by
  have h' : lastL n (U (x - x₀)) = u (projL n (U (x - x₀))) := sub_eq_zero.mp h
  simp only [chartΦ]
  rw [← h']
  exact (recon _).symm

/-- the linear part -/
noncomputable def chartM : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (projL n).comp U.toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def chartN : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ :=
  (lastL n).comp U.toContinuousLinearEquiv.toContinuousLinearMap

lemma chartM_apply (v : EuclideanSpace ℝ (Fin (n + 1))) : chartM U v = projL n (U v) := rfl
lemma chartN_apply (v : EuclideanSpace ℝ (Fin (n + 1))) : chartN U v = lastL n (U v) := rfl

lemma chartP_hasFDerivAt (y : EuclideanSpace ℝ (Fin (n + 1))) :
    HasFDerivAt (fun y => projL n (U (y - x₀))) (chartM U) y := by
  have h := (chartM U).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x₀)
  simpa [chartM_apply, Function.comp_def] using h

lemma chartQ_hasFDerivAt (y : EuclideanSpace ℝ (Fin (n + 1))) :
    HasFDerivAt (fun y => lastL n (U (y - x₀))) (chartN U) y := by
  have h := (chartN U).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x₀)
  simpa [chartN_apply, Function.comp_def] using h

lemma chartP_lip (y y' : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖projL n (U (y - x₀)) - projL n (U (y' - x₀))‖ ≤ 1 * ‖y - y'‖ := by
  rw [← map_sub, ← map_sub, one_mul]
  calc _ ≤ ‖U (y - x₀ - (y' - x₀))‖ := norm_projL_le _
    _ = ‖y - y'‖ := by rw [LinearIsometryEquiv.norm_map]; congr 1; abel

lemma chartΦ_hasFDerivAt (y : EuclideanSpace ℝ (Fin (n + 1)))
    (hy : DifferentiableAt ℝ u (projL n (U (y - x₀)))) :
    HasFDerivAt (chartΦ U x₀ u)
      ((chartM U).prod (chartN U - (fderiv ℝ u (projL n (U (y - x₀)))).comp (chartM U))) y := by
  have hP := chartP_hasFDerivAt U x₀ y
  have hQ := chartQ_hasFDerivAt U x₀ y
  have hu := hy.hasFDerivAt.comp y hP
  exact hP.prodMk (hQ.sub hu)

lemma fderiv_chartΦ_apply (y : EuclideanSpace ℝ (Fin (n + 1)))
    (hy : DifferentiableAt ℝ u (projL n (U (y - x₀)))) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    fderiv ℝ (chartΦ U x₀ u) y v =
      (chartM U v, chartN U v - fderiv ℝ u (projL n (U (y - x₀))) (chartM U v)) := by
  rw [(chartΦ_hasFDerivAt U x₀ u y hy).fderiv]
  simp

end chart


lemma HBon.prodMk {X F G : Type*} [NormedAddCommGroup X] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {μ : ℝ} {S : Set X} {f : X → F} {g : X → G}
    (hf : HBon μ S f) (hg : HBon μ S g) : HBon μ S (fun p => (f p, g p)) := by
  have := (hf.clm (ContinuousLinearMap.inl ℝ F G)).add (hg.clm (ContinuousLinearMap.inr ℝ F G))
  refine this.congr fun p _ => ?_
  simp

lemma fderiv2_eval_eq {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : EuclideanSpace ℝ (Fin d) → F} {y : EuclideanSpace ℝ (Fin d)}
    (h : DifferentiableAt ℝ (fderiv ℝ Φ) y) (v w : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun y => fderiv ℝ Φ y w) y v = fderiv ℝ (fderiv ℝ Φ) y v w := by
  have h' : HasFDerivAt (fun y => fderiv ℝ Φ y w) _ y :=
    h.hasFDerivAt.clm_apply (hasFDerivAt_const w y)
  rw [h'.fderiv]
  simp

section chart2
variable {n : ℕ}
  (U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
  (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (u : EuclideanSpace ℝ (Fin n) → ℝ)

lemma chartP_mem {r : ℝ} {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y ∈ Metric.ball x₀ r) :
    projL n (U (y - x₀)) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := by
  rw [Metric.mem_ball, dist_zero_right]
  calc _ ≤ ‖U (y - x₀)‖ := norm_projL_le _
    _ = ‖y - x₀‖ := LinearIsometryEquiv.norm_map _ _
    _ < r := by rw [← dist_eq_norm]; exact hy

lemma chartΦ_eq : chartΦ U x₀ u = fun y =>
    (projL n (U (y - x₀)), lastL n (U (y - x₀)) - u (projL n (U (y - x₀)))) := rfl

set_option maxHeartbeats 1000000 in
lemma chart_props {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) {D : Set (EuclideanSpace ℝ (Fin n))}
    (hu : EthierKurtz.CTwiceHolder D μ u) (hD : IsOpen D) {r : ℝ}
    (hr : Metric.closedBall 0 r ⊆ D) :
    ContDiffOn ℝ 2 (chartΦ U x₀ u) (Metric.ball x₀ r) ∧
    (∀ v, HBon μ (Metric.ball x₀ r) (fun x => fderiv ℝ (chartΦ U x₀ u) x v)) ∧
    (∀ v w, HBon μ (Metric.ball x₀ r) (fun x => fderiv ℝ (fderiv ℝ (chartΦ U x₀ u)) x v w)) ∧
    ∃ L, 0 ≤ L ∧ ∀ p ∈ Metric.ball x₀ r, ∀ p' ∈ Metric.ball x₀ r,
      ‖chartΦ U x₀ u p - chartΦ U x₀ u p'‖ ≤ L * ‖p - p'‖ := by
  have hPD : ∀ y ∈ Metric.ball x₀ r, projL n (U (y - x₀)) ∈ D := fun y hy =>
    hr (Metric.ball_subset_closedBall (chartP_mem U x₀ hy))
  have hPc : ContDiff ℝ 2 (fun y => projL n (U (y - x₀))) := by
    have : (fun y => projL n (U (y - x₀))) = fun y => chartM U (y - x₀) := rfl
    rw [this]; fun_prop
  have hQc : ContDiff ℝ 2 (fun y => lastL n (U (y - x₀))) := by
    have : (fun y => lastL n (U (y - x₀))) = fun y => chartN U (y - x₀) := rfl
    rw [this]; fun_prop
  have hcd : ContDiffOn ℝ 2 (chartΦ U x₀ u) (Metric.ball x₀ r) := by
    rw [chartΦ_eq]
    exact hPc.contDiffOn.prodMk (hQc.contDiffOn.sub (hu.1.comp hPc.contDiffOn hPD))
  have hud : ∀ y ∈ Metric.ball x₀ r, DifferentiableAt ℝ u (projL n (U (y - x₀))) :=
    fun y hy => (hu.1.contDiffAt (hD.mem_nhds (hPD y hy))).differentiableAt (by norm_num)
  have hmaps : Set.MapsTo (fun y => projL n (U (y - x₀))) (Metric.ball x₀ r)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) := fun y hy => chartP_mem U x₀ hy
  have hlip : ∀ p ∈ Metric.ball x₀ r, ∀ p' ∈ Metric.ball x₀ r,
      ‖projL n (U (p - x₀)) - projL n (U (p' - x₀))‖ ≤ 1 * ‖p - p'‖ :=
    fun p _ p' _ => chartP_lip U x₀ p p'
  have hD1 := (u_d1_hbon hμ hμ1 hu hD hr).comp hμ.le _ hmaps 1 zero_le_one hlip
  have h1 : ∀ v, HBon μ (Metric.ball x₀ r) (fun x => fderiv ℝ (chartΦ U x₀ u) x v) := by
    intro v
    have := HBon.prodMk (HBon.const (μ := μ) (S := Metric.ball x₀ r) (chartM U v))
      ((HBon.const (chartN U v)).sub (hD1.eval (HBon.const (chartM U v))))
    exact this.congr fun y hy => (fderiv_chartΦ_apply U x₀ u y (hud y hy) v).symm
  refine ⟨hcd, h1, fun v w => ?_, ?_⟩
  · have hH := ((u_hess_hbon hμ hμ1 hu hD hr (chartM U v) (chartM U w)).comp hμ.le _ hmaps 1
      zero_le_one hlip).neg
    have := HBon.prodMk (HBon.const (μ := μ) (S := Metric.ball x₀ r) (0 : EuclideanSpace ℝ (Fin n))) hH
    refine this.congr fun y hy => ?_
    have hdiff : DifferentiableAt ℝ (fderiv ℝ (chartΦ U x₀ u)) y :=
      ((hcd.contDiffAt (Metric.isOpen_ball.mem_nhds hy)).fderiv_right (m := 1)
        (by norm_num)).differentiableAt one_ne_zero
    rw [← fderiv2_eval_eq hdiff v w]
    have hev : (fun y => fderiv ℝ (chartΦ U x₀ u) y w) =ᶠ[nhds y]
        fun y => (chartM U w, chartN U w - fderiv ℝ u (projL n (U (y - x₀))) (chartM U w)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hy] with y' hy'
      exact fderiv_chartΦ_apply U x₀ u y' (hud y' hy') w
    rw [hev.fderiv_eq]
    have hDu : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) (projL n (U (y - x₀))))
        (projL n (U (y - x₀))) :=
      ((hu.1.contDiffAt (hD.mem_nhds (hPD y hy))).fderiv_right (m := 1)
        (by norm_num)).differentiableAt one_ne_zero |>.hasFDerivAt
    have hG := (hasFDerivAt_const (chartM U w) y).prodMk ((hasFDerivAt_const (chartN U w) y).sub
      ((hDu.comp y (chartP_hasFDerivAt U x₀ y)).clm_apply (hasFDerivAt_const (chartM U w) y)))
    have hG' : HasFDerivAt (fun y => (chartM U w, chartN U w -
        fderiv ℝ u (projL n (U (y - x₀))) (chartM U w))) _ y := hG
    rw [hG'.fderiv]
    simp
  · exact lip_of_basis (convex_ball x₀ r)
      (fun p hp => (hcd.contDiffAt (Metric.isOpen_ball.mem_nhds hp)).differentiableAt
        (by norm_num))
      fun i => by
        obtain ⟨B, -, -, -, hB, -⟩ := h1 (EuclideanSpace.single i 1)
        exact ⟨B, hB⟩

end chart2

end Pd67abb68Ch

/-! C2e boundary data: a locally `C^{1,μ}` function times a cutoff is a valid C2a input. -/

namespace Pd67abb68Cq

open Pd67abb68C2h

variable {d : ℕ}

lemma global_holder {F : Type*} [NormedAddCommGroup F] {μ : ℝ} (hμ : 0 < μ)
    {f : EuclideanSpace ℝ (Fin d) → F} {c : EuclideanSpace ℝ (Fin d)} {s s' : ℝ} (hs : s' < s)
    (hf : HBon μ (Metric.ball c s) f) (h0 : ∀ x, x ∉ Metric.closedBall c s' → f x = 0) :
    ∃ M, ∀ x y, ‖f x - f y‖ ≤ M * ‖x - y‖ ^ μ := by
  obtain ⟨B, K, hB, hK, h1, h2⟩ := hf
  have hgap : 0 < s - s' := by linarith
  have hpos : 0 < (s - s') ^ μ := Real.rpow_pos_of_pos hgap μ
  have hM1 : K ≤ K + B / (s - s') ^ μ := le_add_of_nonneg_right (div_nonneg hB hpos.le)
  have hM0 : 0 ≤ K + B / (s - s') ^ μ := hK.trans hM1
  have hout : ∀ x, x ∉ Metric.ball c s → f x = 0 :=
    fun x hx => h0 x fun h => hx (Metric.closedBall_subset_ball hs h)
  have key : ∀ x y, x ∈ Metric.ball c s → y ∉ Metric.ball c s →
      ‖f x - f y‖ ≤ (K + B / (s - s') ^ μ) * ‖x - y‖ ^ μ := by
    intro x y hx hy
    rw [hout y hy, sub_zero]
    by_cases hx' : x ∈ Metric.closedBall c s'
    · have hd : s - s' ≤ ‖x - y‖ := by
        rw [Metric.mem_ball, not_lt] at hy
        rw [Metric.mem_closedBall] at hx'
        rw [← dist_eq_norm]
        linarith [dist_triangle y x c, dist_comm x y]
      have hle : (s - s') ^ μ ≤ ‖x - y‖ ^ μ := Real.rpow_le_rpow hgap.le hd hμ.le
      calc ‖f x‖ ≤ B := h1 x hx
        _ = B / (s - s') ^ μ * (s - s') ^ μ := (div_mul_cancel₀ B hpos.ne').symm
        _ ≤ B / (s - s') ^ μ * ‖x - y‖ ^ μ :=
            mul_le_mul_of_nonneg_left hle (div_nonneg hB hpos.le)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK)
            (Real.rpow_nonneg (norm_nonneg _) _)
    · rw [h0 x hx', norm_zero]
      exact mul_nonneg hM0 (Real.rpow_nonneg (norm_nonneg _) _)
  refine ⟨K + B / (s - s') ^ μ, fun x y => ?_⟩
  by_cases hx : x ∈ Metric.ball c s <;> by_cases hy : y ∈ Metric.ball c s
  · exact (h2 x hx y hy).trans (mul_le_mul_of_nonneg_right hM1 (Real.rpow_nonneg (norm_nonneg _) _))
  · exact key x y hx hy
  · rw [norm_sub_rev, norm_sub_rev x y]
    exact key y x hy hx
  · rw [hout x hx, hout y hy, sub_zero, norm_zero]
    exact mul_nonneg hM0 (Real.rpow_nonneg (norm_nonneg _) _)

lemma lift_data {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) (h θ : EuclideanSpace ℝ (Fin d) → ℝ)
    {s s' : ℝ} (hs : s' < s) (hh : ContDiffOn ℝ 1 h (Metric.ball 0 s))
    (hh0 : HBon μ (Metric.ball 0 s) h) (hh1 : HBon μ (Metric.ball 0 s) (fderiv ℝ h))
    (hθ : ContDiff ℝ 2 θ) (hθs : tsupport θ ⊆ Metric.closedBall 0 s') :
    ContDiff ℝ 1 (fun z => θ z * h z) ∧ HasCompactSupport (fun z => θ z * h z) ∧
      ∃ M, ∀ x y, ‖fderiv ℝ (fun z => θ z * h z) x - fderiv ℝ (fun z => θ z * h z) y‖ ≤
        M * ‖x - y‖ ^ μ := by
  have hzero : ∀ x, x ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) s' →
      (fun z => θ z * h z) =ᶠ[nhds x] fun _ => (0:ℝ) := fun x hx => by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (fun h' => hx (hθs h'))] with y hy
    simp [hy]
  have hat : ∀ x, ContDiffAt ℝ 1 (fun z => θ z * h z) x := by
    intro x
    by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s
    · exact (hθ.of_le (by norm_num)).contDiffAt.mul
        (hh.contDiffAt (Metric.isOpen_ball.mem_nhds hx))
    · exact contDiffAt_const.congr_of_eventuallyEq
        (hzero x fun h' => hx (Metric.closedBall_subset_ball hs h'))
  have hθcs : HasCompactSupport θ :=
    HasCompactSupport.intro (isCompact_closedBall 0 s') fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h' => hx (hθs h')
  refine ⟨contDiff_iff_contDiffAt.mpr hat, ?_, ?_⟩
  · exact HasCompactSupport.intro (isCompact_closedBall 0 s') fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h' => hx (hθs h')), zero_mul]
  · apply global_holder hμ hs
    · have hθ0 : HBon μ (Metric.ball 0 s) θ :=
        (Pd67abb68C2g.hbon_of_cpt hμ hμ1 (hθ.of_le (by norm_num)) hθcs).mono (Set.subset_univ _)
      have hθ1 : HBon μ (Metric.ball 0 s) (fderiv ℝ θ) :=
        (Pd67abb68C2g.hbon_of_cpt hμ hμ1 (hθ.fderiv_right (m := 1) (by norm_num))
          (hθcs.fderiv (𝕜 := ℝ))).mono (Set.subset_univ _)
      have key := (HBon.bilin (ContinuousLinearMap.lsmul ℝ ℝ) hθ0 hh1).add
        (HBon.bilin (ContinuousLinearMap.lsmul ℝ ℝ) hh0 hθ1)
      refine key.congr fun x hx => ?_
      have h' : HasFDerivAt (fun z => θ z * h z) _ x :=
        ((hθ.differentiable (by norm_num)) x).hasFDerivAt.mul
          ((hh.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt one_ne_zero).hasFDerivAt
      rw [h'.fderiv]
      simp
    · intro x hx
      rw [(hzero x hx).fderiv_eq]
      simp

end Pd67abb68Cq

/-! C2e normal fact: the chart's last axis is (up to sign) the outward normal. -/

namespace Pd67abb68Cn

open Pd67abb68Ch

variable {n : ℕ}

/-- graph embedding `(z, a) ↦ (z, a)` with `a` in the last slot -/
noncomputable def graphJ (n : ℕ) : (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => WithLp.toLp 2 (Fin.lastCases p.2 (fun i => p.1 i))
      map_add' := fun p q => by ext i; induction i using Fin.lastCases <;> simp
      map_smul' := fun a p => by ext i; induction i using Fin.lastCases <;> simp }

lemma graphJ_apply (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    graphJ n p = WithLp.toLp 2 (Fin.lastCases p.2 (fun i => p.1 i)) := rfl

lemma real_inner_eq_sum {d : ℕ} (a b : EuclideanSpace ℝ (Fin d)) :
    inner ℝ a b = ∑ i, a i * b i := by
  simp [PiLp.inner_apply, mul_comm]

/-- a C^1 defining function vanishes on the frontier inside its chart -/
lemma r_zero_on_frontier {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hopen : IsOpen Ω)
    {V : Set (EuclideanSpace ℝ (Fin d))} (hV : IsOpen V) {r : EuclideanSpace ℝ (Fin d) → ℝ}
    (hr : ContDiffOn ℝ 1 r V) (hΩ : ∀ y ∈ V, y ∈ Ω ↔ r y < 0) {y : EuclideanSpace ℝ (Fin d)}
    (hy : y ∈ frontier Ω) (hyV : y ∈ V) : r y = 0 := by
  rw [hopen.frontier_eq] at hy
  obtain ⟨hcl, hnot⟩ := hy
  have h1 : ¬ r y < 0 := fun h => hnot ((hΩ y hyV).mpr h)
  refine le_antisymm (not_lt.mp fun hpos => ?_) (not_lt.mp h1)
  have hc : ContinuousAt r y := (hr.continuousOn.continuousAt (hV.mem_nhds hyV))
  have hn : {w | 0 < r w} ∩ V ∈ nhds y :=
    Filter.inter_mem (hc.eventually (lt_mem_nhds hpos)) (hV.mem_nhds hyV)
  obtain ⟨w, ⟨hw1, hw2⟩, hw3⟩ := mem_closure_iff_nhds.mp hcl _ hn
  exact absurd ((hΩ w hw2).mp hw3) (not_lt.mpr hw1.le)

set_option maxHeartbeats 1000000 in
lemma normal_last {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hopen : IsOpen Ω)
    {x₀ v : EuclideanSpace ℝ (Fin (n + 1))} (hn : EthierKurtz.IsOutwardUnitNormal Ω x₀ v)
    (U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (h0D : (0 : EuclideanSpace ℝ (Fin n)) ∈ D)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hud : DifferentiableAt ℝ u 0) (hu0 : u 0 = 0)
    (hDu0 : fderiv ℝ u 0 = 0) {ρ : ℝ}
    (hgraph : (fun x => U (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ) =
        (fun z : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)) :
            EuclideanSpace ℝ (Fin (n + 1)))) '' D) :
    ∃ κ : ℝ, κ ^ 2 = 1 ∧ ∀ h, lastL n (U h) = κ * ∑ i, v i * h i := by
  obtain ⟨-, hv1, V, hV, hx₀V, r, scale, hscale, hr, hr0, hΩ, hDr⟩ := hn
  -- the graph parametrisation
  have hXmem : ∀ z ∈ D, x₀ + U.symm (graphJ n (z, u z)) ∈ frontier Ω := by
    intro z hz
    have : graphJ n (z, u z) ∈ (fun x => U (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ) := by
      rw [hgraph]; exact ⟨z, hz, rfl⟩
    obtain ⟨x, ⟨hx, -⟩, hxe⟩ := this
    have : x = x₀ + U.symm (graphJ n (z, u z)) := by
      rw [← hxe, LinearIsometryEquiv.symm_apply_apply]; abel
    rw [← this]; exact hx
  have hX0 : x₀ + U.symm (graphJ n (0, u 0)) = x₀ := by
    rw [hu0, show ((0 : EuclideanSpace ℝ (Fin n)), (0:ℝ)) = 0 from rfl, map_zero, map_zero,
      add_zero]
  have hJd : HasFDerivAt (fun z => graphJ n (z, u z))
      ((graphJ n).comp ((ContinuousLinearMap.id ℝ _).prod (fderiv ℝ u 0))) 0 :=
    (graphJ n).hasFDerivAt.comp 0 ((hasFDerivAt_id 0).prodMk hud.hasFDerivAt)
  have hXd : HasFDerivAt (fun z => x₀ + U.symm (graphJ n (z, u z)))
      ((U.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
        ((graphJ n).comp ((ContinuousLinearMap.id ℝ _).prod (fderiv ℝ u 0)))) 0 :=
    ((U.symm.toContinuousLinearEquiv.toContinuousLinearMap).hasFDerivAt.comp 0 hJd).const_add x₀
  have hrd : HasFDerivAt r (fderiv ℝ r x₀) x₀ :=
    ((hr.contDiffAt (hV.mem_nhds hx₀V)).differentiableAt (by norm_num)).hasFDerivAt
  have hcomp := (hX0 ▸ hrd).comp 0 hXd
  have hev : (fun z => r (x₀ + U.symm (graphJ n (z, u z)))) =ᶠ[nhds 0] fun _ => (0:ℝ) := by
    have hXc : ContinuousAt (fun z => x₀ + U.symm (graphJ n (z, u z))) 0 := hXd.continuousAt
    have hV' : (fun z => x₀ + U.symm (graphJ n (z, u z))) ⁻¹' V ∈ nhds 0 :=
      hXc.preimage_mem_nhds (by rw [hX0]; exact hV.mem_nhds hx₀V)
    filter_upwards [hV', hD.mem_nhds h0D] with z hz1 hz2
    exact r_zero_on_frontier hopen hV hr hΩ (hXmem z hz2) hz1
  have hzero := (hasFDerivAt_const (𝕜 := ℝ) (0:ℝ) (0 : EuclideanSpace ℝ (Fin n))).congr_of_eventuallyEq hev
  have huniq := hcomp.unique hzero
  -- tangential components of U v vanish
  have htan : ∀ i : Fin n, U v (Fin.castSucc i) = 0 := by
    intro i
    have h1 := congrArg (fun L => L (EuclideanSpace.single i 1)) huniq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, hDu0,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply] at h1
    rw [hX0, hDr, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 hscale.ne'
    rw [← real_inner_eq_sum] at h1
    have h2 : inner ℝ (U v) (graphJ n (EuclideanSpace.single i 1, 0)) = 0 := by
      have h3 := LinearIsometryEquiv.inner_map_map U v (U.symm (graphJ n (EuclideanSpace.single i 1, 0)))
      rw [LinearIsometryEquiv.apply_symm_apply] at h3
      rw [h3]
      simpa using h1
    rw [real_inner_eq_sum, Fin.sum_univ_castSucc] at h2
    simpa [graphJ_apply, EuclideanSpace.single_apply] using h2
  have hsplit : ∀ h, ∑ i, v i * h i = U v (Fin.last n) * U h (Fin.last n) := by
    intro h
    rw [← real_inner_eq_sum, ← LinearIsometryEquiv.inner_map_map U v h, real_inner_eq_sum,
      Fin.sum_univ_castSucc]
    simp [htan]
  have hκ : U v (Fin.last n) ^ 2 = 1 := by
    have h1 : ‖U v‖ ^ 2 = 1 := by rw [LinearIsometryEquiv.norm_map, hv1, one_pow]
    rw [← real_inner_self_eq_norm_sq, real_inner_eq_sum, Fin.sum_univ_castSucc] at h1
    simpa [htan, sq] using h1
  refine ⟨U v (Fin.last n), hκ, fun h => ?_⟩
  rw [hsplit h, lastL_apply, ← mul_assoc, ← sq, hκ, one_mul]

end Pd67abb68Cn

/-! C2e L4 core: local `C^{1,μ}` algebra (`LC1`: differentiable, value and derivative `HBon` on `S`). -/

namespace Pd67abb68Cl

open Pd67abb68C2h Pd67abb68C2j

def LC1 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (μ : ℝ) (S : Set X) (f : X → ℝ) :
    Prop :=
  (∀ x ∈ S, DifferentiableAt ℝ f x) ∧ HBon μ S f ∧ HBon μ S (fderiv ℝ f)

section
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {μ : ℝ} {S : Set X}
  {f g : X → ℝ}

lemma LC1.add (hf : LC1 μ S f) (hg : LC1 μ S g) : LC1 μ S (fun x => f x + g x) := by
  refine ⟨fun x hx => (hf.1 x hx).add (hg.1 x hx), hf.2.1.add hg.2.1,
    (hf.2.2.add hg.2.2).congr fun x hx => ?_⟩
  have h' : HasFDerivAt (fun x => f x + g x) _ x :=
    (hf.1 x hx).hasFDerivAt.add (hg.1 x hx).hasFDerivAt
  rw [h'.fderiv]

lemma LC1.mul (hf : LC1 μ S f) (hg : LC1 μ S g) : LC1 μ S (fun x => f x * g x) := by
  refine ⟨fun x hx => (hf.1 x hx).mul (hg.1 x hx), hf.2.1.mul hg.2.1,
    ((HBon.bilin (ContinuousLinearMap.lsmul ℝ ℝ) hf.2.1 hg.2.2).add
      (HBon.bilin (ContinuousLinearMap.lsmul ℝ ℝ) hg.2.1 hf.2.2)).congr fun x hx => ?_⟩
  have h' : HasFDerivAt (fun x => f x * g x) _ x :=
    (hf.1 x hx).hasFDerivAt.mul (hg.1 x hx).hasFDerivAt
  rw [h'.fderiv]
  simp

lemma LC1.const (a : ℝ) : LC1 μ S (fun _ => a) := by
  refine ⟨fun x _ => differentiableAt_const a, HBon.const a, ?_⟩
  have := HBon.const (μ := μ) (S := S) (0 : X →L[ℝ] ℝ)
  refine this.congr fun x _ => ?_
  simp

lemma HBon.inv' {m : ℝ} (hm : 0 < m) (hf : HBon μ S f) (hlow : ∀ x ∈ S, m ≤ |f x|) :
    HBon μ S (fun x => (f x)⁻¹) := by
  obtain ⟨B, K, hB, hK, h1, h2⟩ := hf
  refine ⟨m⁻¹, K / m ^ 2, by positivity, by positivity, fun p hp => ?_, fun p hp p' hp' => ?_⟩
  · rw [norm_inv, Real.norm_eq_abs]
    exact inv_anti₀ hm (hlow p hp)
  · have hne : ∀ x ∈ S, f x ≠ 0 := fun x hx h => by
      have := hlow x hx
      rw [h, abs_zero] at this
      linarith
    rw [inv_sub_inv (hne p hp) (hne p' hp'), norm_div, norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have h3 := h2 p' hp' p hp
    rw [Real.norm_eq_abs, norm_sub_rev p' p] at h3
    have hden : m * m ≤ |f p| * |f p'| :=
      mul_le_mul (hlow p hp) (hlow p' hp') hm.le (abs_nonneg _)
    have hpos : 0 < |f p| * |f p'| := by nlinarith
    rw [div_le_iff₀ hpos]
    have hr : 0 ≤ ‖p - p'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) μ
    have hm2 : m ^ 2 ≠ 0 := by positivity
    calc |f p' - f p| ≤ K * ‖p - p'‖ ^ μ := h3
      _ = K / m ^ 2 * ‖p - p'‖ ^ μ * (m * m) := by field_simp
      _ ≤ K / m ^ 2 * ‖p - p'‖ ^ μ * (|f p| * |f p'|) :=
          mul_le_mul_of_nonneg_left hden (by positivity)

lemma LC1.inv {m : ℝ} (hm : 0 < m) (hf : LC1 μ S f) (hlow : ∀ x ∈ S, m ≤ |f x|) :
    LC1 μ S (fun x => (f x)⁻¹) := by
  have hne : ∀ x ∈ S, f x ≠ 0 := fun x hx h => by
    have := hlow x hx
    rw [h, abs_zero] at this
    linarith
  have hinv := HBon.inv' hm hf.2.1 hlow
  have hsq : HBon μ S (fun x => -((f x) ^ 2)⁻¹) :=
    ((hinv.mul hinv).neg).congr fun x _ => by rw [sq, mul_inv]
  have hd : ∀ x ∈ S, HasFDerivAt (fun x => (f x)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(f x ^ 2)⁻¹)).comp (fderiv ℝ f x)) x :=
    fun x hx => (hasFDerivAt_inv (hne x hx)).comp x (hf.1 x hx).hasFDerivAt
  refine ⟨fun x hx => (hd x hx).differentiableAt, hinv,
    (HBon.bilin (ContinuousLinearMap.lsmul ℝ ℝ) hsq hf.2.2).congr fun x hx => ?_⟩
  rw [(hd x hx).fderiv]
  ext v
  simp [mul_comm]

end

lemma LC1.comp_basis {d : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {μ : ℝ}
    (hμ0 : 0 ≤ μ) {f : Y → ℝ} {T : EuclideanSpace ℝ (Fin d) → Y}
    {S : Set (EuclideanSpace ℝ (Fin d))} {S' : Set Y} (hf : LC1 μ S' f)
    (hT : ∀ x ∈ S, DifferentiableAt ℝ T x) (hmaps : Set.MapsTo T S S') (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ p ∈ S, ∀ p' ∈ S, ‖T p - T p'‖ ≤ L * ‖p - p'‖)
    (hDT : ∀ k, HBon μ S (fun x => fderiv ℝ T x (EuclideanSpace.single k 1))) :
    LC1 μ S (fun x => f (T x)) := by
  refine ⟨fun x hx => (hf.1 (T x) (hmaps hx)).comp x (hT x hx),
    hf.2.1.comp hμ0 T hmaps L hL0 hL, hbon_clm_of_basis _ fun k => ?_⟩
  refine ((hf.2.2.comp hμ0 T hmaps L hL0 hL).eval (hDT k)).congr fun x hx => ?_
  have h' : HasFDerivAt (fun x => f (T x)) _ x :=
    (hf.1 (T x) (hmaps hx)).hasFDerivAt.comp x (hT x hx).hasFDerivAt
  rw [h'.fderiv]
  rfl

end Pd67abb68Cl

set_option autoImplicit false

/-! C2e step 1: two-sided (odd) extension of the one-sided flat lift of C2a. -/

namespace Pd67abb68C2e

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- reflection `(z, t) ↦ (z, -t)` -/
noncomputable def refl (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E × ℝ) ≃L[ℝ] (E × ℝ) :=
  (ContinuousLinearEquiv.refl ℝ E).prodCongr (ContinuousLinearEquiv.neg ℝ)

lemma refl_apply (p : E × ℝ) : refl E p = (p.1, -p.2) := rfl

lemma norm_refl_apply (p : E × ℝ) : ‖refl E p‖ = ‖p‖ := by
  rw [refl_apply, Prod.norm_def, Prod.norm_def, norm_neg]

lemma norm_refl_le : ‖(refl E : (E × ℝ) →L[ℝ] (E × ℝ))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun p => by
    rw [one_mul]; exact (norm_refl_apply p).le)

/-- odd extension across `t = 0` -/
noncomputable def odd (W : E × ℝ → ℝ) : E × ℝ → ℝ :=
  fun p => if 0 ≤ p.2 then W p else -W (refl E p)

/-- the reflected piece -/
noncomputable def oddL (W : E × ℝ → ℝ) : E × ℝ → ℝ := fun p => -W (refl E p)

lemma oddL_hasFDerivAt (W : E × ℝ → ℝ) (p : E × ℝ) (hW : DifferentiableAt ℝ W (refl E p)) :
    HasFDerivAt (oddL W) (-((fderiv ℝ W (refl E p)).comp (refl E : (E × ℝ) →L[ℝ] (E × ℝ)))) p := by
  have h := hW.hasFDerivAt.comp p (refl E).hasFDerivAt
  exact h.neg

lemma snd_comp_refl :
    (ContinuousLinearMap.snd ℝ E ℝ).comp (refl E : (E × ℝ) →L[ℝ] (E × ℝ)) =
      -ContinuousLinearMap.snd ℝ E ℝ := by
  ext p <;> simp [refl_apply]

/-- derivative of the odd extension -/
noncomputable def oddD (W : E × ℝ → ℝ) (p : E × ℝ) : E × ℝ →L[ℝ] ℝ :=
  if 0 ≤ p.2 then fderiv ℝ W p
  else -((fderiv ℝ W (refl E p)).comp (refl E : (E × ℝ) →L[ℝ] (E × ℝ)))

section
variable (W : E × ℝ → ℝ) (q : E → ℝ) (hW : ContDiff ℝ 1 W) (hW0 : ∀ z, W (z, 0) = 0)
  (hDW : ∀ z, fderiv ℝ W (z, 0) = q z • ContinuousLinearMap.snd ℝ E ℝ)
include hW hW0 hDW

lemma odd_hasFDerivAt (p : E × ℝ) : HasFDerivAt (odd W) (oddD W p) p := by
  have hd : Differentiable ℝ W := hW.differentiable one_ne_zero
  rcases lt_trichotomy p.2 0 with h | h | h
  · have hev : oddL W =ᶠ[nhds p] odd W := by
      filter_upwards [continuous_snd.isOpen_preimage _ isOpen_Iio |>.mem_nhds h] with x hx
      simp only [Set.mem_preimage, Set.mem_Iio] at hx
      simp [odd, oddL, not_le.mpr hx]
    have := (oddL_hasFDerivAt W p (hd _)).congr_of_eventuallyEq hev.symm
    simpa [oddD, not_le.mpr h] using this
  · -- the gluing point
    have hp : p = (p.1, 0) := by ext <;> simp [h]
    have hD1 : HasFDerivAt W (oddD W p) p := by
      simpa [oddD, h] using (hd p).hasFDerivAt
    have hD2 : HasFDerivAt (oddL W) (oddD W p) p := by
      have h2 := oddL_hasFDerivAt W p (hd _)
      have hr : refl E p = (p.1, 0) := by rw [refl_apply, h, neg_zero]
      have heq : -((fderiv ℝ W (refl E p)).comp (refl E : (E × ℝ) →L[ℝ] (E × ℝ))) = oddD W p := by
        rw [hr, hDW, oddD, if_pos h.ge, hp, hDW]
        rw [ContinuousLinearMap.smul_comp, snd_comp_refl]; simp
      rwa [heq] at h2
    have hA : HasFDerivWithinAt (odd W) (oddD W p) {x | 0 ≤ x.2} p := by
      refine hD1.hasFDerivWithinAt.congr (fun x hx => ?_) ?_
      · simp [odd, show (0:ℝ) ≤ x.2 from hx]
      · simp [odd, h]
    have hB : HasFDerivWithinAt (odd W) (oddD W p) {x | x.2 ≤ 0} p := by
      refine hD2.hasFDerivWithinAt.congr (fun x hx => ?_) ?_
      · simp only [Set.mem_setOf_eq] at hx
        rcases hx.lt_or_eq with hx | hx
        · simp [odd, oddL, not_le.mpr hx]
        · have : x = (x.1, 0) := by ext <;> simp [hx]
          rw [this]; simp [odd, oddL, refl_apply, hW0]
      · rw [hp]; simp [odd, oddL, refl_apply, hW0]
    have hU := hA.union hB
    have : {x : E × ℝ | 0 ≤ x.2} ∪ {x | x.2 ≤ 0} = Set.univ := by
      ext x; simp [le_total]
    rw [this] at hU
    exact hasFDerivWithinAt_univ.mp hU
  · have hev : W =ᶠ[nhds p] odd W := by
      filter_upwards [continuous_snd.isOpen_preimage _ isOpen_Ioi |>.mem_nhds h] with x hx
      simp only [Set.mem_preimage, Set.mem_Ioi] at hx
      simp [odd, hx.le]
    have := (hd p).hasFDerivAt.congr_of_eventuallyEq hev.symm
    simpa [oddD, h.le] using this

lemma fderiv_odd : fderiv ℝ (odd W) = oddD W :=
  funext fun p => (odd_hasFDerivAt W q hW hW0 hDW p).fderiv

lemma odd_contDiff : ContDiff ℝ 1 (odd W) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun p => (odd_hasFDerivAt W q hW hW0 hDW p).differentiableAt, ?_⟩
  rw [fderiv_odd W q hW hW0 hDW]
  have hc : Continuous (fderiv ℝ W) := hW.continuous_fderiv one_ne_zero
  have hc2 : Continuous fun p : E × ℝ =>
      -((fderiv ℝ W (refl E p)).comp (refl E : (E × ℝ) →L[ℝ] (E × ℝ))) := by
    have : Continuous fun p : E × ℝ => fderiv ℝ W (refl E p) := hc.comp (refl E).continuous
    exact (this.clm_comp continuous_const).neg
  refine Continuous.if_le hc hc2 continuous_const continuous_snd ?_
  intro p hp
  have hp' : p = (p.1, 0) := by ext <;> simp [← hp]
  have hr : refl E p = (p.1, 0) := by rw [refl_apply, ← hp, neg_zero]
  rw [hr, hDW, hp', hDW, ContinuousLinearMap.smul_comp, snd_comp_refl]; simp

lemma odd_zero (z : E) : odd W (z, 0) = 0 := by simp [odd, hW0]

lemma fderiv_odd_zero (z : E) :
    fderiv ℝ (odd W) (z, 0) = q z • ContinuousLinearMap.snd ℝ E ℝ := by
  rw [fderiv_odd W q hW hW0 hDW, oddD, if_pos le_rfl, hDW]

end

lemma odd_abs_le (W : E × ℝ → ℝ) (δ : ℝ) (hδ : ∀ p, |W p| ≤ δ) (p : E × ℝ) : |odd W p| ≤ δ := by
  unfold odd; split_ifs
  · exact hδ p
  · rw [abs_neg]; exact hδ _

lemma odd_hasCompactSupport (W : E × ℝ → ℝ) (hW : HasCompactSupport W) :
    HasCompactSupport (odd W) := by
  have h2 : HasCompactSupport (oddL W) := by
    have : HasCompactSupport (W ∘ (refl E)) :=
      hW.comp_homeomorph (refl E).toHomeomorph
    exact this.neg
  refine HasCompactSupport.intro' (hW.union h2)
    ((isClosed_tsupport _).union (isClosed_tsupport _)) (fun p hp => ?_)
  have h1 : W p = 0 := by
    by_contra h; exact hp (Or.inl (subset_tsupport _ (Function.mem_support.mpr h)))
  have h3 : oddL W p = 0 := by
    by_contra h; exact hp (Or.inr (subset_tsupport _ (Function.mem_support.mpr h)))
  unfold odd; unfold oddL at h3
  split_ifs
  · exact h1
  · exact h3

lemma odd_eventuallyEq_pos (W : E × ℝ → ℝ) (p : E × ℝ) (h : 0 < p.2) : odd W =ᶠ[nhds p] W := by
  filter_upwards [continuous_snd.isOpen_preimage _ isOpen_Ioi |>.mem_nhds h] with x hx
  simp only [Set.mem_preimage, Set.mem_Ioi] at hx
  simp [odd, hx.le]

lemma odd_eventuallyEq_neg (W : E × ℝ → ℝ) (p : E × ℝ) (h : p.2 < 0) :
    odd W =ᶠ[nhds p] oddL W := by
  filter_upwards [continuous_snd.isOpen_preimage _ isOpen_Iio |>.mem_nhds h] with x hx
  simp only [Set.mem_preimage, Set.mem_Iio] at hx
  simp [odd, oddL, not_le.mpr hx]

lemma isOpen_pos : IsOpen {p : E × ℝ | 0 < p.2} := continuous_snd.isOpen_preimage _ isOpen_Ioi
lemma isOpen_neg : IsOpen {p : E × ℝ | p.2 < 0} := continuous_snd.isOpen_preimage _ isOpen_Iio

lemma odd_contDiffOn_pos (W : E × ℝ → ℝ) (hW2 : ContDiffOn ℝ 2 W {p | 0 < p.2}) :
    ContDiffOn ℝ 2 (odd W) {p | 0 < p.2} :=
  hW2.congr (fun p hp => by simp [odd, (show (0:ℝ) < p.2 from hp).le])

lemma odd_contDiffOn_neg (W : E × ℝ → ℝ) (hW2 : ContDiffOn ℝ 2 W {p | 0 < p.2}) :
    ContDiffOn ℝ 2 (odd W) {p | p.2 < 0} := by
  have h1 : ContDiffOn ℝ 2 (oddL W) {p | p.2 < 0} := by
    have : ContDiffOn ℝ 2 (W ∘ (refl E)) {p | p.2 < 0} :=
      hW2.comp (refl E).contDiff.contDiffOn (fun p hp => by
        simp only [Set.mem_setOf_eq] at hp ⊢; rw [refl_apply]; simpa using hp)
    exact this.neg
  exact h1.congr (fun p hp => by
    simp [odd, oddL, not_le.mpr (show p.2 < 0 from hp)])

/-- second derivative of the odd extension on the lower side -/
lemma fderiv2_odd_neg (W : E × ℝ → ℝ) (hW : ContDiff ℝ 1 W) (hW2 : ContDiffOn ℝ 2 W {p | 0 < p.2})
    (p : E × ℝ) (hp : p.2 < 0) :
    fderiv ℝ (fderiv ℝ (odd W)) p =
      -(((ContinuousLinearMap.compL ℝ (E × ℝ) (E × ℝ) ℝ).flip
          (refl E : (E × ℝ) →L[ℝ] (E × ℝ))).comp
        ((fderiv ℝ (fderiv ℝ W) (refl E p)).comp (refl E : (E × ℝ) →L[ℝ] (E × ℝ)))) := by
  set T := (ContinuousLinearMap.compL ℝ (E × ℝ) (E × ℝ) ℝ).flip
    (refl E : (E × ℝ) →L[ℝ] (E × ℝ))
  have hd : Differentiable ℝ W := hW.differentiable one_ne_zero
  -- near p, fderiv (odd W) = - T ∘ fderiv W ∘ refl
  have hev : fderiv ℝ (odd W) =ᶠ[nhds p] fun x => -(T (fderiv ℝ W (refl E x))) := by
    filter_upwards [isOpen_neg.mem_nhds hp] with x hx
    rw [(odd_eventuallyEq_neg W x hx).fderiv_eq]
    rw [(oddL_hasFDerivAt W x (hd _)).fderiv]
    rfl
  rw [hev.fderiv_eq]
  have hrp : refl E p ∈ {x : E × ℝ | 0 < x.2} := by
    simp only [Set.mem_setOf_eq, refl_apply]; linarith
  have hdd : DifferentiableAt ℝ (fderiv ℝ W) (refl E p) := by
    have h3 : ContDiffAt ℝ 2 W (refl E p) := hW2.contDiffAt (isOpen_pos.mem_nhds hrp)
    exact (h3.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hc := (T.hasFDerivAt.comp p (hdd.hasFDerivAt.comp p (refl E).hasFDerivAt)).neg
  exact hc.fderiv

set_option synthInstance.maxHeartbeats 400000 in
lemma odd_holder_neg (W : E × ℝ → ℝ) (hW : ContDiff ℝ 1 W) (hW2 : ContDiffOn ℝ 2 W {p | 0 < p.2})
    (μ K : ℝ) (hK : ∀ p p' : E × ℝ, 0 < p.2 → 0 < p'.2 →
        ‖fderiv ℝ (fderiv ℝ W) p - fderiv ℝ (fderiv ℝ W) p'‖ ≤ K * ‖p - p'‖ ^ μ)
    (p p' : E × ℝ) (hp : p.2 < 0) (hp' : p'.2 < 0) :
    ‖fderiv ℝ (fderiv ℝ (odd W)) p - fderiv ℝ (fderiv ℝ (odd W)) p'‖ ≤ K * ‖p - p'‖ ^ μ := by
  rw [fderiv2_odd_neg W hW hW2 p hp, fderiv2_odd_neg W hW hW2 p' hp']
  set T := (ContinuousLinearMap.compL ℝ (E × ℝ) (E × ℝ) ℝ).flip
    (refl E : (E × ℝ) →L[ℝ] (E × ℝ))
  set R := (refl E : (E × ℝ) →L[ℝ] (E × ℝ))
  have hT : ‖T‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun A => ?_)
    rw [one_mul]
    show ‖A.comp R‖ ≤ ‖A‖
    calc ‖A.comp R‖ ≤ ‖A‖ * ‖R‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left norm_refl_le (norm_nonneg _)
      _ = ‖A‖ := mul_one _
  have h1 : 0 < (refl E p).2 := by rw [refl_apply]; simp; linarith
  have h2 : 0 < (refl E p').2 := by rw [refl_apply]; simp; linarith
  have hK' := hK _ _ h1 h2
  rw [← map_sub, norm_refl_apply] at hK'
  have he : -(T.comp ((fderiv ℝ (fderiv ℝ W) (refl E p)).comp R)) -
      -(T.comp ((fderiv ℝ (fderiv ℝ W) (refl E p')).comp R)) =
      -(T.comp ((fderiv ℝ (fderiv ℝ W) (refl E p) - fderiv ℝ (fderiv ℝ W) (refl E p')).comp R)) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]; abel
  rw [he]; rw [ContinuousLinearMap.opNorm_neg]
  calc _ ≤ ‖T‖ * ‖(fderiv ℝ (fderiv ℝ W) (refl E p) - fderiv ℝ (fderiv ℝ W) (refl E p')).comp R‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖fderiv ℝ (fderiv ℝ W) (refl E p) - fderiv ℝ (fderiv ℝ W) (refl E p')‖ * 1) := by
        exact mul_le_mul hT ((ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left norm_refl_le (ContinuousLinearMap.opNorm_nonneg _)))
          (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
    _ ≤ K * ‖p - p'‖ ^ μ := by rw [one_mul, mul_one]; exact hK'

lemma odd_holder_pos (W : E × ℝ → ℝ)
    (μ K : ℝ) (hK : ∀ p p' : E × ℝ, 0 < p.2 → 0 < p'.2 →
        ‖fderiv ℝ (fderiv ℝ W) p - fderiv ℝ (fderiv ℝ W) p'‖ ≤ K * ‖p - p'‖ ^ μ)
    (p p' : E × ℝ) (hp : 0 < p.2) (hp' : 0 < p'.2) :
    ‖fderiv ℝ (fderiv ℝ (odd W)) p - fderiv ℝ (fderiv ℝ (odd W)) p'‖ ≤ K * ‖p - p'‖ ^ μ := by
  have e : ∀ x : E × ℝ, 0 < x.2 → fderiv ℝ (fderiv ℝ (odd W)) x = fderiv ℝ (fderiv ℝ W) x := by
    intro x hx
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [isOpen_pos.mem_nhds hx] with y hy
    exact (odd_eventuallyEq_pos W y hy).fderiv_eq
  rw [e p hp, e p' hp']; exact hK p p' hp hp'

/-- C2e step 1 packaged: the two-sided lift. -/
theorem two_sided_lift (W : E × ℝ → ℝ) (q : E → ℝ) (μ δ : ℝ)
    (hW : ContDiff ℝ 1 W) (hWs : HasCompactSupport W) (hW2 : ContDiffOn ℝ 2 W {p | 0 < p.2})
    (hW0 : ∀ z, W (z, 0) = 0)
    (hDW : ∀ z, fderiv ℝ W (z, 0) = q z • ContinuousLinearMap.snd ℝ E ℝ)
    (hδ : ∀ p, |W p| ≤ δ)
    (hK : ∃ K : ℝ, ∀ p p' : E × ℝ, 0 < p.2 → 0 < p'.2 →
        ‖fderiv ℝ (fderiv ℝ W) p - fderiv ℝ (fderiv ℝ W) p'‖ ≤ K * ‖p - p'‖ ^ μ) :
    ∃ V : E × ℝ → ℝ, ContDiff ℝ 1 V ∧ HasCompactSupport V ∧
      ContDiffOn ℝ 2 V {p | p.2 ≠ 0} ∧ (∀ z, V (z, 0) = 0) ∧
      (∀ z, fderiv ℝ V (z, 0) = q z • ContinuousLinearMap.snd ℝ E ℝ) ∧ (∀ p, |V p| ≤ δ) ∧
      ∃ K : ℝ, ∀ p p' : E × ℝ, (0 < p.2 ∧ 0 < p'.2) ∨ (p.2 < 0 ∧ p'.2 < 0) →
        ‖fderiv ℝ (fderiv ℝ V) p - fderiv ℝ (fderiv ℝ V) p'‖ ≤ K * ‖p - p'‖ ^ μ := by
  obtain ⟨K, hK⟩ := hK
  refine ⟨odd W, odd_contDiff W q hW hW0 hDW, odd_hasCompactSupport W hWs, ?_,
    odd_zero W q hW hW0 hDW, fderiv_odd_zero W q hW hW0 hDW, odd_abs_le W δ hδ, K, ?_⟩
  · have : {p : E × ℝ | p.2 ≠ 0} = {p | 0 < p.2} ∪ {p | p.2 < 0} := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_union]
      exact ⟨fun h => h.lt_or_gt.symm, fun h => h.elim (fun h => h.ne') (fun h => h.ne)⟩
    rw [this]
    intro p hp
    rcases hp with hp | hp
    · exact ((odd_contDiffOn_pos W hW2).contDiffAt (isOpen_pos.mem_nhds hp)).contDiffWithinAt
    · exact ((odd_contDiffOn_neg W hW2).contDiffAt (isOpen_neg.mem_nhds hp)).contDiffWithinAt
  · rintro p p' (⟨hp, hp'⟩ | ⟨hp, hp'⟩)
    · exact odd_holder_pos W μ K hK p p' hp hp'
    · exact odd_holder_neg W hW hW2 μ K hK p p' hp hp'

end Pd67abb68C2e

/-! C2e L4: the oblique data in the main chart (LC1 of `c ∘ X`, the normal factor `dN`). -/

namespace Pd67abb68Cr

open Pd67abb68C2h Pd67abb68C2j Pd67abb68Ch Pd67abb68Cl Pd67abb68Cn

section gen
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {μ : ℝ} {S : Set X}

lemma HBon.continuousOn' {F : Type*} [NormedAddCommGroup F] (hμ : 0 < μ) {f : X → F}
    (hf : HBon μ S f) : ContinuousOn f S := by
  obtain ⟨B, K, -, hK, -, h2⟩ := hf
  intro p hp
  have ht : Filter.Tendsto (fun x => K * ‖x - p‖ ^ μ) (nhdsWithin p S) (nhds 0) := by
    have hc : Continuous fun x : X => K * ‖x - p‖ ^ μ :=
      continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const
        fun _ => Or.inr hμ.le)
    have h0 := hc.tendsto p
    simp only [sub_self, norm_zero, Real.zero_rpow hμ.ne', mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ ht
  filter_upwards [self_mem_nhdsWithin] with x hx using h2 x hx p hp

lemma LC1.sub {f g : X → ℝ} (hf : LC1 μ S f) (hg : LC1 μ S g) :
    LC1 μ S (fun x => f x - g x) := by
  refine ⟨fun x hx => (hf.1 x hx).sub (hg.1 x hx), hf.2.1.sub hg.2.1,
    (hf.2.2.sub hg.2.2).congr fun x hx => ?_⟩
  have h' : HasFDerivAt (fun x => f x - g x) _ x :=
    (hf.1 x hx).hasFDerivAt.sub (hg.1 x hx).hasFDerivAt
  rw [h'.fderiv]

lemma LC1.sum {ι : Type*} (s : Finset ι) {f : ι → X → ℝ} (hf : ∀ i ∈ s, LC1 μ S (f i)) :
    LC1 μ S (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (LC1.const (μ := μ) (S := S) (0 : ℝ))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma LC1.congr_open (hS : IsOpen S) {f g : X → ℝ} (hf : LC1 μ S f) (h : ∀ x ∈ S, f x = g x) :
    LC1 μ S g := by
  have hev : ∀ x ∈ S, f =ᶠ[nhds x] g := fun x hx => Filter.eventually_of_mem (hS.mem_nhds hx) h
  exact ⟨fun x hx => (hf.1 x hx).congr_of_eventuallyEq (hev x hx).symm, hf.2.1.congr h,
    hf.2.2.congr fun x hx => (hev x hx).fderiv_eq⟩

lemma LC1.contDiffOn (hμ : 0 < μ) (hS : IsOpen S) {f : X → ℝ} (hf : LC1 μ S f) :
    ContDiffOn ℝ 1 f S := by
  have h := (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (n := 0) (f := f) hS).mpr
    ⟨fun x hx => (hf.1 x hx).differentiableWithinAt, fun h => by simp at h,
      contDiffOn_zero.mpr (HBon.continuousOn' hμ hf.2.2)⟩
  simpa using h

end gen

section gen2
variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : ℝ}

/-- `C^2` on an open neighbourhood of a closed ball: the local `C^{1,μ}` facts on the open ball. -/
lemma c2_ball (hμ : 0 < μ) (hμ1 : μ ≤ 1) {f : EuclideanSpace ℝ (Fin d) → F}
    {O : Set (EuclideanSpace ℝ (Fin d))} (hO : IsOpen O) (hf : ContDiffOn ℝ 2 f O)
    {c : EuclideanSpace ℝ (Fin d)} {s : ℝ} (hs : Metric.closedBall c s ⊆ O) :
    (∀ x ∈ Metric.ball c s, DifferentiableAt ℝ f x) ∧ HBon μ (Metric.ball c s) f ∧
      HBon μ (Metric.ball c s) (fderiv ℝ f) ∧
      ∃ L, 0 ≤ L ∧ ∀ p ∈ Metric.ball c s, ∀ p' ∈ Metric.ball c s,
        ‖f p - f p'‖ ≤ L * ‖p - p'‖ := by
  have hsub : Metric.ball c s ⊆ O := Metric.ball_subset_closedBall.trans hs
  have hd : ∀ x ∈ O, DifferentiableAt ℝ f x := fun x hx =>
    (hf.contDiffAt (hO.mem_nhds hx)).differentiableAt (by norm_num)
  have hf1 : ContDiffOn ℝ 1 (fderiv ℝ f) O := hf.fderiv_of_isOpen hO (by norm_num)
  have hdd : ∀ x ∈ O, DifferentiableAt ℝ (fderiv ℝ f) x := fun x hx =>
    (hf1.contDiffAt (hO.mem_nhds hx)).differentiableAt (by norm_num)
  obtain ⟨B0, hB0⟩ :=
    (isCompact_closedBall c s).exists_bound_of_continuousOn (hf.continuousOn.mono hs)
  obtain ⟨B1, hB1⟩ :=
    (isCompact_closedBall c s).exists_bound_of_continuousOn (hf1.continuousOn.mono hs)
  obtain ⟨B2, hB2⟩ := (isCompact_closedBall c s).exists_bound_of_continuousOn
    ((hf1.continuousOn_fderiv_of_isOpen hO le_rfl).mono hs)
  have hcv := convex_ball c s
  have hB1' : ∀ p ∈ Metric.ball c s, ‖fderiv ℝ f p‖ ≤ max B1 0 := fun p hp =>
    (hB1 p (Metric.ball_subset_closedBall hp)).trans (le_max_left _ _)
  exact ⟨fun x hx => hd x (hsub hx),
    HBon.of_fderiv hμ hμ1 hcv (fun x hx => hd x (hsub hx))
      (fun p hp => hB0 p (Metric.ball_subset_closedBall hp)) hB1',
    HBon.of_fderiv hμ hμ1 hcv (fun x hx => hdd x (hsub hx))
      (fun p hp => hB1 p (Metric.ball_subset_closedBall hp))
      (fun p hp => hB2 p (Metric.ball_subset_closedBall hp)),
    max B1 0, le_max_right _ _, lip_of_fderiv_bound hcv (fun x hx => hd x (hsub hx)) hB1'⟩

lemma LC1.of_c2 (hμ : 0 < μ) (hμ1 : μ ≤ 1) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {O : Set (EuclideanSpace ℝ (Fin d))} (hO : IsOpen O) (hf : ContDiffOn ℝ 2 f O)
    {c : EuclideanSpace ℝ (Fin d)} {s : ℝ} (hs : Metric.closedBall c s ⊆ O) :
    LC1 μ (Metric.ball c s) f := by
  obtain ⟨h1, h2, h3, -⟩ := c2_ball hμ hμ1 hO hf hs
  exact ⟨h1, h2, h3⟩

lemma LC1.of_conce (hμ : 0 < μ) (hμ1 : μ ≤ 1) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : IsOpen D) (hf : EthierKurtz.COnceHolder D μ f)
    {c : EuclideanSpace ℝ (Fin d)} {s : ℝ} (hs : Metric.closedBall c s ⊆ D) :
    LC1 μ (Metric.ball c s) f := by
  have hsub : Metric.ball c s ⊆ D := Metric.ball_subset_closedBall.trans hs
  have hd : ∀ x ∈ D, DifferentiableAt ℝ f x := fun x hx =>
    (hf.1.contDiffAt (hD.mem_nhds hx)).differentiableAt (by norm_num)
  have hD1 : HBon μ (Metric.ball c s) (fderiv ℝ f) :=
    hbon_clm_of_basis _ fun i => hbon_of_componentHolder hμ hμ1 (hf.2 i) hs
  have hD1' := hD1
  obtain ⟨B, -, -, -, hB, -⟩ := hD1'
  obtain ⟨B0, hB0⟩ :=
    (isCompact_closedBall c s).exists_bound_of_continuousOn (hf.1.continuousOn.mono hs)
  exact ⟨fun x hx => hd x (hsub hx), HBon.of_fderiv hμ hμ1 (convex_ball c s)
    (fun x hx => hd x (hsub hx)) (fun p hp => hB0 p (Metric.ball_subset_closedBall hp)) hB, hD1⟩

lemma LC1.du (hμ : 0 < μ) (hμ1 : μ ≤ 1) {D : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : EthierKurtz.CTwiceHolder D μ u) (hD : IsOpen D)
    {c : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : Metric.closedBall c r ⊆ D)
    (w : EuclideanSpace ℝ (Fin d)) : LC1 μ (Metric.ball c r) (fun z => fderiv ℝ u z w) := by
  have hsub : Metric.ball c r ⊆ D := Metric.ball_subset_closedBall.trans hr
  have hdiff : ∀ z ∈ D, DifferentiableAt ℝ (fderiv ℝ u) z := fun z hz =>
    ((hu.1.contDiffAt (hD.mem_nhds hz)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      one_ne_zero
  refine ⟨fun z hz => (hdiff z (hsub hz)).clm_apply (differentiableAt_const w),
    (u_d1_hbon hμ hμ1 hu hD hr).eval (HBon.const w),
    hbon_clm_of_basis _ fun i => ?_⟩
  exact (u_hess_hbon hμ hμ1 hu hD hr (EuclideanSpace.single i 1) w).congr fun z hz =>
    (hess_eval_eq (hdiff z (hsub hz)) _ _).symm

end gen2

section chart
variable {n : ℕ}

/-- the main chart parametrisation of the frontier -/
noncomputable def chX (U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  x₀ + U.symm (graphJ n (z, u z))

/-- chart transition into another chart at the same base point -/
noncomputable def trT (U' U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  projL n (U' (chX U x₀ u z - x₀))

/-- the normal factor: `DΦ(X z)(c) ` last slot, in chart coordinates -/
noncomputable def dN (U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (C : Fin (n + 1) → EuclideanSpace ℝ (Fin n) → ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, C i z * (lastL n (U (EuclideanSpace.single i 1)) -
    fderiv ℝ u z (projL n (U (EuclideanSpace.single i 1))))

variable (U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
  (x₀ : EuclideanSpace ℝ (Fin (n + 1)))

lemma chX_zero {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu0 : u 0 = 0) : chX U x₀ u 0 = x₀ := by
  rw [chX, hu0, show ((0 : EuclideanSpace ℝ (Fin n)), (0:ℝ)) = 0 from rfl, map_zero, map_zero,
    add_zero]

lemma chX_contDiffOn {D : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiffOn ℝ 2 u D) : ContDiffOn ℝ 2 (chX U x₀ u) D := by
  show ContDiffOn ℝ 2 (fun z => x₀ + U.symm (graphJ n (z, u z))) D
  exact contDiffOn_const.add
    ((U.symm.toContinuousLinearEquiv.toContinuousLinearMap).contDiff.comp_contDiffOn
      ((graphJ n).contDiff.comp_contDiffOn (contDiffOn_id.prodMk hu)))

lemma trT_contDiffOn (U' : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {D : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiffOn ℝ 2 u D) : ContDiffOn ℝ 2 (trT U' U x₀ u) D := by
  show ContDiffOn ℝ 2 (fun z => projL n (U' (chX U x₀ u z - x₀))) D
  have h1 := (chX_contDiffOn U x₀ hu).sub (contDiffOn_const (c := x₀))
  have h2 := (U'.toContinuousLinearEquiv.toContinuousLinearMap).contDiff.comp_contDiffOn h1
  exact (projL n).contDiff.comp_contDiffOn h2

lemma trT_zero (U' : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu0 : u 0 = 0) : trT U' U x₀ u 0 = 0 := by
  rw [trT, chX_zero U x₀ hu0, sub_self, map_zero, map_zero]

/-- frontier points over `D` -/
lemma chX_mem {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {ρ : ℝ}
    (hgraph : (fun x => U (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ) =
        (fun z : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)) :
            EuclideanSpace ℝ (Fin (n + 1)))) '' D)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ D) : chX U x₀ u z ∈ frontier Ω := by
  have : graphJ n (z, u z) ∈ (fun x => U (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ) := by
    rw [hgraph]; exact ⟨z, hz, rfl⟩
  obtain ⟨x, ⟨hx, -⟩, hxe⟩ := this
  have : x = chX U x₀ u z := by
    rw [chX, ← hxe, LinearIsometryEquiv.symm_apply_apply]; abel
  rw [← this]; exact hx

/-- another chart at `x₀` sees `X z` through the transition `trT` -/
lemma chX_other {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (U' : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {D' : Set (EuclideanSpace ℝ (Fin n))} {u u' : EuclideanSpace ℝ (Fin n) → ℝ} {ρ' : ℝ}
    (hgraph' : (fun x => U' (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ') =
        (fun z : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 (Fin.lastCases (u' z) (fun i => z i)) :
            EuclideanSpace ℝ (Fin (n + 1)))) '' D')
    {z : EuclideanSpace ℝ (Fin n)} (hz : chX U x₀ u z ∈ frontier Ω)
    (hzb : chX U x₀ u z ∈ Metric.ball x₀ ρ') :
    x₀ + U'.symm (WithLp.toLp 2 (Fin.lastCases (u' (trT U' U x₀ u z))
      (fun j => trT U' U x₀ u z j))) = chX U x₀ u z := by
  have hm : U' (chX U x₀ u z - x₀) ∈
      (fun x => U' (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ') := ⟨_, ⟨hz, hzb⟩, rfl⟩
  rw [hgraph'] at hm
  obtain ⟨w, -, hw⟩ := hm
  simp only at hw
  have hwT : w = trT U' U x₀ u z := by
    rw [trT, ← hw, projL_mk]
  rw [← hwT, hw, LinearIsometryEquiv.symm_apply_apply]
  abel

end chart

end Pd67abb68Cr

/-! C2e L4 main: oblique data in the main chart at a frontier point. -/

namespace Pd67abb68Cs

open Pd67abb68C2h Pd67abb68C2j Pd67abb68Ch Pd67abb68Cl Pd67abb68Cn Pd67abb68Cr

variable {n : ℕ}

set_option maxHeartbeats 2000000 in
lemma q_data {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hopen : IsOpen Ω) {μ : ℝ}
    (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    {c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hc : ∀ i, EthierKurtz.BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, EthierKurtz.IsOutwardUnitNormal Ω x (normal x))
    {ε : ℝ} (hε : 0 < ε) (hob : ∀ x ∈ frontier Ω, ε ≤ ∑ i, c x i * normal x i)
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} (hx₀ : x₀ ∈ frontier Ω)
    (U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (h0D : (0 : EuclideanSpace ℝ (Fin n)) ∈ D)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : EthierKurtz.CTwiceHolder D μ u) (hu0 : u 0 = 0)
    (hDu0 : fderiv ℝ u 0 = 0) {ρ : ℝ}
    (hgraph : (fun x => U (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ) =
        (fun z : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)) :
            EuclideanSpace ℝ (Fin (n + 1)))) '' D) :
    ∃ s, 0 < s ∧ Metric.closedBall 0 s ⊆ D ∧
      (∀ i, LC1 μ (Metric.ball 0 s) (fun z => c (chX U x₀ u z) i)) ∧
      LC1 μ (Metric.ball 0 s) (dN U u fun i z => c (chX U x₀ u z) i) ∧
      ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s,
        ε / 2 ≤ |dN U u (fun i z => c (chX U x₀ u z) i) z| := by
  classical
  unfold EthierKurtz.BoundaryCOnceHolder at hc
  have hci := fun i => hc i x₀ hx₀
  choose ρi hρi Ui Di ui hDi h0Di hui hui0 hDui0 hconn hgi hHi using hci
  have hsi : ∀ i, ∃ t, 0 < t ∧ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t ⊆ Di i :=
    fun i => by
      obtain ⟨t, ht, hb⟩ := Metric.isOpen_iff.mp (hDi i) 0 (h0Di i)
      exact ⟨t / 2, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans hb⟩
  choose si hsi0 hsiD using hsi
  have hXc : ContinuousAt (chX U x₀ u) 0 :=
    (chX_contDiffOn U x₀ hu.1).continuousOn.continuousAt (hD.mem_nhds h0D)
  have hTc : ∀ i, ContinuousAt (trT (Ui i) U x₀ u) 0 := fun i =>
    (trT_contDiffOn U x₀ (Ui i) hu.1).continuousOn.continuousAt (hD.mem_nhds h0D)
  have hev1 : ∀ i, ∀ᶠ z in nhds (0 : EuclideanSpace ℝ (Fin n)), z ∈ D ∧
      trT (Ui i) U x₀ u z ∈ Metric.ball 0 (si i) ∧ chX U x₀ u z ∈ Metric.ball x₀ (ρi i) :=
    fun i => Filter.Eventually.and (hD.mem_nhds h0D) (Filter.Eventually.and
      ((hTc i).preimage_mem_nhds (Metric.isOpen_ball.mem_nhds
        (by rw [trT_zero U x₀ (Ui i) hu0]; exact Metric.mem_ball_self (hsi0 i))))
      (hXc.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds
        (by rw [chX_zero U x₀ hu0]; exact Metric.mem_ball_self (hρi i)))))
  have hid : ∀ i z, z ∈ D → chX U x₀ u z ∈ Metric.ball x₀ (ρi i) →
      c (chX U x₀ u z) i = c (x₀ + (Ui i).symm (WithLp.toLp 2 (Fin.lastCases
        (ui i (trT (Ui i) U x₀ u z)) (fun j => trT (Ui i) U x₀ u z j)))) i := by
    intro i z hz hzb
    rw [chX_other U x₀ (Ui i) (hgi i) (chX_mem U x₀ hgraph hz) hzb]
  have hgc : ∀ i, ContinuousAt (fun w => c (x₀ + (Ui i).symm (WithLp.toLp 2 (Fin.lastCases
        (ui i w) (fun j => w j)))) i) 0 := fun i =>
    (hHi i).1.continuousOn.continuousAt ((hDi i).mem_nhds (h0Di i))
  have hCc : ∀ i, ContinuousAt (fun z => c (chX U x₀ u z) i) 0 := fun i => by
    refine ((hgc i).comp_of_eq (hTc i) (trT_zero U x₀ (Ui i) hu0)).congr ?_
    filter_upwards [hev1 i] with z hz using (hid i z hz.1 hz.2.2).symm
  have hDuc : ContinuousAt (fderiv ℝ u) 0 :=
    (hu.1.continuousOn_fderiv_of_isOpen hD (by norm_num)).continuousAt (hD.mem_nhds h0D)
  have hdNc : ContinuousAt (dN U u fun i z => c (chX U x₀ u z) i) 0 := by
    show ContinuousAt (fun z => ∑ i, c (chX U x₀ u z) i * (lastL n (U (EuclideanSpace.single i 1)) -
      fderiv ℝ u z (projL n (U (EuclideanSpace.single i 1))))) 0
    exact tendsto_finset_sum _ fun i _ =>
      (hCc i).mul (continuousAt_const.sub (hDuc.clm_apply continuousAt_const))
  obtain ⟨κ, hκ, hlast⟩ := normal_last hopen (hnormal x₀ hx₀) U hD h0D
    ((hu.1.contDiffAt (hD.mem_nhds h0D)).differentiableAt (by norm_num)) hu0 hDu0 hgraph
  have hdN0 : dN U u (fun i z => c (chX U x₀ u z) i) 0 = κ * ∑ i, normal x₀ i * c x₀ i := by
    rw [← hlast (c x₀)]
    simp only [dN, hDu0, chX_zero U x₀ hu0, ContinuousLinearMap.zero_apply, sub_zero]
    have := clm_expand ((lastL n).comp (U.toContinuousLinearEquiv.toContinuousLinearMap)) (c x₀)
    simp only [ContinuousLinearMap.comp_apply, smul_eq_mul] at this
    exact this.symm
  have hk : |κ| = 1 := by
    have h2 : |κ| ^ 2 = 1 := by rw [sq_abs]; exact hκ
    have h3 := abs_nonneg κ
    nlinarith
  have hsw : ∑ i, normal x₀ i * c x₀ i = ∑ i, c x₀ i * normal x₀ i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hlow0 : ε ≤ |dN U u (fun i z => c (chX U x₀ u z) i) 0| := by
    rw [hdN0, abs_mul, hk, one_mul, hsw]
    exact le_abs.mpr (Or.inl (hob x₀ hx₀))
  have hlow : ∀ᶠ z in nhds (0 : EuclideanSpace ℝ (Fin n)),
      ε / 2 < |dN U u (fun i z => c (chX U x₀ u z) i) z| :=
    (continuous_abs.continuousAt.comp hdNc).eventually (lt_mem_nhds (by
      show ε / 2 < |dN U u (fun i z => c (chX U x₀ u z) i) 0|
      linarith))
  obtain ⟨r, hr, hball⟩ :=
    Metric.eventually_nhds_iff.mp ((Filter.eventually_all.mpr hev1).and hlow)
  have hS : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 2), dist z 0 < r :=
    fun z hz => by rw [Metric.mem_ball] at hz; linarith
  have hsD : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (r / 2) ⊆ D := fun z hz => by
    rw [Metric.mem_closedBall] at hz
    exact ((hball (show dist z 0 < r by linarith)).1 0).1
  have hCi : ∀ i, LC1 μ (Metric.ball 0 (r / 2)) (fun z => c (chX U x₀ u z) i) := fun i => by
    obtain ⟨hTd, -, hTD, L, hL0, hL⟩ := c2_ball hμ hμ1 hD (trT_contDiffOn U x₀ (Ui i) hu.1) hsD
    have hcomp := LC1.comp_basis hμ.le (LC1.of_conce hμ hμ1 (hDi i) (hHi i) (hsiD i)) hTd
      (fun z hz => ((hball (hS z hz)).1 i).2.1) L hL0 hL (fun k => hTD.eval (HBon.const _))
    exact LC1.congr_open Metric.isOpen_ball hcomp fun z hz =>
      (hid i z ((hball (hS z hz)).1 i).1 ((hball (hS z hz)).1 i).2.2).symm
  refine ⟨r / 2, by positivity, hsD, hCi, ?_, fun z hz => (hball (hS z hz)).2.le⟩
  show LC1 μ _ (fun z => ∑ i, c (chX U x₀ u z) i * (lastL n (U (EuclideanSpace.single i 1)) -
      fderiv ℝ u z (projL n (U (EuclideanSpace.single i 1)))))
  exact LC1.sum Finset.univ fun i _ =>
    LC1.mul (hCi i) (LC1.sub (LC1.const _) (LC1.du hμ hμ1 hu hD hsD _))

set_option maxHeartbeats 1000000 in
lemma h_data {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    {c : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (x₀ : EuclideanSpace ℝ (Fin (n + 1)))
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : EthierKurtz.CTwiceHolder D μ u) {s : ℝ}
    (hsD : Metric.closedBall 0 s ⊆ D)
    (hCi : ∀ i, LC1 μ (Metric.ball 0 s) (fun z => c (chX U x₀ u z) i))
    (hdN : LC1 μ (Metric.ball 0 s) (dN U u fun i z => c (chX U x₀ u z) i)) {m : ℝ} (hm : 0 < m)
    (hlow : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s,
      m ≤ |dN U u (fun i z => c (chX U x₀ u z) i) z|)
    {F ξ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hξ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ) :
    LC1 μ (Metric.ball 0 s) (fun z => -(ξ (chX U x₀ u z) *
      fderiv ℝ F (chX U x₀ u z) (c (chX U x₀ u z))) /
        dN U u (fun i z => c (chX U x₀ u z) i) z) := by
  have hX := chX_contDiffOn U x₀ hu.1
  have hξX : LC1 μ (Metric.ball 0 s) (fun z => ξ (chX U x₀ u z)) :=
    LC1.of_c2 hμ hμ1 hD ((hξ.of_le (WithTop.coe_le_coe.mpr le_top)).comp_contDiffOn hX) hsD
  have hFX : ∀ k, LC1 μ (Metric.ball 0 s)
      (fun z => fderiv ℝ F (chX U x₀ u z) (EuclideanSpace.single k 1)) := fun k =>
    LC1.of_c2 hμ hμ1 hD (((hF.fderiv_right (m := 2) (WithTop.coe_le_coe.mpr le_top)).clm_apply
      contDiff_const).comp_contDiffOn hX) hsD
  have hsum := LC1.sum Finset.univ fun k (_ : k ∈ Finset.univ) => LC1.mul (hCi k) (hFX k)
  have hall := LC1.mul (LC1.mul (LC1.const (-1)) (LC1.mul hξX hsum)) (LC1.inv hm hdN hlow)
  refine LC1.congr_open Metric.isOpen_ball hall fun z _ => ?_
  rw [clm_expand (fderiv ℝ F (chX U x₀ u z)) (c (chX U x₀ u z))]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

end Pd67abb68Cs

/-! C2e L7 pieces: chart geometry at frontier/interior points and the boundary formula. -/

namespace Pd67abb68Ct

open Pd67abb68C2h Pd67abb68C2j Pd67abb68Ch Pd67abb68Cl Pd67abb68Cn Pd67abb68Cr

variable {n : ℕ} (U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
  (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (u : EuclideanSpace ℝ (Fin n) → ℝ)

lemma frontier_chart {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {D : Set (EuclideanSpace ℝ (Fin n))} {ρ : ℝ}
    (hgraph : (fun x => U (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ) =
        (fun z : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)) :
            EuclideanSpace ℝ (Fin (n + 1)))) '' D)
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ frontier Ω) (hxb : x ∈ Metric.ball x₀ ρ) :
    chartΦ U x₀ u x = (projL n (U (x - x₀)), 0) ∧ chX U x₀ u (projL n (U (x - x₀))) = x ∧
      projL n (U (x - x₀)) ∈ D := by
  have hm : U (x - x₀) ∈ (fun x => U (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ) :=
    ⟨x, ⟨hx, hxb⟩, rfl⟩
  rw [hgraph] at hm
  obtain ⟨w, hwD, hw⟩ := hm
  simp only at hw
  have hwz : w = projL n (U (x - x₀)) := by rw [← hw, projL_mk]
  rw [hwz] at hw hwD
  refine ⟨chartΦ_of_graph U x₀ u x _ hw.symm, ?_, hwD⟩
  rw [chX, graphJ_apply, hw, LinearIsometryEquiv.symm_apply_apply]
  abel

lemma side_of_open {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hopen : IsOpen Ω)
    {D : Set (EuclideanSpace ℝ (Fin n))} {ρ : ℝ}
    (hgraph : (fun x => U (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ) =
        (fun z : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)) :
            EuclideanSpace ℝ (Fin (n + 1)))) '' D)
    {r0 : ℝ} (hrD : Metric.closedBall 0 r0 ⊆ D)
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hxΩ : x ∈ Ω) (hxb : x ∈ Metric.ball x₀ r0) :
    (chartΦ U x₀ u x).2 ≠ 0 := by
  intro h0
  have hg := graph_of_chartΦ U x₀ u x h0
  have hz : (chartΦ U x₀ u x).1 ∈ D := hrD (Metric.ball_subset_closedBall (by
    show projL n (U (x - x₀)) ∈ _
    exact chartP_mem U x₀ hxb))
  have hm : U (x - x₀) ∈ (fun x => U (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ) := by
    rw [hgraph, hg]; exact ⟨_, hz, rfl⟩
  obtain ⟨x', ⟨hx'f, -⟩, hx'e⟩ := hm
  simp only at hx'e
  have hx' : x' = x := sub_left_inj.mp (U.injective hx'e)
  rw [hopen.frontier_eq] at hx'f
  exact hx'f.2 (hx' ▸ hxΩ)

lemma dN_eq (C : Fin (n + 1) → EuclideanSpace ℝ (Fin n) → ℝ) (z : EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin (n + 1))) (hC : ∀ i, C i z = w i) :
    dN U u C z = lastL n (U w) - fderiv ℝ u z (projL n (U w)) := by
  have := clm_expand ((lastL n).comp (U.toContinuousLinearEquiv.toContinuousLinearMap) -
    (fderiv ℝ u z).comp ((projL n).comp (U.toContinuousLinearEquiv.toContinuousLinearMap))) w
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, smul_eq_mul] at this
  rw [dN]
  refine Eq.trans ?_ this.symm
  exact Finset.sum_congr rfl fun i _ => by rw [hC i]; rfl

set_option maxHeartbeats 1000000 in
lemma bc_formula {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hu : ContDiffOn ℝ 2 u D)
    {ξ' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hξ' : Differentiable ℝ ξ')
    {g : EuclideanSpace ℝ (Fin n) × ℝ → ℝ} {q : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Differentiable ℝ g) (hg0 : ∀ z, g (z, 0) = 0)
    (hDg : ∀ z, fderiv ℝ g (z, 0) = q z • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hzD : projL n (U (x - x₀)) ∈ D)
    (hΦx : chartΦ U x₀ u x = (projL n (U (x - x₀)), 0)) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    fderiv ℝ (fun y => ξ' y * g (chartΦ U x₀ u y)) x v = ξ' x * q (projL n (U (x - x₀))) *
      (lastL n (U v) - fderiv ℝ u (projL n (U (x - x₀))) (projL n (U v))) := by
  have hud : DifferentiableAt ℝ u (projL n (U (x - x₀))) :=
    (hu.contDiffAt (hD.mem_nhds hzD)).differentiableAt (by norm_num)
  have hΦd := chartΦ_hasFDerivAt U x₀ u x hud
  have hcomp := ((hg (chartΦ U x₀ u x)).hasFDerivAt).comp x hΦd
  have h' : HasFDerivAt (fun y => ξ' y * g (chartΦ U x₀ u y)) _ x :=
    (hξ' x).hasFDerivAt.mul hcomp
  rw [h'.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, smul_eq_mul, Function.comp,
    hΦx, hg0, hDg, ContinuousLinearMap.coe_snd', ContinuousLinearMap.sub_apply, chartM_apply,
    chartN_apply, zero_mul, add_zero]
  ring

end Pd67abb68Ct

/-! C2e L7: assembly of the local oblique corrector (given the flat lift C2a as a hypothesis). -/

namespace Pd67abb68Cu

open Pd67abb68C2h Pd67abb68C2j Pd67abb68Ch Pd67abb68Cl Pd67abb68Cn Pd67abb68Cr Pd67abb68Ct

set_option maxHeartbeats 4000000 in
theorem corrector (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hc : ∀ i, EthierKurtz.BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, EthierKurtz.IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω, ε ≤ ∑ i, c x i * normal x i)
    (hlift : ∀ q : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 q → HasCompactSupport q →
      (∃ M : ℝ, ∀ x y, ‖fderiv ℝ q x - fderiv ℝ q y‖ ≤ M * ‖x - y‖ ^ μ) →
      ∀ δ : ℝ, 0 < δ →
      ∃ W : EuclideanSpace ℝ (Fin n) × ℝ → ℝ,
        ContDiff ℝ 1 W ∧ HasCompactSupport W ∧
        ContDiffOn ℝ 2 W {p | 0 < p.2} ∧
        (∀ z, W (z, 0) = 0) ∧
        (∀ z, fderiv ℝ W (z, 0) = q z • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) ∧
        (∀ p, |W p| ≤ δ) ∧
        ∃ K : ℝ, ∀ p p' : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → 0 < p'.2 →
          ‖fderiv ℝ (fderiv ℝ W) p - fderiv ℝ (fderiv ℝ W) p'‖ ≤ K * ‖p - p'‖ ^ μ) :
    ∀ x₀ ∈ frontier Ω, ∃ ρ : ℝ, 0 < ρ ∧
      ∀ F ξ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ → tsupport ξ ⊆ Metric.ball x₀ ρ →
        ∀ δ : ℝ, 0 < δ →
          ∃ V : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
            ContDiff ℝ 1 V ∧ HasCompactSupport V ∧ (∀ x, |V x| ≤ δ) ∧
            EthierKurtz.CTwiceHolder Ω μ V ∧
            ∀ x ∈ frontier Ω, fderiv ℝ V x (c x) = -(ξ x * fderiv ℝ F x (c x)) := by
  intro x₀ hx₀
  obtain ⟨hμ0, hμ1⟩ := hμ
  obtain ⟨ε, hε, hob⟩ := hoblique
  have hc0 := hc 0
  unfold EthierKurtz.BoundaryCOnceHolder at hc0
  obtain ⟨ρ1, hρ1, U, D, u, hD, h0D, hu, hu0, hDu0, -, hgraph, -⟩ := hc0 x₀ hx₀
  obtain ⟨s, hs, hsD, hCi, hdN, hlow⟩ :=
    Pd67abb68Cs.q_data hopen hμ0 hμ1 hc hnormal hε hob hx₀ U hD h0D hu hu0 hDu0 hgraph
  obtain ⟨r0, hr0pos, hr0s, hr0ρ⟩ : ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ s ∧ r0 ≤ ρ1 :=
    ⟨min s ρ1, lt_min hs hρ1, min_le_left _ _, min_le_right _ _⟩
  have hr0D : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r0 ⊆ D :=
    (Metric.closedBall_subset_closedBall hr0s).trans hsD
  obtain ⟨hΦc, hΦ1, hΦ2, L, hL0, hL⟩ := chart_props U x₀ u hμ0 hμ1 hu hD hr0D
  refine ⟨r0 / 2, by positivity, ?_⟩
  intro F ξ hF hξ hξs δ hδ
  obtain ⟨h, hhdef⟩ : ∃ h : EuclideanSpace ℝ (Fin n) → ℝ, h = fun z =>
      -(ξ (chX U x₀ u z) * fderiv ℝ F (chX U x₀ u z) (c (chX U x₀ u z))) /
        dN U u (fun i z => c (chX U x₀ u z) i) z := ⟨_, rfl⟩
  have hh : LC1 μ (Metric.ball 0 s) h := hhdef ▸
    Pd67abb68Cs.h_data hμ0 hμ1 U x₀ hD hu hsD hCi hdN (by positivity : 0 < ε / 2) hlow hF hξ
  let θ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨r0 / 2, 3 * r0 / 4, by positivity, by linarith⟩
  have hθs : tsupport (θ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ Metric.closedBall 0 (3 * r0 / 4) := by
    rw [θ.tsupport_eq]
  obtain ⟨hq1, hqs, hqH⟩ := Pd67abb68Cq.lift_data hμ0 hμ1 h θ (show 3 * r0 / 4 < s by linarith)
    (LC1.contDiffOn hμ0 Metric.isOpen_ball hh) hh.2.1 hh.2.2 θ.contDiff hθs
  obtain ⟨W, hW1, hWs, hW2, hW0, hDW, hWδ, hWK⟩ := hlift _ hq1 hqs hqH δ hδ
  obtain ⟨G, hG1, hGs, hG2, hG0, hDG, hGδ, K, hGK⟩ :=
    Pd67abb68C2e.two_sided_lift W _ μ δ hW1 hWs hW2 hW0 hDW hWδ hWK
  let ξ' : ContDiffBump x₀ := ⟨r0 / 2, 3 * r0 / 4, by positivity, by linarith⟩
  have htO : tsupport (ξ' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) ⊆ Metric.ball x₀ r0 := by
    rw [ξ'.tsupport_eq]
    exact Metric.closedBall_subset_ball (by show 3 * r0 / 4 < r0; linarith)
  have hzero : ∀ x, x ∉ tsupport (ξ' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) →
      (fun x => ξ' x * G (chartΦ U x₀ u x)) =ᶠ[nhds x] fun _ => (0:ℝ) := by
    intro x hxK
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxK] with y hy
    simp [hy]
  have hξ'd : Differentiable ℝ (ξ' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) :=
    (ξ'.contDiff (n := 1)).differentiable one_ne_zero
  refine ⟨fun x => ξ' x * G (chartΦ U x₀ u x), ?_, ?_, ?_, ?_, ?_⟩
  · -- C^1
    refine contDiff_iff_contDiffAt.mpr fun x => ?_
    by_cases hxK : x ∈ tsupport (ξ' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    · have h2 : ContDiffAt ℝ 1 (chartΦ U x₀ u) x :=
        (hΦc.contDiffAt (Metric.isOpen_ball.mem_nhds (htO hxK))).of_le (by norm_num)
      exact (ξ'.contDiff (n := 1)).contDiffAt.mul (hG1.contDiffAt.comp x h2)
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero x hxK)
  · exact ξ'.hasCompactSupport.mul_right
  · intro x
    calc |ξ' x * G (chartΦ U x₀ u x)| = |ξ' x| * |G (chartΦ U x₀ u x)| := abs_mul _ _
      _ ≤ 1 * δ := mul_le_mul (by rw [abs_of_nonneg ξ'.nonneg]; exact ξ'.le_one) (hGδ _)
          (abs_nonneg _) zero_le_one
      _ = δ := one_mul δ
  · -- C^{2,μ}
    have hgp := side_bounds hμ0 hμ1 G Pd67abb68C2e.isOpen_pos convex_pos far_pos hG1 hGs
      (hG2.mono fun p hp => ne_of_gt hp) K fun p hp p' hp' => hGK p p' (Or.inl ⟨hp, hp'⟩)
    have hgn := side_bounds hμ0 hμ1 G Pd67abb68C2e.isOpen_neg convex_neg far_neg hG1 hGs
      (hG2.mono fun p hp => ne_of_lt hp) K fun p hp p' hp' => hGK p p' (Or.inr ⟨hp, hp'⟩)
    exact Pd67abb68C2g.ctwice_of_chart Ω μ hμ0 hμ1 ξ' ξ'.contDiff ξ'.hasCompactSupport G hG2
      hgp hgn (chartΦ U x₀ u) (Metric.ball x₀ r0) Metric.isOpen_ball hΦc hΦ1 hΦ2 L hL0 hL htO
      fun x hx => side_of_open U x₀ u hopen hgraph hr0D hx.1 hx.2
  · -- the oblique boundary condition
    intro x hx
    have hξ0 : x ∉ Metric.ball x₀ (r0 / 2) → ξ x = 0 := fun hxb =>
      eq_zero_of_not_mem_tsupport' fun hxs => hxb (hξs hxs)
    by_cases hxO : x ∈ Metric.ball x₀ r0
    · obtain ⟨hΦx, hXx, hzD⟩ :=
        frontier_chart U x₀ u hgraph hx (Metric.ball_subset_ball hr0ρ hxO)
      rw [bc_formula U x₀ u hD hu.1 hξ'd (hG1.differentiable one_ne_zero) hG0 hDG hzD hΦx (c x),
        ← dN_eq U u (fun i z => c (chX U x₀ u z) i) _ (c x) (fun i => by
          show c (chX U x₀ u (projL n (U (x - x₀)))) i = c x i
          rw [hXx])]
      by_cases hξx : ξ x = 0
      · simp only [hhdef, hXx, hξx, zero_mul, neg_zero, zero_div, mul_zero]
      · have hxs : x ∈ Metric.ball x₀ (r0 / 2) := by
          by_contra hb; exact hξx (hξ0 hb)
        have hξ'1 : ξ' x = 1 := ξ'.one_of_mem_closedBall (Metric.ball_subset_closedBall hxs)
        have hzb := chartP_mem U x₀ hxs
        have hθ1 : θ (projL n (U (x - x₀))) = 1 :=
          θ.one_of_mem_closedBall (Metric.ball_subset_closedBall hzb)
        have hzs : projL n (U (x - x₀)) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s :=
          Metric.ball_subset_ball (by linarith) hzb
        have hne : dN U u (fun i z => c (chX U x₀ u z) i) (projL n (U (x - x₀))) ≠ 0 := by
          intro h0
          have := hlow _ hzs
          rw [h0, abs_zero] at this
          linarith
        simp only [hhdef, hXx, hξ'1, hθ1, one_mul]
        field_simp
    · have hxK : x ∉ tsupport (ξ' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) := fun h => hxO (htO h)
      rw [(hzero x hxK).fderiv_eq, hξ0 fun h => hxO (Metric.ball_subset_ball (by linarith) h)]
      simp

end Pd67abb68Cu

open scoped ContDiff in
open EthierKurtz in
theorem solution (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω, ε ≤ ∑ i, c x i * normal x i)
    (hlift : ∀ q : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 q → HasCompactSupport q →
      (∃ M : ℝ, ∀ x y, ‖fderiv ℝ q x - fderiv ℝ q y‖ ≤ M * ‖x - y‖ ^ μ) →
      ∀ δ : ℝ, 0 < δ →
      ∃ W : EuclideanSpace ℝ (Fin n) × ℝ → ℝ,
        ContDiff ℝ 1 W ∧ HasCompactSupport W ∧
        ContDiffOn ℝ 2 W {p | 0 < p.2} ∧
        (∀ z, W (z, 0) = 0) ∧
        (∀ z, fderiv ℝ W (z, 0) = q z • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) ∧
        (∀ p, |W p| ≤ δ) ∧
        ∃ K : ℝ, ∀ p p' : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → 0 < p'.2 →
          ‖fderiv ℝ (fderiv ℝ W) p - fderiv ℝ (fderiv ℝ W) p'‖ ≤ K * ‖p - p'‖ ^ μ) :
    ∀ x₀ ∈ frontier Ω, ∃ ρ : ℝ, 0 < ρ ∧
      ∀ F ξ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ → tsupport ξ ⊆ Metric.ball x₀ ρ →
        ∀ δ : ℝ, 0 < δ →
          ∃ V : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
            ContDiff ℝ 1 V ∧ HasCompactSupport V ∧ (∀ x, |V x| ≤ δ) ∧
            CTwiceHolder Ω μ V ∧
            ∀ x ∈ frontier Ω, fderiv ℝ V x (c x) = -(ξ x * fderiv ℝ F x (c x)) := by
  exact Pd67abb68Cu.corrector n Ω hopen μ hμ c normal hc hnormal hoblique hlift
