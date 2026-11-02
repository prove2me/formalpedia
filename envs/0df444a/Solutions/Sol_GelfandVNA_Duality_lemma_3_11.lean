-- Prove2me | solution 1 for GelfandVNA.Duality.lemma_3_11
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T02:23:27.685286+00:00
-- url     : https://prove2.me/submissions/3760d494-b769-4852-b572-31335a8bbbeb

import Mathlib
import Definitions.Def_GelfandVNA_Duality_VNA
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

universe u v



set_option autoImplicit false


namespace Gelfand38

open WeakDual

lemma complex_real_unit_iff (z : ℂ) :
    (z.im = 0 ∧ ‖z‖ ≤ 1) ↔
      ∀ t : ℝ, ‖z + (t : ℂ) * Complex.I‖ ≤ Real.sqrt (1 + t ^ 2) := by
  have hs (t : ℝ) : ‖z + (t : ℂ) * Complex.I‖ ^ 2 =
      z.re ^ 2 + (z.im + t) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, sub_self, add_zero,
      Complex.add_im, Complex.mul_im, mul_one]
    ring
  constructor
  · rintro ⟨hi, hn⟩ t
    have hn2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    have hz : z.re ^ 2 ≤ 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hi] at hn2
      nlinarith only [hn2]
    have hr := Real.sq_sqrt (show 0 ≤ 1 + t ^ 2 by positivity)
    have hns := hs t
    rw [hi, zero_add] at hns
    nlinarith [Real.sqrt_nonneg (1 + t ^ 2), norm_nonneg (z + (t : ℂ) * Complex.I)]
  · intro h
    have hi : z.im = 0 := by
      by_contra hne
      have hb := h z.im⁻¹
      have hr := Real.sq_sqrt (show 0 ≤ 1 + (z.im⁻¹) ^ 2 by positivity)
      have hn := norm_nonneg (z + (z.im⁻¹ : ℝ) * Complex.I)
      have hm : z.im * z.im⁻¹ = 1 := mul_inv_cancel₀ hne
      have hns := hs z.im⁻¹
      nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    exact ⟨hi, by simpa using h 0⟩

variable {A : Type*} [CommCStarAlgebra A]

lemma gelfand_norm (a : A) : ‖gelfandTransform ℂ A a‖ = ‖a‖ :=
  (gelfandTransform_isometry A).norm_map_of_map_zero (map_zero _) a

lemma gelfand_selfAdjoint_iff (a : A) :
    IsSelfAdjoint a ↔ ∀ χ : characterSpace ℂ A, (gelfandTransform ℂ A a χ).im = 0 := by
  constructor
  · intro h χ
    have he := congrArg (fun f : C(characterSpace ℂ A, ℂ) => f χ)
      (show gelfandTransform ℂ A (star a) = gelfandTransform ℂ A a from congrArg _ h)
    rw [gelfandTransform_map_star] at he
    have hi := congrArg Complex.im he
    change -(gelfandTransform ℂ A a χ).im = (gelfandTransform ℂ A a χ).im at hi
    linarith
  · intro h
    apply (gelfandTransform_isometry A).injective
    rw [gelfandTransform_map_star]
    ext χ
    apply Complex.ext
    · rfl
    · change -(gelfandTransform ℂ A a χ).im = (gelfandTransform ℂ A a χ).im
      rw [h χ, neg_zero]

lemma selfAdjoint_unit_iff_norm_balls (a : A) :
    (IsSelfAdjoint a ∧ ‖a‖ ≤ 1) ↔
      ∀ t : ℝ, ‖a + ((t : ℂ) * Complex.I) • (1 : A)‖ ≤ Real.sqrt (1 + t ^ 2) := by
  have he (t : ℝ) (χ : characterSpace ℂ A) :
      gelfandTransform ℂ A (a + ((t : ℂ) * Complex.I) • (1 : A)) χ =
        gelfandTransform ℂ A a χ + (t : ℂ) * Complex.I := by
    simp
  constructor
  · rintro ⟨ha, hn⟩ t
    rw [← gelfand_norm]
    apply (ContinuousMap.norm_le _ (Real.sqrt_nonneg _)).2
    intro χ
    rw [he]
    apply (complex_real_unit_iff _).1
    refine ⟨(gelfand_selfAdjoint_iff a).1 ha χ, ?_⟩
    exact (ContinuousMap.norm_coe_le_norm _ χ).trans ((gelfand_norm a).trans_le hn)
  · intro h
    have hv (χ : characterSpace ℂ A) :
        (gelfandTransform ℂ A a χ).im = 0 ∧ ‖gelfandTransform ℂ A a χ‖ ≤ 1 := by
      apply (complex_real_unit_iff _).2
      intro t
      rw [← he t χ]
      exact (ContinuousMap.norm_coe_le_norm _ χ).trans
        ((gelfand_norm _).trans_le (h t))
    refine ⟨(gelfand_selfAdjoint_iff a).2 (fun χ => (hv χ).1), ?_⟩
    rw [← gelfand_norm]
    exact (ContinuousMap.norm_le _ zero_le_one).2 (fun χ => (hv χ).2)


def PositiveUnit (a : A) : Prop :=
  ∀ χ : characterSpace ℂ A,
    (gelfandTransform ℂ A a χ).im = 0 ∧
    0 ≤ (gelfandTransform ℂ A a χ).re ∧ (gelfandTransform ℂ A a χ).re ≤ 1

lemma complex_positive_unit_iff (z : ℂ) :
    (z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1) ↔
      ((z + z - 1).im = 0 ∧ ‖z + z - 1‖ ≤ 1) := by
  have hi : (z + z - 1).im = 2 * z.im := by simp; ring
  have hn : ‖z + z - 1‖ ^ 2 = (2 * z.re - 1) ^ 2 + (2 * z.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.sub_im,
      Complex.add_im, Complex.one_im, sub_zero]
    ring
  constructor
  · rintro ⟨him, h0, h1⟩
    refine ⟨by rw [hi, him, mul_zero], ?_⟩
    rw [him, mul_zero, zero_pow (by decide), add_zero] at hn
    nlinarith [norm_nonneg (z + z - 1)]
  · rintro ⟨him, hnorm⟩
    have him0 : z.im = 0 := by rw [hi] at him; linarith
    refine ⟨him0, ?_, ?_⟩ <;>
      nlinarith [norm_nonneg (z + z - 1), sq_nonneg (2 * z.im)]

lemma positiveUnit_iff_center (a : A) :
    PositiveUnit a ↔ IsSelfAdjoint (a + a - 1) ∧ ‖a + a - 1‖ ≤ 1 := by
  have he (χ : characterSpace ℂ A) :
      gelfandTransform ℂ A (a + a - 1) χ =
        gelfandTransform ℂ A a χ + gelfandTransform ℂ A a χ - 1 := by simp
  constructor
  · intro h
    have hv (χ : characterSpace ℂ A) := (complex_positive_unit_iff _).1 (h χ)
    refine ⟨(gelfand_selfAdjoint_iff _).2 ?_, ?_⟩
    · intro χ
      rw [he]
      exact (hv χ).1
    · rw [← gelfand_norm]
      apply (ContinuousMap.norm_le _ zero_le_one).2
      intro χ
      rw [he]
      exact (hv χ).2
  · rintro ⟨ha, hn⟩ χ
    apply (complex_positive_unit_iff _).2
    rw [← he]
    exact ⟨(gelfand_selfAdjoint_iff _).1 ha χ,
      (ContinuousMap.norm_coe_le_norm _ χ).trans ((gelfand_norm _).trans_le hn)⟩

lemma positiveUnit_norm_le {a : A} (ha : PositiveUnit a) : ‖a‖ ≤ 1 := by
  rw [← gelfand_norm]
  apply (ContinuousMap.norm_le _ zero_le_one).2
  intro χ
  obtain ⟨hi, h0, h1⟩ := ha χ
  have hs := Complex.sq_norm (gelfandTransform ℂ A a χ)
  rw [Complex.normSq_apply, hi] at hs
  nlinarith [norm_nonneg (gelfandTransform ℂ A a χ)]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma isClosed_normBall (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (c : A) (r : ℝ) :
    IsClosed {w : WeakDual ℂ X | ‖e (WeakDual.toStrongDual w) - c‖ ≤ r} := by
  convert WeakDual.isClosed_closedBall (e.symm c) r using 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
  rw [← e.norm_map (WeakDual.toStrongDual w - e.symm c), map_sub, e.apply_symm_apply]

lemma isClosed_positiveUnit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) :
    IsClosed {w : WeakDual ℂ X | PositiveUnit (e (WeakDual.toStrongDual w))} := by
  simp only [positiveUnit_iff_center, selfAdjoint_unit_iff_norm_balls, Set.ofPred_forall]
  apply isClosed_iInter
  intro t
  have hc := (isClosed_normBall e (1 - ((t : ℂ) * Complex.I) • (1 : A))
    (Real.sqrt (1 + t ^ 2))).preimage (continuous_id.add continuous_id)
  convert hc using 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  change (‖e (WeakDual.toStrongDual w) + e (WeakDual.toStrongDual w) - 1 +
    ((t : ℂ) * Complex.I) • (1 : A)‖ ≤ _) ↔
    (‖e (WeakDual.toStrongDual w + WeakDual.toStrongDual w) -
      (1 - ((t : ℂ) * Complex.I) • (1 : A))‖ ≤ _)
  rw [map_add]
  abel_nf

lemma isCompact_positiveUnit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) :
    IsCompact {w : WeakDual ℂ X | PositiveUnit (e (WeakDual.toStrongDual w))} := by
  apply (WeakDual.isCompact_closedBall (0 : StrongDual ℂ X) 1).of_isClosed_subset
    (isClosed_positiveUnit e)
  intro w hw
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  rw [← e.norm_map]
  exact positiveUnit_norm_le hw


def SpectralLE (a b : A) : Prop :=
  ∀ χ : characterSpace ℂ A,
    (gelfandTransform ℂ A a χ).re ≤ (gelfandTransform ℂ A b χ).re

lemma spectralLE_refl (a : A) : SpectralLE a a := fun _ => le_rfl

lemma spectralLE_trans {a b c : A} (hab : SpectralLE a b) (hbc : SpectralLE b c) :
    SpectralLE a c := fun χ => (hab χ).trans (hbc χ)

lemma spectralLE_antisymm {a b : A} (ha : PositiveUnit a) (hb : PositiveUnit b)
    (hab : SpectralLE a b) (hba : SpectralLE b a) : a = b := by
  apply (gelfandTransform_isometry A).injective
  ext χ
  apply Complex.ext
  · exact le_antisymm (hab χ) (hba χ)
  · exact (ha χ).1.trans (hb χ).1.symm

lemma positiveUnit_sub_iff {a b : A} (ha : PositiveUnit a) (hb : PositiveUnit b) :
    PositiveUnit (b - a) ↔ SpectralLE a b := by
  have he (χ : characterSpace ℂ A) :
      gelfandTransform ℂ A (b - a) χ =
        gelfandTransform ℂ A b χ - gelfandTransform ℂ A a χ := by simp
  constructor
  · intro h χ
    have ht := (h χ).2.1
    rw [he, Complex.sub_re] at ht
    linarith
  · intro h χ
    rw [he, Complex.sub_im, Complex.sub_re, (ha χ).1, (hb χ).1, sub_self]
    exact ⟨rfl, sub_nonneg.mpr (h χ), by linarith [(hb χ).2.2, (ha χ).2.1]⟩

lemma isClosed_positiveUnit_lower (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (p : A) (hp : PositiveUnit p) :
    IsClosed {w : WeakDual ℂ X |
      PositiveUnit (e (WeakDual.toStrongDual w)) ∧ SpectralLE p (e (WeakDual.toStrongDual w))} := by
  have ht := (isClosed_positiveUnit e).preimage
    (continuous_id.sub (continuous_const : Continuous (fun _ : WeakDual ℂ X =>
      StrongDual.toWeakDual (e.symm p))))
  have he : {w : WeakDual ℂ X | PositiveUnit (e (WeakDual.toStrongDual w)) ∧
      SpectralLE p (e (WeakDual.toStrongDual w))} =
      {w : WeakDual ℂ X | PositiveUnit (e (WeakDual.toStrongDual w))} ∩
      (fun w : WeakDual ℂ X => w - StrongDual.toWeakDual (e.symm p)) ⁻¹'
        {w : WeakDual ℂ X | PositiveUnit (e (WeakDual.toStrongDual w))} := by
    ext w
    change (_ ∧ _) ↔ (_ ∧ PositiveUnit (e (WeakDual.toStrongDual w - e.symm p)))
    rw [map_sub, e.apply_symm_apply]
    exact and_congr_right (fun hw => (positiveUnit_sub_iff hp hw).symm)
  rw [he]
  exact (isClosed_positiveUnit e).inter ht

lemma isClosed_positiveUnit_upper (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (p : A) (hp : PositiveUnit p) :
    IsClosed {w : WeakDual ℂ X |
      PositiveUnit (e (WeakDual.toStrongDual w)) ∧ SpectralLE (e (WeakDual.toStrongDual w)) p} := by
  have ht := (isClosed_positiveUnit e).preimage
    ((continuous_const : Continuous (fun _ : WeakDual ℂ X =>
      StrongDual.toWeakDual (e.symm p))).sub continuous_id)
  have he : {w : WeakDual ℂ X | PositiveUnit (e (WeakDual.toStrongDual w)) ∧
      SpectralLE (e (WeakDual.toStrongDual w)) p} =
      {w : WeakDual ℂ X | PositiveUnit (e (WeakDual.toStrongDual w))} ∩
      (fun w : WeakDual ℂ X => StrongDual.toWeakDual (e.symm p) - w) ⁻¹'
        {w : WeakDual ℂ X | PositiveUnit (e (WeakDual.toStrongDual w))} := by
    ext w
    change (_ ∧ _) ↔ (_ ∧ PositiveUnit (e (e.symm p - WeakDual.toStrongDual w)))
    rw [map_sub, e.apply_symm_apply]
    exact and_congr_right (fun hw => (positiveUnit_sub_iff hw hp).symm)
  rw [he]
  exact (isClosed_positiveUnit e).inter ht


end Gelfand38


namespace Gelfand38

open WeakDual Set

variable {A : Type*} [CommCStarAlgebra A]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem exists_positive_lub (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    {ι : Type*} [Nonempty ι] (f : ι → A) (hf : ∀ i, PositiveUnit (f i))
    (hd : Directed SpectralLE f) :
    ∃ a : A, PositiveUnit a ∧ (∀ i, SpectralLE (f i) a) ∧
      ∀ b : A, PositiveUnit b → (∀ i, SpectralLE (f i) b) → SpectralLE a b := by
  classical
  let lift : A → WeakDual ℂ X := fun a => StrongDual.toWeakDual (e.symm a)
  let eval : WeakDual ℂ X → A := fun w => e (WeakDual.toStrongDual w)
  have hlift (a : A) : eval (lift a) = a := e.apply_symm_apply a
  let K : Set (WeakDual ℂ X) := {w | PositiveUnit (eval w)}
  have hKc : IsCompact K := isCompact_positiveUnit e
  have hKcl : IsClosed K := isClosed_positiveUnit e
  let tail : ι → Set (WeakDual ℂ X) := fun i =>
    {w | ∃ j, SpectralLE (f i) (f j) ∧ w = lift (f j)}
  have htK (i : ι) : closure (tail i) ⊆ K := by
    apply closure_minimal _ hKcl
    rintro w ⟨j, hij, rfl⟩
    change PositiveUnit (eval (lift (f j)))
    rw [hlift]
    exact hf j
  have htd : Directed (· ⊇ ·) (fun i => closure (tail i)) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hd i j
    refine ⟨k, closure_mono ?_, closure_mono ?_⟩
    · rintro w ⟨l, hkl, hw⟩
      exact ⟨l, spectralLE_trans hik hkl, hw⟩
    · rintro w ⟨l, hkl, hw⟩
      exact ⟨l, spectralLE_trans hjk hkl, hw⟩
  have htn (i : ι) : (closure (tail i)).Nonempty :=
    ⟨lift (f i), subset_closure ⟨i, spectralLE_refl _, rfl⟩⟩
  obtain ⟨w, hw⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun i => closure (tail i)) htd htn
    (fun i => hKc.of_isClosed_subset isClosed_closure (htK i))
    (fun _ => isClosed_closure)
  have hw' : ∀ i, w ∈ closure (tail i) := mem_iInter.mp hw
  refine ⟨eval w, htK (Classical.arbitrary ι) (hw' _), ?_, ?_⟩
  · intro i
    have hc : closure (tail i) ⊆ {w | PositiveUnit (eval w) ∧ SpectralLE (f i) (eval w)} := by
      apply closure_minimal _ (isClosed_positiveUnit_lower e (f i) (hf i))
      rintro w ⟨j, hij, rfl⟩
      change PositiveUnit (eval (lift (f j))) ∧ SpectralLE (f i) (eval (lift (f j)))
      rw [hlift]
      exact ⟨hf j, hij⟩
    exact (hc (hw' i)).2
  · intro b hb hub
    have hc : closure (tail (Classical.arbitrary ι)) ⊆
        {w | PositiveUnit (eval w) ∧ SpectralLE (eval w) b} := by
      apply closure_minimal _ (isClosed_positiveUnit_upper e b hb)
      rintro w ⟨j, hij, rfl⟩
      change PositiveUnit (eval (lift (f j))) ∧ SpectralLE (eval (lift (f j))) b
      rw [hlift]
      exact ⟨hf j, hub j⟩
    exact (hc (hw' _)).2


end Gelfand38


namespace Gelfand38

open WeakDual GelfandVNA.Duality

variable {A : Type*} [CommCStarAlgebra A]

lemma projection_value_zero_or_one (p : ProjAlg A) (χ : characterSpace ℂ A) :
    gelfandTransform ℂ A p.val χ = 0 ∨ gelfandTransform ℂ A p.val χ = 1 := by
  apply IsIdempotentElem.iff_eq_zero_or_one.mp
  have h := congrArg (fun a : A => gelfandTransform ℂ A a χ) p.isStarProjection.1
  change gelfandTransform ℂ A p.val χ * gelfandTransform ℂ A p.val χ =
    gelfandTransform ℂ A p.val χ
  simpa only [map_mul, ContinuousMap.mul_apply] using h

lemma projection_positiveUnit (p : ProjAlg A) : PositiveUnit p.val := by
  intro χ
  rcases projection_value_zero_or_one p χ with h | h <;> simp [h]

lemma projection_le_iff (p q : ProjAlg A) :
    p ≤ q ↔ SpectralLE p.val q.val := by
  change p.val * q.val = p.val ↔ _
  constructor
  · intro h χ
    have hm := congrArg (fun a : A => gelfandTransform ℂ A a χ) h
    have hp := projection_value_zero_or_one p χ
    have hq := projection_value_zero_or_one q χ
    simp only [map_mul, ContinuousMap.mul_apply] at hm
    rcases hp with hp | hp <;> rcases hq with hq | hq <;> simp_all
  · intro h
    apply (gelfandTransform_isometry A).injective
    ext χ
    have hh := h χ
    have hp := projection_value_zero_or_one p χ
    have hq := projection_value_zero_or_one q χ
    simp only [map_mul, ContinuousMap.mul_apply]
    rcases hp with hp | hp <;> rcases hq with hq | hq <;> simp_all
    norm_num at *

lemma positiveUnit_square {a : A} (ha : PositiveUnit a) : PositiveUnit (a * a) := by
  intro χ
  obtain ⟨hi, h0, h1⟩ := ha χ
  simp only [map_mul, ContinuousMap.mul_apply, Complex.mul_im, Complex.mul_re,
    hi, mul_zero, zero_mul, add_zero, sub_zero]
  exact ⟨trivial, mul_self_nonneg _, by nlinarith⟩

lemma positiveUnit_square_le {a : A} (ha : PositiveUnit a) : SpectralLE (a * a) a := by
  intro χ
  obtain ⟨hi, h0, h1⟩ := ha χ
  simp only [map_mul, ContinuousMap.mul_apply, Complex.mul_re, hi, mul_zero, sub_zero]
  nlinarith

lemma projection_le_square (p : ProjAlg A) {a : A} (ha : PositiveUnit a)
    (hpa : SpectralLE p.val a) : SpectralLE p.val (a * a) := by
  intro χ
  obtain ⟨hi, h0, h1⟩ := ha χ
  have hp := hpa χ
  simp only [map_mul, ContinuousMap.mul_apply, Complex.mul_re, hi, mul_zero, sub_zero]
  rcases projection_value_zero_or_one p χ with he | he
  · rw [he, Complex.zero_re]
    exact mul_self_nonneg _
  · rw [he, Complex.one_re] at hp ⊢
    nlinarith

theorem projections_complete [WStarAlgebra A] (s : Set (ProjAlg A)) :
    ∃ p : ProjAlg A, IsLUB s p := by
  classical
  obtain ⟨X, hX, hN, hC, ⟨e⟩⟩ := WStarAlgebra.exists_predual (M := A)
  let f : Finset s → ProjAlg A := fun t => t.sup Subtype.val
  have hf : ∀ t : Finset s, PositiveUnit (f t).val := fun t => projection_positiveUnit (f t)
  have hd : Directed SpectralLE (fun t : Finset s => (f t).val) := by
    intro t u
    refine ⟨t ∪ u, (projection_le_iff _ _).1 ?_, (projection_le_iff _ _).1 ?_⟩
    · exact Finset.sup_mono Finset.subset_union_left
    · exact Finset.sup_mono Finset.subset_union_right
  obtain ⟨a, ha, hub, hleast⟩ := exists_positive_lub e (fun t => (f t).val) hf hd
  have haa : a * a = a := spectralLE_antisymm (positiveUnit_square ha) ha
    (positiveUnit_square_le ha)
    (hleast (a * a) (positiveUnit_square ha) (fun t => projection_le_square (f t) ha (hub t)))
  have hstar : IsSelfAdjoint a := (gelfand_selfAdjoint_iff a).2 (fun χ => (ha χ).1)
  let p : ProjAlg A := ⟨⟨a, haa⟩, hstar⟩
  refine ⟨p, ?_, ?_⟩
  · intro q hq
    apply (projection_le_iff q p).2
    change SpectralLE q.val a
    have hh := hub {⟨q, hq⟩}
    simpa [f] using hh
  · intro q hq
    apply (projection_le_iff p q).2
    apply hleast q.val (projection_positiveUnit q)
    intro t
    apply (projection_le_iff (f t) q).1
    exact Finset.sup_le (fun r hr => hq r.property)


end Gelfand38


open WeakDual

open GelfandVNA.Duality




set_option autoImplicit false

namespace Gelfand39

open Gelfand38 GelfandVNA.Duality WeakDual Set Filter
open QAlgorithms.Papers.Independent.Support21.P20
open scoped Topology

variable {A : Type*} [CommCStarAlgebra A]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma projection_isLUB_positive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (s : Set (ProjAlg A)) (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s)
    (a : ProjAlg A) (ha : IsLUB s a) :
    ∀ b : A, PositiveUnit b → (∀ p ∈ s, SpectralLE p.val b) → SpectralLE a.val b := by
  classical
  let : Nonempty s := hs.to_subtype
  have hdir : Directed SpectralLE (fun p : s => p.val.val) := by
    intro p q
    obtain ⟨r, hr, hpr, hqr⟩ := hd p.val p.property q.val q.property
    exact ⟨⟨r, hr⟩, (projection_le_iff _ _).1 hpr, (projection_le_iff _ _).1 hqr⟩
  obtain ⟨c, hc, hub, hleast⟩ := exists_positive_lub e (fun p : s => p.val.val)
    (fun p => projection_positiveUnit p.val) hdir
  have hcc : c * c = c := spectralLE_antisymm (positiveUnit_square hc) hc
    (positiveUnit_square_le hc)
    (hleast (c * c) (positiveUnit_square hc) (fun p => projection_le_square p.val hc (hub p)))
  let q : ProjAlg A := ⟨⟨c, hcc⟩, (gelfand_selfAdjoint_iff c).2 (fun χ => (hc χ).1)⟩
  have hq : IsLUB s q := by
    constructor
    · intro p hp
      exact (projection_le_iff p q).2 (hub ⟨p, hp⟩)
    · intro p hp
      exact (projection_le_iff q p).2
        (hleast p.val (projection_positiveUnit p)
          (fun r => (projection_le_iff r.val p).1 (hp r.property)))
  have hqa : q = a := hq.unique ha
  intro b hb hub'
  rw [← hqa]
  exact hleast b hb (fun p => hub' p.val p.property)

theorem projections_tendsto_predual (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (s : Set (ProjAlg A)) (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s)
    (a : ProjAlg A) (ha : IsLUB s a) :
    Tendsto (fun p : s => StrongDual.toWeakDual (e.symm p.val.val)) atTop
      (𝓝 (StrongDual.toWeakDual (e.symm a.val))) := by
  classical
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := hd.isDirectedOrder
  let lift : A → WeakDual ℂ X := fun a => StrongDual.toWeakDual (e.symm a)
  let eval : WeakDual ℂ X → A := fun w => e (WeakDual.toStrongDual w)
  have hlift (b : A) : eval (lift b) = b := e.apply_symm_apply b
  change Tendsto (fun p : s => lift p.val.val) atTop (𝓝 (lift a.val))
  apply (isCompact_positiveUnit e).tendsto_nhds_of_unique_mapClusterPt
  · exact Eventually.of_forall (fun p => by
      change PositiveUnit (eval (lift p.val.val))
      rw [hlift]
      exact projection_positiveUnit p.val)
  · intro w hw hcluster
    have hupper : ∀ p ∈ s, SpectralLE p.val (eval w) := by
      intro p hp
      have hc := (isClosed_positiveUnit_lower e p.val (projection_positiveUnit p)).mem_of_mapClusterPt
        hcluster
      apply (hc ?_).2
      filter_upwards [eventually_ge_atTop (⟨p, hp⟩ : s)] with q hq
      change PositiveUnit (eval (lift q.val.val)) ∧ SpectralLE p.val (eval (lift q.val.val))
      rw [hlift]
      exact ⟨projection_positiveUnit q.val, (projection_le_iff p q.val).1 hq⟩
    have hbelow : SpectralLE (eval w) a.val := by
      have hc := (isClosed_positiveUnit_upper e a.val (projection_positiveUnit a)).mem_of_mapClusterPt
        hcluster
      apply (hc ?_).2
      apply Eventually.of_forall
      intro p
      change PositiveUnit (eval (lift p.val.val)) ∧ SpectralLE (eval (lift p.val.val)) a.val
      rw [hlift]
      exact ⟨projection_positiveUnit p.val, (projection_le_iff p.val a).1 (ha.1 p.property)⟩
    have habove := projection_isLUB_positive e s hs hd a ha (eval w) hw hupper
    have heq : eval w = a.val := spectralLE_antisymm hw (projection_positiveUnit a) hbelow habove
    apply WeakDual.toStrongDual.injective
    apply e.injective
    change eval w = eval (lift a.val)
    rw [hlift]
    exact heq

theorem normal_restrict_isContinuousValuation (φ : A → ℂ) (hφ : IsNormalFunctional φ) :
    IsContinuousValuation (fun p : ProjAlg A => φ p.val) := by
  obtain ⟨X, hX, hN, hC, e, x, hφ⟩ := hφ
  have hzero : φ 0 = 0 := by simp [hφ]
  have hadd (a b : A) : φ (a + b) = φ a + φ b := by simp [hφ]
  constructor
  · constructor
    · exact hzero
    · intro p q
      rw [← hadd, ← hadd]
      apply congrArg φ
      change p.val + q.val = (p.val + q.val - p.val * q.val) + p.val * q.val
      abel
  · intro s a hs hd ha
    have hc : Continuous (fun w : WeakDual ℂ X => star (w x)) :=
      (WeakDual.eval_continuous x).star
    have ht := hc.continuousAt.tendsto.comp (projections_tendsto_predual e s hs hd a ha)
    simpa only [Function.comp_def, hφ, StrongDual.toWeakDual_apply] using ht


end Gelfand39


set_option autoImplicit false

namespace Gelfand311

open Gelfand38 Gelfand39 GelfandVNA.Duality WeakDual Set Filter
open QAlgorithms.Papers.Independent.Support21.P20
open scoped Topology

variable {A B : Type u} [CommCStarAlgebra A] [CommCStarAlgebra B]

lemma projection_ext {p q : ProjAlg A} (h : p.val = q.val) : p = q :=
  Subtype.ext (Subtype.ext h)

lemma projMap_inf (f : A →⋆ₐ[ℂ] B) (p q : ProjAlg A) :
    projMap f (p ⊓ q) = projMap f p ⊓ projMap f q := by
  apply projection_ext
  exact map_mul f p.val q.val

lemma projMap_sup (f : A →⋆ₐ[ℂ] B) (p q : ProjAlg A) :
    projMap f (p ⊔ q) = projMap f p ⊔ projMap f q := by
  apply projection_ext
  change f (p.val + q.val - p.val * q.val) = f p.val + f q.val - f p.val * f q.val
  simp

lemma projMap_compl (f : A →⋆ₐ[ℂ] B) (p : ProjAlg A) :
    projMap f pᶜ = (projMap f p)ᶜ := by
  apply projection_ext
  change f (1 - p.val) = 1 - f p.val
  simp

lemma projMap_bot (f : A →⋆ₐ[ℂ] B) : projMap f ⊥ = ⊥ :=
  projection_ext (map_zero f)

lemma projMap_top (f : A →⋆ₐ[ℂ] B) : projMap f ⊤ = ⊤ :=
  projection_ext (map_one f)

lemma projMap_mono (f : A →⋆ₐ[ℂ] B) : Monotone (projMap f) := by
  intro p q hpq
  change p.val * q.val = p.val at hpq
  change f p.val * f q.val = f p.val
  rw [← map_mul, hpq]

lemma projMap_finset_sup (f : A →⋆ₐ[ℂ] B) {ι : Type*} (t : Finset ι) (g : ι → ProjAlg A) :
    projMap f (t.sup g) = t.sup (fun i => projMap f (g i)) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact projMap_bot f
  | @insert i t hit ih => simp only [Finset.sup_insert, projMap_sup, ih]

theorem projMap_directed_isLUB [WStarAlgebra B] (f : A →⋆ₐ[ℂ] B) (hf : IsNormalStarHom f)
    (s : Set (ProjAlg A)) (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s)
    (a : ProjAlg A) (ha : IsLUB s a) : IsLUB (projMap f '' s) (projMap f a) := by
  classical
  let t : Set (ProjAlg B) := projMap f '' s
  have ht : t.Nonempty := hs.image _
  have htd : DirectedOn (· ≤ ·) t := by
    rintro p ⟨p', hp', rfl⟩ q ⟨q', hq', rfl⟩
    obtain ⟨r, hr, hpr, hqr⟩ := hd p' hp' q' hq'
    exact ⟨projMap f r, ⟨r, hr, rfl⟩, projMap_mono f hpr, projMap_mono f hqr⟩
  obtain ⟨b, hb⟩ := projections_complete t
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := hd.isDirectedOrder
  let g : s → t := fun p => ⟨projMap f p.val, ⟨p.val, p.property, rfl⟩⟩
  have hg : Tendsto g atTop atTop := by
    apply Monotone.tendsto_atTop_atTop
    · intro p q hpq
      exact projMap_mono f hpq
    · rintro ⟨q, ⟨p, hp, rfl⟩⟩
      exact ⟨⟨p, hp⟩, le_rfl⟩
  obtain ⟨X, hX, hN, hC, ⟨e⟩⟩ := WStarAlgebra.exists_predual (M := B)
  have hval : (projMap f a).val = b.val := by
    apply e.symm.injective
    apply ContinuousLinearMap.ext
    intro x
    let φ : B → ℂ := fun z => star ((e.symm z) x)
    have hφ : IsNormalFunctional φ := ⟨X, hX, hN, hC, e, x, fun _ => rfl⟩
    have hsource := (normal_restrict_isContinuousValuation (φ ∘ f) (hf φ hφ)).2 s a hs hd ha
    have htarget := ((normal_restrict_isContinuousValuation φ hφ).2 t b ht htd hb).comp hg
    have hsource' : Tendsto (fun p : s => φ (f p.val.val)) atTop (𝓝 (φ (f a.val))) := hsource
    have htarget' : Tendsto (fun p : s => φ (f p.val.val)) atTop (𝓝 (φ b.val)) := htarget
    have heq := tendsto_nhds_unique hsource' htarget'
    exact star_injective heq
  have heq : projMap f a = b := projection_ext hval
  rw [heq]
  exact hb

theorem projMap_isLUB [WStarAlgebra B] (f : A →⋆ₐ[ℂ] B) (hf : IsNormalStarHom f)
    (s : Set (ProjAlg A)) (a : ProjAlg A) (ha : IsLUB s a) :
    IsLUB (projMap f '' s) (projMap f a) := by
  classical
  let joins : Finset s → ProjAlg A := fun t => t.sup Subtype.val
  let d : Set (ProjAlg A) := Set.range joins
  have hdne : d.Nonempty := ⟨joins ∅, ⟨∅, rfl⟩⟩
  have hddir : DirectedOn (· ≤ ·) d := by
    rintro p ⟨t, rfl⟩ q ⟨u, rfl⟩
    exact ⟨joins (t ∪ u), ⟨t ∪ u, rfl⟩,
      Finset.sup_mono Finset.subset_union_left, Finset.sup_mono Finset.subset_union_right⟩
  have hda : IsLUB d a := by
    constructor
    · rintro p ⟨t, rfl⟩
      exact Finset.sup_le (fun p hp => ha.1 p.property)
    · intro p hp
      apply ha.2
      intro q hq
      have hh := hp (show joins {⟨q, hq⟩} ∈ d from ⟨{⟨q, hq⟩}, rfl⟩)
      simpa [joins] using hh
  have hmap := projMap_directed_isLUB f hf d hdne hddir a hda
  constructor
  · rintro p ⟨q, hq, rfl⟩
    exact projMap_mono f (ha.1 hq)
  · intro p hp
    apply hmap.2
    rintro q ⟨r, ⟨t, rfl⟩, rfl⟩
    change projMap f (t.sup Subtype.val) ≤ p
    rw [projMap_finset_sup]
    exact Finset.sup_le (fun q hq => hp ⟨q.val, q.property, rfl⟩)

theorem normal_projMap_complete [WStarAlgebra A] [WStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) (hf : IsNormalStarHom f) :
    (∀ p q : ProjAlg A, projMap f (p ⊓ q) = projMap f p ⊓ projMap f q) ∧
    (∀ p q : ProjAlg A, projMap f (p ⊔ q) = projMap f p ⊔ projMap f q) ∧
    (∀ p : ProjAlg A, projMap f pᶜ = (projMap f p)ᶜ) ∧
    projMap f ⊥ = ⊥ ∧ projMap f ⊤ = ⊤ ∧
    (∀ (s : Set (ProjAlg A)) (a : ProjAlg A), IsLUB s a →
      IsLUB (projMap f '' s) (projMap f a)) :=
  ⟨projMap_inf f, projMap_sup f, projMap_compl f, projMap_bot f, projMap_top f,
    projMap_isLUB f hf⟩


end Gelfand311

/- Reused accepted proof by fizzyinc3, submission e058f284-c40d-45c0-b2f0-1f111145c267. Only a wrapper namespace and final theorem name change. -/

namespace Gelfand311Jordan
open QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal Topology


section g72gk34
variable {L : Type*} [Order.Frame L]

def g72gk34_Pos (ν : L → ℝ) (a : L) : Prop := ∀ b : L, b ≤ a → 0 ≤ ν b

lemma g72gk34_le_compl {x y : L} (h : x ⊓ y = ⊥) : x ≤ yᶜ :=
  le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr h)

lemma g72gk34_bot {ν : L → ℝ} (h : IsNormalValuation ν) : ν ⊥ = 0 := h.1.1.1

lemma g72gk34_disj {ν : L → ℝ} (h : IsNormalValuation ν) {x y : L} (hxy : x ⊓ y = ⊥) :
    ν (x ⊔ y) = ν x + ν y := by
  have := h.1.1.2 x y
  rw [hxy, g72gk34_bot h] at this
  linarith

lemma g72gk34_compl_eq {x b : L} (hx : x ≤ b) : (x ⊔ (b ⊓ xᶜ))ᶜ = bᶜ := by
  apply le_antisymm
  · rw [compl_sup]
    apply g72gk34_le_compl
    apply le_bot_iff.mp
    calc xᶜ ⊓ (b ⊓ xᶜ)ᶜ ⊓ b ≤ (b ⊓ xᶜ) ⊓ (b ⊓ xᶜ)ᶜ :=
          le_inf (le_inf inf_le_right (inf_le_left.trans inf_le_left))
            (inf_le_left.trans inf_le_right)
      _ = ⊥ := inf_compl_self _
  · exact compl_le_compl (sup_le hx inf_le_left)

lemma g72gk34_split {ν : L → ℝ} (h : IsNormalValuation ν) {x b : L} (hx : x ≤ b) :
    ν b = ν x + ν (b ⊓ xᶜ) := by
  have h1 : ν b = ν (x ⊔ (b ⊓ xᶜ)) := by
    rw [← h.2 b, ← g72gk34_compl_eq hx, h.2]
  rw [h1, g72gk34_disj h]
  apply le_bot_iff.mp
  calc x ⊓ (b ⊓ xᶜ) ≤ x ⊓ xᶜ := inf_le_inf_left _ inf_le_right
    _ = ⊥ := inf_compl_self _

lemma g72gk34_pos_bot (ν : L → ℝ) (h : IsNormalValuation ν) : g72gk34_Pos ν ⊥ := by
  intro b hb
  rw [le_bot_iff.mp hb, g72gk34_bot h]

lemma g72gk34_pos_sup {ν : L → ℝ} (h : IsNormalValuation ν) {a1 a2 : L}
    (h1 : g72gk34_Pos ν a1) (h2 : g72gk34_Pos ν a2) : g72gk34_Pos ν (a1 ⊔ a2) := by
  intro b hb
  set x := b ⊓ a1 with hxdef
  set y := b ⊓ xᶜ ⊓ a2 with hydef
  have e1 := g72gk34_split h (x := x) (b := b) inf_le_left
  have e2 := g72gk34_split h (x := y) (b := b ⊓ xᶜ) inf_le_left
  have hw : b ⊓ xᶜ ⊓ yᶜ = ⊥ := by
    apply le_bot_iff.mp
    have hw1 : b ⊓ xᶜ ⊓ yᶜ = (b ⊓ xᶜ ⊓ yᶜ) ⊓ (a1 ⊔ a2) :=
      (inf_eq_left.mpr ((inf_le_left.trans inf_le_left).trans hb)).symm
    rw [hw1, inf_sup_left]
    apply sup_le
    · calc b ⊓ xᶜ ⊓ yᶜ ⊓ a1 ≤ x ⊓ xᶜ :=
            le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left)) inf_le_right)
              (inf_le_left.trans (inf_le_left.trans inf_le_right))
        _ = ⊥ := inf_compl_self _
    · calc b ⊓ xᶜ ⊓ yᶜ ⊓ a2 ≤ y ⊓ yᶜ :=
            le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
              (inf_le_left.trans inf_le_right)
        _ = ⊥ := inf_compl_self _
  rw [hw, g72gk34_bot h] at e2
  have p1 : 0 ≤ ν x := h1 x inf_le_right
  have p2 : 0 ≤ ν y := h2 y inf_le_right
  linarith

lemma g72gk34_isDir {s : Set L} (hd : DirectedOn (· ≤ ·) s) : IsDirected s (· ≤ ·) :=
  ⟨fun x y => by
    obtain ⟨z, hz, h1, h2⟩ := hd x x.2 y y.2
    exact ⟨⟨z, hz⟩, h1, h2⟩⟩

lemma g72gk34_lim_ge {ν : L → ℝ} (h : IsNormalValuation ν) {s : Set L} {a : L}
    (hne : s.Nonempty) (hd : DirectedOn (· ≤ ·) s) (hl : IsLUB s a)
    (hp : ∀ b ∈ s, 0 ≤ ν b) : 0 ≤ ν a := by
  haveI : Nonempty s := hne.to_subtype
  haveI := g72gk34_isDir hd
  exact ge_of_tendsto' (h.1.2 s a hne hd hl) (fun b => hp b b.2)

lemma g72gk34_carrier_pos {ν : L → ℝ} (h : IsNormalValuation ν) :
    g72gk34_Pos ν (positiveCarrier ν) := by
  intro b hb
  let s : Set L := {z | ∃ a, g72gk34_Pos ν a ∧ z = b ⊓ a}
  apply g72gk34_lim_ge h (s := s) (a := b)
  · exact ⟨b ⊓ ⊥, ⊥, g72gk34_pos_bot ν h, rfl⟩
  · rintro _ ⟨a1, h1, rfl⟩ _ ⟨a2, h2, rfl⟩
    exact ⟨b ⊓ (a1 ⊔ a2), ⟨a1 ⊔ a2, g72gk34_pos_sup h h1 h2, rfl⟩,
      inf_le_inf_left _ le_sup_left, inf_le_inf_left _ le_sup_right⟩
  · constructor
    · rintro _ ⟨a, _, rfl⟩
      exact inf_le_left
    · intro u hu
      have : b = b ⊓ positiveCarrier ν := (inf_eq_left.mpr hb).symm
      rw [this, positiveCarrier, inf_sSup_eq]
      exact iSup₂_le fun a ha => hu ⟨a, ha, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ha _ inf_le_right

lemma g72gk34_pos_iff {ν : L → ℝ} (h : IsNormalValuation ν) (a : L) :
    g72gk34_Pos ν a ↔ a ≤ positiveCarrier ν :=
  ⟨fun ha => le_sSup ha, fun ha b hb => g72gk34_carrier_pos h b (hb.trans ha)⟩

lemma g72gk34_choose {ν : L → ℝ} (h : IsNormalValuation ν) (r : L) :
    ∃ x ≤ r, ∀ y ≤ r, min 1 (-ν y) ≤ 2 * (-ν x) := by
  let S : Set ℝ := (fun y => min 1 (-ν y)) '' Set.Iic r
  have hS : BddAbove S := ⟨1, by rintro _ ⟨y, _, rfl⟩; exact min_le_left _ _⟩
  have hSn : S.Nonempty := ⟨_, r, le_refl r, rfl⟩
  by_cases hm : sSup S ≤ 0
  · refine ⟨⊥, bot_le, fun y hy => ?_⟩
    rw [g72gk34_bot h, neg_zero, mul_zero]
    exact (le_csSup hS ⟨y, hy, rfl⟩).trans hm
  · push_neg at hm
    obtain ⟨_, ⟨y0, hy0, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hSn (half_lt_self hm)
    refine ⟨y0, hy0, fun y hy => ?_⟩
    have h1 := le_csSup hS ⟨y, hy, rfl⟩
    have h2 : min 1 (-ν y0) ≤ -ν y0 := min_le_right _ _
    linarith

def g72gk34_seq (f : L → L) (b : L) : ℕ → L
  | 0 => ⊥
  | k + 1 => g72gk34_seq f b k ⊔ f (b ⊓ (g72gk34_seq f b k)ᶜ)

lemma g72gk34_exhaust {ν : L → ℝ} (h : IsNormalValuation ν) (b : L) :
    ∃ d ≤ b, g72gk34_Pos ν d ∧ ν b ≤ ν d := by
  choose f hf1 hf2 using g72gk34_choose h
  set X := g72gk34_seq f b with hXdef
  have hXs : ∀ k, X (k + 1) = X k ⊔ f (b ⊓ (X k)ᶜ) := fun k => rfl
  have hX0 : X 0 = ⊥ := rfl
  have hXb : ∀ k, X k ≤ b := by
    intro k
    induction k with
    | zero => rw [hX0]; exact bot_le
    | succ k ih => rw [hXs]; exact sup_le ih ((hf1 _).trans inf_le_left)
  have hmono : Monotone X := monotone_nat_of_le_succ fun k => by rw [hXs]; exact le_sup_left
  have hstep : ∀ k, ν (X (k + 1)) = ν (X k) + ν (f (b ⊓ (X k)ᶜ)) := by
    intro k
    rw [hXs, g72gk34_disj h]
    apply le_bot_iff.mp
    calc X k ⊓ f (b ⊓ (X k)ᶜ) ≤ X k ⊓ (X k)ᶜ :=
          inf_le_inf_left _ ((hf1 _).trans inf_le_right)
      _ = ⊥ := inf_compl_self _
  have hxneg : ∀ k, ν (f (b ⊓ (X k)ᶜ)) ≤ 0 := by
    intro k
    have := hf2 (b ⊓ (X k)ᶜ) ⊥ bot_le
    rw [g72gk34_bot h, neg_zero, min_eq_right zero_le_one] at this
    linarith
  have hXneg : ∀ k, ν (X k) ≤ 0 := by
    intro k
    induction k with
    | zero => rw [hX0, g72gk34_bot h]
    | succ k ih => rw [hstep]; linarith [hxneg k]
  set Xi := ⨆ k, X k with hXi
  have hXib : Xi ≤ b := iSup_le hXb
  have hdir : DirectedOn (· ≤ ·) (Set.range X) := directedOn_range.mpr (hmono.directed_le)
  have hlub : IsLUB (Set.range X) Xi := isLUB_iSup
  have hT := h.1.2 (Set.range X) Xi (Set.range_nonempty X) hdir hlub
  let g : ℕ → Set.range X := fun k => ⟨X k, k, rfl⟩
  have hg : Tendsto g atTop atTop := by
    rw [tendsto_atTop_atTop]
    rintro ⟨_, j, rfl⟩
    exact ⟨j, fun k hk => hmono hk⟩
  have hTX : Tendsto (fun k => ν (X k)) atTop (𝓝 (ν Xi)) := hT.comp hg
  have hTX1 : Tendsto (fun k => ν (X (k + 1))) atTop (𝓝 (ν Xi)) :=
    hTX.comp (tendsto_add_atTop_nat 1)
  have hx0 : Tendsto (fun k => 2 * (-ν (f (b ⊓ (X k)ᶜ)))) atTop (𝓝 0) := by
    have : Tendsto (fun k => 2 * (-(ν (X (k + 1)) - ν (X k)))) atTop
        (𝓝 (2 * (-(ν Xi - ν Xi)))) := ((hTX1.sub hTX).neg).const_mul 2
    rw [sub_self, neg_zero, mul_zero] at this
    refine this.congr fun k => ?_
    rw [hstep k]; ring
  have hXile : ν Xi ≤ 0 := le_of_tendsto' hTX hXneg
  refine ⟨b ⊓ Xiᶜ, inf_le_left, ?_, ?_⟩
  · intro y hy
    have hk : ∀ k, min 1 (-ν y) ≤ 2 * (-ν (f (b ⊓ (X k)ᶜ))) := fun k =>
      hf2 _ y (hy.trans (inf_le_inf_left _ (compl_le_compl (le_iSup X k))))
    have hle : min 1 (-ν y) ≤ 0 := ge_of_tendsto' hx0 hk
    by_contra hc
    push_neg at hc
    have : 0 < min 1 (-ν y) := lt_min one_pos (by linarith)
    linarith
  · have := g72gk34_split h hXib
    linarith

lemma g72gk34_negative {ν : L → ℝ} (h : IsNormalValuation ν) {c : L}
    (hc : c ⊓ positiveCarrier ν = ⊥) {b : L} (hb : b ≤ c) : ν b ≤ 0 := by
  obtain ⟨d, hdb, hdp, hle⟩ := g72gk34_exhaust h b
  have h1 : d ≤ positiveCarrier ν := le_sSup hdp
  have h2 : d = ⊥ := le_bot_iff.mp (hc ▸ le_inf (hdb.trans hb) h1)
  rw [h2, g72gk34_bot h] at hle
  exact hle

lemma g72gk34_neg {ν : L → ℝ} (h : IsNormalValuation ν) :
    IsNormalValuation (fun a => -ν a) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp [g72gk34_bot h]
  · intro a b; have := h.1.1.2 a b; simp only; linarith
  · intro s a hne hd hl
    exact (h.1.2 s a hne hd hl).neg
  · intro a; simp only [h.2]

lemma g72gk34_regular {ν : L → ℝ} (h : IsNormalValuation ν) :
    (positiveCarrier ν)ᶜᶜ = positiveCarrier ν := by
  set P := positiveCarrier ν
  apply le_antisymm _ le_compl_compl
  apply le_sSup
  intro b hb
  have e := g72gk34_split h (x := b ⊓ P) (b := b) inf_le_left
  have hw : b ⊓ (b ⊓ P)ᶜ = ⊥ := by
    apply le_bot_iff.mp
    have hw1 : b ⊓ (b ⊓ P)ᶜ ≤ Pᶜ := by
      apply g72gk34_le_compl
      apply le_bot_iff.mp
      calc b ⊓ (b ⊓ P)ᶜ ⊓ P ≤ (b ⊓ P) ⊓ (b ⊓ P)ᶜ :=
            le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
              (inf_le_left.trans inf_le_right)
        _ = ⊥ := inf_compl_self _
    calc b ⊓ (b ⊓ P)ᶜ ≤ Pᶜ ⊓ Pᶜᶜ := le_inf hw1 (inf_le_left.trans hb)
      _ = ⊥ := inf_compl_self _
  rw [hw, g72gk34_bot h] at e
  have := g72gk34_carrier_pos h (b ⊓ P) inf_le_right
  linarith

lemma g72gk34_hahn {ν : L → ℝ} (h : IsNormalValuation ν) :
    (positiveCarrier ν ⊔ negativeCarrier ν)ᶜ = ⊥ := by
  set P := positiveCarrier ν
  set N := negativeCarrier ν
  set c := (P ⊔ N)ᶜ
  have hcP : c ⊓ P = ⊥ := by
    apply le_bot_iff.mp
    calc c ⊓ P ≤ Pᶜ ⊓ P := inf_le_inf_right _ (compl_le_compl le_sup_left)
      _ = ⊥ := compl_inf_self _
  have hcN : c ≤ N := by
    apply (g72gk34_pos_iff (g72gk34_neg h) c).mp
    intro b hb
    have := g72gk34_negative h hcP hb
    simp only; linarith
  apply le_bot_iff.mp
  calc c ≤ N ⊓ Nᶜ := le_inf hcN (compl_le_compl le_sup_right)
    _ = ⊥ := inf_compl_self _

lemma g72gk34_decomp {ν : L → ℝ} (h : IsNormalValuation ν) (a : L) :
    ν a = ν (positiveCarrier ν ⊓ a) + ν (negativeCarrier ν ⊓ a) := by
  set P := positiveCarrier ν
  set N := negativeCarrier ν
  have hQ := g72gk34_hahn h
  have h1 : ν a = ν ((P ⊔ N) ⊓ a) := by
    rw [← h.2 a, ← h.2 ((P ⊔ N) ⊓ a), compl_compl_inf_distrib, hQ, compl_bot, top_inf_eq]
  have h2 := h.1.1.2 (P ⊓ a) (N ⊓ a)
  rw [← inf_sup_right] at h2
  have hz1 : 0 ≤ ν (P ⊓ a ⊓ (N ⊓ a)) :=
    g72gk34_carrier_pos h _ (inf_le_left.trans inf_le_left)
  have hz2 : 0 ≤ -ν (P ⊓ a ⊓ (N ⊓ a)) :=
    g72gk34_carrier_pos (g72gk34_neg h) _ (inf_le_right.trans inf_le_left)
  linarith

lemma g72gk34_restrict {ν : L → ℝ} (h : IsNormalValuation ν) {Q : L} (hQ : Qᶜᶜ = Q) :
    IsNormalValuation (fun a => ν (Q ⊓ a)) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [inf_bot_eq, g72gk34_bot h]
  · intro a b
    have := h.1.1.2 (Q ⊓ a) (Q ⊓ b)
    simp only
    rw [← inf_sup_left, ← inf_inf_distrib_left] at this
    exact this
  · intro s a hne hd hl
    let s' : Set L := (fun b => Q ⊓ b) '' s
    have hne' : s'.Nonempty := hne.image _
    have hd' : DirectedOn (· ≤ ·) s' := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, h1, h2⟩ := hd x hx y hy
      exact ⟨Q ⊓ z, ⟨z, hz, rfl⟩, inf_le_inf_left _ h1, inf_le_inf_left _ h2⟩
    have hl' : IsLUB s' (Q ⊓ a) := by
      constructor
      · rintro _ ⟨x, hx, rfl⟩
        exact inf_le_inf_left _ (hl.1 hx)
      · intro u hu
        rw [← hl.sSup_eq, inf_sSup_eq]
        exact iSup₂_le fun b hb => hu ⟨b, hb, rfl⟩
    have hT := h.1.2 s' (Q ⊓ a) hne' hd' hl'
    let g : s → s' := fun b => ⟨Q ⊓ b.1, b.1, b.2, rfl⟩
    haveI : Nonempty s := hne.to_subtype
    haveI := g72gk34_isDir hd
    have hg : Tendsto g atTop atTop := by
      rw [tendsto_atTop_atTop]
      rintro ⟨_, b0, hb0, rfl⟩
      exact ⟨⟨b0, hb0⟩, fun b hb => inf_le_inf_left _ hb⟩
    exact hT.comp hg
  · intro a
    simp only
    rw [← hQ, ← compl_compl_inf_distrib, h.2, hQ]

lemma g72gk34_bool_cc (hB : ∀ a : L, a ⊔ aᶜ = ⊤) (a : L) : aᶜᶜ = a := by
  apply le_antisymm _ le_compl_compl
  calc aᶜᶜ = aᶜᶜ ⊓ (a ⊔ aᶜ) := by rw [hB, inf_top_eq]
    _ = (aᶜᶜ ⊓ a) ⊔ (aᶜᶜ ⊓ aᶜ) := inf_sup_left _ _ _
    _ ≤ a := sup_le inf_le_right (by rw [compl_inf_self]; exact bot_le)

lemma g72gk34_HJ {ν : L → ℝ} (h : IsNormalValuation ν)
    (hPP : positiveCarrier ν ⊔ (positiveCarrier ν)ᶜ = ⊤) : HahnJordanConclusions ν := by
  have hn := g72gk34_neg h
  refine ⟨fun a => g72gk34_pos_iff h a, fun a => g72gk34_pos_iff hn a, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply top_le_iff.mp
    rw [← hPP]
    apply sup_le_sup_left
    apply (g72gk34_pos_iff hn _).mp
    intro b hb
    have := g72gk34_negative h (c := (positiveCarrier ν)ᶜ) (compl_inf_self _) hb
    simp only; linarith
  · intro a
    constructor
    · intro ha
      exact le_inf ((g72gk34_pos_iff h a).mp fun b hb => (ha b hb).ge)
        ((g72gk34_pos_iff hn a).mp fun b hb => by show 0 ≤ -ν b; rw [ha b hb, neg_zero])
    · intro ha b hb
      have h1 := g72gk34_carrier_pos h b (hb.trans (ha.trans inf_le_left))
      have h2 : 0 ≤ -ν b := g72gk34_carrier_pos hn b (hb.trans (ha.trans inf_le_right))
      linarith
  · exact g72gk34_restrict h (g72gk34_regular h)
  · exact g72gk34_restrict hn (g72gk34_regular hn)
  · intro a; exact g72gk34_carrier_pos h _ inf_le_left
  · intro a; exact g72gk34_carrier_pos hn _ inf_le_left
  · intro a
    have := g72gk34_decomp h a
    simp only [jordanPositive, jordanNegative]
    linarith

lemma g72gk34_regime {ν : L → ℝ} (h : IsJordanRegime ν) : HahnJordanConclusions ν := by
  rcases h with ⟨hS, hN⟩ | ⟨hB, hC⟩
  · apply g72gk34_HJ hN
    have := hS.2 (positiveCarrier ν)
    rw [g72gk34_regular hN, sup_comm] at this
    exact this
  · have hN : IsNormalValuation ν := ⟨hC, fun a => by rw [g72gk34_bool_cc hB a]⟩
    exact g72gk34_HJ hN (hB _)

end g72gk34

section g72gk34b
variable {L : Type*} [Order.Frame L]

lemma g72gk34_cmap {nu : L → ℂ} (φ : ℂ → ℝ) (hφ0 : φ 0 = 0)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hc : Continuous φ)
    (h : IsContinuousValuation nu) : IsContinuousValuation (fun a => φ (nu a)) :=
  ⟨⟨by simp only [h.1.1, hφ0], fun a b => by simp only; rw [← hadd, ← hadd, h.1.2 a b]⟩,
    fun s a hne hd hl => (hc.tendsto _).comp (h.2 s a hne hd hl)⟩

lemma g72gk34_nmap {nu : L → ℂ} (φ : ℂ → ℝ) (hφ0 : φ 0 = 0)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hc : Continuous φ)
    (h : IsNormalValuation nu) : IsNormalValuation (fun a => φ (nu a)) :=
  ⟨g72gk34_cmap φ hφ0 hadd hc h.1, fun a => by simp only [h.2]⟩

lemma g72gk34_rmap {nu : L → ℂ} (φ : ℂ → ℝ) (hφ0 : φ 0 = 0)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hc : Continuous φ)
    (h : IsJordanRegime nu) : IsJordanRegime (fun a => φ (nu a)) := by
  rcases h with ⟨hS, hN⟩ | ⟨hB, hC⟩
  · exact Or.inl ⟨hS, g72gk34_nmap φ hφ0 hadd hc hN⟩
  · exact Or.inr ⟨hB, g72gk34_cmap φ hφ0 hadd hc hC⟩

end g72gk34b

theorem hahnJordan_decomposition (L : Type u) [Order.Frame L] :
    (∀ nu : L → ℝ, IsJordanRegime nu → HahnJordanConclusions nu) ∧
    (∀ nu : L → ℂ, IsJordanRegime nu → ComplexJordanConclusions nu) := by
  refine ⟨fun nu h => g72gk34_regime h, fun nu h => ?_⟩
  have hre := g72gk34_rmap Complex.re Complex.zero_re Complex.add_re Complex.continuous_re h
  have him := g72gk34_rmap Complex.im Complex.zero_im Complex.add_im Complex.continuous_im h
  have H1 := g72gk34_regime hre
  have H2 := g72gk34_regime him
  unfold ComplexJordanConclusions
  intro re im
  refine ⟨H1, H2, fun a => ?_⟩
  have e1 := H1.2.2.2.2.2.2.2.2 a
  have e2 := H2.2.2.2.2.2.2.2.2 a
  apply Complex.ext
  · simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.sub_im, Complex.ofReal_im]
    simp only at e1
    linarith
  · simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.ofReal_re]
    simp only at e2
    linarith

end Gelfand311Jordan

/- Reused accepted proof by fizzyinc3, submission e4ac8c1d-3289-4144-baeb-8ddb71a3176f. Only a wrapper namespace and theorem name change. -/

namespace Gelfand273Criterion

open QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal


theorem g67c_restrict {A : Type u} [CompleteBooleanAlgebra A] (nu : A → ℝ≥0)
    (hnu : IsPositiveContinuousValuation nu) (a : A) :
    IsPositiveContinuousValuation (fun x : Set.Iic a => nu x.val) := by
  obtain ⟨⟨hbot, hmod⟩, hmono, hcont⟩ := hnu
  refine ⟨⟨hbot, fun x y => hmod x.val y.val⟩, fun x y hxy => hmono hxy, ?_⟩
  intro s b hsne hdir hlub
  have hl : IsLUB (Subtype.val '' s) b.val := by
    constructor
    · rintro _ ⟨x, hx, rfl⟩; exact hlub.1 hx
    · intro u hu
      have : b ≤ ⟨u ⊓ a, inf_le_right⟩ := hlub.2 (fun x hx =>
        show x.val ≤ u ⊓ a from le_inf (hu ⟨x, hx, rfl⟩) x.2)
      exact (show b.val ≤ u ⊓ a from this).trans inf_le_left
  have hd : DirectedOn (· ≤ ·) (Subtype.val '' s) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
    exact ⟨z.val, ⟨z, hz, rfl⟩, hxz, hyz⟩
  have h := hcont _ _ (hsne.image _) hd hl
  rw [Set.image_image] at h
  exact h

theorem g67c_extend {A : Type u} [CompleteBooleanAlgebra A] (a : A) (mu : Set.Iic a → ℝ≥0)
    (hmu : IsPositiveContinuousValuation mu) :
    IsPositiveContinuousValuation (fun x : A => mu ⟨x ⊓ a, inf_le_right⟩) := by
  obtain ⟨⟨hbot, hmod⟩, hmono, hcont⟩ := hmu
  refine ⟨⟨?_, fun x y => ?_⟩, fun x y hxy => hmono (show x ⊓ a ≤ y ⊓ a from inf_le_inf_right a hxy), ?_⟩
  · have : (⟨(⊥ : A) ⊓ a, inf_le_right⟩ : Set.Iic a) = ⊥ := Subtype.ext (by simp)
    simp only; rw [this, hbot]
  · have h1 : (⟨(x ⊔ y) ⊓ a, inf_le_right⟩ : Set.Iic a) =
        (⟨x ⊓ a, inf_le_right⟩ : Set.Iic a) ⊔ ⟨y ⊓ a, inf_le_right⟩ :=
      Subtype.ext (by
        show (x ⊔ y) ⊓ a = (x ⊓ a) ⊔ (y ⊓ a)
        rw [inf_sup_right])
    have h2 : (⟨(x ⊓ y) ⊓ a, inf_le_right⟩ : Set.Iic a) =
        (⟨x ⊓ a, inf_le_right⟩ : Set.Iic a) ⊓ ⟨y ⊓ a, inf_le_right⟩ :=
      Subtype.ext (by
        show (x ⊓ y) ⊓ a = (x ⊓ a) ⊓ (y ⊓ a)
        rw [inf_inf_distrib_right])
    simp only; rw [h1, h2]; exact hmod _ _
  · intro s b hsne hdir hlub
    let g : A → Set.Iic a := fun x => ⟨x ⊓ a, inf_le_right⟩
    have hb : b = sSup s := hlub.unique (isLUB_sSup s)
    have hl : IsLUB (g '' s) (g b) := by
      constructor
      · rintro _ ⟨x, hx, rfl⟩
        exact show x ⊓ a ≤ b ⊓ a from inf_le_inf_right a (hlub.1 hx)
      · intro u hu
        show b ⊓ a ≤ u.val
        rw [hb, sSup_inf_eq]
        exact iSup₂_le fun x hx => (show g x ≤ u from hu ⟨x, hx, rfl⟩)
    have hd : DirectedOn (· ≤ ·) (g '' s) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
      exact ⟨g z, ⟨z, hz, rfl⟩, show x ⊓ a ≤ z ⊓ a from inf_le_inf_right a hxz,
        show y ⊓ a ≤ z ⊓ a from inf_le_inf_right a hyz⟩
    have h := hcont _ _ (hsne.image _) hd hl
    rw [Set.image_image] at h
    exact h

theorem localizableCriterion (A : Type u) [CompleteBooleanAlgebra A] :
    HasFiniteValuationCover A ↔ ∀ b : A, b ≠ ⊥ →
      ∃ nu : A → ℝ≥0, IsPositiveContinuousValuation nu ∧ nu b ≠ 0 := by
  constructor
  · intro hcov b hb
    have : ∃ g ∈ {a : A | ∃ nu : Set.Iic a → ℝ≥0,
        IsPositiveContinuousValuation nu ∧ ∀ b, nu b = 0 → b = ⊥}, b ⊓ g ≠ ⊥ := by
      by_contra hall
      push Not at hall
      apply hb
      have : b = b ⊓ ⊤ := (inf_top_eq b).symm
      rw [this, ← hcov, inf_sSup_eq]
      exact le_antisymm (iSup₂_le fun d hd => (hall d hd).le) bot_le
    obtain ⟨g, ⟨mu, hmu, hfaith⟩, hbg⟩ := this
    refine ⟨_, g67c_extend g mu hmu, fun h0 => hbg ?_⟩
    have := hfaith _ h0
    exact congrArg Subtype.val this
  · intro h
    unfold HasFiniteValuationCover
    set G := {a : A | ∃ nu : Set.Iic a → ℝ≥0,
        IsPositiveContinuousValuation nu ∧ ∀ b, nu b = 0 → b = ⊥}
    set g := sSup G
    by_contra hne
    have hgc : gᶜ ≠ ⊥ := fun h' => hne (compl_eq_bot.1 h')
    obtain ⟨nu, hnu, hnz⟩ := h gᶜ hgc
    have hnu' := hnu
    obtain ⟨⟨hbot, hmod⟩, hmono, hcont⟩ := hnu'
    let Z : Set A := {x | nu x = 0}
    set n := sSup Z
    have hsupz : ∀ x y, x ∈ Z → y ∈ Z → x ⊔ y ∈ Z := by
      intro x y hx hy
      have := hmod x y
      simp only [Z, Set.mem_setOf_eq] at hx hy ⊢
      rw [hx, hy, zero_add] at this
      exact (add_eq_zero.1 this.symm).1
    have hn : nu n = 0 := by
      have hc := hcont Z n ⟨⊥, hbot⟩
        (fun x hx y hy => ⟨x ⊔ y, hsupz x y hx hy, le_sup_left, le_sup_right⟩) (isLUB_sSup Z)
      exact le_antisymm (hc.2 (by rintro _ ⟨x, hx, rfl⟩; exact le_of_eq hx)) bot_le
    set c := gᶜ ⊓ nᶜ
    have hcG : c ∈ G := by
      refine ⟨fun x => nu x.val, g67c_restrict nu hnu c, fun x hx => ?_⟩
      apply Subtype.ext
      have hxn : x.val ≤ n := le_sSup hx
      have hxc : x.val ≤ nᶜ := x.2.trans inf_le_right
      show x.val = ⊥
      exact le_antisymm (le_inf hxn hxc |>.trans (inf_compl_self n).le) bot_le
    have hcle : c ≤ g := le_sSup hcG
    have hc0 : c = ⊥ := le_antisymm ((le_inf hcle inf_le_left).trans (inf_compl_self g).le) bot_le
    apply hnz
    have h1 : gᶜ ≤ c ⊔ n := by
      rw [sup_comm, sup_inf_left, sup_compl_eq_top, inf_top_eq]; exact le_sup_right
    have h2 := hmono h1
    rw [hc0, bot_sup_eq, hn] at h2
    exact le_antisymm h2 bot_le

end Gelfand273Criterion


set_option autoImplicit false

namespace Gelfand311

open Gelfand38 Gelfand39 GelfandVNA.Duality WeakDual Set Filter
open QAlgorithms.Papers.Independent.Support21.P20
open scoped Topology NNReal


noncomputable def projectionCompleteBooleanAlgebra (A : Type u) [CommCStarAlgebra A]
    [WStarAlgebra A] : CompleteBooleanAlgebra (ProjAlg A) := by
  let sup : Set (ProjAlg A) → ProjAlg A := fun s => (projections_complete s).choose
  have hsup (s : Set (ProjAlg A)) : IsLUB s (sup s) := (projections_complete s).choose_spec
  exact {
    (inferInstance : BooleanAlgebra (ProjAlg A)) with
    sSup := sup
    sInf := fun s => sup (lowerBounds s)
    isLUB_sSup := hsup
    isGLB_sInf := fun s => isLUB_lowerBounds.mp (hsup (lowerBounds s)) }

lemma real_normal_to_positive {L : Type*} [Order.Frame L] (ν : L → ℝ)
    (hν : IsNormalValuation ν) (hpos : ∀ a, 0 ≤ ν a) :
    IsPositiveContinuousValuation (fun a => (⟨ν a, hpos a⟩ : ℝ≥0)) := by
  let μ : L → ℝ≥0 := fun a => ⟨ν a, hpos a⟩
  have hmono : Monotone μ := by
    intro a b hab
    change ν a ≤ ν b
    have hh := Gelfand311Jordan.g72gk34_split hν hab
    linarith [hpos (b ⊓ aᶜ)]
  refine ⟨⟨Subtype.ext hν.1.1.1, fun a b => Subtype.ext (hν.1.1.2 a b)⟩, hmono, ?_⟩
  intro s a hs hd ha
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := hd.isDirectedOrder
  have ht : Tendsto (fun b : s => μ b.val) atTop (𝓝 (μ a)) :=
    tendsto_subtype_rng.mpr (hν.1.2 s a hs hd ha)
  have hl := isLUB_of_tendsto_atTop (fun (p q : s) hpq => hmono hpq) ht
  have he : Set.range (fun p : s => μ p.val) = μ '' s := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.val, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  rw [he] at hl
  exact hl

lemma complex_valuation_positive_witness (L : Type*) [CompleteBooleanAlgebra L]
    (ν : L → ℂ) (hν : IsContinuousValuation ν) (p : L) (hp : ν p ≠ 0) :
    ∃ μ : L → ℝ≥0, IsPositiveContinuousValuation μ ∧ μ p ≠ 0 := by
  have hj := (Gelfand311Jordan.hahnJordan_decomposition L).2 ν
    (Or.inr ⟨fun a => sup_compl_eq_top, hν⟩)
  rcases hj with ⟨hr, hi, heq⟩
  rcases hr with ⟨_, _, _, _, hrpn, hrmn, hrp, hrm, _⟩
  rcases hi with ⟨_, _, _, _, hipn, himn, hip, him, _⟩
  have hn : jordanPositive (fun a => (ν a).re) p ≠ 0 ∨
      jordanNegative (fun a => (ν a).re) p ≠ 0 ∨
      jordanPositive (fun a => (ν a).im) p ≠ 0 ∨
      jordanNegative (fun a => (ν a).im) p ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hp
    rw [heq p, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2]
    simp
  have helper (r : L → ℝ) (hr : IsNormalValuation r) (hpos : ∀ a, 0 ≤ r a)
      (hne : r p ≠ 0) : ∃ μ : L → ℝ≥0, IsPositiveContinuousValuation μ ∧ μ p ≠ 0 := by
    refine ⟨fun a => ⟨r a, hpos a⟩, real_normal_to_positive r hr hpos, ?_⟩
    intro hzero
    exact hne (congrArg (fun z : ℝ≥0 => (z : ℝ)) hzero)
  rcases hn with hn | hn | hn | hn
  · exact helper _ hrpn hrp hn
  · exact helper _ hrmn hrm hn
  · exact helper _ hipn hip hn
  · exact helper _ himn him hn

theorem projections_localizable (A : Type u) [CommCStarAlgebra A] [WStarAlgebra A] :
    letI := projectionCompleteBooleanAlgebra A
    HasFiniteValuationCover (ProjAlg A) := by
  let := projectionCompleteBooleanAlgebra A
  apply (Gelfand273Criterion.localizableCriterion (ProjAlg A)).2
  intro p hp
  obtain ⟨X, hX, hN, hC, ⟨e⟩⟩ := WStarAlgebra.exists_predual (M := A)
  have hdual : e.symm p.val ≠ 0 := by
    intro hzero
    apply hp
    apply projection_ext
    change p.val = 0
    apply e.symm.injective
    simpa only [map_zero] using hzero
  obtain ⟨x, hx⟩ : ∃ x : X, (e.symm p.val) x ≠ 0 := by
    by_contra h
    push Not at h
    apply hdual
    ext x
    exact h x
  let φ : A → ℂ := fun a => star ((e.symm a) x)
  have hφ : IsNormalFunctional φ := ⟨X, hX, hN, hC, e, x, fun _ => rfl⟩
  have hn : φ p.val ≠ 0 := by
    intro hzero
    exact hx (star_eq_zero.mp hzero)
  exact complex_valuation_positive_witness (ProjAlg A) (fun q => φ q.val)
    (normal_restrict_isContinuousValuation φ hφ) p hn


end Gelfand311


open GelfandVNA.Duality

open QAlgorithms.Papers.Independent.Support21.P20


/-- Lemma 3.11 with Definition 3.10, pp. 24–25: `ProjAlg` is a functor `CVNA → LBAlg`. The algebra
`ProjAlg(A)` is (order-isomorphic to) a localizable Boolean algebra, and for a normal
*-homomorphism `f : A → B` the restriction `ProjAlg(f)` is a homomorphism of Boolean algebras that
preserves all existing suprema. -/
theorem solution (A B : Type u) [CommCStarAlgebra A] [WStarAlgebra A]
    [CommCStarAlgebra B] [WStarAlgebra B] (f : A →⋆ₐ[ℂ] B) (hf : IsNormalStarHom f) :
    (∃ (C : Type u) (_ : CompleteBooleanAlgebra C),
      HasFiniteValuationCover C ∧ Nonempty (ProjAlg A ≃o C)) ∧
    (∀ p q : ProjAlg A, projMap f (p ⊓ q) = projMap f p ⊓ projMap f q) ∧
    (∀ p q : ProjAlg A, projMap f (p ⊔ q) = projMap f p ⊔ projMap f q) ∧
    (∀ p : ProjAlg A, projMap f pᶜ = (projMap f p)ᶜ) ∧
    projMap f ⊥ = ⊥ ∧ projMap f ⊤ = ⊤ ∧
    (∀ (s : Set (ProjAlg A)) (a : ProjAlg A), IsLUB s a →
      IsLUB (projMap f '' s) (projMap f a)) := by
  refine ⟨?_, Gelfand311.normal_projMap_complete f hf⟩
  let := Gelfand311.projectionCompleteBooleanAlgebra A
  exact ⟨ProjAlg A, inferInstance, Gelfand311.projections_localizable A,
    ⟨OrderIso.refl _⟩⟩


