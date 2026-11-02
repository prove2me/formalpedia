-- Prove2me | solution 1 for GelfandVNA.Duality.proposition_3_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T02:01:35.801865+00:00
-- url     : https://prove2.me/submissions/32516d9f-d861-46e3-897d-3b91ef559303

import Mathlib
import Definitions.Def_GelfandVNA_Duality_VNA

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

universe u

/-- Proposition 3.8, p. 24: for a commutative von Neumann algebra `A`, the projections
`ProjAlg(A) = {x ∈ A | x* = x, x² = x}`, with multiplication as meet and `a ⊕ b = (a - b)²` as
addition, form a complete Boolean algebra. -/
theorem solution (A : Type u) [CommCStarAlgebra A] [WStarAlgebra A] :
    (∀ x : A, (∃ p : ProjAlg A, p.val = x) ↔ (star x = x ∧ x * x = x)) ∧
    (∀ p q : ProjAlg A, (p ⊓ q).val = p.val * q.val) ∧
    (∀ p q : ProjAlg A, (symmDiff p q).val = (p.val - q.val) ^ 2) ∧
    (∀ s : Set (ProjAlg A), ∃ a : ProjAlg A, IsLUB s a) := by
  refine ⟨?_, ?_, ?_, Gelfand38.projections_complete⟩
  · intro x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.isStarProjection.2, p.isStarProjection.1⟩
    · rintro ⟨hstar, hmul⟩
      exact ⟨⟨⟨x, hmul⟩, hstar⟩, rfl⟩
  · intro p q
    rfl
  · intro p q
    change p.val * (1 - q.val) + q.val * (1 - p.val) -
      p.val * (1 - q.val) * (q.val * (1 - p.val)) = (p.val - q.val) ^ 2
    apply (gelfandTransform_isometry A).injective
    ext χ
    simp only [map_add, map_sub, map_mul, map_one, map_pow, ContinuousMap.add_apply,
      ContinuousMap.sub_apply, ContinuousMap.mul_apply, ContinuousMap.one_apply,
      ContinuousMap.pow_apply]
    rcases Gelfand38.projection_value_zero_or_one p χ with hp | hp <;>
      rcases Gelfand38.projection_value_zero_or_one q χ with hq | hq <;> simp [hp, hq]



