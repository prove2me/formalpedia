-- Prove2me | solution 1 for GelfandVNA.Duality.proposition_3_9
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T04:29:05.302716+00:00
-- url     : https://prove2.me/submissions/c86b662a-c81a-4e96-8c76-1ad36580e4d0

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20
import Definitions.Def_GelfandVNA_Duality_VNA

/- Source module Work.Gelfand39BoundedExtension; SHA256 65767134f0cf12786a5ab77bbad9999be1b947e9d99e54eedc8bea3a86e68091. -/
section Gelfand39Source0


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



set_option autoImplicit false

namespace Gelfand39Inverse

open Gelfand38 GelfandVNA.Duality WeakDual

noncomputable section

variable {A : Type*} [CommCStarAlgebra A]

def ramp (f : C(characterSpace ℂ A, ℝ)) (n : ℕ) : C(characterSpace ℂ A, ℂ) :=
  ⟨fun χ => (min ((n : ℝ) * max (f χ) 0) 1 : ℝ), by fun_prop⟩

def rampElement (f : C(characterSpace ℂ A, ℝ)) (n : ℕ) : A :=
  (gelfandStarTransform A).symm (ramp f n)

lemma ramp_eval (f : C(characterSpace ℂ A, ℝ)) (n : ℕ) (χ : characterSpace ℂ A) :
    gelfandTransform ℂ A (rampElement f n) χ =
      (min ((n : ℝ) * max (f χ) 0) 1 : ℝ) := by
  change gelfandStarTransform A ((gelfandStarTransform A).symm (ramp f n)) χ = _
  rw [StarAlgEquiv.apply_symm_apply]
  rfl

lemma ramp_positive (f : C(characterSpace ℂ A, ℝ)) (n : ℕ) :
    PositiveUnit (rampElement f n) := by
  intro χ
  rw [ramp_eval]
  exact ⟨rfl, le_min (mul_nonneg (Nat.cast_nonneg n) (le_max_right _ _)) zero_le_one,
    min_le_right _ _⟩

lemma ramp_monotone (f : C(characterSpace ℂ A, ℝ)) {n m : ℕ} (hnm : n ≤ m) :
    SpectralLE (rampElement f n) (rampElement f m) := by
  intro χ
  rw [ramp_eval, ramp_eval]
  exact min_le_min (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnm) (le_max_right _ _)) le_rfl

theorem exists_support_projection [WStarAlgebra A] (f : C(characterSpace ℂ A, ℝ)) :
    ∃ p : ProjAlg A,
      (∀ χ : characterSpace ℂ A, 0 < f χ → gelfandTransform ℂ A p.val χ = 1) ∧
      (∀ n : ℕ, SpectralLE (rampElement f n) p.val) ∧
      ∀ b : A, PositiveUnit b → (∀ n : ℕ, SpectralLE (rampElement f n) b) →
        SpectralLE p.val b := by
  obtain ⟨X, hX, hN, hC, ⟨e⟩⟩ := WStarAlgebra.exists_predual (M := A)
  have hd : Directed SpectralLE (rampElement f) := by
    intro n m
    exact ⟨max n m, ramp_monotone f (le_max_left _ _), ramp_monotone f (le_max_right _ _)⟩
  obtain ⟨a, ha, hub, hleast⟩ := exists_positive_lub e (rampElement f) (ramp_positive f) hd
  have hone (χ : characterSpace ℂ A) (hχ : 0 < f χ) : gelfandTransform ℂ A a χ = 1 := by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / f χ)
    have hlarge : 1 ≤ (n : ℝ) * max (f χ) 0 := by
      rw [max_eq_left hχ.le]
      exact (div_le_iff₀ hχ).mp hn.le
    have hu := hub n χ
    rw [ramp_eval] at hu
    change min ((n : ℝ) * max (f χ) 0) 1 ≤ (gelfandTransform ℂ A a χ).re at hu
    rw [min_eq_right hlarge] at hu
    apply Complex.ext
    · exact le_antisymm (ha χ).2.2 hu
    · exact (ha χ).1
  have hsq : ∀ n : ℕ, SpectralLE (rampElement f n) (a * a) := by
    intro n χ
    rw [ramp_eval]
    simp only [map_mul, ContinuousMap.mul_apply, Complex.mul_re, (ha χ).1,
      mul_zero, sub_zero, Complex.ofReal_re]
    by_cases hχ : f χ ≤ 0
    · rw [max_eq_right hχ, mul_zero, min_eq_left zero_le_one]
      exact mul_self_nonneg _
    · rw [hone χ (lt_of_not_ge hχ), Complex.one_re, mul_one]
      exact min_le_right _ _
  have haa : a * a = a := spectralLE_antisymm (positiveUnit_square ha) ha
    (positiveUnit_square_le ha) (hleast (a * a) (positiveUnit_square ha) hsq)
  let p : ProjAlg A := ⟨⟨a, haa⟩, (gelfand_selfAdjoint_iff a).2 (fun χ => (ha χ).1)⟩
  exact ⟨p, hone, hub, hleast⟩


end
end Gelfand39Inverse


set_option autoImplicit false

namespace Gelfand39Inverse

open Gelfand38 GelfandVNA.Duality WeakDual Set
open scoped Pointwise

variable {A : Type*} [CommCStarAlgebra A]

lemma inverse_eval (F : C(characterSpace ℂ A, ℂ)) (χ : characterSpace ℂ A) :
    gelfandTransform ℂ A ((gelfandStarTransform A).symm F) χ = F χ := by
  change gelfandStarTransform A ((gelfandStarTransform A).symm F) χ = _
  rw [StarAlgEquiv.apply_symm_apply]

theorem projections_separate_characters [WStarAlgebra A]
    (χ ψ : characterSpace ℂ A) (hne : χ ≠ ψ) :
    ∃ p : ProjAlg A, gelfandTransform ℂ A p.val χ = 1 ∧ gelfandTransform ℂ A p.val ψ = 0 := by
  obtain ⟨k, hk0, hk1, hk⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton : IsClosed ({ψ} : Set (characterSpace ℂ A)))
    (isClosed_singleton : IsClosed ({χ} : Set (characterSpace ℂ A)))
    (show Disjoint ({ψ} : Set (characterSpace ℂ A)) {χ} by simp [hne.symm])
  have hkψ : k ψ = 0 := hk0 (Set.mem_singleton ψ)
  have hkχ : k χ = 1 := hk1 (Set.mem_singleton χ)
  let f : C(characterSpace ℂ A, ℝ) := ⟨fun x => k x - 1 / 2, by fun_prop⟩
  let F : C(characterSpace ℂ A, ℂ) := ⟨fun x => (min (2 * k x) 1 : ℝ), by fun_prop⟩
  let b : A := (gelfandStarTransform A).symm F
  have hb : PositiveUnit b := by
    intro x
    rw [inverse_eval]
    exact ⟨rfl, le_min (mul_nonneg (by norm_num) (hk x).1) zero_le_one, min_le_right _ _⟩
  obtain ⟨p, hpone, hpup, hleast⟩ := exists_support_projection f
  have hpb : SpectralLE p.val b := by
    apply hleast b hb
    intro n x
    rw [ramp_eval, inverse_eval]
    change min ((n : ℝ) * max (k x - 1 / 2) 0) 1 ≤ min (2 * k x) 1
    by_cases hx : k x ≤ 1 / 2
    · rw [max_eq_right (by linarith), mul_zero, min_eq_left zero_le_one]
      exact le_min (mul_nonneg (by norm_num) (hk x).1) zero_le_one
    · rw [min_eq_right (show 1 ≤ 2 * k x by linarith)]
      exact min_le_right _ _
  have hpψ : gelfandTransform ℂ A p.val ψ = 0 := by
    have hle := hpb ψ
    rw [inverse_eval] at hle
    change (gelfandTransform ℂ A p.val ψ).re ≤ min (2 * k ψ) 1 at hle
    rw [hkψ, mul_zero, min_eq_left zero_le_one] at hle
    apply Complex.ext
    · exact le_antisymm hle (projection_positiveUnit p ψ).2.1
    · exact (projection_positiveUnit p ψ).1
  refine ⟨p, hpone χ ?_, hpψ⟩
  change 0 < k χ - 1 / 2
  rw [hkχ]
  norm_num

def projectionMonoid (A : Type*) [CommCStarAlgebra A] : Submonoid A where
  carrier := Set.range (ProjAlg.val : ProjAlg A → A)
  one_mem' := ⟨⊤, rfl⟩
  mul_mem' := by
    rintro a b ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p ⊓ q, rfl⟩

lemma projection_adjoin_span (A : Type*) [CommCStarAlgebra A] :
    (StarAlgebra.adjoin ℂ (Set.range (ProjAlg.val : ProjAlg A → A))).toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range (ProjAlg.val : ProjAlg A → A)) := by
  have hs : star (Set.range (ProjAlg.val : ProjAlg A → A)) =
      Set.range (ProjAlg.val : ProjAlg A → A) := by
    rw [← Set.image_star]
    ext a
    constructor
    · rintro ⟨b, ⟨p, rfl⟩, rfl⟩
      exact ⟨p, p.isStarProjection.2.symm⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p.val, ⟨p, rfl⟩, p.isStarProjection.2⟩
  rw [StarAlgebra.adjoin_eq_span, hs, Set.union_self]
  change Submodule.span ℂ (Submonoid.closure (projectionMonoid A : Set A) : Set A) = _
  rw [Submonoid.closure_eq]
  rfl

theorem projection_span_dense (A : Type*) [CommCStarAlgebra A] [WStarAlgebra A] :
    Dense (Submodule.span ℂ (Set.range (ProjAlg.val : ProjAlg A → A)) : Set A) := by
  let S : StarSubalgebra ℂ A := StarAlgebra.adjoin ℂ (Set.range (ProjAlg.val : ProjAlg A → A))
  let g : A →⋆ₐ[ℂ] C(characterSpace ℂ A, ℂ) := (gelfandStarTransform A).toStarAlgHom
  have hsep : (S.map g).SeparatesPoints := by
    intro χ ψ hne
    obtain ⟨p, hpχ, hpψ⟩ := projections_separate_characters χ ψ hne
    refine ⟨fun x => g p.val x, ⟨g p.val, ?_, rfl⟩, ?_⟩
    · exact StarSubalgebra.mem_map.mpr
        ⟨p.val, StarAlgebra.subset_adjoin ℂ _ ⟨p, rfl⟩, rfl⟩
    · change gelfandTransform ℂ A p.val χ ≠ gelfandTransform ℂ A p.val ψ
      rw [hpχ, hpψ]
      exact one_ne_zero
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (S.map g) hsep
  have hdense : Dense (S : Set A) := by
    apply (gelfandTransform_isometry A).isEmbedding.isInducing.dense_iff.mpr
    intro a
    change g a ∈ (S.map g).topologicalClosure
    rw [htop]
    trivial
  rw [← projection_adjoin_span A]
  exact hdense


end Gelfand39Inverse


set_option autoImplicit false

namespace Gelfand39Inverse

open scoped BigOperators

noncomputable section

variable {B : Type*} [BooleanAlgebra B]

def binaryPartition (p : B) : Finpartition (⊤ : B) := by
  classical
  apply Finpartition.ofErase {p, pᶜ}
  · rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact disjoint_compl_right
    · exact disjoint_compl_left
    · exact (hab rfl).elim
  · simp

lemma binaryPartition_decides (p q : B) (hq : q ∈ (binaryPartition p).parts) :
    q ≤ p ∨ q ≤ pᶜ := by
  classical
  have h : q ∈ ({p, pᶜ} : Finset B) := Finset.mem_of_mem_erase hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl
  · exact Or.inl le_rfl
  · exact Or.inr le_rfl

theorem exists_deciding_partition (s : Finset B) :
    ∃ P : Finpartition (⊤ : B), ∀ q ∈ P.parts, ∀ p ∈ s, q ≤ p ∨ q ≤ pᶜ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, by simp⟩
  | @insert p s hp ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨P ⊓ binaryPartition p, ?_⟩
    intro q hq r hr
    rcases Finset.mem_insert.mp hr with hr | hr
    · rw [hr]
      obtain ⟨b, hb, hqb⟩ := (inf_le_right : P ⊓ binaryPartition p ≤ binaryPartition p) hq
      exact (binaryPartition_decides p b hb).imp (hqb.trans) (hqb.trans)
    · obtain ⟨b, hb, hqb⟩ := (inf_le_left : P ⊓ binaryPartition p ≤ P) hq
      exact (hP b hb r hr).imp (hqb.trans) (hqb.trans)

variable {M : Type*} [AddCommMonoid M] (ν : B → M)
    (hzero : ν ⊥ = 0) (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q)

include hzero hadd

lemma valuation_sup_sum (s : Finset B) (hs : (s : Set B).PairwiseDisjoint id) :
    ν (s.sup id) = ∑ p ∈ s, ν p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hzero
  | @insert p s hp ih =>
    have hps : Disjoint p (s.sup id) := by
      rw [Finset.disjoint_sup_right]
      intro q hq
      exact hs (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hq) (by
        intro he; exact hp (he ▸ hq))
    rw [Finset.sup_insert, id_eq, hadd p (s.sup id) hps, Finset.sum_insert hp]
    rw [ih (fun a ha b hb hab => hs (Finset.mem_insert_of_mem ha)
      (Finset.mem_insert_of_mem hb) hab)]

lemma valuation_partition_sum {a : B} (P : Finpartition a) :
    ∑ q ∈ P.parts, ν q = ν a := by
  rw [← valuation_sup_sum ν hzero hadd P.parts P.disjoint, P.sup_parts]

lemma valuation_partition_inf_sum (P : Finpartition (⊤ : B)) (p : B) :
    ∑ q ∈ P.parts, ν (q ⊓ p) = ν p := by
  classical
  rw [← P.sum_restrict le_top ν hzero]
  exact valuation_partition_sum ν hzero hadd (P.restrict le_top)

end
end Gelfand39Inverse


set_option autoImplicit false

namespace Gelfand39Inverse

open Gelfand38 GelfandVNA.Duality WeakDual
open scoped BigOperators

noncomputable section

variable {A : Type*} [CommCStarAlgebra A]

lemma exists_character_projection_one (p : ProjAlg A) (hp : p ≠ ⊥) :
    ∃ χ : characterSpace ℂ A, gelfandTransform ℂ A p.val χ = 1 := by
  by_contra! hn
  have hz : gelfandTransform ℂ A p.val = 0 := by
    ext χ
    rcases projection_value_zero_or_one p χ with h | h
    · exact h
    · exact (hn χ h).elim
  have hpz : p.val = 0 := (gelfandTransform_isometry A).injective (by simpa using hz)
  apply hp
  apply Subtype.ext
  apply Subtype.ext
  exact hpz

lemma character_norm_le (χ : characterSpace ℂ A) (a : A) :
    ‖gelfandTransform ℂ A a χ‖ ≤ ‖a‖ := by
  simpa only [gelfand_norm] using ContinuousMap.norm_coe_le_norm (gelfandTransform ℂ A a) χ

def partitionFunctional (ν : ProjAlg A → ℝ) (P : Finpartition (⊤ : ProjAlg A)) : A →L[ℂ] ℂ :=
  ∑ q : P.parts, (ν q.val : ℂ) • CharacterSpace.toCLM
    (Classical.choose (exists_character_projection_one q.val (P.ne_bot q.property)))

lemma partitionFunctional_apply (ν : ProjAlg A → ℝ) (P : Finpartition (⊤ : ProjAlg A)) (a : A) :
    partitionFunctional ν P a = ∑ q : P.parts, (ν q.val : ℂ) *
      gelfandTransform ℂ A a
        (Classical.choose (exists_character_projection_one q.val (P.ne_bot q.property))) := by
  simp only [partitionFunctional, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl

variable (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q)

include hzero hadd

lemma partitionFunctional_norm_le (hpos : ∀ p, 0 ≤ ν p)
    (P : Finpartition (⊤ : ProjAlg A)) (a : A) :
    ‖partitionFunctional ν P a‖ ≤ ν ⊤ * ‖a‖ := by
  classical
  rw [partitionFunctional_apply]
  calc
    _ ≤ ∑ q : P.parts, ‖(ν q.val : ℂ) * gelfandTransform ℂ A a
        (Classical.choose (exists_character_projection_one q.val (P.ne_bot q.property)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q : P.parts, ν q.val * ‖a‖ := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos q.val)]
      exact mul_le_mul_of_nonneg_left (character_norm_le _ a) (hpos q.val)
    _ = ν ⊤ * ‖a‖ := by
      rw [← Finset.sum_mul]
      congr 1
      simpa only [Finset.sum_coe_sort] using valuation_partition_sum ν hzero hadd P

lemma partitionFunctional_projection (P : Finpartition (⊤ : ProjAlg A)) (p : ProjAlg A)
    (hdec : ∀ q ∈ P.parts, q ≤ p ∨ q ≤ pᶜ) :
    partitionFunctional ν P p.val = (ν p : ℂ) := by
  classical
  rw [partitionFunctional_apply]
  calc
    _ = ∑ q : P.parts, (ν (q.val ⊓ p) : ℂ) := by
      apply Finset.sum_congr rfl
      intro q hq
      let χ := Classical.choose (exists_character_projection_one q.val (P.ne_bot q.property))
      have hχ : gelfandTransform ℂ A q.val.val χ = 1 :=
        Classical.choose_spec (exists_character_projection_one q.val (P.ne_bot q.property))
      change (ν q.val : ℂ) * gelfandTransform ℂ A p.val χ = _
      rcases hdec q.val q.property with hqp | hqp
      · have he := congrArg (fun r : ProjAlg A => gelfandTransform ℂ A r.val χ)
          (inf_eq_left.mpr hqp)
        change gelfandTransform ℂ A (q.val.val * p.val) χ = _ at he
        simp only [map_mul, ContinuousMap.mul_apply, hχ, one_mul] at he
        rw [he, mul_one, inf_eq_left.mpr hqp]
      · have hdis : Disjoint q.val p := le_compl_iff_disjoint_right.mp hqp
        have he := congrArg (fun r : ProjAlg A => gelfandTransform ℂ A r.val χ) hdis.eq_bot
        change gelfandTransform ℂ A (q.val.val * p.val) χ = gelfandTransform ℂ A 0 χ at he
        simp only [map_mul, ContinuousMap.mul_apply, hχ, one_mul, map_zero,
          ContinuousMap.zero_apply] at he
        rw [he, mul_zero, hdis.eq_bot, hzero, Complex.ofReal_zero]
    _ = (ν p : ℂ) := by
      rw [← Complex.ofReal_sum]
      congr 1
      exact (Finset.sum_coe_sort P.parts (fun q => ν (q ⊓ p))).trans
        (valuation_partition_inf_sum ν hzero hadd P p)


end
end Gelfand39Inverse


set_option autoImplicit false

namespace Gelfand39Inverse

open GelfandVNA.Duality

noncomputable section

variable {A : Type*} [CommCStarAlgebra A]

lemma projection_linearCombination_bound (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q) (hpos : ∀ p, 0 ≤ ν p)
    (c : ProjAlg A →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ (fun p => (ν p : ℂ)) c‖ ≤
      ν ⊤ * ‖Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A) c‖ := by
  obtain ⟨P, hP⟩ := exists_deciding_partition c.support
  have he : partitionFunctional ν P
      (Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A) c) =
      Finsupp.linearCombination ℂ (fun p => (ν p : ℂ)) c := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [partitionFunctional_projection ν hzero hadd P p (fun q hq => hP q hq p hp)]
  rw [← he]
  exact partitionFunctional_norm_le ν hzero hadd hpos P _

lemma projection_linearCombination_dense [WStarAlgebra A] :
    DenseRange (Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A)) := by
  change Dense (LinearMap.range (Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A)) : Set A)
  rw [Finsupp.range_linearCombination]
  exact projection_span_dense A

theorem positive_valuation_bounded_extension [WStarAlgebra A]
    (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q) (hpos : ∀ p, 0 ≤ ν p) :
    ∃! φ : A →L[ℂ] ℂ, ∀ p : ProjAlg A, φ p.val = (ν p : ℂ) := by
  let f := Finsupp.linearCombination ℂ (fun p : ProjAlg A => (ν p : ℂ))
  let e := Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A)
  have hd : DenseRange e := projection_linearCombination_dense
  have hb : ∃ C : ℝ, ∀ c, ‖f c‖ ≤ C * ‖e c‖ :=
    ⟨ν ⊤, projection_linearCombination_bound ν hzero hadd hpos⟩
  refine ⟨f.extendOfNorm e, ?_, ?_⟩
  · intro p
    have h := LinearMap.extendOfNorm_eq hd hb (Finsupp.single p (1 : ℂ))
    simpa only [f, e, Finsupp.linearCombination_single, one_smul] using h
  · intro φ hφ
    apply ContinuousLinearMap.ext_on (projection_span_dense A)
    rintro a ⟨p, rfl⟩
    rw [hφ p]
    have h := LinearMap.extendOfNorm_eq hd hb (Finsupp.single p (1 : ℂ))
    simpa only [f, e, Finsupp.linearCombination_single, one_smul] using h.symm


end
end Gelfand39Inverse


set_option autoImplicit false

namespace Gelfand39Inverse

open GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20

noncomputable section

variable {A : Type*} [CommCStarAlgebra A]

theorem normal_functional_existsCLM (φ : A → ℂ) (hφ : IsNormalFunctional φ) :
    ∃ Φ : A →L[ℂ] ℂ, ∀ a, Φ a = φ a := by
  obtain ⟨X, hX, hN, hC, e, x, hφ⟩ := hφ
  have heq : φ = fun a => star ((e.symm a) x) := funext hφ
  refine ⟨{ toFun := φ
            map_add' := ?_
            map_smul' := ?_
            cont := ?_ }, fun _ => rfl⟩
  · intro a b
    simp [hφ]
  · intro c a
    rw [hφ, hφ, e.symm.map_smulₛₗ]
    simp
  · rw [heq]
    fun_prop

theorem normal_functionals_ext_projections [WStarAlgebra A]
    (φ ψ : A → ℂ) (hφ : IsNormalFunctional φ) (hψ : IsNormalFunctional ψ)
    (h : ∀ p : ProjAlg A, φ p.val = ψ p.val) : φ = ψ := by
  obtain ⟨Φ, hΦ⟩ := normal_functional_existsCLM φ hφ
  obtain ⟨Ψ, hΨ⟩ := normal_functional_existsCLM ψ hψ
  have he : Φ = Ψ := by
    apply ContinuousLinearMap.ext_on (projection_span_dense A)
    rintro a ⟨p, rfl⟩
    rw [hΦ, hΨ, h p]
  funext a
  rw [← hΦ a, ← hΨ a, he]

theorem positive_continuous_valuation_bounded_extension [WStarAlgebra A]
    (ν : ProjAlg A → NNReal) (hν : IsPositiveContinuousValuation ν) :
    ∃! Φ : A →L[ℂ] ℂ, ∀ p : ProjAlg A, Φ p.val = (ν p : ℂ) := by
  apply positive_valuation_bounded_extension (fun p => (ν p : ℝ))
  · exact_mod_cast hν.1.1
  · intro p q hd
    have h := hν.1.2 p q
    rw [hd.eq_bot, hν.1.1, add_zero] at h
    exact_mod_cast h.symm
  · intro p
    exact (ν p).coe_nonneg


end
end Gelfand39Inverse
end Gelfand39Source0

/- Source module Work.Gelfand39OrderContinuity; SHA256 aaa0af2575525ac15c5498967879f48f4c52914cf2c33da57a89649b2aef5966. -/
section Gelfand39Source1

set_option autoImplicit false

namespace Gelfand39OrderContinuity

open GelfandVNA.Duality Gelfand38 Gelfand39Inverse WeakDual
open scoped BigOperators ComplexOrder

noncomputable section

variable {A : Type*} [CommCStarAlgebra A]

section OrderBridge

variable [PartialOrder A] [StarOrderedRing A]

lemma gelfand_le_iff (a b : A) :
    (∀ χ : characterSpace ℂ A, gelfandTransform ℂ A a χ ≤ gelfandTransform ℂ A b χ) ↔ a ≤ b := by
  constructor
  · intro h
    have h' : gelfandStarTransform A a ≤ gelfandStarTransform A b := h
    simpa only [StarAlgEquiv.symm_apply_apply] using
      OrderHomClass.mono (gelfandStarTransform A).symm h'
  · intro h
    exact OrderHomClass.mono (gelfandStarTransform A) h

lemma spectralLE_iff_le {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    SpectralLE a b ↔ a ≤ b := by
  rw [← gelfand_le_iff]
  constructor
  · intro h χ
    exact Complex.le_def.mpr ⟨h χ, by
      rw [(gelfand_selfAdjoint_iff a).mp ha χ, (gelfand_selfAdjoint_iff b).mp hb χ]⟩
  · intro h χ
    exact (Complex.le_def.mp (h χ)).1

lemma positiveUnit_iff_mem_Icc (a : A) : PositiveUnit a ↔ a ∈ Set.Icc (0 : A) 1 := by
  rw [Set.mem_Icc, ← gelfand_le_iff, ← gelfand_le_iff]
  simp only [map_zero, ContinuousMap.zero_apply, map_one, ContinuousMap.one_apply]
  constructor
  · intro h
    exact ⟨fun χ => Complex.nonneg_iff.mpr ⟨(h χ).2.1, (h χ).1.symm⟩,
      fun χ => Complex.le_def.mpr ⟨(h χ).2.2, (h χ).1⟩⟩
  · rintro ⟨h0, h1⟩ χ
    exact ⟨(Complex.nonneg_iff.mp (h0 χ)).2.symm,
      (Complex.nonneg_iff.mp (h0 χ)).1, (Complex.le_def.mp (h1 χ)).1⟩

lemma partitionFunctional_nonneg (ν : ProjAlg A → ℝ) (hpos : ∀ p, 0 ≤ ν p)
    (P : Finpartition (⊤ : ProjAlg A)) {a : A} (ha : 0 ≤ a) :
    0 ≤ partitionFunctional ν P a := by
  classical
  rw [partitionFunctional_apply]
  apply Finset.sum_nonneg
  intro q hq
  apply mul_nonneg
  · exact Complex.nonneg_iff.mpr ⟨hpos q.val, rfl⟩
  · have hg : 0 ≤ gelfandStarTransform A a := map_nonneg (gelfandStarTransform A) ha
    exact hg _

end OrderBridge

variable [WStarAlgebra A]

lemma extension_norm_bound (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q) (hpos : ∀ p, 0 ≤ ν p)
    (Φ : A →L[ℂ] ℂ) (hΦ : ∀ p : ProjAlg A, Φ p.val = (ν p : ℂ)) (a : A) :
    ‖Φ a‖ ≤ ν ⊤ * ‖a‖ := by
  refine (projection_linearCombination_dense (A := A)).induction_on
    (p := fun a => ‖Φ a‖ ≤ ν ⊤ * ‖a‖) a
    (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro c
  have he : Φ (Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A) c) =
      Finsupp.linearCombination ℂ (fun p => (ν p : ℂ)) c := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hΦ]
  rw [he]
  exact projection_linearCombination_bound ν hzero hadd hpos c

lemma extension_opNorm_bound (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q) (hpos : ∀ p, 0 ≤ ν p)
    (Φ : A →L[ℂ] ℂ) (hΦ : ∀ p : ProjAlg A, Φ p.val = (ν p : ℂ)) :
    ‖Φ‖ ≤ ν ⊤ :=
  Φ.opNorm_le_bound (hpos ⊤) (extension_norm_bound ν hzero hadd hpos Φ hΦ)

lemma extension_nonneg [PartialOrder A] [StarOrderedRing A]
    (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q) (hpos : ∀ p, 0 ≤ ν p)
    (Φ : A →L[ℂ] ℂ) (hΦ : ∀ p : ProjAlg A, Φ p.val = (ν p : ℂ))
    {a : A} (ha : 0 ≤ a) : 0 ≤ Φ a := by
  classical
  have hcl : Φ a ∈ closure {z : ℂ | 0 ≤ z} := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let K : ℝ := ‖Φ‖ + ν ⊤ + 1
    have hK : 0 < K := by dsimp [K]; linarith [norm_nonneg Φ, hpos ⊤]
    obtain ⟨c, hc⟩ := (projection_linearCombination_dense (A := A)).exists_dist_lt a
      (div_pos hε hK)
    let b := Finsupp.linearCombination ℂ (ProjAlg.val : ProjAlg A → A) c
    obtain ⟨P, hP⟩ := exists_deciding_partition c.support
    let F := partitionFunctional ν P
    have he : Φ b = F b := by
      dsimp [b]
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [hΦ, partitionFunctional_projection ν hzero hadd P p (fun q hq => hP q hq p hp)]
    refine ⟨F a, partitionFunctional_nonneg ν hpos P ha, ?_⟩
    rw [dist_eq_norm]
    have heq : Φ a - F a = Φ (a - b) - F (a - b) := by
      rw [map_sub, map_sub, he]
      abel
    rw [heq]
    calc
      _ ≤ ‖Φ (a - b)‖ + ‖F (a - b)‖ := norm_sub_le _ _
      _ ≤ ‖Φ‖ * ‖a - b‖ + ν ⊤ * ‖a - b‖ :=
        add_le_add (Φ.le_opNorm _) (partitionFunctional_norm_le ν hzero hadd hpos P _)
      _ ≤ K * ‖a - b‖ := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (norm_nonneg _)
      _ < ε := by
        have hc' : ‖a - b‖ < ε / K := by simpa only [dist_eq_norm] using hc
        exact (lt_div_iff₀' hK).mp hc'
  rw [(show IsClosed {z : ℂ | 0 ≤ z} from isClosed_Ici).closure_eq] at hcl
  exact hcl

def extensionPositiveLinearMap [PartialOrder A] [StarOrderedRing A]
    (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p q, Disjoint p q → ν (p ⊔ q) = ν p + ν q) (hpos : ∀ p, 0 ≤ ν p)
    (Φ : A →L[ℂ] ℂ) (hΦ : ∀ p : ProjAlg A, Φ p.val = (ν p : ℂ)) : A →ₚ[ℂ] ℂ where
  toLinearMap := Φ.toLinearMap
  monotone' := by
    intro a b hab
    change Φ a ≤ Φ b
    have h := extension_nonneg ν hzero hadd hpos Φ hΦ (sub_nonneg.mpr hab)
    simpa only [map_sub, sub_nonneg] using h


end
end Gelfand39OrderContinuity
end Gelfand39Source1

/- Source module Work.Gelfand39TruncationExtension; SHA256 7cf68e8829232d29be5be85ad60d5401537153c4ca57b9ad2f4e361d1f219ef0. -/
section Gelfand39Source2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GelfandVNA.Duality Gelfand39OrderContinuity

namespace Gelfand39Truncation
universe u
variable {A : Type u} [CommCStarAlgebra A] [WStarAlgebra A]

def bandRestriction (q : ProjAlg A) (Φ : A →L[ℂ] ℂ) : A →L[ℂ] ℂ where
  toFun a := Φ (q.val * a)
  map_add' := by intro a b; rw [mul_add, map_add]
  map_smul' := by intro c a; rw [mul_smul_comm, map_smul]; rfl
  cont := by fun_prop

theorem band_valuation_add (ν : ProjAlg A → ℝ)
    (hadd : ∀ p r, Disjoint p r → ν (p ⊔ r) = ν p + ν r)
    (q p r : ProjAlg A) (hpr : Disjoint p r) :
    ν (q ⊓ (p ⊔ r)) = ν (q ⊓ p) + ν (q ⊓ r) := by
  rw [inf_sup_left]
  exact hadd _ _ (hpr.mono inf_le_right inf_le_right)

theorem band_restriction_projection (ν : ProjAlg A → ℝ)
    (Φ : A →L[ℂ] ℂ) (hΦ : ∀ p : ProjAlg A, Φ p.val = (ν p : ℂ))
    (q p : ProjAlg A) :
    bandRestriction q Φ p.val = (ν (q ⊓ p) : ℂ) := by
  change Φ (q ⊓ p).val = _
  exact hΦ _

/-- Removing a projection band has norm at most the valuation of its complement. -/
theorem band_tail_bound (ν : ProjAlg A → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ p r, Disjoint p r → ν (p ⊔ r) = ν p + ν r)
    (hpos : ∀ p, 0 ≤ ν p)
    (Φ : A →L[ℂ] ℂ) (hΦ : ∀ p : ProjAlg A, Φ p.val = (ν p : ℂ))
    (q : ProjAlg A) (a : A) :
    ‖Φ a - bandRestriction q Φ a‖ ≤ ν qᶜ * ‖a‖ := by
  have hdiff : Φ a - bandRestriction q Φ a = bandRestriction qᶜ Φ a := by
    change Φ a - Φ (q.val * a) = Φ ((1 - q.val) * a)
    rw [sub_mul, one_mul, map_sub]
  rw [hdiff]
  have h := extension_norm_bound (fun p => ν (qᶜ ⊓ p))
    (by simpa using hzero) (band_valuation_add ν hadd qᶜ) (fun p => hpos _)
    (bandRestriction qᶜ Φ) (band_restriction_projection ν Φ hΦ qᶜ) a
  simpa only [inf_top_eq] using h

end Gelfand39Truncation
end
end Gelfand39Source2

/- Source module Work.Gelfand39DominatedGNS; SHA256 58a863f92e902d0f519969b9ebb05af082ffb112cec545193f4df7436c9369b7. -/
section Gelfand39Source3

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProductSpace ComplexOrder
open UniformSpace

namespace Gelfand39GNS
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A functional bounded for the positive functional's GNS seminorm is represented
by a vector in its actual Hilbert completion. -/
theorem exists_gns_vector (μ : A →ₚ[ℂ] ℂ) (Φ : A →ₗ[ℂ] ℂ) (C : ℝ)
    (hbound : ∀ a : A, ‖Φ a‖ ≤ C * ‖μ.toPreGNS a‖) :
    ∃ ξ : μ.GNS, ∀ a : A,
      Φ a = ⟪ξ, (μ.toPreGNS a : μ.GNS)⟫_ℂ := by
  let f : μ.PreGNS →L[ℂ] ℂ :=
    (Φ.comp μ.ofPreGNS.toLinearMap).mkContinuous C (fun a => by
      simpa using hbound (μ.ofPreGNS a))
  refine ⟨(InnerProductSpace.toDual ℂ μ.GNS).symm f.fromCompletion, ?_⟩
  intro a
  rw [InnerProductSpace.toDual_symm_apply,
    ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

/-- GNS vectors can be approximated uniformly on the algebra's norm unit ball by
the multiplication functionals coming from algebra elements. -/
theorem exists_multiplication_approximation (μ : A →ₚ[ℂ] ℂ)
    (Φ : A →ₗ[ℂ] ℂ) (ξ : μ.GNS)
    (hξ : ∀ a : A, Φ a = ⟪ξ, (μ.toPreGNS a : μ.GNS)⟫_ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ a : A, ‖μ.toPreGNS a‖ ≤ K * ‖a‖)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ b : A, ∀ a : A, ‖Φ a - μ (star b * a)‖ ≤ ε * ‖a‖ := by
  let δ : ℝ := ε / (K + 1)
  have hK1 : 0 < K + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hK1
  obtain ⟨b, hb⟩ :=
    Completion.denseRange_coe.exists_dist_lt ξ hδ
  refine ⟨μ.ofPreGNS b, ?_⟩
  intro a
  have hb' : ‖ξ - (b : μ.GNS)‖ ≤ δ := by
    simpa only [dist_eq_norm] using hb.le
  have hδK : δ * K ≤ ε := by
    calc
      δ * K ≤ δ * (K + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
      _ = ε := div_mul_cancel₀ ε (ne_of_gt hK1)
  calc
    ‖Φ a - μ (star (μ.ofPreGNS b) * a)‖ =
        ‖⟪ξ - (b : μ.GNS), (μ.toPreGNS a : μ.GNS)⟫_ℂ‖ := by
      rw [hξ, inner_sub_left, Completion.inner_coe]
      rw [PositiveLinearMap.preGNS_inner_def]
      simp
    _ ≤ ‖ξ - (b : μ.GNS)‖ * ‖(μ.toPreGNS a : μ.GNS)‖ := norm_inner_le_norm _ _
    _ ≤ δ * (K * ‖a‖) := by
      apply mul_le_mul hb'
      · simpa only [Completion.norm_coe] using hbound a
      · positivity
      · exact hδ.le
    _ = (δ * K) * ‖a‖ := (mul_assoc _ _ _).symm
    _ ≤ ε * ‖a‖ := mul_le_mul_of_nonneg_right hδK (norm_nonneg a)

end Gelfand39GNS
end
end Gelfand39Source3

/- Source module Work.Gelfand39DominatedBounds; SHA256 4f4eec22f2799af4961d5dcddf600db31314a48c3fdeeb610c61c650e986d05c. -/
section Gelfand39Source4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProductSpace ComplexOrder

namespace Gelfand39GNS
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem preGNS_norm_sq_re (μ : A →ₚ[ℂ] ℂ) (a : A) :
    ‖μ.toPreGNS a‖ ^ 2 = (μ (star a * a)).re := by
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re,
    PositiveLinearMap.ofPreGNS_toPreGNS] using
    congrArg Complex.re (μ.preGNS_norm_sq (μ.toPreGNS a))

/-- The GNS seminorm is bounded by the original C*-norm, with an explicit
constant obtained from positivity at the identity. -/
theorem preGNS_norm_le (μ : A →ₚ[ℂ] ℂ) (a : A) :
    ‖μ.toPreGNS a‖ ≤ Real.sqrt ‖μ 1‖ * ‖a‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (norm_nonneg _), preGNS_norm_sq_re]
  calc
    (μ (star a * a)).re ≤ ‖μ (star a * a)‖ := Complex.re_le_norm _
    _ ≤ ‖μ 1‖ * ‖star a * a‖ := μ.norm_apply_le_of_nonneg _ (star_mul_self_nonneg a)
    _ = ‖μ 1‖ * ‖a‖ ^ 2 := by rw [CStarRing.norm_star_mul_self, pow_two]

/-- Positive domination on squares controls the dominated functional in the
dominating functional's GNS seminorm. -/
theorem norm_le_preGNS_of_domination (μ ν : A →ₚ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (ν (star a * a)).re ≤ C * (μ (star a * a)).re)
    (a : A) :
    ‖ν a‖ ≤ (‖ν.toPreGNS 1‖ * Real.sqrt C) * ‖μ.toPreGNS a‖ := by
  have hnorm : ‖ν.toPreGNS a‖ ≤ Real.sqrt C * ‖μ.toPreGNS a‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hC, preGNS_norm_sq_re, preGNS_norm_sq_re]
    exact hdom a
  have heq : ν a = ⟪ν.toPreGNS 1, ν.toPreGNS a⟫_ℂ := by
    rw [PositiveLinearMap.preGNS_inner_def]
    simp
  calc
    ‖ν a‖ = ‖⟪ν.toPreGNS 1, ν.toPreGNS a⟫_ℂ‖ := congrArg norm heq
    _ ≤ ‖ν.toPreGNS 1‖ * ‖ν.toPreGNS a‖ := norm_inner_le_norm _ _
    _ ≤ ‖ν.toPreGNS 1‖ * (Real.sqrt C * ‖μ.toPreGNS a‖) :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

end Gelfand39GNS
end
end Gelfand39Source4

/- Source module Work.Gelfand39PredualCriterion; SHA256 05b6f7f916c0ca77e18daa404a2ad0bf9e795500c07873ecf127209d542a37a6. -/
section Gelfand39Source5

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set

namespace Gelfand39Predual
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Finite-coordinate control on the norm unit ball forces a bounded bidual
functional to be evaluation at an actual element of the given predual. -/
theorem eval_of_finite_kernel_control (Φ : StrongDual ℂ (StrongDual ℂ X))
    (hΦ : ∀ ε : ℝ, 0 < ε → ∃ s : Finset X,
      ∀ f : StrongDual ℂ X, ‖f‖ ≤ 1 → (∀ x ∈ s, f x = 0) → ‖Φ f‖ ≤ ε) :
    ∃ x : X, ∀ f : StrongDual ℂ X, Φ f = f x := by
  classical
  let J : X →ₗᵢ[ℂ] StrongDual ℂ (StrongDual ℂ X) :=
    NormedSpace.inclusionInDoubleDualLi (E := X) ℂ
  let M : Submodule ℂ (StrongDual ℂ (StrongDual ℂ X)) := J.toLinearMap.range
  have hiso : Isometry (fun x : X => J x) := J.isometry
  have hcomplete : IsComplete (Set.range (fun x : X => J x)) :=
    hiso.isUniformInducing.isComplete_range
  have hclosed : IsClosed (Set.range (fun x : X => J x)) := hcomplete.isClosed
  have hmem : Φ ∈ closure (Set.range (fun x : X => J x)) := by
    refine (Metric.mem_closure_iff (a := Φ) (s := Set.range (fun x : X => J x))).2 ?_
    intro ε hε
    obtain ⟨s, hs⟩ := hΦ (ε / 2) (half_pos hε)
    let L : s → StrongDual ℂ X →ₗ[ℂ] ℂ := fun x => (J x.val).toLinearMap
    let N : Submodule ℂ (StrongDual ℂ X) := ⨅ x : s, (L x).ker
    letI : NormedAddCommGroup N := inferInstance
    letI : NormedSpace ℂ N := inferInstance
    let r : StrongDual ℂ N := Φ.comp N.subtypeL
    have hr : ‖r‖ ≤ ε / 2 := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm (half_pos hε).le
      intro f hf
      apply hs f.val (by change ‖f‖ ≤ 1; rw [hf])
      intro x hx
      have hfx := ((Submodule.mem_iInf (fun y : s => (L y).ker)).mp f.property) ⟨x, hx⟩
      exact hfx
    obtain ⟨g, hg, hgnorm⟩ := exists_extension_norm_eq N r
    let m : StrongDual ℂ (StrongDual ℂ X) := Φ - g
    have hker : (⨅ x : s, (L x).ker) ≤ m.toLinearMap.ker := by
      intro f hf
      change Φ f - g f = 0
      have h := hg (⟨f, hf⟩ : N)
      exact sub_eq_zero.mpr h.symm
    have hm : m.toLinearMap ∈ Submodule.span ℂ (Set.range L) :=
      mem_span_of_iInf_ker_le_ker hker
    have hspan : Submodule.span ℂ (Set.range L) ≤
        M.map (ContinuousLinearMap.coeLM ℂ) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x, rfl⟩
      exact Submodule.mem_map.mpr ⟨J x.val, ⟨x.val, rfl⟩, rfl⟩
    obtain ⟨m', hm', heq⟩ := Submodule.mem_map.mp (hspan hm)
    have he : m' = m := by
      ext f
      exact LinearMap.congr_fun heq f
    have hmM : m ∈ M := he ▸ hm'
    obtain ⟨x, hx⟩ : ∃ x : X, J x = m := hmM
    refine ⟨m, ⟨x, hx⟩, ?_⟩
    have hdist : dist Φ m ≤ ε / 2 := by
      have hd : dist Φ m = ‖Φ - m‖ := dist_eq_norm Φ m
      rw [hd]
      change ‖Φ - (Φ - g)‖ ≤ ε / 2
      calc
        ‖Φ - (Φ - g)‖ = ‖g‖ :=
          congrArg (fun h : StrongDual ℂ (StrongDual ℂ X) => ‖h‖) (sub_sub_cancel Φ g)
        _ = ‖r‖ := hgnorm
        _ ≤ ε / 2 := hr
    exact hdist.trans_lt (half_lt_self hε)
  rw [hclosed.closure_eq] at hmem
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, ?_⟩
  intro f
  have h := congrArg (fun ψ : StrongDual ℂ (StrongDual ℂ X) => ψ f) hx
  exact h.symm

end Gelfand39Predual
end
end Gelfand39Source5

/- Source module Work.Gelfand39PredualClosed; SHA256 7dd059d822e4540ded77e03a6d9c7eb2c37e54bb7959fa5a40edd3378461c040. -/
section Gelfand39Source6

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GelfandVNA.Duality

namespace Gelfand39Predual
universe u
variable {A X : Type u} [CStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Uniform norm approximation by vectors from one fixed predual stays in that
same predual. The witnesses are not allowed to vary their ambient predual. -/
theorem exists_predual_vector_of_norm_approximation
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (Φ : A →L[ℂ] ℂ)
    (hΦ : ∀ ε : ℝ, 0 < ε → ∃ x : X,
      ∀ a : A, ‖Φ a - star ((e.symm a) x)‖ ≤ ε * ‖a‖) :
    ∃ x : X, ∀ a : A, Φ a = star ((e.symm a) x) := by
  classical
  let ψ : StrongDual ℂ X →L[ℂ] ℂ := {
    toFun := fun f => star (Φ (e f))
    map_add' := by intro f g; simp
    map_smul' := by
      intro c f
      change star (Φ (e (c • f))) = c • star (Φ (e f))
      rw [e.map_smulₛₗ, Φ.map_smul]
      simp
    cont := (Φ.continuous.comp e.continuous).star }
  obtain ⟨x, hx⟩ := eval_of_finite_kernel_control ψ (by
    intro ε hε
    obtain ⟨x, hx⟩ := hΦ ε hε
    refine ⟨{x}, ?_⟩
    intro f hf hfzero
    have hfx : f x = 0 := hfzero x (Finset.mem_singleton_self x)
    have h := hx (e f)
    simp only [e.symm_apply_apply, hfx, star_zero, sub_zero, e.norm_map] at h
    change ‖star (Φ (e f))‖ ≤ ε
    rw [norm_star]
    exact h.trans ((mul_le_mul_of_nonneg_left hf hε.le).trans_eq (mul_one ε)))
  refine ⟨x, ?_⟩
  intro a
  have h := hx (e.symm a)
  change star (Φ (e (e.symm a))) = (e.symm a) x at h
  rw [e.apply_symm_apply] at h
  rw [← h, star_star]

end Gelfand39Predual
end
end Gelfand39Source6

/- Source module Work.Gelfand39DominatedNormal; SHA256 481a71f3786343060a4aedfaf93dd5e5eaa7a2541c61158784ba7930f8d43e3c. -/
section Gelfand39Source7

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped ComplexOrder
open GelfandVNA.Duality

namespace Gelfand39GNS
universe u
variable {A X : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Positive domination preserves membership in the supplied predual once the
dominating functional's multiplication functionals belong to that predual. -/
theorem exists_predual_vector_of_positive_domination
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (μ ν : A →ₚ[ℂ] ℂ)
    (hμ : ∀ b : A, ∃ x : X, ∀ a : A,
      μ (star b * a) = star ((e.symm a) x))
    (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (ν (star a * a)).re ≤ C * (μ (star a * a)).re) :
    ∃ x : X, ∀ a : A, ν a = star ((e.symm a) x) := by
  let νc : A →L[ℂ] ℂ := {
    toLinearMap := ν.toLinearMap
    cont := map_continuous ν }
  obtain ⟨ξ, hξ⟩ := exists_gns_vector μ (ν : A →ₗ[ℂ] ℂ)
    (‖ν.toPreGNS 1‖ * Real.sqrt C)
    (norm_le_preGNS_of_domination μ ν C hC hdom)
  apply Gelfand39Predual.exists_predual_vector_of_norm_approximation e νc
  intro ε hε
  obtain ⟨b, hb⟩ := exists_multiplication_approximation μ (ν : A →ₗ[ℂ] ℂ)
    ξ hξ (Real.sqrt ‖μ 1‖) (Real.sqrt_nonneg _) (preGNS_norm_le μ) ε hε
  obtain ⟨x, hx⟩ := hμ b
  refine ⟨x, ?_⟩
  intro a
  rw [← hx a]
  exact hb a

theorem normal_of_positive_domination
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (μ ν : A →ₚ[ℂ] ℂ)
    (hμ : ∀ b : A, ∃ x : X, ∀ a : A,
      μ (star b * a) = star ((e.symm a) x))
    (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (ν (star a * a)).re ≤ C * (μ (star a * a)).re) :
    IsNormalFunctional ν := by
  obtain ⟨x, hx⟩ := exists_predual_vector_of_positive_domination e μ ν hμ C hC hdom
  exact ⟨X, inferInstance, inferInstance, inferInstance, e, x, hx⟩

end Gelfand39GNS
end
end Gelfand39Source7

/- Source module Work.Gelfand39TruncationDomination; SHA256 1a9680f0731e0c0bc6f048a06bd40944bb00cf307545977c6c4833e1ea8a2798. -/
section Gelfand39Source8

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GelfandVNA.Duality Gelfand39OrderContinuity
open scoped ComplexOrder

namespace Gelfand39Truncation
universe u
variable {A X : Type u} [CommCStarAlgebra A] [WStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

local instance : LE (ProjAlg A) :=
  (inferInstance : BooleanAlgebra (ProjAlg A)).toPartialOrder.toLE
local instance : Preorder (ProjAlg A) :=
  (inferInstance : BooleanAlgebra (ProjAlg A)).toPartialOrder.toPreorder
local instance : PartialOrder (ProjAlg A) :=
  (inferInstance : BooleanAlgebra (ProjAlg A)).toPartialOrder

theorem band_le_of_projection_bound (μ ν : ProjAlg A → ℝ)
    (hμzero : μ ⊥ = 0)
    (hμadd : ∀ p r, Disjoint p r → μ (p ⊔ r) = μ p + μ r)
    (hμmono : Monotone μ)
    (hνzero : ν ⊥ = 0)
    (hνadd : ∀ p r, Disjoint p r → ν (p ⊔ r) = ν p + ν r)
    (Φ Ψ : A →L[ℂ] ℂ)
    (hΦ : ∀ p : ProjAlg A, Φ p.val = (μ p : ℂ))
    (hΨ : ∀ p : ProjAlg A, Ψ p.val = (ν p : ℂ))
    (q : ProjAlg A) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ p, p ≤ q → ν p ≤ C * μ p)
    {a : A} (ha : 0 ≤ a) :
    bandRestriction q Ψ a ≤ (C : ℂ) * Φ a := by
  let d : ProjAlg A → ℝ := fun p => C * μ p - ν (q ⊓ p)
  let D : A →L[ℂ] ℂ := (C : ℂ) • Φ - bandRestriction q Ψ
  have hd0 : d ⊥ = 0 := by simp [d, hμzero, hνzero]
  have hdadd : ∀ p r, Disjoint p r → d (p ⊔ r) = d p + d r := by
    intro p r hpr
    dsimp [d]
    rw [hμadd p r hpr, band_valuation_add ν hνadd q p r hpr]
    ring
  have hdpos (p : ProjAlg A) : 0 ≤ d p := by
    have h₁ := hbound (q ⊓ p) inf_le_left
    have h₂ := mul_le_mul_of_nonneg_left (hμmono (show q ⊓ p ≤ p from inf_le_right)) hC
    dsimp [d]
    linarith
  have hD (p : ProjAlg A) : D p.val = (d p : ℂ) := by
    change (C : ℂ) * Φ p.val - bandRestriction q Ψ p.val = (d p : ℂ)
    rw [hΦ, band_restriction_projection ν Ψ hΨ]
    dsimp [d]
    push_cast
    rfl
  have h := extension_nonneg d hd0 hdadd hdpos D hD ha
  change 0 ≤ (C : ℂ) * Φ a - bandRestriction q Ψ a at h
  exact sub_nonneg.mp h

/-- Domination on projections of a band makes its positive extension belong to
the given fixed predual. -/
theorem band_exists_predual_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (μ ν : ProjAlg A → ℝ)
    (hμzero : μ ⊥ = 0)
    (hμadd : ∀ p r, Disjoint p r → μ (p ⊔ r) = μ p + μ r)
    (hμpos : ∀ p, 0 ≤ μ p) (hμmono : Monotone μ)
    (hνzero : ν ⊥ = 0)
    (hνadd : ∀ p r, Disjoint p r → ν (p ⊔ r) = ν p + ν r)
    (hνpos : ∀ p, 0 ≤ ν p)
    (Φ Ψ : A →L[ℂ] ℂ)
    (hΦ : ∀ p : ProjAlg A, Φ p.val = (μ p : ℂ))
    (hΨ : ∀ p : ProjAlg A, Ψ p.val = (ν p : ℂ))
    (hΦmult : ∀ b : A, ∃ x : X, ∀ a : A,
      Φ (star b * a) = star ((e.symm a) x))
    (q : ProjAlg A) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ p, p ≤ q → ν p ≤ C * μ p) :
    ∃ x : X, ∀ a : A, bandRestriction q Ψ a = star ((e.symm a) x) := by
  let μp : A →ₚ[ℂ] ℂ := extensionPositiveLinearMap μ hμzero hμadd hμpos Φ hΦ
  let νp : A →ₚ[ℂ] ℂ := extensionPositiveLinearMap
    (fun p => ν (q ⊓ p)) (by simpa using hνzero)
    (band_valuation_add ν hνadd q) (fun p => hνpos _)
    (bandRestriction q Ψ) (band_restriction_projection ν Ψ hΨ q)
  apply Gelfand39GNS.exists_predual_vector_of_positive_domination e μp νp hΦmult C hC
  intro a
  have h := band_le_of_projection_bound μ ν hμzero hμadd hμmono hνzero hνadd
    Φ Ψ hΦ hΨ q C hC hbound (star_mul_self_nonneg a)
  have hr := (Complex.le_def.mp h).1
  change ((bandRestriction q Ψ) (star a * a)).re ≤ C * (Φ (star a * a)).re
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using hr

/-- If positive dominated bands leave arbitrarily small valuation tails, the
whole bounded extension is represented in the same fixed predual. -/
theorem exists_predual_vector_of_dominated_bands (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (μ ν : ProjAlg A → ℝ)
    (hμzero : μ ⊥ = 0)
    (hμadd : ∀ p r, Disjoint p r → μ (p ⊔ r) = μ p + μ r)
    (hμpos : ∀ p, 0 ≤ μ p) (hμmono : Monotone μ)
    (hνzero : ν ⊥ = 0)
    (hνadd : ∀ p r, Disjoint p r → ν (p ⊔ r) = ν p + ν r)
    (hνpos : ∀ p, 0 ≤ ν p)
    (Φ Ψ : A →L[ℂ] ℂ)
    (hΦ : ∀ p : ProjAlg A, Φ p.val = (μ p : ℂ))
    (hΨ : ∀ p : ProjAlg A, Ψ p.val = (ν p : ℂ))
    (hΦmult : ∀ b : A, ∃ x : X, ∀ a : A,
      Φ (star b * a) = star ((e.symm a) x))
    (hbands : ∀ ε : ℝ, 0 < ε → ∃ q : ProjAlg A, ∃ C : ℝ,
      0 ≤ C ∧ (∀ p, p ≤ q → ν p ≤ C * μ p) ∧ ν qᶜ ≤ ε) :
    ∃ x : X, ∀ a : A, Ψ a = star ((e.symm a) x) := by
  apply Gelfand39Predual.exists_predual_vector_of_norm_approximation e Ψ
  intro ε hε
  obtain ⟨q, C, hC, hb, htail⟩ := hbands ε hε
  obtain ⟨x, hx⟩ := band_exists_predual_vector e μ ν hμzero hμadd hμpos hμmono
    hνzero hνadd hνpos Φ Ψ hΦ hΨ hΦmult q C hC hb
  refine ⟨x, ?_⟩
  intro a
  rw [← hx a]
  exact (band_tail_bound ν hνzero hνadd hνpos Ψ hΨ q a).trans
    (mul_le_mul_of_nonneg_right htail (norm_nonneg a))

end Gelfand39Truncation
end
end Gelfand39Source8

/- Source module Work.Gelfand39Truncation; SHA256 05045be01afdd9354bb64d65bc3c06ac889d78f9076ca7bdb5331405f2f99a39. -/
section Gelfand39Source9

set_option autoImplicit false
noncomputable section
open Set

namespace Gelfand39Truncation
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

/-- Maximal negative carriers of ν-(n+1)μ increase with n. -/
theorem monotone_carriers (μ ν : B → ℝ) (hμpos : ∀ a, 0 ≤ μ a)
    (q : ℕ → B)
    (hneg : ∀ (n : ℕ) a, a ≤ q n → ν a ≤ ((n : ℝ) + 1) * μ a)
    (hmax : ∀ (n : ℕ) r, (∀ a, a ≤ r → ν a ≤ ((n : ℝ) + 1) * μ a) → r ≤ q n) :
    Monotone q := by
  intro n m hnm
  apply hmax m (q n)
  intro a ha
  exact (hneg n a ha).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hnm 1)
    (hμpos a))

/-- Absolute continuity forces the union of the dominated carrier pieces to
have full ν-measure. No ambient strict positivity of μ is required. -/
theorem carrier_sup_full (μ ν : B → ℝ)
    (hμpos : ∀ a, 0 ≤ μ a) (hμmono : Monotone μ) (hνmono : Monotone ν)
    (hνsplit : ∀ a, ν a + ν aᶜ = ν ⊤)
    (hac : ∀ a, μ a = 0 → ν a = 0)
    (q : ℕ → B)
    (hbound : ∀ n : ℕ, ((n : ℝ) + 1) * μ (q n)ᶜ ≤ ν (q n)ᶜ) :
    ν (iSup q) = ν ⊤ := by
  have hμnull : μ (iSup q)ᶜ = 0 := by
    by_contra hne
    have hpos : 0 < μ (iSup q)ᶜ :=
      lt_of_le_of_ne (hμpos _) (Ne.symm hne)
    obtain ⟨n, hn⟩ := exists_nat_gt (ν ⊤ / μ (iSup q)ᶜ)
    have hstrict : ν ⊤ < (n : ℝ) * μ (iSup q)ᶜ := (div_lt_iff₀ hpos).mp hn
    have hle : μ (iSup q)ᶜ ≤ μ (q n)ᶜ :=
      hμmono (compl_le_compl (le_iSup q n))
    have hcap : (n : ℝ) * μ (iSup q)ᶜ ≤ ν ⊤ := by
      calc
        (n : ℝ) * μ (iSup q)ᶜ ≤ ((n : ℝ) + 1) * μ (iSup q)ᶜ :=
          mul_le_mul_of_nonneg_right (by linarith) hpos.le
        _ ≤ ((n : ℝ) + 1) * μ (q n)ᶜ :=
          mul_le_mul_of_nonneg_left hle (by positivity)
        _ ≤ ν (q n)ᶜ := hbound n
        _ ≤ ν ⊤ := hνmono le_top
    exact (not_lt_of_ge hcap) hstrict
  have hνnull := hac _ hμnull
  have h := hνsplit (iSup q)
  rw [hνnull, add_zero] at h
  exact h

/-- Finite directed-supremum continuity turns full carrier measure into
arbitrarily small positive tails, the estimate needed for norm approximation. -/
theorem exists_small_complement (ν : B → ℝ) (q : ℕ → B)
    (hνsplit : ∀ a, ν a + ν aᶜ = ν ⊤)
    (hfull : ν (iSup q) = ν ⊤)
    (hSup : IsLUB (ν '' Set.range q) (ν (iSup q)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n, ν (q n)ᶜ < ε := by
  by_contra h
  push_neg at h
  have hle : ν (iSup q) ≤ ν ⊤ - ε := hSup.2 (by
    rintro y ⟨b, ⟨n, rfl⟩, rfl⟩
    have hn := h n
    have hs := hνsplit (q n)
    linarith)
  rw [hfull] at hle
  linarith

end Gelfand39Truncation
end
end Gelfand39Source9

/- Source module Work.Gelfand39TruncationCarriers; SHA256 be2b6ae9e5364908500fe0259be1173dd398e10eb9008ca5c346c6b6c62e5764. -/
section Gelfand39Source10

set_option autoImplicit false
noncomputable section
open Set QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand39Truncation
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

def carrier (μ ν : B → ℝ) (n : ℕ) : B :=
  negativeCarrier (fun a => ν a - ((n : ℝ) + 1) * μ a)

theorem carrier_bound (μ ν : B → ℝ)
    (hHahn : ∀ n : ℕ, HahnJordanConclusions
      (fun a => ν a - ((n : ℝ) + 1) * μ a))
    (n : ℕ) (a : B) (ha : a ≤ carrier μ ν n) :
    ν a ≤ ((n : ℝ) + 1) * μ a := by
  have h := ((hHahn n).2.1 (carrier μ ν n)).2 le_rfl a ha
  change 0 ≤ -(ν a - ((n : ℝ) + 1) * μ a) at h
  linarith

theorem carrier_maximal (μ ν : B → ℝ)
    (hHahn : ∀ n : ℕ, HahnJordanConclusions
      (fun a => ν a - ((n : ℝ) + 1) * μ a))
    (n : ℕ) (r : B)
    (hr : ∀ a, a ≤ r → ν a ≤ ((n : ℝ) + 1) * μ a) :
    r ≤ carrier μ ν n := by
  apply ((hHahn n).2.1 r).1
  intro a ha
  change 0 ≤ -(ν a - ((n : ℝ) + 1) * μ a)
  linarith [hr a ha]

theorem carrier_complement_bound (μ ν : B → ℝ)
    (hHahn : ∀ n : ℕ, HahnJordanConclusions
      (fun a => ν a - ((n : ℝ) + 1) * μ a)) (n : ℕ) :
    ((n : ℝ) + 1) * μ (carrier μ ν n)ᶜ ≤ ν (carrier μ ν n)ᶜ := by
  let d : B → ℝ := fun a => ν a - ((n : ℝ) + 1) * μ a
  have hcover : positiveCarrier d ⊔ negativeCarrier d = ⊤ := (hHahn n).2.2.1
  have hle : (negativeCarrier d)ᶜ ≤ positiveCarrier d := by
    calc
      (negativeCarrier d)ᶜ =
          (negativeCarrier d)ᶜ ⊓ (positiveCarrier d ⊔ negativeCarrier d) := by
        rw [hcover, inf_top_eq]
      _ = ((negativeCarrier d)ᶜ ⊓ positiveCarrier d) ⊔
          ((negativeCarrier d)ᶜ ⊓ negativeCarrier d) :=
        inf_sup_left (negativeCarrier d)ᶜ (positiveCarrier d) (negativeCarrier d)
      _ ≤ positiveCarrier d := sup_le inf_le_right (by simp)
  have h := ((hHahn n).1 (negativeCarrier d)ᶜ).2 hle _ le_rfl
  change 0 ≤ ν (carrier μ ν n)ᶜ - ((n : ℝ) + 1) * μ (carrier μ ν n)ᶜ at h
  linarith

/-- Hahn carriers give dominated truncations with arbitrarily small ν-tails. -/
theorem exists_small_carrier_complement (μ ν : B → ℝ)
    (hμpos : ∀ a, 0 ≤ μ a) (hμmono : Monotone μ) (hνmono : Monotone ν)
    (hνsplit : ∀ a, ν a + ν aᶜ = ν ⊤)
    (hac : ∀ a, μ a = 0 → ν a = 0)
    (hHahn : ∀ n : ℕ, HahnJordanConclusions
      (fun a => ν a - ((n : ℝ) + 1) * μ a))
    (hSup : ∀ s : Set B, s.Nonempty → DirectedOn (· ≤ ·) s →
      IsLUB (ν '' s) (ν (sSup s))) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ν (carrier μ ν n)ᶜ < ε := by
  let q : ℕ → B := carrier μ ν
  have hmono : Monotone q := monotone_carriers μ ν hμpos q
    (carrier_bound μ ν hHahn) (carrier_maximal μ ν hHahn)
  have hfull : ν (iSup q) = ν ⊤ := carrier_sup_full μ ν hμpos hμmono hνmono
    hνsplit hac q (carrier_complement_bound μ ν hHahn)
  apply exists_small_complement ν q hνsplit hfull
  · simpa only [sSup_range] using
      hSup (Set.range q) (Set.range_nonempty q) (directedOn_range.mpr hmono.directed_le)
  · exact hε

end Gelfand39Truncation
end
end Gelfand39Source10

/- Source module Work.Gelfand39ValuationSup; SHA256 de19a3a4ede458eb9d6a911c67ff01fcda84ad0e196a2921ca72926595378c78. -/
section Gelfand39Source11

set_option autoImplicit false
noncomputable section
open Set Filter QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand39ValuationSup
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

theorem disjoint_add (ν : B → ℝ) (hν : IsValuation ν)
    (p q : B) (hpq : Disjoint p q) : ν (p ⊔ q) = ν p + ν q := by
  have h := hν.2 p q
  rw [hpq.eq_bot, hν.1] at h
  linarith

theorem monotone_of_positive (ν : B → ℝ) (hν : IsValuation ν)
    (hpos : ∀ p, 0 ≤ ν p) : Monotone ν := by
  intro p q hpq
  have hunion : p ⊔ (q ⊓ pᶜ) = q := by
    rw [sup_inf_left, sup_eq_right.mpr hpq, sup_compl_eq_top, inf_top_eq]
  have hdis : Disjoint p (q ⊓ pᶜ) :=
    (disjoint_compl_right (a := p)).mono_right inf_le_right
  have h := disjoint_add ν hν p (q ⊓ pᶜ) hdis
  rw [hunion] at h
  linarith [hpos (q ⊓ pᶜ)]

/-- Real positive continuous valuations preserve each indicated actual directed
supremum in the order-theoretic sense as well as as a net limit. -/
theorem isLUB_image (ν : B → ℝ) (hν : IsContinuousValuation ν)
    (hpos : ∀ p, 0 ≤ ν p) (s : Set B) (hs : s.Nonempty)
    (hd : DirectedOn (· ≤ ·) s) :
    IsLUB (ν '' s) (ν (sSup s)) := by
  haveI : Nonempty s := hs.to_subtype
  haveI : IsDirected s (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hc, hac, hbc⟩ := hd a a.property b b.property
    exact ⟨⟨c, hc⟩, hac, hbc⟩⟩
  have hmono := monotone_of_positive ν hν.1 hpos
  refine ⟨?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact hmono (le_sSup hb)
  · intro c hc
    exact le_of_tendsto' (hν.2 s (sSup s) hs hd (isLUB_sSup s))
      (fun b => hc ⟨b.val, b.property, rfl⟩)

theorem sub_const_mul_continuous (μ ν : B → ℝ)
    (hμ : IsContinuousValuation μ) (hν : IsContinuousValuation ν) (C : ℝ) :
    IsContinuousValuation (fun p => ν p - C * μ p) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [hμ.1.1, hν.1.1, mul_zero, sub_self]
  · intro p q
    have h₁ := hμ.1.2 p q
    have h₂ := hν.1.2 p q
    linear_combination h₂ - C * h₁
  · intro s a hs hd ha
    exact (hν.2 s a hs hd ha).sub ((hμ.2 s a hs hd ha).const_mul C)

end Gelfand39ValuationSup
end
end Gelfand39Source11

/- Source module Work.Gelfand39JordanSource; SHA256 d42d3560b8be14075b9a9432cbc2621882fc317ee26982a17679a198bd23f907. -/
section Gelfand39Source12

universe u
set_option autoImplicit false

/- Reused accepted proof by fizzyinc3, submission e058f284-c40d-45c0-b2f0-1f111145c267, as audited in accepted Gelfand lemma 3.11. Namespace and theorem body unchanged from that accepted source. -/

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
end Gelfand39Source12

/- Source module Work.Gelfand39AbsoluteContinuity; SHA256 c11b8ea030b2b4445dd05c86ca40d701e9a1de5f9307dac5fb4ea8b609167588. -/
section Gelfand39Source13

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GelfandVNA.Duality Gelfand39OrderContinuity Gelfand311Jordan
open QAlgorithms.Papers.Independent.Support21.P20
open scoped ComplexOrder

namespace Gelfand39Truncation
universe u
variable {A X : Type u} [CommCStarAlgebra A] [WStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

local instance : LE (ProjAlg A) :=
  (inferInstance : BooleanAlgebra (ProjAlg A)).toPartialOrder.toLE
local instance : Preorder (ProjAlg A) :=
  (inferInstance : BooleanAlgebra (ProjAlg A)).toPartialOrder.toPreorder
local instance : PartialOrder (ProjAlg A) :=
  (inferInstance : BooleanAlgebra (ProjAlg A)).toPartialOrder

/-- The supplied complete structure retains the canonical Boolean operations. -/
def canonicalProjectionCompleteBooleanAlgebra : CompleteBooleanAlgebra (ProjAlg A) := by
  let sup : Set (ProjAlg A) → ProjAlg A := fun s => (Gelfand38.projections_complete s).choose
  have hsup (s : Set (ProjAlg A)) : IsLUB s (sup s) :=
    (Gelfand38.projections_complete s).choose_spec
  exact {
    (inferInstance : BooleanAlgebra (ProjAlg A)) with
    sSup := sup
    sInf := fun s => sup (lowerBounds s)
    isLUB_sSup := hsup
    isGLB_sInf := fun s => isLUB_lowerBounds.mp (hsup (lowerBounds s)) }

/-- A positive continuous projection valuation absolutely continuous with respect
to a fixed-predual positive functional has its own vector in that same predual. -/
theorem exists_predual_vector_of_absolute_continuity
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (μ ν : ProjAlg A → ℝ)
    (hμ : IsContinuousValuation μ) (hν : IsContinuousValuation ν)
    (hμpos : ∀ p, 0 ≤ μ p) (hνpos : ∀ p, 0 ≤ ν p)
    (Φ Ψ : A →L[ℂ] ℂ)
    (hΦ : ∀ p : ProjAlg A, Φ p.val = (μ p : ℂ))
    (hΨ : ∀ p : ProjAlg A, Ψ p.val = (ν p : ℂ))
    (hΦmult : ∀ b : A, ∃ x : X, ∀ a : A,
      Φ (star b * a) = star ((e.symm a) x))
    (hac : ∀ p, μ p = 0 → ν p = 0) :
    ∃ x : X, ∀ a : A, Ψ a = star ((e.symm a) x) := by
  letI := canonicalProjectionCompleteBooleanAlgebra (A := A)
  have hμmono := Gelfand39ValuationSup.monotone_of_positive μ hμ.1 hμpos
  have hνmono := Gelfand39ValuationSup.monotone_of_positive ν hν.1 hνpos
  have hνsplit (p : ProjAlg A) : ν p + ν pᶜ = ν ⊤ := by
    have h := hν.1.2 p pᶜ
    simpa only [sup_compl_eq_top, inf_compl_eq_bot, hν.1.1, add_zero] using h
  have hHahn (n : ℕ) : HahnJordanConclusions
      (fun p => ν p - ((n : ℝ) + 1) * μ p) := by
    apply (hahnJordan_decomposition (ProjAlg A)).1
    exact Or.inr ⟨fun _ => sup_compl_eq_top,
      Gelfand39ValuationSup.sub_const_mul_continuous μ ν hμ hν _⟩
  apply exists_predual_vector_of_dominated_bands e μ ν hμ.1.1
    (Gelfand39ValuationSup.disjoint_add μ hμ.1) hμpos hμmono hν.1.1
    (Gelfand39ValuationSup.disjoint_add ν hν.1) hνpos Φ Ψ hΦ hΨ hΦmult
  intro ε hε
  obtain ⟨n, hn⟩ := exists_small_carrier_complement μ ν hμpos hμmono hνmono
    hνsplit hac hHahn (Gelfand39ValuationSup.isLUB_image ν hν hνpos) ε hε
  refine ⟨carrier μ ν n, (n : ℝ) + 1, by positivity, ?_, hn.le⟩
  exact carrier_bound μ ν hHahn n

end Gelfand39Truncation
end
end Gelfand39Source13

/- Source module Work.Gelfand39ProjectionBand; SHA256 057120f0cafa2b835cc49dfcc16acdcefca15cd04df4f92729c4f489b943c322. -/
section Gelfand39Source14

set_option autoImplicit false

namespace Gelfand39ProjectionBand

open GelfandVNA.Duality Gelfand38 Gelfand39Inverse WeakDual

noncomputable section

lemma complex_eq_zero_of_norm_translate_bound (z : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ c : ℂ, ‖z + c‖ ≤ max r ‖c‖) : z = 0 := by
  by_contra hz
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let k : ℝ := (r + 1) / ‖z‖
  have hk : 0 < k := div_pos (by linarith) hn
  have hkn : k * ‖z‖ = r + 1 := div_mul_cancel₀ _ hn.ne'
  have hnorm : ‖k • z‖ = r + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk, hkn]
  have heq : z + k • z = (1 + k) • z := by rw [add_smul, one_smul]
  have ht := h (k • z)
  rw [hnorm, max_eq_right (by linarith), heq, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by linarith)] at ht
  nlinarith

variable {A : Type*} [CommCStarAlgebra A]

lemma projection_bandBall_iff (p : ProjAlg A) (r : ℝ) (hr : 0 ≤ r) (a : A) :
    (p.val * a = a ∧ ‖a‖ ≤ r) ↔
      ∀ c : ℂ, ‖a + c • (1 - p.val)‖ ≤ max r ‖c‖ := by
  constructor
  · rintro ⟨hpa, hnorm⟩ c
    rw [← gelfand_norm]
    apply (ContinuousMap.norm_le _ (hr.trans (le_max_left _ _))).mpr
    intro χ
    have hmul := congrArg (fun a : A => gelfandTransform ℂ A a χ) hpa
    simp only [map_mul, ContinuousMap.mul_apply] at hmul
    simp only [map_add, ContinuousMap.add_apply, map_smul, ContinuousMap.smul_apply,
      map_sub, ContinuousMap.sub_apply, map_one, ContinuousMap.one_apply, smul_eq_mul]
    rcases projection_value_zero_or_one p χ with hp | hp
    · have ha0 : gelfandTransform ℂ A a χ = 0 := by simpa only [hp, zero_mul] using hmul.symm
      rw [hp, ha0, sub_zero, mul_one, zero_add]
      exact le_max_right _ _
    · rw [hp, sub_self, mul_zero, add_zero]
      exact (character_norm_le χ a).trans (hnorm.trans (le_max_left _ _))
  · intro h
    have hn : ‖a‖ ≤ r := by
      simpa only [zero_smul, add_zero, norm_zero, max_eq_left hr] using h 0
    refine ⟨?_, hn⟩
    apply (gelfandTransform_isometry A).injective
    ext χ
    simp only [map_mul, ContinuousMap.mul_apply]
    rcases projection_value_zero_or_one p χ with hp | hp
    · have ha0 : gelfandTransform ℂ A a χ = 0 := by
        apply complex_eq_zero_of_norm_translate_bound _ r hr
        intro c
        have hi := (character_norm_le χ (a + c • (1 - p.val))).trans (h c)
        simpa only [map_add, ContinuousMap.add_apply, map_smul, ContinuousMap.smul_apply,
          map_sub, ContinuousMap.sub_apply, map_one, ContinuousMap.one_apply,
          hp, sub_zero, smul_eq_mul, mul_one] using hi
      rw [hp, ha0, mul_zero]
    · rw [hp, one_mul]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma isClosed_projection_bandBall (p : ProjAlg A) (r : ℝ) (hr : 0 ≤ r)
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) :
    IsClosed {w : WeakDual ℂ X |
      p.val * e (WeakDual.toStrongDual w) = e (WeakDual.toStrongDual w) ∧
        ‖e (WeakDual.toStrongDual w)‖ ≤ r} := by
  simp only [projection_bandBall_iff p r hr, Set.ofPred_forall]
  apply isClosed_iInter
  intro c
  simpa only [sub_neg_eq_add] using
    isClosed_normBall e (-(c • (1 - p.val))) (max r ‖c‖)


end
end Gelfand39ProjectionBand
end Gelfand39Source14

/- Source module Work.Gelfand39ProjectionGraph; SHA256 3e0d48f1c14a21ada87d8a39d6b8f1e4f5a7a520728045b70e9ee3636af707a9. -/
section Gelfand39Source15

set_option autoImplicit false

namespace Gelfand39ProjectionBand

open GelfandVNA.Duality Gelfand38 Gelfand39Inverse WeakDual

noncomputable section

lemma continuous_of_isClosed_graph {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [CompactSpace T] (f : S → T) (hg : IsClosed {z : S × T | f z.1 = z.2}) : Continuous f := by
  apply continuous_iff_isClosed.mpr
  intro C hC
  have hc := isClosedMap_fst_of_compactSpace
    ({z : S × T | f z.1 = z.2} ∩ Prod.snd ⁻¹' C) (hg.inter (hC.preimage continuous_snd))
  convert hc using 1
  ext x
  constructor
  · intro hx
    exact ⟨(x, f x), ⟨rfl, hx⟩, rfl⟩
  · rintro ⟨⟨y, z⟩, ⟨h, hz⟩, rfl⟩
    change f y ∈ C
    change f y = z at h
    change z ∈ C at hz
    rw [h]
    exact hz

variable {A : Type*} [CommCStarAlgebra A]

lemma projection_mul_norm_le (p : ProjAlg A) (a : A) : ‖p.val * a‖ ≤ ‖a‖ := by
  calc
    _ ≤ ‖p.val‖ * ‖a‖ := norm_mul_le _ _
    _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right
      (positiveUnit_norm_le (projection_positiveUnit p)) (norm_nonneg a)
    _ = ‖a‖ := one_mul _

lemma projection_graph_band_iff (p : ProjAlg A) (a b : A) (ha : ‖a‖ ≤ 1) :
    p.val * a = b ↔
      (p.val * b = b ∧ ‖b‖ ≤ 1) ∧
      ((pᶜ : ProjAlg A).val * (a - b) = a - b ∧ ‖a - b‖ ≤ 1) := by
  constructor
  · rintro rfl
    have hp : p.val * p.val = p.val := p.isStarProjection.1
    have he : a - p.val * a = (pᶜ : ProjAlg A).val * a := by
      change a - p.val * a = (1 - p.val) * a
      ring
    refine ⟨⟨?_, (projection_mul_norm_le p a).trans ha⟩, ?_⟩
    · rw [← mul_assoc, hp]
    · rw [he]
      constructor
      · rw [← mul_assoc, (pᶜ : ProjAlg A).isStarProjection.1]
      · exact (projection_mul_norm_le pᶜ a).trans ha
  · rintro ⟨⟨hpb, hbn⟩, hcomp, hcn⟩
    change (1 - p.val) * (a - b) = a - b at hcomp
    have hzero : p.val * (a - b) = 0 := by
      rw [sub_mul, one_mul, sub_eq_self] at hcomp
      exact hcomp
    have h := hzero
    rw [mul_sub, hpb, sub_eq_zero] at h
    exact h

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def weakUnitBall (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] : Set (WeakDual ℂ X) :=
  {w | ‖WeakDual.toStrongDual w‖ ≤ 1}

lemma isCompact_weakUnitBall : IsCompact (weakUnitBall X) := by
  simpa only [weakUnitBall, Set.preimage, Metric.mem_closedBall, dist_zero_right] using
    (WeakDual.isCompact_closedBall (0 : StrongDual ℂ X) 1)

def projectWeak (p : ProjAlg A) (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (w : WeakDual ℂ X) : WeakDual ℂ X :=
  StrongDual.toWeakDual (e.symm (p.val * e (WeakDual.toStrongDual w)))

lemma projectWeak_mem (p : ProjAlg A) (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    {w : WeakDual ℂ X} (hw : w ∈ weakUnitBall X) : projectWeak p e w ∈ weakUnitBall X := by
  change ‖e.symm (p.val * e (WeakDual.toStrongDual w))‖ ≤ 1
  rw [e.symm.norm_map]
  change ‖WeakDual.toStrongDual w‖ ≤ 1 at hw
  exact (projection_mul_norm_le p _).trans (by simpa only [e.norm_map] using hw)

lemma projectWeak_eq_iff (p : ProjAlg A) (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (w v : WeakDual ℂ X) : projectWeak p e w = v ↔
      p.val * e (WeakDual.toStrongDual w) = e (WeakDual.toStrongDual v) := by
  change (e.symm (p.val * e (WeakDual.toStrongDual w)) = WeakDual.toStrongDual v) ↔ _
  constructor
  · intro h
    simpa only [e.apply_symm_apply] using congrArg e h
  · intro h
    apply e.injective
    simpa only [e.apply_symm_apply] using h

def projectWeakBall (p : ProjAlg A) (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) :
    weakUnitBall X → weakUnitBall X :=
  fun w => ⟨projectWeak p e w.val, projectWeak_mem p e w.property⟩

lemma continuous_projectWeakBall (p : ProjAlg A) (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) :
    Continuous (projectWeakBall p e) := by
  letI : CompactSpace (weakUnitBall X) := isCompact_iff_compactSpace.mp isCompact_weakUnitBall
  apply continuous_of_isClosed_graph
  have hd : IsClosed {z : WeakDual ℂ X × WeakDual ℂ X |
      (pᶜ : ProjAlg A).val * (e (WeakDual.toStrongDual z.1) - e (WeakDual.toStrongDual z.2)) =
        e (WeakDual.toStrongDual z.1) - e (WeakDual.toStrongDual z.2) ∧
      ‖e (WeakDual.toStrongDual z.1) - e (WeakDual.toStrongDual z.2)‖ ≤ 1} := by
    convert (isClosed_projection_bandBall pᶜ 1 zero_le_one e).preimage
      (continuous_fst.sub continuous_snd) using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    change (_ ∧ _) ↔ (_ * e (WeakDual.toStrongDual z.1 - WeakDual.toStrongDual z.2) =
      e (WeakDual.toStrongDual z.1 - WeakDual.toStrongDual z.2) ∧
      ‖e (WeakDual.toStrongDual z.1 - WeakDual.toStrongDual z.2)‖ ≤ 1)
    rw [map_sub]
  have h1 := (isClosed_projection_bandBall p 1 zero_le_one e).preimage
    (continuous_subtype_val.comp (continuous_snd : Continuous (Prod.snd :
      weakUnitBall X × weakUnitBall X → weakUnitBall X)))
  have hc2 : Continuous (fun z : weakUnitBall X × weakUnitBall X => (z.1.val, z.2.val)) := by
    fun_prop
  have h2 := hd.preimage hc2
  convert h1.inter h2 using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
  rw [Subtype.ext_iff]
  change projectWeak p e z.1.val = z.2.val ↔ _
  rw [projectWeak_eq_iff]
  have hz1 : ‖WeakDual.toStrongDual z.1.val‖ ≤ 1 := z.1.property
  exact projection_graph_band_iff p _ _ (by simpa only [e.norm_map] using hz1)


end
end Gelfand39ProjectionBand
end Gelfand39Source15

/- Source module Work.Gelfand39StarGraph; SHA256 bd9eda9e636f47fb30ccf51eae62f05a93235636ba93460f59f30fb42124bbe3. -/
section Gelfand39Source16

set_option autoImplicit false

namespace Gelfand39ProjectionBand

open GelfandVNA.Duality Gelfand38 Gelfand39Inverse WeakDual

noncomputable section

variable {A : Type*} [CommCStarAlgebra A]

def halfSum (a b : A) : A := (1 / 2 : ℂ) • (a + b)
def imagHalfDiff (a b : A) : A := (Complex.I / 2) • (a - b)

lemma star_graph_unit_iff (a b : A) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    star a = b ↔
      (IsSelfAdjoint (halfSum a b) ∧ ‖halfSum a b‖ ≤ 1) ∧
      (IsSelfAdjoint (imagHalfDiff a b) ∧ ‖imagHalfDiff a b‖ ≤ 1) := by
  have hI : star (Complex.I : ℂ) = -Complex.I := by
    change (starRingEnd ℂ) Complex.I = -Complex.I
    exact Complex.conj_I
  have hnorm1 : ‖halfSum a b‖ ≤ 1 := by
    have h := norm_add_le a b
    dsimp [halfSum]
    rw [norm_smul]
    norm_num [norm_div]
    linarith
  have hnorm2 : ‖imagHalfDiff a b‖ ≤ 1 := by
    have h := norm_sub_le a b
    dsimp [imagHalfDiff]
    rw [norm_smul]
    norm_num [norm_div]
    linarith
  constructor
  · rintro rfl
    refine ⟨⟨?_, hnorm1⟩, ⟨?_, hnorm2⟩⟩
    · change star ((1 / 2 : ℂ) • (a + star a)) = (1 / 2 : ℂ) • (a + star a)
      simp [star_smul, add_comm]
    · change star ((Complex.I / 2) • (a - star a)) = (Complex.I / 2) • (a - star a)
      simp only [star_smul, star_div₀, hI, star_ofNat, star_sub, star_star]
      module
  · rintro ⟨⟨hx, hnx⟩, ⟨hy, hny⟩⟩
    have hi : (Complex.I : ℂ) * (Complex.I / 2) = -(1 / 2 : ℂ) := by
      rw [← mul_div_assoc, Complex.I_mul_I]
      norm_num
    have h1 : halfSum a b - Complex.I • imagHalfDiff a b = a := by
      dsimp [halfSum, imagHalfDiff]
      rw [smul_smul, hi]
      module
    have h2 : halfSum a b + Complex.I • imagHalfDiff a b = b := by
      dsimp [halfSum, imagHalfDiff]
      rw [smul_smul, hi]
      module
    calc
      star a = star (halfSum a b - Complex.I • imagHalfDiff a b) := congrArg star h1.symm
      _ = halfSum a b + Complex.I • imagHalfDiff a b := by
        rw [star_sub, star_smul, hx.star_eq, hy.star_eq, hI]
        module
      _ = b := h2

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma e_conj_smul (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (c : ℂ) (u : StrongDual ℂ X) :
    e (star c • u) = c • e u := by
  rw [e.map_smulₛₗ, starRingEnd_apply, star_star]

lemma isClosed_selfAdjoint_unit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) :
    IsClosed {w : WeakDual ℂ X |
      IsSelfAdjoint (e (WeakDual.toStrongDual w)) ∧ ‖e (WeakDual.toStrongDual w)‖ ≤ 1} := by
  simp only [selfAdjoint_unit_iff_norm_balls, Set.ofPred_forall]
  apply isClosed_iInter
  intro t
  simpa only [sub_neg_eq_add] using
    isClosed_normBall e (-(((t : ℂ) * Complex.I) • (1 : A))) (Real.sqrt (1 + t ^ 2))

def starWeak (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (w : WeakDual ℂ X) : WeakDual ℂ X :=
  StrongDual.toWeakDual (e.symm (star (e (WeakDual.toStrongDual w))))

lemma starWeak_mem (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    {w : WeakDual ℂ X} (hw : w ∈ weakUnitBall X) : starWeak e w ∈ weakUnitBall X := by
  change ‖e.symm (star (e (WeakDual.toStrongDual w)))‖ ≤ 1
  rw [e.symm.norm_map, norm_star, e.norm_map]
  exact hw

lemma starWeak_eq_iff (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (w v : WeakDual ℂ X) :
    starWeak e w = v ↔ star (e (WeakDual.toStrongDual w)) = e (WeakDual.toStrongDual v) := by
  change (e.symm (star (e (WeakDual.toStrongDual w))) = WeakDual.toStrongDual v) ↔ _
  constructor
  · intro h
    simpa only [e.apply_symm_apply] using congrArg e h
  · intro h
    apply e.injective
    simpa only [e.apply_symm_apply] using h

def starWeakBall (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) : weakUnitBall X → weakUnitBall X :=
  fun w => ⟨starWeak e w.val, starWeak_mem e w.property⟩

lemma continuous_starWeakBall (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) : Continuous (starWeakBall e) := by
  letI : CompactSpace (weakUnitBall X) := isCompact_iff_compactSpace.mp isCompact_weakUnitBall
  apply continuous_of_isClosed_graph
  have h1 : IsClosed {z : weakUnitBall X × weakUnitBall X |
      IsSelfAdjoint (halfSum (e (WeakDual.toStrongDual z.1.val)) (e (WeakDual.toStrongDual z.2.val))) ∧
      ‖halfSum (e (WeakDual.toStrongDual z.1.val)) (e (WeakDual.toStrongDual z.2.val))‖ ≤ 1} := by
    have hc : Continuous (fun z : weakUnitBall X × weakUnitBall X =>
        star (1 / 2 : ℂ) • (z.1.val + z.2.val)) := by fun_prop
    convert (isClosed_selfAdjoint_unit e).preimage hc using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    change (_ ∧ _) ↔ (IsSelfAdjoint (e (star (1 / 2 : ℂ) •
      (WeakDual.toStrongDual z.1.val + WeakDual.toStrongDual z.2.val))) ∧
      ‖e (star (1 / 2 : ℂ) • (WeakDual.toStrongDual z.1.val + WeakDual.toStrongDual z.2.val))‖ ≤ 1)
    simp only [e_conj_smul, map_add, halfSum]
  have h2 : IsClosed {z : weakUnitBall X × weakUnitBall X |
      IsSelfAdjoint (imagHalfDiff (e (WeakDual.toStrongDual z.1.val)) (e (WeakDual.toStrongDual z.2.val))) ∧
      ‖imagHalfDiff (e (WeakDual.toStrongDual z.1.val)) (e (WeakDual.toStrongDual z.2.val))‖ ≤ 1} := by
    have hc : Continuous (fun z : weakUnitBall X × weakUnitBall X =>
        star (Complex.I / 2) • (z.1.val - z.2.val)) := by fun_prop
    convert (isClosed_selfAdjoint_unit e).preimage hc using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    change (_ ∧ _) ↔ (IsSelfAdjoint (e (star (Complex.I / 2) •
      (WeakDual.toStrongDual z.1.val - WeakDual.toStrongDual z.2.val))) ∧
      ‖e (star (Complex.I / 2) • (WeakDual.toStrongDual z.1.val - WeakDual.toStrongDual z.2.val))‖ ≤ 1)
    simp only [e_conj_smul, map_sub, imagHalfDiff]
  convert h1.inter h2 using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [Subtype.ext_iff]
  change starWeak e z.1.val = z.2.val ↔ _
  rw [starWeak_eq_iff]
  have hz1 : ‖WeakDual.toStrongDual z.1.val‖ ≤ 1 := z.1.property
  have hz2 : ‖WeakDual.toStrongDual z.2.val‖ ≤ 1 := z.2.property
  exact star_graph_unit_iff _ _ (by simpa only [e.norm_map] using hz1)
    (by simpa only [e.norm_map] using hz2)


end
end Gelfand39ProjectionBand
end Gelfand39Source16

/- Source module Work.Gelfand39ProjectionEvaluation; SHA256 14d005ded358a475c5aaa236352486de11f8e7e92fc554665e16f9cad3274b7a. -/
section Gelfand39Source17

set_option autoImplicit false

namespace Gelfand39ProjectionBand

open GelfandVNA.Duality WeakDual
noncomputable section

variable {A X : Type*} [CommCStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Evaluation at a fixed vector in a supplied predual. -/
def fixedEvaluation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) : A →L[ℂ] ℂ where
  toFun a := star ((e.symm a) x)
  map_add' := by intro a b; simp
  map_smul' := by
    intro c a
    rw [e.symm.map_smulₛₗ]
    simp
  cont := by fun_prop

/-- Restrict a fixed predual evaluation to the band of a projection. -/
def projectionEvaluation (p : ProjAlg A) (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    A →L[ℂ] ℂ where
  toFun a := fixedEvaluation e x (p.val * a)
  map_add' := by intro a b; rw [mul_add, map_add]
  map_smul' := by intro c a; rw [mul_smul_comm, map_smul]; rfl
  cont := by fun_prop

/-- Conjugate a fixed predual evaluation by the algebra adjoint. -/
def adjointEvaluation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) : A →L[ℂ] ℂ where
  toFun a := (e.symm (star a)) x
  map_add' := by intro a b; simp
  map_smul' := by
    intro c a
    rw [star_smul, e.symm.map_smulₛₗ]
    simp
  cont := by fun_prop

lemma fixedEvaluation_add_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x y : X) (a : A) :
    fixedEvaluation e (x + y) a = fixedEvaluation e x a + fixedEvaluation e y a := by
  simp only [fixedEvaluation, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, map_add, star_add]

lemma fixedEvaluation_conj_smul_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (c : ℂ) (x : X) (a : A) :
    fixedEvaluation e (star c • x) a = c • fixedEvaluation e x a := by
  change star ((e.symm a) (star c • x)) = c • star ((e.symm a) x)
  rw [map_smul, star_smul, star_star]

lemma adjointEvaluation_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (x : X) (p : ProjAlg A) :
    adjointEvaluation e x p.val = star (fixedEvaluation e x p.val) := by
  change (e.symm (star p.val)) x = star (star ((e.symm p.val) x))
  rw [p.isStarProjection.2.star_eq, star_star]

lemma continuous_projectionEvaluation_ball (p : ProjAlg A)
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    Continuous (fun w : weakUnitBall X => projectionEvaluation p e x (e (toStrongDual w.val))) := by
  have hc := ((WeakDual.eval_continuous (𝕜 := ℂ) x).comp continuous_subtype_val).comp
    (continuous_projectWeakBall p e)
  exact hc.star

lemma continuous_adjointEvaluation_ball (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    Continuous (fun w : weakUnitBall X => adjointEvaluation e x (e (toStrongDual w.val))) := by
  exact ((WeakDual.eval_continuous (𝕜 := ℂ) x).comp continuous_subtype_val).comp
    (continuous_starWeakBall e)


end
end Gelfand39ProjectionBand
end Gelfand39Source17

/- Source module Work.Gelfand39PredualBall; SHA256 27a86e121b8c59b2d1c8bf5a066eac6a25d0d421f1c098f3ddd489efc126345b. -/
section Gelfand39Source18

set_option autoImplicit false
noncomputable section
open Set Filter Topology WeakDual

namespace Gelfand39Predual
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Weak-star continuity on the closed norm unit ball already forces a
bounded bidual functional to come from the given complete predual. -/
theorem eval_of_weakStarContinuousOn_ball (Φ : StrongDual ℂ (StrongDual ℂ X))
    (hΦ : ContinuousOn (fun w : WeakDual ℂ X => Φ (WeakDual.toStrongDual w))
      (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ X) 1)) :
    ∃ x : X, ∀ f : StrongDual ℂ X, Φ f = f x := by
  classical
  apply eval_of_finite_kernel_control Φ
  intro ε hε
  let K : Set (WeakDual ℂ X) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ X) 1
  let g : WeakDual ℂ X → ℂ := fun w => Φ (WeakDual.toStrongDual w)
  have hz : (0 : WeakDual ℂ X) ∈ K := by simp [K]
  have hc : ContinuousWithinAt g K 0 := hΦ 0 hz
  have hsmall : {w : WeakDual ℂ X | ‖g w‖ < ε} ∈ nhdsWithin 0 K := by
    have h := hc.preimage_mem_nhdsWithin (Metric.ball_mem_nhds (g 0) hε)
    change {w : WeakDual ℂ X | dist (g w) (g 0) < ε} ∈ nhdsWithin 0 K at h
    simpa only [g, map_zero, dist_zero_right] using h
  obtain ⟨U, hU, hUK⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hsmall
  obtain ⟨⟨s, r⟩, hr, hsub⟩ :=
    ((topDualPairing ℂ X).weakBilin_withSeminorms.hasBasis_zero_ball).mem_iff.mp hU
  refine ⟨s, ?_⟩
  intro f hf hzero
  have hfU : StrongDual.toWeakDual f ∈ U := by
    apply hsub
    rw [Seminorm.ball_zero_eq]
    apply Seminorm.finset_sup_apply_lt hr
    intro x hx
    change ‖f x‖ < r
    rw [hzero x hx, norm_zero]
    exact hr
  have hfK : StrongDual.toWeakDual f ∈ K := by
    change dist f (0 : StrongDual ℂ X) ≤ 1
    simpa only [dist_zero_right] using hf
  exact (hUK ⟨hfU, hfK⟩).le

end Gelfand39Predual
end
end Gelfand39Source18

/- Source module Work.Gelfand39NormalOnBall; SHA256 bcfdc1f3030b7f477cf51e833e246847856c39af5aee1e7352fd45a26645bac3. -/
section Gelfand39Source19

set_option autoImplicit false
noncomputable section
open WeakDual GelfandVNA.Duality

namespace Gelfand39Predual
universe u
variable {A X : Type u} [CStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The unit-ball criterion keeps the witness in the supplied fixed predual. -/
theorem exists_predual_vector_of_weakStarContinuousOn_ball
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (Φ : A →L[ℂ] ℂ)
    (hΦ : ContinuousOn (fun w : WeakDual ℂ X => Φ (e (WeakDual.toStrongDual w)))
      (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ X) 1)) :
    ∃ x : X, ∀ a : A, Φ a = star ((e.symm a) x) := by
  let ψ : StrongDual ℂ X →L[ℂ] ℂ := {
    toFun := fun f => star (Φ (e f))
    map_add' := by
      intro f g
      simp
    map_smul' := by
      intro c f
      change star (Φ (e (c • f))) = c • star (Φ (e f))
      rw [e.map_smulₛₗ, Φ.map_smul]
      simp
    cont := (Φ.continuous.comp e.continuous).star }
  have hc : ContinuousOn (fun w : WeakDual ℂ X => ψ (WeakDual.toStrongDual w))
      (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ X) 1) := hΦ.star
  obtain ⟨x, hx⟩ := eval_of_weakStarContinuousOn_ball ψ hc
  refine ⟨x, ?_⟩
  intro a
  have h := hx (e.symm a)
  change star (Φ (e (e.symm a))) = (e.symm a) x at h
  rw [e.apply_symm_apply] at h
  rw [← h, star_star]

/-- Continuity on the fixed predual's closed norm unit ball suffices for the
exact canonical normal-functional predicate. -/
theorem normal_of_weakStarContinuousOn_ball (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (Φ : A →L[ℂ] ℂ)
    (hΦ : ContinuousOn (fun w : WeakDual ℂ X => Φ (e (WeakDual.toStrongDual w)))
      (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ X) 1)) :
    IsNormalFunctional Φ := by
  obtain ⟨x, hx⟩ := exists_predual_vector_of_weakStarContinuousOn_ball e Φ hΦ
  exact ⟨X, inferInstance, inferInstance, inferInstance, e, x, hx⟩

end Gelfand39Predual
end
end Gelfand39Source19

/- Source module Work.Gelfand39NormalActions; SHA256 ae7ca5c5341e9a57e1fee4dbe382a54c0bce5daaf4cbfb4e662a251a59fa5fb0. -/
section Gelfand39Source20

set_option autoImplicit false

namespace Gelfand39ProjectionBand

open GelfandVNA.Duality WeakDual Gelfand39Predual
noncomputable section
universe u

variable {A X : Type u} [CommCStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma weakUnitBall_eq : weakUnitBall X =
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ X) 1 := by
  ext w
  simp only [weakUnitBall, Set.mem_ofPred_eq, Set.mem_preimage,
    Metric.mem_closedBall, dist_zero_right]

/-- The projection-band action preserves the original supplied predual. -/
theorem exists_projection_vector (p : ProjAlg A)
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    ∃ y : X, ∀ a, projectionEvaluation p e x a = fixedEvaluation e y a := by
  apply exists_predual_vector_of_weakStarContinuousOn_ball e (projectionEvaluation p e x)
  rw [← weakUnitBall_eq]
  exact continuousOn_iff_continuous_restrict.mpr (continuous_projectionEvaluation_ball p e x)

/-- Adjoint-conjugation of functionals preserves the original supplied predual. -/
theorem exists_adjoint_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    ∃ y : X, ∀ a, adjointEvaluation e x a = fixedEvaluation e y a := by
  apply exists_predual_vector_of_weakStarContinuousOn_ball e (adjointEvaluation e x)
  rw [← weakUnitBall_eq]
  exact continuousOn_iff_continuous_restrict.mpr (continuous_adjointEvaluation_ball e x)

theorem normal_projection (p : ProjAlg A) (φ : A → ℂ) (hφ : IsNormalFunctional φ) :
    IsNormalFunctional (fun a => φ (p.val * a)) := by
  obtain ⟨Y, hY, hN, hC, e, x, hx⟩ := hφ
  obtain ⟨y, hy⟩ := exists_projection_vector p e x
  refine ⟨Y, inferInstance, inferInstance, inferInstance, e, y, ?_⟩
  intro a
  change φ (p.val * a) = star ((e.symm a) y)
  rw [hx]
  exact hy a

theorem normal_adjoint (φ : A → ℂ) (hφ : IsNormalFunctional φ) :
    IsNormalFunctional (fun a => star (φ (star a))) := by
  obtain ⟨Y, hY, hN, hC, e, x, hx⟩ := hφ
  obtain ⟨y, hy⟩ := exists_adjoint_vector e x
  refine ⟨Y, inferInstance, inferInstance, inferInstance, e, y, ?_⟩
  intro a
  change star (φ (star a)) = star ((e.symm a) y)
  rw [hx, star_star]
  exact hy a


end
end Gelfand39ProjectionBand
end Gelfand39Source20

/- Source module Work.Gelfand39Hermitian; SHA256 1a122da1318b360ce98c3d858e419838a11df86751a8e3a3a2b10d926b8f2119. -/
section Gelfand39Source21

set_option autoImplicit false

namespace Gelfand39ProjectionBand
open GelfandVNA.Duality WeakDual Gelfand39Predual
noncomputable section
universe u
variable {A X : Type u} [CommCStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def realEvaluation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) : A →L[ℂ] ℂ :=
  (1 / 2 : ℂ) • (fixedEvaluation e x + adjointEvaluation e x)

def imagEvaluation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) : A →L[ℂ] ℂ :=
  (-Complex.I / 2) • (fixedEvaluation e x - adjointEvaluation e x)

lemma realEvaluation_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (x : X) (p : ProjAlg A) :
    realEvaluation e x p.val = ((fixedEvaluation e x p.val).re : ℂ) := by
  change (1 / 2 : ℂ) * (fixedEvaluation e x p.val + adjointEvaluation e x p.val) = _
  rw [adjointEvaluation_projection]
  change (1 / 2 : ℂ) * (fixedEvaluation e x p.val +
    (starRingEnd ℂ) (fixedEvaluation e x p.val)) = _
  rw [Complex.add_conj, Complex.ofReal_mul]
  norm_num <;> ring

lemma imagEvaluation_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (x : X) (p : ProjAlg A) :
    imagEvaluation e x p.val = ((fixedEvaluation e x p.val).im : ℂ) := by
  change (-Complex.I / 2) * (fixedEvaluation e x p.val - adjointEvaluation e x p.val) = _
  rw [adjointEvaluation_projection]
  change (-Complex.I / 2) * (fixedEvaluation e x p.val -
    (starRingEnd ℂ) (fixedEvaluation e x p.val)) = _
  rw [Complex.sub_conj, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hI := Complex.I_mul_I
  linear_combination -((fixedEvaluation e x p.val).im : ℂ) * hI

lemma continuous_fixedEvaluation_ball (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    Continuous (fun w : weakUnitBall X => fixedEvaluation e x (e (toStrongDual w.val))) := by
  have hc := ((WeakDual.eval_continuous (𝕜 := ℂ) x).comp
    (continuous_subtype_val : Continuous (Subtype.val : weakUnitBall X → WeakDual ℂ X))).star
  simpa only [fixedEvaluation, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, e.symm_apply_apply, WeakDual.toStrongDual_apply, Function.comp_def] using hc

lemma exists_real_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    ∃ y : X, ∀ a, realEvaluation e x a = fixedEvaluation e y a := by
  apply exists_predual_vector_of_weakStarContinuousOn_ball e (realEvaluation e x)
  rw [← weakUnitBall_eq]
  apply continuousOn_iff_continuous_restrict.mpr
  exact (continuous_fixedEvaluation_ball e x |>.add
    (continuous_adjointEvaluation_ball e x)).const_smul (1 / 2 : ℂ)

lemma exists_imag_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    ∃ y : X, ∀ a, imagEvaluation e x a = fixedEvaluation e y a := by
  apply exists_predual_vector_of_weakStarContinuousOn_ball e (imagEvaluation e x)
  rw [← weakUnitBall_eq]
  apply continuousOn_iff_continuous_restrict.mpr
  exact (continuous_fixedEvaluation_ball e x |>.sub
    (continuous_adjointEvaluation_ball e x)).const_smul (-Complex.I / 2)

end
end Gelfand39ProjectionBand
end Gelfand39Source21

/- Source module Work.Gelfand39ForwardCore; SHA256 9b85295d30d57f362080c9c0a173ac0bd1b569b27f36e5a3aad0209088077339. -/
section Gelfand39Source22

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
end Gelfand39Source22

/- Source module Work.Gelfand39NormalJordan; SHA256 c1588cf21d510abd79835cbe8dc6f1d59f8df5ae9b5149f67bb4041baf61d94d. -/
section Gelfand39Source23

set_option autoImplicit false

namespace Gelfand39NormalJordan
open GelfandVNA.Duality Gelfand38 Gelfand39 Gelfand39Inverse Gelfand39ProjectionBand
open Gelfand39OrderContinuity Gelfand311Jordan
open QAlgorithms.Papers.Independent.Support21.P20
open scoped ComplexOrder
noncomputable section
universe u
variable {A X : Type u} [CommCStarAlgebra A] [WStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def projectionCompleteBooleanAlgebra (A : Type u) [CommCStarAlgebra A]
    [WStarAlgebra A] : CompleteBooleanAlgebra (ProjAlg A) := by
  let sup : Set (ProjAlg A) → ProjAlg A := fun s => (projections_complete s).choose
  have hsup (s : Set (ProjAlg A)) : IsLUB s (sup s) := (projections_complete s).choose_spec
  exact {
    (inferInstance : BooleanAlgebra (ProjAlg A)) with
    sSup := sup
    sInf := fun s => sup (lowerBounds s)
    isLUB_sSup := hsup
    isGLB_sInf := fun s => isLUB_lowerBounds.mp (hsup (lowerBounds s)) }

/-- Real-on-projections fixed-predual functionals have a positive Jordan
split whose two representing vectors remain in that same predual. -/
theorem real_jordan_vectors (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X)
    (hx : ∀ p : ProjAlg A, (fixedEvaluation e x p.val).im = 0) :
    letI := CStarAlgebra.spectralOrder A
    ∃ y z : X,
      (∀ a : A, 0 ≤ a → 0 ≤ fixedEvaluation e y a) ∧
      (∀ a : A, 0 ≤ a → 0 ≤ fixedEvaluation e z a) ∧
      ∀ a : A, fixedEvaluation e x a = fixedEvaluation e y a - fixedEvaluation e z a := by
  letI := CStarAlgebra.spectralOrder A
  letI := CStarAlgebra.spectralOrderedRing A
  letI := projectionCompleteBooleanAlgebra A
  let ν : ProjAlg A → ℝ := fun p => (fixedEvaluation e x p.val).re
  have hreal (p : ProjAlg A) : fixedEvaluation e x p.val = (ν p : ℂ) := by
    apply Complex.ext
    · rfl
    · exact hx p
  have hn : IsNormalFunctional (fixedEvaluation e x) :=
    ⟨X, inferInstance, inferInstance, inferInstance, e, x, fun _ => rfl⟩
  have hc := normal_restrict_isContinuousValuation (fixedEvaluation e x) hn
  have hν : IsContinuousValuation ν := g72gk34_cmap Complex.re Complex.zero_re
    Complex.add_re Complex.continuous_re hc
  have hj := (hahnJordan_decomposition (ProjAlg A)).1 ν
    (Or.inr ⟨fun _ => sup_compl_eq_top, hν⟩)
  rcases hj with ⟨_, _, _, _, hpn, hmn, hp, hm, hsplit⟩
  obtain ⟨y, hy⟩ := exists_projection_vector (positiveCarrier ν) e x
  obtain ⟨w, hw⟩ := exists_projection_vector (negativeCarrier ν) e x
  have hneg (a : A) : fixedEvaluation e (-w) a = -fixedEvaluation e w a := by
    change star ((e.symm a) (-w)) = -star ((e.symm a) w)
    rw [map_neg, star_neg]
  have hyproj (p : ProjAlg A) : fixedEvaluation e y p.val = (jordanPositive ν p : ℂ) := by
    rw [← hy p.val]
    change fixedEvaluation e x (positiveCarrier ν ⊓ p).val = _
    exact hreal _
  have hzproj (p : ProjAlg A) : fixedEvaluation e (-w) p.val = (jordanNegative ν p : ℂ) := by
    rw [hneg, ← hw p.val]
    change -fixedEvaluation e x (negativeCarrier ν ⊓ p).val = _
    rw [hreal]
    exact (Complex.ofReal_neg _).symm
  refine ⟨y, -w, ?_, ?_, ?_⟩
  · intro a ha
    exact extension_nonneg (jordanPositive ν) hpn.1.1.1
      (fun p q hd => g72gk34_disj hpn hd.eq_bot) hp (fixedEvaluation e y) hyproj ha
  · intro a ha
    exact extension_nonneg (jordanNegative ν) hmn.1.1.1
      (fun p q hd => g72gk34_disj hmn hd.eq_bot) hm (fixedEvaluation e (-w)) hzproj ha
  · have he : fixedEvaluation e x = fixedEvaluation e y - fixedEvaluation e (-w) := by
      apply ContinuousLinearMap.ext_on (projection_span_dense A)
      rintro a ⟨p, rfl⟩
      change fixedEvaluation e x p.val = fixedEvaluation e y p.val - fixedEvaluation e (-w) p.val
      rw [hreal, hyproj, hzproj]
      exact_mod_cast hsplit p
    intro a
    exact congrArg (fun F : A →L[ℂ] ℂ => F a) he

/-- Every evaluation in a fixed predual splits into four positive evaluations
in that same predual, with the usual real/imaginary Jordan identity. -/
theorem complex_jordan_vectors (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    letI := CStarAlgebra.spectralOrder A
    ∃ y₁ y₂ y₃ y₄ : X,
      (∀ a : A, 0 ≤ a → 0 ≤ fixedEvaluation e y₁ a) ∧
      (∀ a : A, 0 ≤ a → 0 ≤ fixedEvaluation e y₂ a) ∧
      (∀ a : A, 0 ≤ a → 0 ≤ fixedEvaluation e y₃ a) ∧
      (∀ a : A, 0 ≤ a → 0 ≤ fixedEvaluation e y₄ a) ∧
      ∀ a : A, fixedEvaluation e x a = fixedEvaluation e y₁ a - fixedEvaluation e y₂ a +
        Complex.I * (fixedEvaluation e y₃ a - fixedEvaluation e y₄ a) := by
  letI := CStarAlgebra.spectralOrder A
  obtain ⟨xr, hxr⟩ := exists_real_vector e x
  obtain ⟨xi, hxi⟩ := exists_imag_vector e x
  have hr (p : ProjAlg A) : (fixedEvaluation e xr p.val).im = 0 := by
    rw [← hxr, realEvaluation_projection]
    rfl
  have hi (p : ProjAlg A) : (fixedEvaluation e xi p.val).im = 0 := by
    rw [← hxi, imagEvaluation_projection]
    rfl
  obtain ⟨y₁, y₂, hy₁, hy₂, hyr⟩ := real_jordan_vectors e xr hr
  obtain ⟨y₃, y₄, hy₃, hy₄, hyi⟩ := real_jordan_vectors e xi hi
  refine ⟨y₁, y₂, y₃, y₄, hy₁, hy₂, hy₃, hy₄, ?_⟩
  have he : fixedEvaluation e x = realEvaluation e x + Complex.I • imagEvaluation e x := by
    apply ContinuousLinearMap.ext_on (projection_span_dense A)
    rintro a ⟨p, rfl⟩
    change fixedEvaluation e x p.val = realEvaluation e x p.val + Complex.I * imagEvaluation e x p.val
    rw [realEvaluation_projection, imagEvaluation_projection]
    simpa only [mul_comm] using (Complex.re_add_im (fixedEvaluation e x p.val)).symm
  intro a
  have h := congrArg (fun F : A →L[ℂ] ℂ => F a) he
  change fixedEvaluation e x a = realEvaluation e x a + Complex.I * imagEvaluation e x a at h
  rw [hxr, hxi, hyr, hyi] at h
  exact h

/-- Positive evaluations in any fixed supplied predual detect every nonzero
canonical projection. -/
theorem positive_evaluation_separates_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (p : ProjAlg A) (hp : p ≠ ⊥) :
    letI := CStarAlgebra.spectralOrder A
    ∃ y : X, (∀ a : A, 0 ≤ a → 0 ≤ fixedEvaluation e y a) ∧ fixedEvaluation e y p.val ≠ 0 := by
  classical
  letI := CStarAlgebra.spectralOrder A
  have hex : ∃ x : X, fixedEvaluation e x p.val ≠ 0 := by
    by_contra h
    push Not at h
    have hz : e.symm p.val = 0 := by
      ext x
      exact star_eq_zero.mp (h x)
    have hpv : p.val = 0 := by
      simpa only [e.apply_symm_apply, map_zero] using congrArg e hz
    apply hp
    apply Subtype.ext
    apply Subtype.ext
    exact hpv
  obtain ⟨x, hx⟩ := hex
  obtain ⟨y₁, y₂, y₃, y₄, hy₁, hy₂, hy₃, hy₄, he⟩ := complex_jordan_vectors e x
  by_cases h₁ : fixedEvaluation e y₁ p.val = 0
  · by_cases h₂ : fixedEvaluation e y₂ p.val = 0
    · by_cases h₃ : fixedEvaluation e y₃ p.val = 0
      · refine ⟨y₄, hy₄, ?_⟩
        intro h₄
        apply hx
        rw [he, h₁, h₂, h₃, h₄]
        simp
      · exact ⟨y₃, hy₃, h₃⟩
    · exact ⟨y₂, hy₂, h₂⟩
  · exact ⟨y₁, hy₁, h₁⟩

end
end Gelfand39NormalJordan
end Gelfand39Source23

/- Source module Work.Gelfand39FaithfulValuation; SHA256 a6e7c4a5a11460e52e760cbb13007f9d19911b906cb3272025e78c3d0c80768c. -/
section Gelfand39Source24

set_option autoImplicit false
noncomputable section
open Set

namespace Gelfand39FaithfulValuation
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

/-- Faithfulness makes a finite positive valuation strictly increasing. -/
theorem strictMono_of_faithful (ν : B → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ a b, ν a + ν b = ν (a ⊔ b) + ν (a ⊓ b))
    (hpos : ∀ a, 0 ≤ ν a) (hfaithful : ∀ a, ν a = 0 → a = ⊥) :
    StrictMono ν := by
  intro a b hab
  let d := b ⊓ aᶜ
  have hd : d ≠ ⊥ := by
    intro hd
    have hba : b ≤ a := by
      calc
        b = b ⊓ (a ⊔ aᶜ) := by simp
        _ = (b ⊓ a) ⊔ (b ⊓ aᶜ) := inf_sup_left b a aᶜ
        _ = b ⊓ a := by change (b ⊓ a) ⊔ d = b ⊓ a; rw [hd, sup_bot_eq]
        _ ≤ a := inf_le_right
    exact (not_le_of_gt hab) hba
  have hdpos : 0 < ν d := lt_of_le_of_ne (hpos d) (by
    intro h
    exact hd (hfaithful d h.symm))
  have hunion : a ⊔ d = b := by
    dsimp [d]
    rw [sup_inf_left, sup_eq_right.mpr hab.le, sup_compl_eq_top, inf_top_eq]
  have hinter : a ⊓ d = ⊥ := by
    dsimp [d]
    calc
      a ⊓ (b ⊓ aᶜ) = (a ⊓ aᶜ) ⊓ b := by ac_rfl
      _ = ⊥ := by simp
  have h := hadd a d
  rw [hunion, hinter, hzero] at h
  linarith

/-- Directed-supremum continuity makes the supremum of all null elements null. -/
theorem null_sup_null (ν : B → ℝ) (hzero : ν ⊥ = 0)
    (hadd : ∀ a b, ν a + ν b = ν (a ⊔ b) + ν (a ⊓ b))
    (hpos : ∀ a, 0 ≤ ν a)
    (hSup : ∀ s : Set B, s.Nonempty → DirectedOn (· ≤ ·) s →
      IsLUB (ν '' s) (ν (sSup s))) :
    ν (sSup {b : B | ν b = 0}) = 0 := by
  let s : Set B := {b | ν b = 0}
  have hs : s.Nonempty := ⟨⊥, hzero⟩
  have hd : DirectedOn (· ≤ ·) s := by
    intro a ha b hb
    have h := hadd a b
    change ν a = 0 at ha
    change ν b = 0 at hb
    rw [ha, hb] at h
    have hjoin : ν (a ⊔ b) = 0 := by
      have h₁ := hpos (a ⊔ b)
      have h₂ := hpos (a ⊓ b)
      linarith
    exact ⟨a ⊔ b, hjoin, le_sup_left, le_sup_right⟩
  have hle : ν (sSup s) ≤ 0 := (hSup s hs hd).2 (by
    rintro y ⟨b, hb, rfl⟩
    exact le_of_eq hb)
  exact le_antisymm hle (hpos _)

/-- The complement of the maximal null element is a faithful principal part. -/
theorem faithful_on_null_complement (ν : B → ℝ) (hpos : ∀ a, 0 ≤ ν a)
    (hmono : Monotone ν)
    (hnull : ν (sSup {b : B | ν b = 0}) = 0)
    (b : B) (hb : b ≤ (sSup {c : B | ν c = 0})ᶜ) (hbzero : ν b = 0) :
    b = ⊥ := by
  let n : B := sSup {c : B | ν c = 0}
  have hn : b ≤ n := le_sSup hbzero
  exact bot_unique ((le_inf hn hb).trans (by simp [n]))

/-- Nullity is exactly membership below the maximal null element. -/
theorem null_iff_le_null_sup (ν : B → ℝ) (hpos : ∀ a, 0 ≤ ν a)
    (hmono : Monotone ν) (hnull : ν (sSup {b : B | ν b = 0}) = 0) (b : B) :
    ν b = 0 ↔ b ≤ sSup {c : B | ν c = 0} := by
  constructor
  · intro hb
    exact le_sSup hb
  · intro hb
    exact le_antisymm ((hmono hb).trans_eq hnull) (hpos b)

end Gelfand39FaithfulValuation
end
end Gelfand39Source24

/- Source module Work.Gelfand39FaithfulCover; SHA256 d453a3cde7bbec4ea85f0e44cb4a42755ea4a4ec62339018de797a3e6cd3e6c9. -/
section Gelfand39Source25

set_option autoImplicit false
noncomputable section
open Set Filter

namespace Gelfand39FaithfulCover
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

theorem strictMonoOn_of_faithful_on (ν : B → ℝ) (p : B) (hzero : ν ⊥ = 0)
    (hadd : ∀ a b, ν a + ν b = ν (a ⊔ b) + ν (a ⊓ b))
    (hpos : ∀ a, 0 ≤ ν a)
    (hfaithful : ∀ a, a ≤ p → ν a = 0 → a = ⊥) :
    StrictMonoOn ν (Set.Iic p) := by
  intro a ha b hb hab
  let d := b ⊓ aᶜ
  have hdle : d ≤ p := inf_le_left.trans hb
  have hd : d ≠ ⊥ := by
    intro hd
    have hba : b ≤ a := by
      calc
        b = b ⊓ (a ⊔ aᶜ) := by simp
        _ = (b ⊓ a) ⊔ (b ⊓ aᶜ) := inf_sup_left b a aᶜ
        _ = b ⊓ a := by change (b ⊓ a) ⊔ d = b ⊓ a; rw [hd, sup_bot_eq]
        _ ≤ a := inf_le_right
    exact (not_le_of_gt hab) hba
  have hdpos : 0 < ν d := lt_of_le_of_ne (hpos d) (by
    intro h
    exact hd (hfaithful d hdle h.symm))
  have hunion : a ⊔ d = b := by
    dsimp [d]
    rw [sup_inf_left, sup_eq_right.mpr hab.le, sup_compl_eq_top, inf_top_eq]
  have hinter : a ⊓ d = ⊥ := by
    dsimp [d]
    calc
      a ⊓ (b ⊓ aᶜ) = (a ⊓ aᶜ) ⊓ b := by ac_rfl
      _ = ⊥ := by simp
  have h := hadd a d
  rw [hunion, hinter, hzero] at h
  linarith

/-- Countable selection within a faithful principal part needs no Boolean
algebra structure on the subtype interval. -/
theorem exists_sequence_sup_on (ν : B → ℝ) (hmono : Monotone ν) (p : B)
    (hν : StrictMonoOn ν (Set.Iic p))
    (s : Set B) (hs : s.Nonempty) (hsp : s ⊆ Set.Iic p)
    (hSup : IsLUB (ν '' s) (ν (sSup s))) :
    ∃ f : ℕ → B, (∀ n, f n ∈ s) ∧ iSup f = sSup s := by
  classical
  obtain ⟨v, _, _, hvlim, hv⟩ := hSup.exists_seq_monotone_tendsto (hs.image ν)
  choose f hfs hfv using hv
  refine ⟨f, hfs, ?_⟩
  have hf_le : iSup f ≤ sSup s := iSup_le (fun n => le_sSup (hfs n))
  have hs_le : sSup s ≤ p := sSup_le hsp
  have hf_le_p : iSup f ≤ p := hf_le.trans hs_le
  have hval : ν (sSup s) ≤ ν (iSup f) := by
    apply le_of_tendsto hvlim
    apply Eventually.of_forall
    intro n
    rw [← hfv n]
    exact hmono (le_iSup f n)
  by_contra hne
  have hlt : iSup f < sSup s := lt_of_le_of_ne hf_le hne
  exact (not_lt_of_ge hval) (hν hf_le_p hs_le hlt)

end Gelfand39FaithfulCover
end
end Gelfand39Source25

/- Source module Work.Gelfand39PredualSeries; SHA256 bb8196ec6fdaee280a2415a44df12cb3ba82e070b125f331614d440cfe6b0cff. -/
section Gelfand39Source26

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped ComplexOrder

namespace Gelfand39PredualSeries
universe u
variable {A X : Type u} [CStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Evaluation, viewed as a real continuous linear map in the predual vector. -/
def evaluation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (a : A) : X →L[ℝ] ℂ :=
  (starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.comp ((e.symm a).restrictScalars ℝ)

@[simp] theorem evaluation_apply (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (a : A) (x : X) :
    evaluation e a x = star ((e.symm a) x) := rfl

/-- A countable family of positive fixed-predual evaluations has one positive
fixed-predual evaluation with exactly their common zero set. -/
theorem exists_positive_sum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (S : Set A) (x : ℕ → X)
    (hx : ∀ n a, a ∈ S → 0 ≤ evaluation e a (x n)) :
    ∃ y : X, ∀ a ∈ S, 0 ≤ evaluation e a y ∧
      (evaluation e a y = 0 ↔ ∀ n, evaluation e a (x n) = 0) := by
  let w : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n / (‖x n‖ + 1)
  have hw (n : ℕ) : 0 < w n := div_pos (by positivity) (by positivity)
  let z : ℕ → X := fun n => w n • x n
  have hz : Summable z := by
    apply Summable.of_norm_bounded
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
    intro n
    change ‖w n • x n‖ ≤ (1 / 2 : ℝ) ^ n
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hw n)]
    calc
      w n * ‖x n‖ ≤ w n * (‖x n‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (hw n).le
      _ = (1 / 2 : ℝ) ^ n := div_mul_cancel₀ _ (by positivity)
  refine ⟨∑' n, z n, ?_⟩
  intro a ha
  let E : X →L[ℝ] ℂ := evaluation e a
  have hsum : E (∑' n, z n) = ∑' n, E (z n) := E.map_tsum hz
  have hEsum : Summable (fun n => E (z n)) := E.summable hz
  have hEpos (n : ℕ) : 0 ≤ E (z n) := by
    change 0 ≤ E (w n • x n)
    rw [map_smul]
    exact smul_nonneg (hw n).le (hx n a ha)
  change 0 ≤ E (∑' n, z n) ∧
    (E (∑' n, z n) = 0 ↔ ∀ n, E (x n) = 0)
  rw [hsum]
  refine ⟨tsum_nonneg hEpos, ?_⟩
  constructor
  · intro hzero n
    have hle : E (z n) ≤ ∑' k, E (z k) := by
      simpa using hEsum.sum_le_tsum ({n} : Finset ℕ) (fun k _ => hEpos k)
    have hn : E (z n) = 0 := le_antisymm (hzero ▸ hle) (hEpos n)
    change E (w n • x n) = 0 at hn
    rw [map_smul, smul_eq_zero] at hn
    exact hn.resolve_left (ne_of_gt (hw n))
  · intro hzero
    have hterm (n : ℕ) : E (z n) = 0 := by
      change E (w n • x n) = 0
      rw [map_smul, hzero n, smul_zero]
    simp only [hterm, tsum_zero]

end Gelfand39PredualSeries
end
end Gelfand39Source26

/- Source module Work.Gelfand39NormalMeasure; SHA256 79abc80c3bfee97e34e126ccf0bc436e643706e64f8a945b9d3e9d64ea0762be. -/
section Gelfand39Source27

set_option autoImplicit false

namespace Gelfand39NormalMeasure
open Set Filter GelfandVNA.Duality Gelfand39ProjectionBand Gelfand39NormalJordan
open Gelfand39FaithfulValuation Gelfand39 Gelfand39OrderContinuity Gelfand38
open QAlgorithms.Papers.Independent.Support21.P20
open scoped ComplexOrder Topology
noncomputable section
universe u

section Support
variable {B : Type*} [CompleteBooleanAlgebra B]

def support (ν : B → ℝ) : B := (sSup {b : B | ν b = 0})ᶜ

lemma valuation_monotone (ν : B → ℝ) (hc : IsContinuousValuation ν)
    (hp : ∀ b, 0 ≤ ν b) : Monotone ν := by
  have hn : IsNormalValuation ν := ⟨hc, fun b => by rw [compl_compl]⟩
  intro a b hab
  have h := Gelfand311Jordan.g72gk34_split hn hab
  linarith [hp (b ⊓ aᶜ)]

lemma valuation_sup (ν : B → ℝ) (hc : IsContinuousValuation ν)
    (hp : ∀ b, 0 ≤ ν b) (s : Set B) (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s) :
    IsLUB (ν '' s) (ν (sSup s)) := by
  letI : Nonempty s := hs.to_subtype
  letI : IsDirectedOrder s := hd.isDirectedOrder
  have hm := valuation_monotone ν hc hp
  have hl := isLUB_of_tendsto_atTop (fun (p q : s) hpq => hm hpq)
    (hc.2 s (sSup s) hs hd (isLUB_sSup s))
  simpa only [Set.image_eq_range] using hl

lemma null_sup_zero (ν : B → ℝ) (hc : IsContinuousValuation ν)
    (hp : ∀ b, 0 ≤ ν b) : ν (sSup {b : B | ν b = 0}) = 0 :=
  null_sup_null ν hc.1.1 hc.1.2 hp (valuation_sup ν hc hp)

lemma null_iff_disjoint_support (ν : B → ℝ) (hc : IsContinuousValuation ν)
    (hp : ∀ b, 0 ≤ ν b) (b : B) : ν b = 0 ↔ Disjoint b (support ν) := by
  rw [support, disjoint_compl_right_iff]
  exact null_iff_le_null_sup ν hp (valuation_monotone ν hc hp) (null_sup_zero ν hc hp) b

lemma eq_of_same_disjoint (a b : B) (h : ∀ q, Disjoint q a ↔ Disjoint q b) : a = b := by
  have he : aᶜ = bᶜ := le_antisymm
    (((h aᶜ).mp disjoint_compl_left).le_compl_right)
    (((h bᶜ).mpr disjoint_compl_left).le_compl_right)
  simpa only [compl_compl] using congrArg (fun q : B => qᶜ) he

lemma support_sup (ν μ ρ : B → ℝ)
    (hν : IsContinuousValuation ν) (hμ : IsContinuousValuation μ) (hρ : IsContinuousValuation ρ)
    (hpν : ∀ b, 0 ≤ ν b) (hpμ : ∀ b, 0 ≤ μ b) (hpρ : ∀ b, 0 ≤ ρ b)
    (he : ∀ b, ρ b = 0 ↔ ν b = 0 ∧ μ b = 0) : support ρ = support ν ⊔ support μ := by
  apply eq_of_same_disjoint
  intro b
  rw [disjoint_sup_right, ← null_iff_disjoint_support ρ hρ hpρ,
    ← null_iff_disjoint_support ν hν hpν, ← null_iff_disjoint_support μ hμ hpμ]
  exact he b

lemma support_iSup (ν : ℕ → B → ℝ) (μ : B → ℝ)
    (hν : ∀ n, IsContinuousValuation (ν n)) (hμ : IsContinuousValuation μ)
    (hpν : ∀ n b, 0 ≤ ν n b) (hpμ : ∀ b, 0 ≤ μ b)
    (he : ∀ b, μ b = 0 ↔ ∀ n, ν n b = 0) : support μ = ⨆ n, support (ν n) := by
  apply eq_of_same_disjoint
  intro b
  rw [disjoint_iSup_iff, ← null_iff_disjoint_support μ hμ hpμ, he b]
  exact forall_congr' (fun n => null_iff_disjoint_support (ν n) (hν n) (hpν n) b)

end Support

variable {A X : Type u} [CommCStarAlgebra A] [WStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
local instance : CompleteBooleanAlgebra (ProjAlg A) := projectionCompleteBooleanAlgebra A

/-- Positivity of the actual complex-linear evaluation in the canonical C*-order. -/
def Positive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) : Prop :=
  letI := CStarAlgebra.spectralOrder A
  ∀ a : A, 0 ≤ a → 0 ≤ fixedEvaluation e x a

def value (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) (p : ProjAlg A) : ℝ :=
  (fixedEvaluation e x p.val).re

lemma value_continuous (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X) :
    IsContinuousValuation (value e x) := by
  have hn : IsNormalFunctional (fixedEvaluation e x) :=
    ⟨X, inferInstance, inferInstance, inferInstance, e, x, fun _ => rfl⟩
  exact Gelfand311Jordan.g72gk34_cmap Complex.re Complex.zero_re Complex.add_re Complex.continuous_re
    (normal_restrict_isContinuousValuation (fixedEvaluation e x) hn)

lemma evaluation_projection_nonneg (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) {x : X}
    (hx : Positive e x) (p : ProjAlg A) : 0 ≤ fixedEvaluation e x p.val := by
  letI := CStarAlgebra.spectralOrder A
  letI := CStarAlgebra.spectralOrderedRing A
  exact hx p.val ((positiveUnit_iff_mem_Icc p.val).mp (projection_positiveUnit p)).1

lemma value_nonneg (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) {x : X}
    (hx : Positive e x) (p : ProjAlg A) : 0 ≤ value e x p :=
  (Complex.nonneg_iff.mp (evaluation_projection_nonneg e hx p)).1

lemma value_zero_iff (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) {x : X}
    (hx : Positive e x) (p : ProjAlg A) : value e x p = 0 ↔ fixedEvaluation e x p.val = 0 := by
  constructor
  · intro h
    apply Complex.ext h
    exact (Complex.nonneg_iff.mp (evaluation_projection_nonneg e hx p)).2.symm
  · intro h
    exact congrArg Complex.re h

lemma positive_add (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) {x y : X}
    (hx : Positive e x) (hy : Positive e y) : Positive e (x + y) := by
  intro a ha
  rw [fixedEvaluation_add_vector]
  exact add_nonneg (hx a ha) (hy a ha)

lemma support_add (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) {x y : X}
    (hx : Positive e x) (hy : Positive e y) :
    support (value e (x + y)) = support (value e x) ⊔ support (value e y) := by
  apply support_sup _ _ _ (value_continuous e x) (value_continuous e y)
    (value_continuous e (x + y)) (value_nonneg e hx) (value_nonneg e hy)
    (value_nonneg e (positive_add e hx hy))
  intro p
  change (fixedEvaluation e (x + y) p.val).re = 0 ↔ _
  rw [fixedEvaluation_add_vector, Complex.add_re]
  exact add_eq_zero_iff_of_nonneg (value_nonneg e hx p) (value_nonneg e hy p)

lemma exists_positive_projection_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (x : X) (hx : Positive e x) (p : ProjAlg A) :
    ∃ y : X, Positive e y ∧ (∀ a, fixedEvaluation e y a = fixedEvaluation e x (p.val * a)) ∧
      support (value e y) ≤ p := by
  obtain ⟨y, hy⟩ := exists_projection_vector p e x
  have he (a : A) : fixedEvaluation e y a = fixedEvaluation e x (p.val * a) := (hy a).symm
  have hpos : Positive e y := by
    letI := CStarAlgebra.spectralOrder A
    letI := CStarAlgebra.spectralOrderedRing A
    intro a ha
    rw [he]
    apply hx
    exact Commute.mul_nonneg
      ((positiveUnit_iff_mem_Icc p.val).mp (projection_positiveUnit p)).1 ha (mul_comm _ _)
  refine ⟨y, hpos, he, ?_⟩
  have hz : value e y pᶜ = 0 := by
    change (fixedEvaluation e y (pᶜ : ProjAlg A).val).re = 0
    rw [he]
    have hmul : p.val * (pᶜ : ProjAlg A).val = 0 := by
      change p.val * (1 - p.val) = 0
      rw [mul_sub, mul_one, p.isStarProjection.1, sub_self]
    rw [hmul, map_zero, Complex.zero_re]
  have hd := (null_iff_disjoint_support _ (value_continuous e y) (value_nonneg e hpos) pᶜ).mp hz
  have hh := hd.le_compl_left
  change (support (value e y)).val * (1 - (1 - p.val)) = (support (value e y)).val at hh
  change (support (value e y)).val * p.val = (support (value e y)).val
  simpa only [sub_sub_cancel] using hh

lemma positive_zero (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) : Positive e (0 : X) := by
  intro a ha
  simp [fixedEvaluation]

lemma support_zero (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) : support (value e (0 : X)) = ⊥ := by
  simp [support, value, fixedEvaluation] <;> rfl

lemma exists_positive_iSup (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : ℕ → X)
    (hx : ∀ n, Positive e (x n)) :
    ∃ y : X, Positive e y ∧ support (value e y) = ⨆ n, support (value e (x n)) := by
  letI := CStarAlgebra.spectralOrder A
  letI := CStarAlgebra.spectralOrderedRing A
  obtain ⟨y, hy⟩ := Gelfand39PredualSeries.exists_positive_sum e {a : A | 0 ≤ a} x
    (fun n a ha => hx n a ha)
  have hpos : Positive e y := fun a ha => (hy a ha).1
  refine ⟨y, hpos, ?_⟩
  apply support_iSup _ _ (fun n => value_continuous e (x n)) (value_continuous e y)
    (fun n => value_nonneg e (hx n)) (value_nonneg e hpos)
  intro p
  rw [value_zero_iff e hpos]
  have hp0 : 0 ≤ p.val := ((positiveUnit_iff_mem_Icc p.val).mp (projection_positiveUnit p)).1
  change Gelfand39PredualSeries.evaluation e p.val y = 0 ↔ _
  rw [(hy p.val hp0).2]
  exact forall_congr' (fun n => (value_zero_iff e (hx n) p).symm)

/-- A finite positive continuous valuation has exactly the same support as a
positive evaluation in the supplied predual. -/
theorem exists_positive_same_support (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (ν : ProjAlg A → ℝ) (hν : IsContinuousValuation ν) (hpν : ∀ p, 0 ≤ ν p) :
    ∃ y : X, Positive e y ∧ support (value e y) = support ν := by
  classical
  let pν : ProjAlg A := support ν
  let S : Set (ProjAlg A) := {p | ∃ x : X, Positive e x ∧ support (value e x) = p ∧ p ≤ pν}
  have hSne : S.Nonempty := ⟨⊥, 0, positive_zero e, support_zero e, bot_le⟩
  have hSdir : DirectedOn (· ≤ ·) S := by
    rintro p ⟨x, hx, hxp, hp⟩ q ⟨y, hy, hyq, hq⟩
    refine ⟨p ⊔ q, ⟨x + y, positive_add e hx hy, ?_, sup_le hp hq⟩, le_sup_left, le_sup_right⟩
    rw [support_add e hx hy, hxp, hyq]
  have hsp : S ⊆ Set.Iic pν := by
    rintro p ⟨x, hx, he, hp⟩
    exact hp
  have hStop : sSup S = pν := by
    apply le_antisymm (sSup_le hsp)
    by_contra hnot
    let r : ProjAlg A := pν ⊓ (sSup S)ᶜ
    have hr : r ≠ ⊥ := by
      intro hz
      apply hnot
      apply disjoint_compl_right_iff.mp
      exact disjoint_iff.mpr hz
    obtain ⟨x, hx, hxr⟩ := positive_evaluation_separates_projection e r hr
    obtain ⟨y, hy, he, hys⟩ := exists_positive_projection_vector e x hx r
    have hyr : fixedEvaluation e y r.val ≠ 0 := by
      rw [he, r.isStarProjection.1]
      exact hxr
    have hq : support (value e y) ∈ S := ⟨y, hy, rfl, hys.trans inf_le_left⟩
    have hle : support (value e y) ≤ sSup S := le_sSup hq
    have hcomp : support (value e y) ≤ (sSup S)ᶜ := hys.trans inf_le_right
    have hz : support (value e y) = ⊥ := by
      apply bot_unique
      calc
        support (value e y) ≤ sSup S ⊓ (sSup S)ᶜ := le_inf hle hcomp
        _ = ⊥ := inf_compl_eq_bot
    apply hyr
    apply (value_zero_iff e hy r).mp
    apply (null_iff_disjoint_support _ (value_continuous e y) (value_nonneg e hy) r).mpr
    rw [hz]
    exact disjoint_bot_right
  have hmono := valuation_monotone ν hν hpν
  have hstrict : StrictMonoOn ν (Set.Iic pν) :=
    Gelfand39FaithfulCover.strictMonoOn_of_faithful_on ν pν hν.1.1 hν.1.2 hpν
      (fun q hq hz => faithful_on_null_complement ν hpν hmono (null_sup_zero ν hν hpν) q hq hz)
  obtain ⟨f, hf, hfsup⟩ := Gelfand39FaithfulCover.exists_sequence_sup_on
    ν hmono pν hstrict S hSne hsp (valuation_sup ν hν hpν S hSne hSdir)
  change ∀ n, ∃ x : X, Positive e x ∧ support (value e x) = f n ∧ f n ≤ pν at hf
  choose x hx hxeq hle using hf
  obtain ⟨y, hy, hysup⟩ := exists_positive_iSup e x hx
  refine ⟨y, hy, ?_⟩
  calc
    support (value e y) = ⨆ n, support (value e (x n)) := hysup
    _ = ⨆ n, f n := iSup_congr hxeq
    _ = pν := hfsup.trans hStop
    _ = support ν := rfl

/-- A normal positive evaluation in the original predual detects every projection
that is non-null for the given positive valuation. -/
theorem exists_positive_dominating_nulls (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (ν : ProjAlg A → ℝ) (hν : IsContinuousValuation ν) (hpν : ∀ p, 0 ≤ ν p) :
    ∃ y : X, Positive e y ∧ ∀ p : ProjAlg A, value e y p = 0 → ν p = 0 := by
  obtain ⟨y, hy, he⟩ := exists_positive_same_support e ν hν hpν
  refine ⟨y, hy, ?_⟩
  intro p hp
  apply (null_iff_disjoint_support ν hν hpν p).mpr
  rw [← he]
  exact (null_iff_disjoint_support _ (value_continuous e y) (value_nonneg e hy) p).mp hp


end
end Gelfand39NormalMeasure
end Gelfand39Source27

/- Source module Work.Gelfand39Multiplication; SHA256 3752dc998366a5896d2a48c12bb7b0fd0de30758983b4bbcdd130d89d7a61ca6. -/
section Gelfand39Source28

set_option autoImplicit false

namespace Gelfand39ProjectionBand
open GelfandVNA.Duality Gelfand39Inverse WeakDual Gelfand39Predual
noncomputable section
universe u
variable {A X : Type u} [CommCStarAlgebra A] [WStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma continuous_multiplicationEvaluation_ball (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (x : X) (b : A) :
    Continuous (fun w : weakUnitBall X => fixedEvaluation e x (b * e (toStrongDual w.val))) := by
  let Φ := fixedEvaluation e x
  have hLip (w : weakUnitBall X) :
      LipschitzWith ‖Φ‖₊ (fun a : A => Φ (a * e (toStrongDual w.val))) := by
    apply LipschitzWith.of_dist_le_mul
    intro a c
    have hw : ‖e (toStrongDual w.val)‖ ≤ 1 := by
      rw [e.norm_map]
      exact w.property
    change dist (Φ (a * e (toStrongDual w.val))) (Φ (c * e (toStrongDual w.val))) ≤
      ‖Φ‖ * dist a c
    rw [dist_eq_norm, ← map_sub, ← sub_mul, dist_eq_norm]
    calc
      ‖Φ ((a - c) * e (toStrongDual w.val))‖ ≤ ‖Φ‖ * ‖(a - c) * e (toStrongDual w.val)‖ :=
        Φ.le_opNorm _
      _ ≤ ‖Φ‖ * (‖a - c‖ * ‖e (toStrongDual w.val)‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg Φ)
      _ ≤ ‖Φ‖ * (‖a - c‖ * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw (norm_nonneg _)) (norm_nonneg Φ)
      _ = ‖Φ‖ * ‖a - c‖ := by rw [mul_one]
  have hF : Continuous (fun a : A => UniformFun.ofFun
      (fun w : weakUnitBall X => Φ (a * e (toStrongDual w.val)))) :=
    (UniformFun.lipschitzWith_ofFun_iff.mpr hLip).continuous
  let M : Submodule ℂ A := {
    carrier := {a | Continuous (fun w : weakUnitBall X => Φ (a * e (toStrongDual w.val)))}
    zero_mem' := by
      change Continuous (fun w : weakUnitBall X => Φ (0 * e (toStrongDual w.val)))
      simpa only [zero_mul, map_zero] using (continuous_const : Continuous (fun _ : weakUnitBall X => (0 : ℂ)))
    add_mem' := by
      intro a c ha hc
      change Continuous (fun w : weakUnitBall X => Φ ((a + c) * e (toStrongDual w.val)))
      apply (ha.add hc).congr
      intro w
      change Φ (a * e (toStrongDual w.val)) + Φ (c * e (toStrongDual w.val)) =
        Φ ((a + c) * e (toStrongDual w.val))
      rw [add_mul, map_add]
    smul_mem' := by
      intro c a ha
      change Continuous (fun w : weakUnitBall X => Φ ((c • a) * e (toStrongDual w.val)))
      apply (ha.const_smul c).congr
      intro w
      change c • Φ (a * e (toStrongDual w.val)) = Φ ((c • a) * e (toStrongDual w.val))
      rw [smul_mul_assoc, map_smul] }
  have hclosed : IsClosed (M : Set A) :=
    (UniformFun.isClosed_setOfPred_continuous (α := weakUnitBall X) (β := ℂ)).preimage hF
  have hspan : Submodule.span ℂ (Set.range (ProjAlg.val : ProjAlg A → A)) ≤ M := by
    apply Submodule.span_le.mpr
    rintro a ⟨p, rfl⟩
    exact continuous_projectionEvaluation_ball p e x
  have hd : Dense (M : Set A) := (projection_span_dense A).mono hspan
  have htop : (M : Set A) = Set.univ := by
    simpa only [hclosed.closure_eq] using hd.closure_eq
  have hb : b ∈ M := by
    change b ∈ (M : Set A)
    rw [htop]
    trivial
  exact hb

/-- Multiplication by any algebra element preserves the original predual. -/
theorem exists_multiplication_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (x : X) (b : A) :
    ∃ y : X, ∀ a, fixedEvaluation e x (b * a) = fixedEvaluation e y a := by
  let Φ : A →L[ℂ] ℂ := {
    toFun a := fixedEvaluation e x (b * a)
    map_add' := by intro a c; rw [mul_add, map_add]
    map_smul' := by intro c a; rw [mul_smul_comm, map_smul]; rfl
    cont := by fun_prop }
  apply exists_predual_vector_of_weakStarContinuousOn_ball e Φ
  rw [← weakUnitBall_eq]
  exact continuousOn_iff_continuous_restrict.mpr (continuous_multiplicationEvaluation_ball e x b)

end
end Gelfand39ProjectionBand
end Gelfand39Source28

/- Source module Work.Gelfand39ComplexAssembly; SHA256 afb91f5edf55cf4255607400c0986843a86c4434b0e6e549f2ae1d7a3eb10de0. -/
section Gelfand39Source29

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GelfandVNA.Duality Gelfand311Jordan
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand39ComplexAssembly
universe u v
variable {A X : Type u} [CStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {B : Type v} [CompleteBooleanAlgebra B]

/-- The four canonical Hahn--Jordan parts combine positive representations
inside one fixed predual. -/
theorem exists_complex_vector_of_positive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (k : B → A)
    (hpositive : ∀ ρ : B → ℝ, IsContinuousValuation ρ → (∀ p, 0 ≤ ρ p) →
      ∃ x : X, ∀ p : B, star ((e.symm (k p)) x) = (ρ p : ℂ))
    (ν : B → ℂ) (hν : IsContinuousValuation ν) :
    ∃ x : X, ∀ p : B, star ((e.symm (k p)) x) = ν p := by
  have hj := (hahnJordan_decomposition B).2 ν
    (Or.inr ⟨fun _ => sup_compl_eq_top, hν⟩)
  rcases hj with ⟨hr, hi, hformula⟩
  rcases hr with ⟨_, _, _, _, hrp, hrm, hpr, hmr, _⟩
  rcases hi with ⟨_, _, _, _, hip, him, hpi, hmi, _⟩
  obtain ⟨x₁, hx₁⟩ := hpositive _ hrp.1 hpr
  obtain ⟨x₂, hx₂⟩ := hpositive _ hrm.1 hmr
  obtain ⟨x₃, hx₃⟩ := hpositive _ hip.1 hpi
  obtain ⟨x₄, hx₄⟩ := hpositive _ him.1 hmi
  let x : X := (x₁ - x₂) + star Complex.I • (x₃ - x₄)
  refine ⟨x, ?_⟩
  intro p
  have heq : star ((e.symm (k p)) x) =
      star ((e.symm (k p)) x₁) - star ((e.symm (k p)) x₂) +
      Complex.I * (star ((e.symm (k p)) x₃) - star ((e.symm (k p)) x₄)) := by
    dsimp [x]
    simp only [map_add, map_sub, map_smul, starRingEnd_apply, star_add, star_sub,
      star_smul, star_mul, star_star, smul_eq_mul] <;> ring
  rw [heq, hx₁, hx₂, hx₃, hx₄]
  exact (hformula p).symm

end Gelfand39ComplexAssembly
end
end Gelfand39Source29

/- Source module Work.Gelfand39Complete; SHA256 6c4d94efb700b914ca12ed99911f79be1d4c18a5f7a0a6cbdffd210da952d7ea. -/
section Gelfand39Source30

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GelfandVNA.Duality Gelfand39ProjectionBand
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand39Complete
universe u
variable {A X : Type u} [CommCStarAlgebra A] [WStarAlgebra A]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem positive_extension_exists_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (ν : ProjAlg A → ℝ) (hν : IsContinuousValuation ν) (hpν : ∀ p, 0 ≤ ν p)
    (Ψ : A →L[ℂ] ℂ) (hΨ : ∀ p : ProjAlg A, Ψ p.val = (ν p : ℂ)) :
    ∃ x : X, ∀ a : A, Ψ a = star ((e.symm a) x) := by
  letI := CStarAlgebra.spectralOrder A
  letI := CStarAlgebra.spectralOrderedRing A
  letI := Gelfand39NormalJordan.projectionCompleteBooleanAlgebra A
  obtain ⟨y, hy, hac⟩ := Gelfand39NormalMeasure.exists_positive_dominating_nulls e ν hν hpν
  let μ : ProjAlg A → ℝ := Gelfand39NormalMeasure.value e y
  let Φ : A →L[ℂ] ℂ := fixedEvaluation e y
  have hμ : IsContinuousValuation μ := Gelfand39NormalMeasure.value_continuous e y
  have hpμ : ∀ p, 0 ≤ μ p := Gelfand39NormalMeasure.value_nonneg e hy
  have hΦ (p : ProjAlg A) : Φ p.val = (μ p : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp
        (Gelfand39NormalMeasure.evaluation_projection_nonneg e hy p)).2.symm
  have hΦmult (b : A) : ∃ x : X, ∀ a : A,
      Φ (star b * a) = star ((e.symm a) x) := by
    obtain ⟨x, hx⟩ := exists_multiplication_vector e y (star b)
    exact ⟨x, hx⟩
  exact Gelfand39Truncation.exists_predual_vector_of_absolute_continuity e μ ν
    hμ hν hpμ hpν Φ Ψ hΦ hΨ hΦmult hac

theorem positive_valuation_exists_vector (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (ν : ProjAlg A → ℝ) (hν : IsContinuousValuation ν) (hpν : ∀ p, 0 ≤ ν p) :
    ∃ x : X, ∀ p : ProjAlg A, star ((e.symm p.val) x) = (ν p : ℂ) := by
  letI := Gelfand39NormalJordan.projectionCompleteBooleanAlgebra A
  obtain ⟨Ψ, hΨ, _⟩ := Gelfand39Inverse.positive_valuation_bounded_extension ν hν.1.1
    (Gelfand39ValuationSup.disjoint_add ν hν.1) hpν
  obtain ⟨x, hx⟩ := positive_extension_exists_vector e ν hν hpν Ψ hΨ
  exact ⟨x, fun p => (hx p.val).symm.trans (hΨ p)⟩

end Gelfand39Complete

namespace GelfandVNA.Duality
universe u

/-- Restriction to projections identifies normal functionals with complex
continuous valuations. -/
theorem proposition_3_9 (A : Type u) [CommCStarAlgebra A] [WStarAlgebra A] :
    (∀ φ : A → ℂ, IsNormalFunctional φ → IsContinuousValuation (fun p : ProjAlg A => φ p.val)) ∧
    (∀ ν : ProjAlg A → ℂ, IsContinuousValuation ν →
      ∃! φ : A → ℂ, IsNormalFunctional φ ∧ ∀ p : ProjAlg A, φ p.val = ν p) := by
  refine ⟨Gelfand39.normal_restrict_isContinuousValuation, ?_⟩
  intro ν hν
  obtain ⟨X, hX, hN, hC, ⟨e⟩⟩ := WStarAlgebra.exists_predual (M := A)
  letI := Gelfand39NormalJordan.projectionCompleteBooleanAlgebra A
  obtain ⟨x, hx⟩ := Gelfand39ComplexAssembly.exists_complex_vector_of_positive e
    (ProjAlg.val : ProjAlg A → A) (Gelfand39Complete.positive_valuation_exists_vector e) ν hν
  let φ : A → ℂ := fun a => star ((e.symm a) x)
  have hφ : IsNormalFunctional φ :=
    ⟨X, inferInstance, inferInstance, inferInstance, e, x, fun _ => rfl⟩
  refine ⟨φ, ⟨hφ, hx⟩, ?_⟩
  intro ψ hψ
  exact Gelfand39Inverse.normal_functionals_ext_projections ψ φ hψ.1 hφ
    (fun p => (hψ.2 p).trans (hx p).symm)

end GelfandVNA.Duality
end
end Gelfand39Source30

open GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20
universe u

theorem solution (A : Type u) [CommCStarAlgebra A] [WStarAlgebra A] :
    (∀ φ : A → ℂ, IsNormalFunctional φ → IsContinuousValuation (fun p : ProjAlg A => φ p.val)) ∧
    (∀ ν : ProjAlg A → ℂ, IsContinuousValuation ν →
      ∃! φ : A → ℂ, IsNormalFunctional φ ∧ ∀ p : ProjAlg A, φ p.val = ν p) := by
  exact GelfandVNA.Duality.proposition_3_9 A

#print axioms GelfandVNA.Duality.proposition_3_9
#print axioms solution
