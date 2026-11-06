-- Prove2me | solution 1 for FriendlyShadow.Gaussian.lemma_39
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T13:12:08.767197+00:00
-- url     : https://prove2.me/submissions/cad68e0f-43ab-4246-a5a7-40abb1f94f63

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Shape

open scoped RealInnerProductSpace

set_option autoImplicit false

namespace FSL36
open FriendlyShadow.Gaussian

lemma hull_iff {d : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E] (b : Fin d → E) (p : E) :
    p ∈ convexHull ℝ (Set.range b) ↔
      ∃ l : Fin d → ℝ, (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1 ∧ ∑ i, l i • b i = p := by
  classical
  constructor
  · intro hp
    have e : convexHull ℝ (Set.range b) =
        (Fintype.linearCombination ℝ b) '' stdSimplex ℝ (Fin d) := by
      have hf : (⇑(Fintype.linearCombination ℝ b) ∘ fun i j : Fin d => if i = j then (1:ℝ) else 0)
          = b := by
        funext i; simp [Fintype.linearCombination_apply, ite_smul]
      rw [← convexHull_basis_eq_stdSimplex, LinearMap.image_convexHull, ← Set.range_comp, hf]
    rw [e] at hp
    obtain ⟨l, ⟨hl0, hl1⟩, rfl⟩ := hp
    exact ⟨l, hl0, hl1, by simp [Fintype.linearCombination_apply]⟩
  · rintro ⟨l, hl0, hl1, rfl⟩
    exact mem_convexHull_of_exists_fintype l b hl0 hl1 (fun i => Set.mem_range_self i) rfl

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma b_decomp {d : ℕ} [NeZero d] (ω : V) (b : Fin d → V) (i : Fin d) :
    b i = projPerp ω (b 0) + shapeOf ω b i + ⟪ω, b i⟫ • ω := by
  simp only [shapeOf, projPerp]; abel

lemma inner_projPerp (ω v : V) (hω : ‖ω‖ = 1) : ⟪ω, projPerp ω v⟫ = 0 := by
  simp only [projPerp, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hω]; ring

lemma inner_shape {d : ℕ} [NeZero d] (ω : V) (hω : ‖ω‖ = 1) (b : Fin d → V) (i : Fin d) :
    ⟪ω, shapeOf ω b i⟫ = 0 := by
  simp only [shapeOf, inner_sub_right, inner_projPerp ω _ hω, sub_zero]

lemma inner_comb {d : ℕ} [NeZero d] (ω : V) (hω : ‖ω‖ = 1) (b : Fin d → V) (l : Fin d → ℝ) :
    ⟪ω, ∑ i, l i • shapeOf ω b i⟫ = 0 := by
  simp [inner_sum, inner_smul_right, inner_shape ω hω b]

lemma sum_decomp {d : ℕ} [NeZero d] (ω : V) (b : Fin d → V) (l : Fin d → ℝ) :
    ∑ i, l i • b i = (∑ i, l i) • projPerp ω (b 0) + ∑ i, l i • shapeOf ω b i +
      (∑ i, l i * ⟪ω, b i⟫) • ω := by
  rw [Finset.sum_congr rfl (fun i _ => congrArg (l i • ·) (b_decomp ω b i))]
  simp only [smul_add, Finset.sum_add_distrib, Finset.sum_smul, smul_smul]

lemma mem_T {d : ℕ} [NeZero d] (b : Fin d → V) (ω : V) (hω : ‖ω‖ = 1) (q : V)
    (hq : ⟪ω, q⟫ = 0) (p : V) :
    p ∈ ({p | ∃ t : ℝ, p = projPerp ω (b 0) + q + t • ω} ∩ convexHull ℝ (Set.range b)) ↔
      ∃ l ∈ chordSet (shapeOf ω b) q,
        p = projPerp ω (b 0) + q + (∑ i, l i * ⟪ω, b i⟫) • ω := by
  have hωω : ⟪ω, ω⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hω]; norm_num
  constructor
  · rintro ⟨⟨t, ht⟩, hp⟩
    obtain ⟨l, hl0, hl1, hlp⟩ := (hull_iff b p).mp hp
    rw [sum_decomp ω b l, hl1, one_smul, ht, add_assoc, add_assoc] at hlp
    have e1 := add_left_cancel hlp
    have e2 := congrArg (fun v => ⟪ω, v⟫) e1
    simp only [inner_add_right, inner_smul_right, inner_comb ω hω b l, hq, hωω] at e2
    have htl : t = ∑ i, l i * ⟪ω, b i⟫ := by linarith
    rw [← htl] at e1
    have e3 : ∑ i, l i • shapeOf ω b i = q := add_right_cancel e1
    exact ⟨l, ⟨hl0, hl1, e3⟩, by rw [ht, htl]⟩
  · rintro ⟨l, ⟨hl0, hl1, hls⟩, rfl⟩
    refine ⟨⟨_, rfl⟩, (hull_iff b _).mpr ⟨l, hl0, hl1, ?_⟩⟩
    rw [sum_decomp ω b l, hl1, one_smul, hls]

/-- Under the rank condition the difference of two chord combinations is a multiple of the
kernel combination. -/
lemma diff_mul {d : ℕ} [NeZero d] (hd : 3 ≤ d) (s : Fin d → V) (hs0 : s 0 = 0)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range s)) = d - 2)
    (z : Fin d → ℝ) (hz : IsKernelComb s z) (q : V) (l l' : Fin d → ℝ)
    (hl : l ∈ chordSet s q) (hl' : l' ∈ chordSet s q) :
    ∃ c : ℝ, ∀ i, l i - l' i = c * z i := by
  classical
  obtain ⟨hzs, hz0, hz1⟩ := hz
  obtain ⟨-, hl1, hls⟩ := hl
  obtain ⟨-, hl1', hls'⟩ := hl'
  set A := Fintype.linearCombination ℝ s with hA
  have hAapp : ∀ f : Fin d → ℝ, A f = ∑ i, f i • s i := fun f => by
    rw [hA, Fintype.linearCombination_apply]
  have hrk : Module.finrank ℝ (LinearMap.range A) = d - 2 := by
    rw [hA, Fintype.range_linearCombination]; exact hrank
  have hker : Module.finrank ℝ (LinearMap.ker A) = 2 := by
    have := LinearMap.finrank_range_add_finrank_ker A
    rw [hrk, Module.finrank_fin_fun] at this
    omega
  set e0 : Fin d → ℝ := Pi.single 0 1 with he0
  have he0A : e0 ∈ LinearMap.ker A := by
    rw [LinearMap.mem_ker, hAapp]
    simp [he0, Pi.single_apply, ite_smul, hs0]
  have hzA : z ∈ LinearMap.ker A := by rw [LinearMap.mem_ker, hAapp]; exact hzs
  have hzne : z ≠ 0 := by
    rintro rfl; simp at hz1
  have hsum_e0 : ∑ i, e0 i = 1 := by simp [he0]
  have hli : LinearIndependent ℝ ![e0, z] := by
    rw [LinearIndependent.pair_iff]
    intro a c hac
    have h1 := congrArg (fun f : Fin d → ℝ => ∑ i, f i) hac
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hsum_e0, hz0, Pi.zero_apply, Finset.sum_const_zero] at h1
    have ha : a = 0 := by linarith
    refine ⟨ha, ?_⟩
    rw [ha, zero_smul, zero_add] at hac
    exact (smul_eq_zero.mp hac).resolve_right hzne
  have hP : Submodule.span ℝ (Set.range ![e0, z]) = LinearMap.ker A := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact he0A
      · exact hzA
    · rw [finrank_span_eq_card hli, hker]; simp
  have hδ : l - l' ∈ LinearMap.ker A := by
    rw [LinearMap.mem_ker, hAapp]
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hls, hls', sub_self]
  rw [← hP, Submodule.mem_span_range_iff_exists_fun] at hδ
  obtain ⟨c, hc⟩ := hδ
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  have h2 := congrArg (fun f : Fin d → ℝ => ∑ i, f i) hc
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hsum_e0, hz0, Pi.sub_apply, Finset.sum_sub_distrib, hl1, hl1'] at h2
  have hc0 : c 0 = 0 := by linarith
  refine ⟨c 1, fun i => ?_⟩
  have h3 := congrFun hc i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc0, zero_mul, zero_add,
    Pi.sub_apply] at h3
  linarith

lemma sum_abs_le_two {d : ℕ} {s : Fin d → V} {q : V} {l l' : Fin d → ℝ}
    (hl : l ∈ chordSet s q) (hl' : l' ∈ chordSet s q) : ∑ i, |l i - l' i| ≤ 2 := by
  obtain ⟨h0, h1, -⟩ := hl
  obtain ⟨h0', h1', -⟩ := hl'
  calc ∑ i, |l i - l' i| ≤ ∑ i, (l i + l' i) :=
        Finset.sum_le_sum (fun i _ => abs_le.mpr ⟨by linarith [h0 i, h0' i], by linarith [h0 i, h0' i]⟩)
    _ = 2 := by rw [Finset.sum_add_distrib, h1, h1']; norm_num



variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma D_bdd {d : ℕ} (s : Fin d → V) (q : V) :
    BddAbove {t | ∃ l ∈ chordSet s q, ∃ l' ∈ chordSet s q, t = ∑ i, |l i - l' i|} :=
  ⟨2, by rintro _ ⟨l, hl, l', hl', rfl⟩; exact sum_abs_le_two hl hl'⟩

lemma C_ne {d : ℕ} (s : Fin d → V) (q : V) (hq : q ∈ convexHull ℝ (Set.range s)) :
    ∃ l, l ∈ chordSet s q := by
  obtain ⟨l, h0, h1, h2⟩ := (hull_iff s q).mp hq
  exact ⟨l, h0, h1, h2⟩

lemma D_ne {d : ℕ} (s : Fin d → V) (q : V) (hq : q ∈ convexHull ℝ (Set.range s)) :
    {t | ∃ l ∈ chordSet s q, ∃ l' ∈ chordSet s q, t = ∑ i, |l i - l' i|}.Nonempty := by
  obtain ⟨l, hl⟩ := C_ne s q hq
  exact ⟨_, l, hl, l, hl, rfl⟩

lemma le_two {d : ℕ} (s : Fin d → V) (q : V) (hq : q ∈ convexHull ℝ (Set.range s)) :
    chordLen s q ≤ 2 :=
  csSup_le (D_ne s q hq) (by rintro _ ⟨l, hl, l', hl', rfl⟩; exact sum_abs_le_two hl hl')

lemma oriented {d : ℕ} [NeZero d] (hd : 3 ≤ d) (s : Fin d → V) (hs0 : s 0 = 0)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range s)) = d - 2)
    (z : Fin d → ℝ) (hz : IsKernelComb s z) (q : V) (l l' : Fin d → ℝ)
    (hl : l ∈ chordSet s q) (hl' : l' ∈ chordSet s q) :
    ∃ m ∈ chordSet s q, ∃ m' ∈ chordSet s q,
      ∀ i, m i - m' i = (∑ j, |l j - l' j|) * z i := by
  obtain ⟨c, hc⟩ := diff_mul hd s hs0 hrank z hz q l l' hl hl'
  have e : ∑ j, |l j - l' j| = |c| := by
    simp only [hc, abs_mul, ← Finset.mul_sum, hz.2.2, mul_one]
  rw [e]
  rcases le_total 0 c with h | h
  · exact ⟨l, hl, l', hl', fun i => by rw [abs_of_nonneg h, hc i]⟩
  · exact ⟨l', hl', l, hl, fun i => by rw [abs_of_nonpos h]; linarith [hc i]⟩

lemma comb_mem {d : ℕ} (s : Fin d → V) (q1 q2 : V) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (m1 m2 : Fin d → ℝ) (h1 : m1 ∈ chordSet s q1) (h2 : m2 ∈ chordSet s q2) :
    (fun i => a * m1 i + b * m2 i) ∈ chordSet s (a • q1 + b • q2) := by
  obtain ⟨p1, s1, v1⟩ := h1
  obtain ⟨p2, s2, v2⟩ := h2
  refine ⟨fun i => add_nonneg (mul_nonneg ha (p1 i)) (mul_nonneg hb (p2 i)), ?_, ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, s1, s2]; linarith
  · simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, v1, v2]

lemma sup_comb (D1 D2 : Set ℝ) (M a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1n : D1.Nonempty) (h2n : D2.Nonempty)
    (h : ∀ t1 ∈ D1, ∀ t2 ∈ D2, a * t1 + b * t2 ≤ M) :
    a * sSup D1 + b * sSup D2 ≤ M := by
  have step : ∀ t2 ∈ D2, a * sSup D1 ≤ M - b * t2 := by
    intro t2 ht2
    rw [← smul_eq_mul, ← Real.sSup_smul_of_nonneg ha]
    refine csSup_le (h1n.smul_set) ?_
    rintro _ ⟨t1, ht1, rfl⟩
    have := h t1 ht1 t2 ht2
    simp only [smul_eq_mul]; linarith
  have step2 : b * sSup D2 ≤ M - a * sSup D1 := by
    rw [← smul_eq_mul, ← Real.sSup_smul_of_nonneg hb]
    refine csSup_le (h2n.smul_set) ?_
    rintro _ ⟨t2, ht2, rfl⟩
    have := step t2 ht2
    simp only [smul_eq_mul]; linarith
  linarith

end FSL36

open FriendlyShadow.Gaussian RealInnerProductSpace in
theorem FSL35_main {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {d : ℕ}
    [NeZero d] (hd : 3 ≤ d) (s : Fin d → V) (hs0 : s 0 = 0)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range s)) = d - 2)
    (z : Fin d → ℝ) (hz : IsKernelComb s z) :
    ConcaveOn ℝ (convexHull ℝ (Set.range s)) (chordLen s) ∧
      chordLen s (∑ i, |z i| • s i) = 2 ∧
      ∀ q ∈ convexHull ℝ (Set.range s), chordLen s q ≤ 2 := by
  refine ⟨⟨convex_convexHull ℝ _, ?_⟩, ?_, fun q hq => FSL36.le_two s q hq⟩
  · intro q1 hq1 q2 hq2 a b ha hb hab
    simp only [smul_eq_mul]
    refine FSL36.sup_comb _ _ _ a b ha hb (FSL36.D_ne s q1 hq1) (FSL36.D_ne s q2 hq2) ?_
    rintro _ ⟨l1, hl1, l1', hl1', rfl⟩ _ ⟨l2, hl2, l2', hl2', rfl⟩
    obtain ⟨m1, hm1, m1', hm1', e1⟩ := FSL36.oriented hd s hs0 hrank z hz q1 l1 l1' hl1 hl1'
    obtain ⟨m2, hm2, m2', hm2', e2⟩ := FSL36.oriented hd s hs0 hrank z hz q2 l2 l2' hl2 hl2'
    set t1 := ∑ j, |l1 j - l1' j| with ht1
    set t2 := ∑ j, |l2 j - l2' j| with ht2
    have ht10 : 0 ≤ t1 := Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have ht20 : 0 ≤ t2 := Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have hn := FSL36.comb_mem s q1 q2 a b ha hb hab m1 m2 hm1 hm2
    have hn' := FSL36.comb_mem s q1 q2 a b ha hb hab m1' m2' hm1' hm2'
    have hval : ∑ i, |(a * m1 i + b * m2 i) - (a * m1' i + b * m2' i)| = a * t1 + b * t2 := by
      have : ∀ i, (a * m1 i + b * m2 i) - (a * m1' i + b * m2' i) = (a * t1 + b * t2) * z i := by
        intro i; have := e1 i; have := e2 i
        calc (a * m1 i + b * m2 i) - (a * m1' i + b * m2' i)
            = a * (m1 i - m1' i) + b * (m2 i - m2' i) := by ring
          _ = (a * t1 + b * t2) * z i := by rw [e1 i, e2 i]; ring
      simp only [this, abs_mul, ← Finset.mul_sum, hz.2.2, mul_one]
      exact abs_of_nonneg (by positivity)
    rw [← hval]
    exact le_csSup (FSL36.D_bdd s _) ⟨_, hn, _, hn', rfl⟩
  · obtain ⟨hzs, hz0, hz1⟩ := hz
    have hpm : ∀ r : ℝ, max r 0 - max (-r) 0 = r ∧ max r 0 + max (-r) 0 = |r| := by
      intro r
      rcases le_total 0 r with h | h
      · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; constructor <;> ring
      · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; constructor <;> ring
    set zp : Fin d → ℝ := fun i => max (z i) 0 with hzp
    set zm : Fin d → ℝ := fun i => max (-z i) 0 with hzm
    have hsub : ∀ i, zp i - zm i = z i := fun i => (hpm (z i)).1
    have hadd : ∀ i, zp i + zm i = |z i| := fun i => (hpm (z i)).2
    have hS1 : ∑ i, zp i - ∑ i, zm i = 0 := by
      rw [← Finset.sum_sub_distrib]; simp only [hsub]; exact hz0
    have hS2 : ∑ i, zp i + ∑ i, zm i = 1 := by
      rw [← Finset.sum_add_distrib]; simp only [hadd]; exact hz1
    have hV1 : ∑ i, zp i • s i = ∑ i, zm i • s i := by
      have : ∑ i, (zp i - zm i) • s i = 0 := by simp only [hsub]; exact hzs
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
      simpa only [sub_smul] using this
    have hy : ∑ i, |z i| • s i = ∑ i, (2 * zp i) • s i := by
      simp only [← hadd, add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, hV1]
      rw [two_smul]
    have hy' : ∑ i, |z i| • s i = ∑ i, (2 * zm i) • s i := by
      rw [hy]; simp only [mul_smul, ← Finset.smul_sum, hV1]
    have hl : (fun i => 2 * zp i) ∈ chordSet s (∑ i, |z i| • s i) :=
      ⟨fun i => by positivity, by rw [← Finset.mul_sum]; linarith, hy.symm⟩
    have hl' : (fun i => 2 * zm i) ∈ chordSet s (∑ i, |z i| • s i) :=
      ⟨fun i => by positivity, by rw [← Finset.mul_sum]; linarith, hy'.symm⟩
    have hval : ∑ i, |2 * zp i - 2 * zm i| = 2 := by
      have : ∀ i, |2 * zp i - 2 * zm i| = 2 * |z i| := by
        intro i; rw [← mul_sub, hsub, abs_mul, abs_two]
      simp only [this, ← Finset.mul_sum, hz1, mul_one]
    have hq : ∑ i, |z i| • s i ∈ convexHull ℝ (Set.range s) :=
      (FSL36.hull_iff s _).mpr ⟨_, hl.1, hl.2.1, hl.2.2⟩
    refine le_antisymm (FSL36.le_two s _ hq) ?_
    rw [← hval]
    exact le_csSup (FSL36.D_bdd s _) ⟨_, hl, _, hl', rfl⟩

namespace FSL39
open MeasureTheory

lemma cv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (G : E → ENNReal) (y : E) {c : ℝ} (hc : 0 < c) :
    ∫⁻ x, G x ∂μ =
      ENNReal.ofReal (c ^ Module.finrank ℝ E) * ∫⁻ q, G (y + c • (q - y)) ∂μ := by
  have h1 : ∫⁻ q, G (y + c • (q - y)) ∂μ = ∫⁻ w, G (y + c • w) ∂μ := by
    have := lintegral_add_right_eq_self (μ := μ) (fun w => G (y + c • w)) (-y)
    simpa [sub_eq_add_neg] using this
  have h2 : ∫⁻ w, G (y + c • w) ∂μ =
      ENNReal.ofReal (|(c ^ Module.finrank ℝ E)⁻¹|) * ∫⁻ w, G (y + w) ∂μ := by
    have hm := Measure.map_addHaar_smul μ hc.ne'
    have := lintegral_map_equiv (μ := μ) (fun w => G (y + w)) (MeasurableEquiv.smul₀ c hc.ne')
    rw [show ⇑(MeasurableEquiv.smul₀ c hc.ne' : E ≃ᵐ E) = (c • · : E → E) from rfl, hm,
      lintegral_smul_measure] at this
    rw [← this]; rfl
  have h3 : ∫⁻ w, G (y + w) ∂μ = ∫⁻ x, G x ∂μ := lintegral_add_left_eq_self G y
  rw [h1, h2, h3, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hp : 0 < c ^ Module.finrank ℝ E := by positivity
  rw [abs_of_pos (inv_pos.mpr hp), mul_inv_cancel₀ hp.ne', ENNReal.ofReal_one, one_mul]

end FSL39

open FriendlyShadow.Gaussian MeasureTheory RealInnerProductSpace in
theorem solution {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    (s : Fin d → EuclideanSpace ℝ (Fin (d - 2))) (hs0 : s 0 = 0)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range s)) = d - 2)
    (L R : ℝ) (hL : 0 < L) (hR : 0 ≤ R) (hdiam : ∀ i j, ‖s i - s j‖ ≤ 2 + 2 * R)
    (hLR : (d : ℝ) / 3 ≤ L * R) (z : Fin d → ℝ) (hz : IsKernelComb s z)
    (mubar : Fin d → EuclideanSpace ℝ (Fin (d - 2)) → ℝ → ℝ)
    (hpos : ∀ i u h, 0 < mubar i u h)
    (hlip : ∀ i u u' h h', mubar i u h ≤
      Real.exp (L * Real.sqrt (‖u - u'‖ ^ 2 + (h - h') ^ 2)) * mubar i u' h')
    (p : EuclideanSpace ℝ (Fin (d - 2))) :
    ENNReal.ofReal (Real.exp (-2) / (d * L * (1 + R))) *
        ∫⁻ q in convexHull ℝ (Set.range s), heightMarginal mubar s z (p - q) ≤
      ∫⁻ q in convexHull ℝ (Set.range s),
        ENNReal.ofReal (chordLen s q) * heightMarginal mubar s z (p - q) := by
  classical
  set K := convexHull ℝ (Set.range s) with hKdef
  set f : EuclideanSpace ℝ (Fin (d - 2)) → ENNReal :=
    fun q => heightMarginal mubar s z (p - q) with hfdef
  obtain ⟨hconc, hy2, -⟩ := FSL35_main hd s hs0 hrank z hz
  set y : EuclideanSpace ℝ (Fin (d - 2)) := ∑ i, |z i| • s i with hydef
  have hyK : y ∈ K := Convex.sum_mem (convex_convexHull ℝ (Set.range s))
    (fun i _ => abs_nonneg (z i)) hz.2.2 (fun i _ => subset_convexHull ℝ (Set.range s) ⟨i, rfl⟩)
  have hKc : IsCompact K := (Set.finite_range s).isCompact_convexHull ℝ
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  -- numbers
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hM : 0 < (d : ℝ) * L * (1 + R) := by positivity
  set δ : ℝ := 1 / ((d : ℝ) * L * (1 + R)) with hδdef
  have hδpos : 0 < δ := by positivity
  have hδM : δ * ((d : ℝ) * L * (1 + R)) = 1 := by rw [hδdef]; field_simp
  have hdcast : ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hsmall : ((d - 2 : ℕ) : ℝ) * δ ≤ 1 / 2 := by
    rw [hdcast, hδdef, mul_one_div, div_le_iff₀ hM]
    have : (d : ℝ) * (d / 3) ≤ (d : ℝ) * L * (1 + R) := by
      have := mul_le_mul_of_nonneg_left hLR hdpos.le
      nlinarith [mul_pos hdpos hL]
    nlinarith
  have hδle : δ ≤ 1 / 2 := by
    have h1 : (1 : ℝ) ≤ ((d - 2 : ℕ) : ℝ) := by rw [hdcast]; linarith
    nlinarith
  set c : ℝ := 1 - δ with hcdef
  have hcpos : 0 < c := by rw [hcdef]; linarith
  have hcn : (1 / 2 : ℝ) ≤ c ^ (d - 2) := by
    have := one_add_mul_le_pow (a := -δ) (by linarith) (d - 2)
    rw [hcdef, sub_eq_add_neg]; nlinarith
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin (d - 2))) = d - 2 := by simp
  -- pointwise facts
  have hφ : ∀ q, y + c • (q - y) = δ • y + c • q := by
    intro q; rw [hcdef]; module
  have hφK : ∀ q ∈ K, y + c • (q - y) ∈ K := by
    intro q hq; rw [hφ]
    exact convex_convexHull ℝ _ hyK hq hδpos.le hcpos.le (by rw [hcdef]; ring)
  have hg0 : ∀ q ∈ K, 0 ≤ chordLen s q := by
    intro q hq
    obtain ⟨l, hl⟩ := FSL36.C_ne s q hq
    exact le_csSup (FSL36.D_bdd s q) ⟨l, hl, l, hl, by simp⟩
  have hgφ : ∀ q ∈ K, 2 * δ ≤ chordLen s (y + c • (q - y)) := by
    intro q hq
    have h := hconc.2 hyK hq hδpos.le hcpos.le (by rw [hcdef]; ring)
    rw [hφ]
    simp only [smul_eq_mul] at h
    rw [hy2] at h
    nlinarith [hg0 q hq]
  have hdist : ∀ q ∈ K, ‖(y + c • (q - y)) - q‖ ≤ δ * (2 + 2 * R) := by
    intro q hq
    have he : (y + c • (q - y)) - q = (-δ) • (q - y) := by rw [hcdef]; module
    rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hδpos]
    refine mul_le_mul_of_nonneg_left ?_ hδpos.le
    obtain ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, hab⟩ := convexHull_exists_dist_ge2 hq hyK
    rw [← dist_eq_norm]
    exact hab.trans (by rw [dist_eq_norm]; exact hdiam i j)
  have hf : ∀ q ∈ K, f q ≤ ENNReal.ofReal (Real.exp 2) * f (y + c • (q - y)) := by
    intro q hq
    set v := (y + c • (q - y)) - q
    have hv := hdist q hq
    have hexp : Real.exp (L * ‖v‖) ^ d ≤ Real.exp 2 := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have : (d : ℝ) * (L * ‖v‖) ≤ (d : ℝ) * (L * (δ * (2 + 2 * R))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hL.le) hdpos.le
      nlinarith
    simp only [hfdef, heightMarginal]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun h => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos 2).le]
    apply ENNReal.ofReal_le_ofReal
    have hprod : ∏ i, mubar i (p - q + s i) (h i) ≤
        Real.exp (L * ‖v‖) ^ d * ∏ i, mubar i (p - (y + c • (q - y)) + s i) (h i) := by
      rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun i _ => (hpos _ _ _).le) (fun i _ => ?_)
      have := hlip i (p - q + s i) (p - (y + c • (q - y)) + s i) (h i) (h i)
      have hn : ‖(p - q + s i) - (p - (y + c • (q - y)) + s i)‖ = ‖v‖ := by
        congr 1; simp only [v]; abel
      rwa [hn, sub_self, zero_pow two_ne_zero, add_zero, Real.sqrt_sq (norm_nonneg _)] at this
    have hP : 0 ≤ ∏ i, mubar i (p - (y + c • (q - y)) + s i) (h i) :=
      Finset.prod_nonneg fun i _ => (hpos _ _ _).le
    calc |∑ i, z i * h i| * ∏ i, mubar i (p - q + s i) (h i)
        ≤ |∑ i, z i * h i| * (Real.exp (L * ‖v‖) ^ d *
            ∏ i, mubar i (p - (y + c • (q - y)) + s i) (h i)) :=
          mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
      _ ≤ |∑ i, z i * h i| * (Real.exp 2 *
            ∏ i, mubar i (p - (y + c • (q - y)) + s i) (h i)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hP) (abs_nonneg _)
      _ = Real.exp 2 * (|∑ i, z i * h i| *
            ∏ i, mubar i (p - (y + c • (q - y)) + s i) (h i)) := by ring
  -- assembly
  set G : EuclideanSpace ℝ (Fin (d - 2)) → ENNReal :=
    fun q => ENNReal.ofReal (chordLen s q) * f q with hGdef
  set κ : ENNReal := ENNReal.ofReal (2 * δ) * ENNReal.ofReal (Real.exp (-2)) with hκ
  have hpt : ∀ q, K.indicator (fun q => κ * f q) q ≤ K.indicator G (y + c • (q - y)) := by
    intro q
    by_cases hq : q ∈ K
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (hφK q hq)]
      have h1 := hf q hq
      have h2 : ENNReal.ofReal (Real.exp (-2)) * f q ≤ f (y + c • (q - y)) := by
        calc ENNReal.ofReal (Real.exp (-2)) * f q
            ≤ ENNReal.ofReal (Real.exp (-2)) *
                (ENNReal.ofReal (Real.exp 2) * f (y + c • (q - y))) := by gcongr
          _ = f (y + c • (q - y)) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
            norm_num
      simp only [hGdef, hκ, mul_assoc]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hgφ q hq)) h2
    · rw [Set.indicator_of_notMem hq]; exact bot_le
  have hR1 : ∫⁻ q in K, G q = ENNReal.ofReal (c ^ (d - 2)) *
      ∫⁻ q, K.indicator G (y + c • (q - y)) := by
    rw [← lintegral_indicator hKm, FSL39.cv volume (K.indicator G) y hcpos, hfin]
  have hL1 : ∫⁻ q, K.indicator (fun q => κ * f q) q = κ * ∫⁻ q in K, f q := by
    rw [lintegral_indicator hKm, lintegral_const_mul' _ _ (by
      rw [hκ]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  have hmain : ENNReal.ofReal (c ^ (d - 2)) * κ * ∫⁻ q in K, f q ≤ ∫⁻ q in K, G q := by
    rw [hR1, mul_assoc, ← hL1]
    gcongr with q
    exact hpt q
  refine le_trans ?_ hmain
  gcongr
  rw [hκ, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have he : Real.exp (-2) / ((d : ℝ) * L * (1 + R)) = Real.exp (-2) * δ := by
    rw [hδdef]; ring
  rw [he]
  have hE := Real.exp_pos (-2)
  nlinarith [mul_pos hE hδpos]
