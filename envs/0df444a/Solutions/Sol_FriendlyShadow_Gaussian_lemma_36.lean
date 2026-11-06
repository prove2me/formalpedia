-- Prove2me | solution 1 for FriendlyShadow.Gaussian.lemma_36
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T12:49:44.457944+00:00
-- url     : https://prove2.me/submissions/12d620e7-417b-4b13-8680-59f948d9b8ba

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

end FSL36

open FriendlyShadow.Gaussian RealInnerProductSpace in
theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {d : ℕ}
    [NeZero d] (hd : 3 ≤ d) (b : Fin d → V) (ω : V) (hω : ‖ω‖ = 1)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range (shapeOf ω b))) = d - 2)
    (z : Fin d → ℝ) (hz : IsKernelComb (shapeOf ω b) z)
    (q : V) (hq : q ∈ convexHull ℝ (Set.range (shapeOf ω b))) :
    Metric.diam ({p | ∃ t : ℝ, p = projPerp ω (b 0) + q + t • ω} ∩
        convexHull ℝ (Set.range b)) =
      chordLen (shapeOf ω b) q * |∑ i, z i * ⟪ω, b i⟫| := by
  set s := shapeOf ω b with hs
  set x := projPerp ω (b 0) with hx
  set T := ({p | ∃ t : ℝ, p = x + q + t • ω} ∩ convexHull ℝ (Set.range b)) with hT
  set H := |∑ i, z i * ⟪ω, b i⟫| with hH
  have hs0 : s 0 = 0 := by simp [hs, shapeOf]
  have hqω : ⟪ω, q⟫ = 0 := by
    obtain ⟨l, -, -, rfl⟩ := (FSL36.hull_iff _ q).mp hq
    exact FSL36.inner_comb ω hω b l
  -- a point of the chord set
  obtain ⟨l0, hl00, hl01, hl0s⟩ := (FSL36.hull_iff _ q).mp hq
  have hl0 : l0 ∈ chordSet s q := ⟨hl00, hl01, hl0s⟩
  -- key identity
  have key : ∀ l ∈ chordSet s q, ∀ l' ∈ chordSet s q,
      dist (x + q + (∑ i, l i * ⟪ω, b i⟫) • ω) (x + q + (∑ i, l' i * ⟪ω, b i⟫) • ω) =
        (∑ i, |l i - l' i|) * H := by
    intro l hl l' hl'
    obtain ⟨c, hc⟩ := FSL36.diff_mul hd s hs0 hrank z hz q l l' hl hl'
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hω, mul_one,
      Real.norm_eq_abs, ← Finset.sum_sub_distrib]
    have e1 : ∑ i, (l i * ⟪ω, b i⟫ - l' i * ⟪ω, b i⟫) = c * ∑ i, z i * ⟪ω, b i⟫ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← sub_mul, hc i]; ring
    have e2 : ∑ i, |l i - l' i| = |c| := by
      simp only [hc, abs_mul, ← Finset.mul_sum, hz.2.2, mul_one]
    rw [e1, e2, abs_mul, hH]
  set D := {t | ∃ l ∈ chordSet s q, ∃ l' ∈ chordSet s q, t = ∑ i, |l i - l' i|} with hD
  have hDbdd : BddAbove D := ⟨2, by rintro _ ⟨l, hl, l', hl', rfl⟩; exact FSL36.sum_abs_le_two hl hl'⟩
  have hDne : D.Nonempty := ⟨_, l0, hl0, l0, hl0, rfl⟩
  have hCL : chordLen s q = sSup D := rfl
  have hCL0 : 0 ≤ chordLen s q := by
    rw [hCL]
    exact le_csSup_of_le hDbdd ⟨l0, hl0, l0, hl0, rfl⟩ (by simp)
  have hTbdd : Bornology.IsBounded T :=
    (show IsCompact (convexHull ℝ (Set.range b)) from
      Set.Finite.isCompact_convexHull (𝕜 := ℝ) (Set.finite_range b)).isBounded.subset Set.inter_subset_right
  have hmem : ∀ l ∈ chordSet s q, x + q + (∑ i, l i * ⟪ω, b i⟫) • ω ∈ T := fun l hl =>
    (FSL36.mem_T b ω hω q hqω _).mpr ⟨l, hl, rfl⟩
  apply le_antisymm
  · apply Metric.diam_le_of_forall_dist_le (mul_nonneg hCL0 (abs_nonneg _))
    intro p hp p' hp'
    obtain ⟨l, hl, rfl⟩ := (FSL36.mem_T b ω hω q hqω p).mp hp
    obtain ⟨l', hl', rfl⟩ := (FSL36.mem_T b ω hω q hqω p').mp hp'
    rw [key l hl l' hl']
    exact mul_le_mul_of_nonneg_right (le_csSup hDbdd ⟨l, hl, l', hl', rfl⟩) (abs_nonneg _)
  · rcases (abs_nonneg (∑ i, z i * ⟪ω, b i⟫)).eq_or_lt with h0 | hpos
    · rw [← hH] at h0; rw [← h0, mul_zero]; exact Metric.diam_nonneg
    · rw [← hH] at hpos
      rw [← le_div_iff₀ hpos, hCL]
      refine csSup_le hDne ?_
      rintro _ ⟨l, hl, l', hl', rfl⟩
      rw [le_div_iff₀ hpos, ← key l hl l' hl']
      exact Metric.dist_le_diam_of_mem hTbdd (hmem l hl) (hmem l' hl')
