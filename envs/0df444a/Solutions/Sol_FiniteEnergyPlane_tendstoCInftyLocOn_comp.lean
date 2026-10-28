-- Prove2me | solution 1 for FiniteEnergyPlane.tendstoCInftyLocOn_comp
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-26T00:03:42.762045+00:00
-- url     : https://prove2.me/submissions/2916435f-0410-4a21-95ca-6f8a38f85cac

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Operator.LinearIsometry

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

section TCLComp

universe u v w

/-- `D^{m+1} h_k → D^{m+1} h` follows from `D^m (Dh_k) → D^m (Dh)`. -/
lemma tclc_succ {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {h : ℕ → E → F} {h0 : E → F} {K : Set E} {m : ℕ}
    (H : TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (fun y => fderiv ℝ (h k) y))
      (iteratedFDeriv ℝ m (fun y => fderiv ℝ h0 y)) atTop K) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ (m + 1) (h k))
      (iteratedFDeriv ℝ (m + 1) h0) atTop K := by
  have hs : ∀ f : E → F, iteratedFDeriv ℝ (m + 1) f =
      (continuousMultilinearCurryRightEquiv' ℝ m E F).symm ∘
        iteratedFDeriv ℝ m (fun y => fderiv ℝ f y) :=
    fun f => funext fun x => iteratedFDeriv_succ_eq_comp_right
  have key : (fun k => iteratedFDeriv ℝ (m + 1) (h k)) = fun k =>
      (continuousMultilinearCurryRightEquiv' ℝ m E F).symm ∘
        iteratedFDeriv ℝ m (fun y => fderiv ℝ (h k) y) := funext fun k => hs _
  rw [key, hs h0]
  exact (continuousMultilinearCurryRightEquiv' ℝ m E F).symm.isometry.uniformContinuous.comp_tendstoUniformlyOn H

/-- `D^m (Dh_k) → D^m (Dh)` follows from `D^{m+1} h_k → D^{m+1} h`. -/
lemma tclc_fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {h : ℕ → E → F} {h0 : E → F} {K : Set E} {m : ℕ}
    (H : TendstoUniformlyOn (fun k => iteratedFDeriv ℝ (m + 1) (h k))
      (iteratedFDeriv ℝ (m + 1) h0) atTop K) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (fun y => fderiv ℝ (h k) y))
      (iteratedFDeriv ℝ m (fun y => fderiv ℝ h0 y)) atTop K := by
  have hs : ∀ f : E → F, iteratedFDeriv ℝ (m + 1) f =
      (continuousMultilinearCurryRightEquiv' ℝ m E F).symm ∘
        iteratedFDeriv ℝ m (fun y => fderiv ℝ f y) :=
    fun f => funext fun x => iteratedFDeriv_succ_eq_comp_right
  have key : (fun k => iteratedFDeriv ℝ (m + 1) (h k)) = fun k =>
      (continuousMultilinearCurryRightEquiv' ℝ m E F).symm ∘
        iteratedFDeriv ℝ m (fun y => fderiv ℝ (h k) y) := funext fun k => hs _
  rw [key, hs h0] at H
  have := (continuousMultilinearCurryRightEquiv' ℝ m E F).isometry.uniformContinuous.comp_tendstoUniformlyOn H
  simpa [Function.comp_def] using this

/-- Order-`0` derivatives converge uniformly iff the functions do. -/
lemma tclc_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {h : ℕ → E → F} {h0 : E → F} {K : Set E} :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ 0 (h k)) (iteratedFDeriv ℝ 0 h0) atTop K ↔
      TendstoUniformlyOn h h0 atTop K := by
  simp only [iteratedFDeriv_zero_eq_comp]
  constructor
  · intro H
    have := (continuousMultilinearCurryFin0 ℝ E F).isometry.uniformContinuous.comp_tendstoUniformlyOn H
    simpa [Function.comp_def] using this
  · intro H
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.isometry.uniformContinuous.comp_tendstoUniformlyOn H

/-- Uniform convergence of `D^m` is preserved by post-composition with a continuous linear
equivalence. -/
lemma tclc_compLeft {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F ≃L[ℝ] G) {h : ℕ → E → F} {h0 : E → F} {K : Set E} {m : ℕ}
    (H : TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (h k)) (iteratedFDeriv ℝ m h0) atTop K) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (L ∘ h k)) (iteratedFDeriv ℝ m (L ∘ h0))
      atTop K := by
  have hs : ∀ f : E → F, iteratedFDeriv ℝ m (L ∘ f) =
      (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin m => E) F G
        (L : F →L[ℝ] G)) ∘ iteratedFDeriv ℝ m f :=
    fun f => funext fun x => by
      rw [L.iteratedFDeriv_comp_left]; rfl
  have key : (fun k => iteratedFDeriv ℝ m (L ∘ h k)) = fun k =>
      (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin m => E) F G
        (L : F →L[ℝ] G)) ∘ iteratedFDeriv ℝ m (h k) := funext fun k => hs _
  rw [key, hs h0]
  exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin m => E) F G
    (L : F →L[ℝ] G)).uniformContinuous.comp_tendstoUniformlyOn H

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma tclc_iFW {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : X → F} (n : ℕ) :
    iteratedFDerivWithin ℝ n f U x = iteratedFDeriv ℝ n f x :=
  iteratedFDerivWithin_of_isOpen n hU hx

lemma tclc_cont {U : Set X} (hU : IsOpen U) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : X → F} (hf : ContDiffOn ℝ ∞ f U) (j : ℕ) : ContinuousOn (iteratedFDeriv ℝ j f) U :=
  (hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hU.uniqueDiffOn).congr
    fun _ hx => (iteratedFDerivWithin_of_isOpen j hU hx).symm

lemma tclc_bound {K : Set X} (hK : IsCompact K) {U : Set X} (hU : IsOpen U) (hKU : K ⊆ U)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : X → F} (hf : ContDiffOn ℝ ∞ f U)
    (m : ℕ) : ∃ M, 0 ≤ M ∧ ∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ M := by
  have : ∀ j, ∃ M, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ M := fun j =>
    hK.exists_bound_of_continuousOn ((tclc_cont hU hf j).mono hKU)
  choose M hM using this
  refine ⟨∑ j ∈ Finset.range (m + 1), |M j|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro j hj x hx
  calc ‖iteratedFDeriv ℝ j f x‖ ≤ M j := hM j x hx
    _ ≤ |M j| := le_abs_self _
    _ ≤ _ := Finset.single_le_sum (f := fun j => |M j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))

lemma tclc_bil_cd {U : Set X} {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Bl : E →L[ℝ] F →L[ℝ] G) {A : X → E} {B : X → F} (hA : ContDiffOn ℝ ∞ A U)
    (hB : ContDiffOn ℝ ∞ B U) : ContDiffOn ℝ ∞ (fun y => Bl (A y) (B y)) U :=
  (Bl.contDiff.comp_contDiffOn hA).clm_apply hB

lemma tclc_bil_bound {U : Set X} (hU : IsOpen U) {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (Bl : E →L[ℝ] F →L[ℝ] G) {A : X → E} {B : X → F}
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) {x : X} (hx : x ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => Bl (A y) (B y)) x‖ ≤
      ‖Bl‖ * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i A x‖ *
        ‖iteratedFDeriv ℝ (m - i) B x‖ := by
  have := Bl.norm_iteratedFDerivWithin_le_of_bilinear hA hB hU.uniqueDiffOn hx (n := m)
    (by exact_mod_cast le_top)
  simpa only [tclc_iFW hU hx] using this

lemma tclc_cdAt {U : Set X} (hU : IsOpen U) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : X → F} (hf : ContDiffOn ℝ ∞ f U) {x : X} (hx : x ∈ U) (m : ℕ) : ContDiffAt ℝ m f x :=
  (hf.contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast le_top)

/-- Product rule for `C^m` convergence on a compact set. -/
lemma tclc_prod {U : Set X} (hU : IsOpen U) {K : Set X} (hKU : K ⊆ U) (hK : IsCompact K)
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (Bl : E →L[ℝ] F →L[ℝ] G)
    (A : ℕ → X → E) (A0 : X → E) (B : ℕ → X → F) (B0 : X → F)
    (hA : ∀ k, ContDiffOn ℝ ∞ (A k) U) (hA0 : ContDiffOn ℝ ∞ A0 U)
    (hB : ∀ k, ContDiffOn ℝ ∞ (B k) U) (hB0 : ContDiffOn ℝ ∞ B0 U) (m : ℕ)
    (hAc : ∀ j ≤ m, TendstoUniformlyOn (fun k => iteratedFDeriv ℝ j (A k))
      (iteratedFDeriv ℝ j A0) atTop K)
    (hBc : ∀ j ≤ m, TendstoUniformlyOn (fun k => iteratedFDeriv ℝ j (B k))
      (iteratedFDeriv ℝ j B0) atTop K) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (fun y => Bl (A k y) (B k y)))
      (iteratedFDeriv ℝ m (fun y => Bl (A0 y) (B0 y))) atTop K := by
  obtain ⟨MA, hMA0, hMA⟩ := tclc_bound hK hU hKU hA0 m
  obtain ⟨MB, hMB0, hMB⟩ := tclc_bound hK hU hKU hB0 m
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set C : ℝ := (‖Bl‖ + 1) * 2 ^ m * (MA + MB + 1) with hC
  have hCpos : 0 < C := by positivity
  set δ : ℝ := min 1 (ε / (2 * C)) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδC : C * δ ≤ ε / 2 := by
    have : δ ≤ ε / (2 * C) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hA' : ∀ᶠ k in atTop, ∀ j ∈ Finset.range (m + 1), ∀ x ∈ K,
      dist (iteratedFDeriv ℝ j A0 x) (iteratedFDeriv ℝ j (A k) x) < δ :=
    (Filter.eventually_all_finset _).2 fun j hj =>
      Metric.tendstoUniformlyOn_iff.1 (hAc j (by simp at hj; omega)) δ hδpos
  have hB' : ∀ᶠ k in atTop, ∀ j ∈ Finset.range (m + 1), ∀ x ∈ K,
      dist (iteratedFDeriv ℝ j B0 x) (iteratedFDeriv ℝ j (B k) x) < δ :=
    (Filter.eventually_all_finset _).2 fun j hj =>
      Metric.tendstoUniformlyOn_iff.1 (hBc j (by simp at hj; omega)) δ hδpos
  filter_upwards [hA', hB'] with k hk1 hk2 x hx
  have hxU := hKU hx
  -- smoothness facts
  have cA : ContDiffOn ℝ ∞ (fun y => A k y - A0 y) U := (hA k).sub hA0
  have cB : ContDiffOn ℝ ∞ (fun y => B k y - B0 y) U := (hB k).sub hB0
  have c1 := tclc_bil_cd Bl cA (hB k)
  have c2 := tclc_bil_cd Bl hA0 cB
  have c0 := tclc_bil_cd Bl hA0 hB0
  have e1 : (fun y => Bl (A k y) (B k y)) =
      ((fun y => Bl (A k y - A0 y) (B k y)) + (fun y => Bl (A0 y) (B k y - B0 y))) +
        (fun y => Bl (A0 y) (B0 y)) := by
    funext y
    simp only [Pi.add_apply, map_sub, ContinuousLinearMap.sub_apply]
    abel
  have hsplit : iteratedFDeriv ℝ m (fun y => Bl (A k y) (B k y)) x =
      (iteratedFDeriv ℝ m (fun y => Bl (A k y - A0 y) (B k y)) x +
        iteratedFDeriv ℝ m (fun y => Bl (A0 y) (B k y - B0 y)) x) +
        iteratedFDeriv ℝ m (fun y => Bl (A0 y) (B0 y)) x := by
    rw [e1, iteratedFDeriv_add_apply
      (f := (fun y => Bl (A k y - A0 y) (B k y)) + (fun y => Bl (A0 y) (B k y - B0 y)))
      (g := fun y => Bl (A0 y) (B0 y))
      ((tclc_cdAt hU c1 hxU m).add (tclc_cdAt hU c2 hxU m)) (tclc_cdAt hU c0 hxU m),
      iteratedFDeriv_add_apply (f := fun y => Bl (A k y - A0 y) (B k y))
      (g := fun y => Bl (A0 y) (B k y - B0 y)) (tclc_cdAt hU c1 hxU m) (tclc_cdAt hU c2 hxU m)]
  have hsubA : ∀ i, iteratedFDeriv ℝ i (fun y => A k y - A0 y) x =
      iteratedFDeriv ℝ i (A k) x - iteratedFDeriv ℝ i A0 x := fun i =>
    iteratedFDeriv_sub_apply (tclc_cdAt hU (hA k) hxU i) (tclc_cdAt hU hA0 hxU i)
  have hsubB : ∀ i, iteratedFDeriv ℝ i (fun y => B k y - B0 y) x =
      iteratedFDeriv ℝ i (B k) x - iteratedFDeriv ℝ i B0 x := fun i =>
    iteratedFDeriv_sub_apply (tclc_cdAt hU (hB k) hxU i) (tclc_cdAt hU hB0 hxU i)
  have hchoose : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) = 2 ^ m := by
    exact_mod_cast Nat.sum_range_choose m
  -- bound the first piece
  have b1 : ‖iteratedFDeriv ℝ m (fun y => Bl (A k y - A0 y) (B k y)) x‖ ≤
      ‖Bl‖ * (2 ^ m * (δ * (MB + 1))) := by
    refine (tclc_bil_bound hU Bl cA (hB k) hxU m).trans ?_
    gcongr
    rw [← hchoose, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [mul_assoc, hsubA]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have h1 : ‖iteratedFDeriv ℝ i (A k) x - iteratedFDeriv ℝ i A0 x‖ < δ := by
      rw [← dist_eq_norm, dist_comm]; exact hk1 i (Finset.mem_range.2 (by omega)) x hx
    have h2 : ‖iteratedFDeriv ℝ (m - i) (B k) x‖ ≤ MB + 1 := by
      have e1 := hk2 (m - i) (Finset.mem_range.2 (by omega)) x hx
      have e2 := hMB (m - i) (by omega) x hx
      have e3 := norm_sub_norm_le (iteratedFDeriv ℝ (m - i) (B k) x)
        (iteratedFDeriv ℝ (m - i) B0 x)
      rw [dist_comm, dist_eq_norm] at e1
      linarith
    exact mul_le_mul h1.le h2 (norm_nonneg _) hδpos.le
  have b2 : ‖iteratedFDeriv ℝ m (fun y => Bl (A0 y) (B k y - B0 y)) x‖ ≤
      ‖Bl‖ * (2 ^ m * (MA * δ)) := by
    refine (tclc_bil_bound hU Bl hA0 cB hxU m).trans ?_
    gcongr
    rw [← hchoose, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [mul_assoc, hsubB]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have h1 : ‖iteratedFDeriv ℝ (m - i) (B k) x - iteratedFDeriv ℝ (m - i) B0 x‖ < δ := by
      rw [← dist_eq_norm, dist_comm]; exact hk2 (m - i) (Finset.mem_range.2 (by omega)) x hx
    exact mul_le_mul (hMA i hi' x hx) h1.le (norm_nonneg _) hMA0
  rw [dist_comm, dist_eq_norm, hsplit, add_sub_cancel_right]
  calc ‖iteratedFDeriv ℝ m (fun y => Bl (A k y - A0 y) (B k y)) x +
        iteratedFDeriv ℝ m (fun y => Bl (A0 y) (B k y - B0 y)) x‖
      ≤ ‖Bl‖ * (2 ^ m * (δ * (MB + 1))) + ‖Bl‖ * (2 ^ m * (MA * δ)) :=
        (norm_add_le _ _).trans (add_le_add b1 b2)
    _ = ‖Bl‖ * 2 ^ m * (MA + MB + 1) * δ := by ring
    _ ≤ C * δ := by
        rw [hC]; gcongr; linarith
    _ < ε := by linarith

variable {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma tclc_K' [FiniteDimensional ℝ Y] {W : Set Y} (hW : IsOpen W) {K : Set X} (hK : IsCompact K)
    {f : ℕ → X → Y} {f0 : X → Y} (hf0 : ContinuousOn f0 K) (hmap : Set.MapsTo f0 K W)
    (hfc : TendstoUniformlyOn f f0 atTop K) :
    ∃ K' : Set Y, IsCompact K' ∧ K' ⊆ W ∧ Set.MapsTo f0 K K' ∧
      ∀ᶠ k in atTop, Set.MapsTo (f k) K K' := by
  have hc : IsCompact (f0 '' K) := hK.image_of_continuousOn hf0
  obtain ⟨δ, hδ, hsub⟩ := hc.exists_cthickening_subset_open hW (Set.image_subset_iff.2 hmap)
  refine ⟨cthickening δ (f0 '' K), hc.cthickening, hsub,
    fun x hx => self_subset_cthickening _ (Set.mem_image_of_mem f0 hx), ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hfc δ hδ] with k hk x hx
  exact mem_cthickening_of_dist_le (f k x) (f0 x) δ (f0 '' K) (Set.mem_image_of_mem _ hx)
    (by rw [dist_comm]; exact (hk x hx).le)

lemma tclc_comp0 {Z : Type*} [NormedAddCommGroup Z] {K : Set X} {K' : Set Y}
    (hK' : IsCompact K') {f : ℕ → X → Y} {f0 : X → Y} {g : ℕ → Y → Z} {g0 : Y → Z}
    (hg0 : ContinuousOn g0 K') (hgc : TendstoUniformlyOn g g0 atTop K')
    (hfc : TendstoUniformlyOn f f0 atTop K) (h0 : Set.MapsTo f0 K K')
    (hk : ∀ᶠ k in atTop, Set.MapsTo (f k) K K') :
    TendstoUniformlyOn (fun k => g k ∘ f k) (g0 ∘ f0) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hUC⟩ := Metric.uniformContinuousOn_iff.1
    (hK'.uniformContinuousOn_of_continuous hg0) (ε / 2) (by positivity)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hfc δ hδ,
    Metric.tendstoUniformlyOn_iff.1 hgc (ε / 2) (by positivity), hk] with k h1 h2 h3 x hx
  simp only [Function.comp_apply]
  calc dist (g0 (f0 x)) (g k (f k x))
      ≤ dist (g0 (f0 x)) (g0 (f k x)) + dist (g0 (f k x)) (g k (f k x)) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hUC _ (h0 hx) _ (h3 hx) (h1 x hx)) (h2 _ (h3 hx))
    _ = ε := by ring

lemma tclc_main [FiniteDimensional ℝ Y] {U : Set X} (hU : IsOpen U) {W : Set Y} (hW : IsOpen W)
    (f : ℕ → X → Y) (f₀ : X → Y) (hf : ∀ k, ContDiffOn ℝ ∞ (f k) U) (hf₀ : ContDiffOn ℝ ∞ f₀ U)
    (hfW : ∀ k, Set.MapsTo (f k) U W) (hf₀W : Set.MapsTo f₀ U W)
    (hff : JHolomorphic.TendstoCInftyLocOn f f₀ U) :
    ∀ m : ℕ, ∀ (Z : Type (max v w)) [NormedAddCommGroup Z] [NormedSpace ℝ Z]
      (g : ℕ → Y → Z) (g₀ : Y → Z), (∀ k, ContDiffOn ℝ ∞ (g k) W) → ContDiffOn ℝ ∞ g₀ W →
      JHolomorphic.TendstoCInftyLocOn g g₀ W → ∀ K ⊆ U, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (g k ∘ f k))
        (iteratedFDeriv ℝ m (g₀ ∘ f₀)) atTop K := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro Z _ _ g g₀ hg hg₀ hgg K hKU hK
  have hf0K : TendstoUniformlyOn f f₀ atTop K := tclc_zero.1 (hff K hKU hK 0)
  obtain ⟨K', hK', hK'W, h0, hk⟩ :=
    tclc_K' hW hK (hf₀.continuousOn.mono hKU) (hf₀W.mono_left hKU) hf0K
  cases m with
  | zero =>
    exact tclc_zero.2 (tclc_comp0 hK' (hg₀.continuousOn.mono hK'W)
      (tclc_zero.1 (hgg K' hK'W hK' 0)) hf0K h0 hk)
  | succ m =>
    apply tclc_succ
    have hfd : ∀ (gg : Y → Z) (ff : X → Y), ContDiffOn ℝ ∞ gg W → ContDiffOn ℝ ∞ ff U →
        Set.MapsTo ff U W → ∀ x ∈ U,
        iteratedFDeriv ℝ m (fun y => fderiv ℝ (gg ∘ ff) y) x =
          iteratedFDeriv ℝ m (fun y => ContinuousLinearMap.compL ℝ X Y Z
            (fderiv ℝ gg (ff y)) (fderiv ℝ ff y)) x := by
      intro gg ff hgg' hff' hmap x hx
      apply Filter.EventuallyEq.eq_of_nhds
      apply Filter.EventuallyEq.iteratedFDeriv
      filter_upwards [hU.mem_nhds hx] with y hy
      have h1 : DifferentiableAt ℝ gg (ff y) :=
        (hgg'.contDiffAt (hW.mem_nhds (hmap hy))).differentiableAt (by simp)
      have h2 : DifferentiableAt ℝ ff y :=
        (hff'.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
      rw [fderiv_comp y h1 h2]
      rfl
    have hDg : ∀ k, ContDiffOn ℝ ∞ (fun y => fderiv ℝ (g k) y) W := fun k =>
      (hg k).fderiv_of_isOpen hW (by simp)
    have hDg₀ : ContDiffOn ℝ ∞ (fun y => fderiv ℝ g₀ y) W := hg₀.fderiv_of_isOpen hW (by simp)
    have hDf : ∀ k, ContDiffOn ℝ ∞ (fun y => fderiv ℝ (f k) y) U := fun k =>
      (hf k).fderiv_of_isOpen hU (by simp)
    have hDf₀ : ContDiffOn ℝ ∞ (fun y => fderiv ℝ f₀ y) U := hf₀.fderiv_of_isOpen hU (by simp)
    have hggD : JHolomorphic.TendstoCInftyLocOn (fun k => fun y => fderiv ℝ (g k) y)
        (fun y => fderiv ℝ g₀ y) W := fun K hKW hK j => tclc_fderiv (hgg K hKW hK (j + 1))
    have hP := tclc_prod hU hKU hK (ContinuousLinearMap.compL ℝ X Y Z)
      (fun k y => fderiv ℝ (g k) (f k y)) (fun y => fderiv ℝ g₀ (f₀ y))
      (fun k y => fderiv ℝ (f k) y) (fun y => fderiv ℝ f₀ y)
      (fun k => (hDg k).comp (hf k) (hfW k)) (hDg₀.comp hf₀ hf₀W) hDf hDf₀ m
      (fun j hj => ih j (by omega) (Y →L[ℝ] Z) (fun k y => fderiv ℝ (g k) y)
        (fun y => fderiv ℝ g₀ y) hDg hDg₀ hggD K hKU hK)
      (fun j _ => tclc_fderiv (hff K hKU hK (j + 1)))
    refine (hP.congr (Filter.Eventually.of_forall fun k x hx => ?_)).congr_right ?_
    · exact (hfd (g k) (f k) (hg k) (hf k) (hfW k) x (hKU hx)).symm
    · intro x hx
      exact (hfd g₀ f₀ hg₀ hf₀ hf₀W x (hKU hx)).symm

end TCLComp

/-- `C^∞_loc` convergence is preserved under composition. -/
theorem tclc_final {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] {U : Set X} (hU : IsOpen U) {W : Set Y} (hW : IsOpen W)
    (f : ℕ → X → Y) (f₀ : X → Y) (g : ℕ → Y → Z) (g₀ : Y → Z)
    (hf : ∀ k, ContDiffOn ℝ ∞ (f k) U) (hf₀ : ContDiffOn ℝ ∞ f₀ U)
    (hg : ∀ k, ContDiffOn ℝ ∞ (g k) W) (hg₀ : ContDiffOn ℝ ∞ g₀ W)
    (hfW : ∀ k, Set.MapsTo (f k) U W) (hf₀W : Set.MapsTo f₀ U W)
    (hff : JHolomorphic.TendstoCInftyLocOn f f₀ U) (hgg : JHolomorphic.TendstoCInftyLocOn g g₀ W) :
    JHolomorphic.TendstoCInftyLocOn (fun k => g k ∘ f k) (g₀ ∘ f₀) U := by
  intro K hKU hK m
  let e : Z ≃L[ℝ] ULift.{u_2} Z := ContinuousLinearEquiv.ulift.symm
  have h1 := tclc_main.{u_1, u_2, u_3} hU hW f f₀ hf hf₀ hfW hf₀W hff m (ULift.{u_2} Z)
    (fun k => e ∘ g k) (e ∘ g₀) (fun k => e.contDiff.comp_contDiffOn (hg k))
    (e.contDiff.comp_contDiffOn hg₀)
    (fun K' hK'W hK' j => tclc_compLeft e (hgg K' hK'W hK' j)) K hKU hK
  have h2 := tclc_compLeft e.symm h1
  have h3 : ∀ q : X → Z, e.symm ∘ ((e ∘ q)) = q := fun q => funext fun x => by simp
  simpa only [Function.comp_assoc, h3] using h2

end FiniteEnergyPlane

open scoped ContDiff in
theorem solution {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] {U : Set X} (hU : IsOpen U) {W : Set Y} (hW : IsOpen W)
    (f : ℕ → X → Y) (f₀ : X → Y) (g : ℕ → Y → Z) (g₀ : Y → Z)
    (hf : ∀ k, ContDiffOn ℝ ∞ (f k) U) (hf₀ : ContDiffOn ℝ ∞ f₀ U)
    (hg : ∀ k, ContDiffOn ℝ ∞ (g k) W) (hg₀ : ContDiffOn ℝ ∞ g₀ W)
    (hfW : ∀ k, Set.MapsTo (f k) U W) (hf₀W : Set.MapsTo f₀ U W)
    (hff : JHolomorphic.TendstoCInftyLocOn f f₀ U) (hgg : JHolomorphic.TendstoCInftyLocOn g g₀ W) :
    JHolomorphic.TendstoCInftyLocOn (fun k => g k ∘ f k) (g₀ ∘ f₀) U :=
  FiniteEnergyPlane.tclc_final hU hW f f₀ g g₀ hf hf₀ hg hg₀ hfW hf₀W hff hgg
