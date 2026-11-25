-- Prove2me | solution 1 for FiniteEnergyPlane.exists_contDiffOn_transition_of_pageMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T14:05:42.625858+00:00
-- url     : https://prove2.me/submissions/c36858bc-774e-4277-b0a0-d5d2d693e6c9

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_affine_slice_relation_of_pageMap_eq
import Theorems.Thm_FiniteEnergyPlane_injOn_pageMap_of_isPageFamilyOn
import Theorems.Thm_FiniteEnergyPlane_exists_contDiffOn_lift_of_injective_fderiv
import Theorems.Thm_FiniteEnergyPlane_proj_aCoord_exp_smul
import Theorems.Thm_FiniteEnergyPlane_proj_smul_eq_of_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_pageMap



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_contDiffOn_transition_of_pageMap_eq_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I : Set ℝ) (hI : IsOpen I) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U)
    (hinj : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), Function.Injective (fderiv ℝ (pageMap H U) p))
    (hpos : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), IsReebPositiveAt H U p)
    (t₀ t₁ : ℝ) (ht₀ : t₀ ∈ I) (ht₁ : t₁ ∈ I) (z₀ z₁ : ℂ)
    (h01 : pageMap H U (t₀, z₀) = pageMap H U (t₁, z₁)) :
    ∃ η > 0, ball t₀ η ⊆ I ∧ ∃ (β c : ℝ → ℝ) (A B : ℝ → ℂ),
      ContDiffOn ℝ l β (ball t₀ η) ∧ ContDiffOn ℝ l c (ball t₀ η) ∧
      ContDiffOn ℝ l A (ball t₀ η) ∧ ContDiffOn ℝ l B (ball t₀ η) ∧ β t₀ = t₁ ∧
      ∀ s ∈ ball t₀ η, β s ∈ I ∧ 0 < deriv β s ∧ A s ≠ 0 ∧
        ∀ z, U (s, z) = Real.exp (2 * c s) • U (β s, A s * z + B s) := by
  have hne : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), U p ≠ 0 := fun p hp =>
    (hU.2 p.1 hp.1).1.1.1.2.1 p.2 trivial
  have hps : ∀ (c : ℝ) (p : ℝ × ℂ), p ∈ I ×ˢ (Set.univ : Set ℂ) →
      proj H (Real.exp (2 * c) • U p) = pageMap H U p := fun c p hp =>
    (proj_aCoord_exp_smul H hH c _ (hne p hp)).1
  have hIo : IsOpen (I ×ˢ (Set.univ : Set ℂ)) := hI.prod isOpen_univ
  have hpd : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), DifferentiableAt ℝ (pageMap H U) p := fun p hp =>
    ((contDiffOn_pageMap H hH U I hI (hU.1.of_le (by exact_mod_cast hl)) hne).contDiffAt
      (hIo.mem_nhds hp)).differentiableAt (by norm_num)
  -- the relation between two slices
  have hrel : ∀ s ∈ I, ∀ s' ∈ I, ∀ z z', pageMap H U (s, z) = pageMap H U (s', z') →
      ∃ (c : ℝ) (A B : ℂ), A ≠ 0 ∧ ∀ w, U (s, w) = Real.exp (2 * c) • U (s', A * w + B) := by
    intro s hs s' hs' z z' h
    obtain ⟨σ, σ', c, A, B, hσ, hA, -, hw⟩ := exists_affine_slice_relation_of_pageMap_eq H hH J hJ
      P hcz γ y l I U hU s s' hs hs' z z' h
    rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨c, A⁻¹, -(A⁻¹ * B), inv_ne_zero hA, fun w => ?_⟩
      rw [← hw]
      congr 2
      field_simp
      ring
    · refine ⟨-c, A, B, hA, fun w => ?_⟩
      rw [hw, smul_smul, ← Real.exp_add]
      simp
  obtain ⟨c₀, A₀, B₀, hA₀, hr₀⟩ := hrel t₀ ht₀ t₁ ht₁ z₀ z₁ h01
  -- the four-dimensional map
  let Φ : ℝ × ℝ × ℂ → V 1 := fun p => Real.exp (2 * p.1) • U p.2
  let O : Set (ℝ × ℝ × ℂ) := Set.univ ×ˢ (I ×ˢ Set.univ)
  have hO : IsOpen O := isOpen_univ.prod hIo
  have hΦ : ContDiffOn ℝ l Φ O := by
    have u1 : ContDiffOn ℝ l (fun p : ℝ × ℝ × ℂ => U p.2) O :=
      hU.1.comp contDiffOn_snd fun p hp => hp.2
    have u2 : ContDiffOn ℝ l (fun p : ℝ × ℝ × ℂ => Real.exp (2 * p.1)) O :=
      (contDiffOn_const.mul contDiffOn_fst).exp
    exact u2.smul u1
  have hl0 : ((l : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
  have hΦi : ∀ p ∈ O, Function.Injective (fderiv ℝ Φ p) := by
    rintro ⟨a, q⟩ ⟨-, hq⟩
    have hUd : HasFDerivAt U (fderiv ℝ U q) q :=
      ((hU.1.contDiffAt (hIo.mem_nhds hq)).differentiableAt hl0).hasFDerivAt
    have hΦd : HasFDerivAt Φ (fderiv ℝ Φ (a, q)) (a, q) :=
      ((hΦ.contDiffAt (hO.mem_nhds ⟨trivial, hq⟩)).differentiableAt hl0).hasFDerivAt
    have hprojd : DifferentiableAt ℝ (proj H) (Φ (a, q)) :=
      ((contDiffAt_aCoord_proj H hH _ (smul_ne_zero (Real.exp_ne_zero _)
        (hne q hq))).2).differentiableAt (by simp)
    have e1 : HasFDerivAt (fun p : ℝ × ℝ × ℂ => pageMap H U p.2)
        ((fderiv ℝ (pageMap H U) q).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ))) (a, q) :=
      HasFDerivAt.comp (a, q) (g := pageMap H U) (hpd q hq).hasFDerivAt hasFDerivAt_snd
    have e2 : HasFDerivAt (fun p : ℝ × ℝ × ℂ => pageMap H U p.2)
        ((fderiv ℝ (proj H) (Φ (a, q))).comp (fderiv ℝ Φ (a, q))) (a, q) := by
      refine (hprojd.hasFDerivAt.comp (a, q) hΦd).congr_of_eventuallyEq ?_
      filter_upwards [hO.mem_nhds (show (a, q) ∈ O from ⟨trivial, hq⟩)] with p hp
      exact (hps p.1 p.2 hp.2).symm
    have e0 : HasFDerivAt (fun p : ℝ × ℝ × ℂ => Real.exp (2 * p.1))
        (Real.exp (2 * a) • ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ))) (a, q) :=
      ((hasFDerivAt_fst (𝕜 := ℝ) (p := (a, q))).const_mul 2).exp
    have e3 := e0.smul (HasFDerivAt.comp (a, q) (g := U) hUd hasFDerivAt_snd)
    rw [injective_iff_map_eq_zero]
    rintro ⟨k, v⟩ h
    have h1 : fderiv ℝ (pageMap H U) q v = 0 := by
      have := congrArg (fun F => F (k, v)) (e1.unique e2)
      simp only [ContinuousLinearMap.comp_apply, h, map_zero] at this
      exact this
    have hv : v = 0 := hinj q hq (by rw [h1, map_zero])
    subst hv
    have h2 : fderiv ℝ Φ (a, q) (k, 0) = (Real.exp (2 * a) * (2 * k)) • U q := by
      rw [hΦd.unique e3]
      simp
    rw [h2] at h
    have h3 := (smul_eq_zero.1 h).resolve_right (hne q hq)
    have h4 := (mul_eq_zero.1 h3).resolve_left (Real.exp_ne_zero _)
    have h5 : k = 0 := by linarith
    rw [h5]; rfl
  have hdim : Module.finrank ℝ (ℝ × ℝ × ℂ) = Module.finrank ℝ (V 1) := by
    simp [Module.finrank_prod, Complex.finrank_real_complex]
  obtain ⟨r, hr, hrI⟩ := Metric.isOpen_iff.1 hI t₀ ht₀
  have hg : ∀ z : ℂ, ContDiffOn ℝ l (fun s => U (s, z)) (ball t₀ r) := fun z =>
    hU.1.comp (contDiffOn_id.prodMk contDiffOn_const) fun s hs => ⟨hrI hs, trivial⟩
  have hlift : ∀ z : ℂ, ∃ ε > 0, ∃ p : ℝ → ℝ × ℝ × ℂ, ContDiffOn ℝ l p (ball t₀ ε) ∧
      p t₀ = (c₀, t₁, A₀ * z + B₀) ∧ ∀ t ∈ ball t₀ ε, p t ∈ O ∧ Φ (p t) = U (t, z) := fun z =>
    exists_contDiffOn_lift_of_injective_fderiv hdim hl hO hΦ
      (a := (c₀, t₁, A₀ * z + B₀)) ⟨trivial, ht₁, trivial⟩
      (hΦi _ ⟨trivial, ht₁, trivial⟩) hr (hg z) (hr₀ z)
  obtain ⟨ε₀, hε₀, p, hp, hp0, hpU⟩ := hlift 0
  obtain ⟨ε₁, hε₁, q, hq, hq0, hqU⟩ := hlift 1
  obtain ⟨ε, hε, hεI, hinjε⟩ := injOn_pageMap_of_isPageFamilyOn H hH J hJ P hcz γ y hy l hl I hI U
    hU t₁ ht₁
  have hev : ∀ᶠ s in 𝓝 t₀, (p s).2.1 ∈ ball t₁ ε ∧ (q s).2.1 ∈ ball t₁ ε := by
    have c1 : ContinuousAt (fun s => (p s).2.1) t₀ :=
      (hp.continuousOn.continuousAt (ball_mem_nhds _ hε₀)).snd.fst
    have c2 : ContinuousAt (fun s => (q s).2.1) t₀ :=
      (hq.continuousOn.continuousAt (ball_mem_nhds _ hε₁)).snd.fst
    refine (c1.eventually_mem ?_).and (c2.eventually_mem ?_)
    · rw [hp0]; exact ball_mem_nhds _ hε
    · rw [hq0]; exact ball_mem_nhds _ hε
  obtain ⟨ε₂, hε₂, hs₂⟩ := Metric.eventually_nhds_iff_ball.1 hev
  obtain ⟨η, hη, k0, k1, k2, k3⟩ : ∃ η > 0, η ≤ ε₀ ∧ η ≤ ε₁ ∧ η ≤ ε₂ ∧ η ≤ r :=
    ⟨min (min ε₀ ε₁) (min ε₂ r), lt_min (lt_min hε₀ hε₁) (lt_min hε₂ hr),
      (min_le_left _ _).trans (min_le_left _ _),
      (min_le_left _ _).trans (min_le_right _ _), (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  have hp' := hp.mono (ball_subset_ball k0)
  have hq' := hq.mono (ball_subset_ball k1)
  refine ⟨η, hη, (ball_subset_ball k3).trans hrI, fun s => (p s).2.1, fun s => (p s).1,
    fun s => (q s).2.2 - (p s).2.2, fun s => (p s).2.2, hp'.snd.fst, hp'.fst,
    hq'.snd.snd.sub hp'.snd.snd, hp'.snd.snd, by simp [hp0], fun s hs => ?_⟩
  have hsI : s ∈ I := hrI (ball_subset_ball k3 hs)
  obtain ⟨hpO, hpe⟩ := hpU s (ball_subset_ball k0 hs)
  obtain ⟨hqO, hqe⟩ := hqU s (ball_subset_ball k1 hs)
  obtain ⟨hpb, hqb⟩ := hs₂ s (ball_subset_ball k2 hs)
  have hpg : ∀ s ∈ ball t₀ η, pageMap H U (p s).2 = pageMap H U (s, 0) := by
    intro s hs
    obtain ⟨hpO, hpe⟩ := hpU s (ball_subset_ball k0 hs)
    rw [← hps (p s).1 _ hpO.2]
    exact congrArg (proj H) hpe
  have hqg : pageMap H U (q s).2 = pageMap H U (s, 1) := by
    rw [← hps (q s).1 _ hqO.2]
    exact congrArg (proj H) hqe
  obtain ⟨c', A', B', hA', hw⟩ := hrel s hsI (p s).2.1 hpO.2.1 0 (p s).2.2 (hpg s hs).symm
  have hwp : ∀ z, pageMap H U (s, z) = pageMap H U ((p s).2.1, A' * z + B') := by
    intro z
    rw [← hps c' ((p s).2.1, A' * z + B') ⟨hpO.2.1, trivial⟩]
    exact congrArg (proj H) (hw z)
  have hB : B' = (p s).2.2 := by
    have := hinjε (x₁ := ((p s).2.1, A' * 0 + B')) ⟨hpb, trivial⟩ (x₂ := (p s).2) ⟨hpb, trivial⟩
      ((hwp 0).symm.trans (hpg s hs).symm)
    simpa using congrArg Prod.snd this
  have hA : (q s).2.2 = A' + B' := by
    have := hinjε (x₁ := ((p s).2.1, A' * 1 + B')) ⟨hpb, trivial⟩ (x₂ := (q s).2) ⟨hqb, trivial⟩
      ((hwp 1).symm.trans hqg.symm)
    simpa using (congrArg Prod.snd this).symm
  have hc : c' = (p s).1 := by
    have h1 : Real.exp (2 * c') • U (p s).2 = Real.exp (2 * (p s).1) • U (p s).2 := by
      have := hw 0
      rw [mul_zero, zero_add, hB] at this
      exact this.symm.trans hpe.symm
    have := Real.exp_injective (smul_left_injective ℝ (hne _ hpO.2) h1)
    linarith
  refine ⟨hpO.2.1, ?_, ?_, ?_⟩
  · have hpdiff : DifferentiableAt ℝ p s :=
      (hp'.contDiffAt (isOpen_ball.mem_nhds hs)).differentiableAt hl0
    have d1 : HasDerivAt (fun s => (p s).2) (deriv (fun s => (p s).2) s) s :=
      hpdiff.snd.hasDerivAt
    have d2 : HasDerivAt (fun s => pageMap H U (p s).2)
        (fderiv ℝ (pageMap H U) (p s).2 (deriv (fun s => (p s).2) s)) s :=
      HasFDerivAt.comp_hasDerivAt s (f := fun s => (p s).2) (hpd _ hpO.2).hasFDerivAt d1
    have hU0 : ∀ x ∈ ball t₀ η, pageMap H U (p x).2 = y x := by
      intro x hx
      rw [hpg x hx]
      have h0 : U (x, 0) = y x := (hU.2 x (hrI (ball_subset_ball k3 hx))).1.2.2.1
      show proj H (U (x, 0)) = y x
      rw [h0]
      simpa using proj_smul_eq_of_mem_energySurface H hH (y x) (hy.1 x) 1 one_pos
    have d3 : HasDerivAt (fun s => pageMap H U (p s).2) (reeb H (y s)) s := by
      refine (hy.2 s).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ball.mem_nhds hs] with x hx
      exact hU0 x hx
    obtain ⟨k, hk, v, hkv⟩ := hpos _ hpO.2
    rw [hU0 s hs] at hkv
    have := hinj _ hpO.2 (hkv.trans (d3.unique d2))
    have d4 : HasDerivAt (fun s => (p s).2.1) (deriv (fun s => (p s).2) s).1 s :=
      (ContinuousLinearMap.fst ℝ ℝ ℂ).hasFDerivAt.comp_hasDerivAt s d1
    have e : deriv (fun s => (p s).2.1) s = (deriv (fun s => (p s).2) s).1 := d4.deriv
    rw [e, ← this]
    exact hk
  · show (q s).2.2 - (p s).2.2 ≠ 0
    rw [hA, hB]; simpa using hA'
  · intro z
    show U (s, z) = Real.exp (2 * (p s).1) • U ((p s).2.1, ((q s).2.2 - (p s).2.2) * z + (p s).2.2)
    rw [hw z, hA, hB, hc]
    simp

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I : Set ℝ) (hI : IsOpen I) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U)
    (hinj : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), Function.Injective (fderiv ℝ (pageMap H U) p))
    (hpos : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), IsReebPositiveAt H U p)
    (t₀ t₁ : ℝ) (ht₀ : t₀ ∈ I) (ht₁ : t₁ ∈ I) (z₀ z₁ : ℂ)
    (h01 : pageMap H U (t₀, z₀) = pageMap H U (t₁, z₁)) :
    ∃ η > 0, ball t₀ η ⊆ I ∧ ∃ (β c : ℝ → ℝ) (A B : ℝ → ℂ),
      ContDiffOn ℝ l β (ball t₀ η) ∧ ContDiffOn ℝ l c (ball t₀ η) ∧
      ContDiffOn ℝ l A (ball t₀ η) ∧ ContDiffOn ℝ l B (ball t₀ η) ∧ β t₀ = t₁ ∧
      ∀ s ∈ ball t₀ η, β s ∈ I ∧ 0 < deriv β s ∧ A s ≠ 0 ∧
        ∀ z, U (s, z) = Real.exp (2 * c s) • U (β s, A s * z + B s) :=
  exists_contDiffOn_transition_of_pageMap_eq_aux H hH J hJ P hcz γ y hy l hl I hI U hU hinj hpos t₀ t₁ ht₀ ht₁ z₀ z₁ h01
