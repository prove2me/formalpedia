-- Prove2me | solution 2 for FiniteEnergyPlane.exists_pageFamily_injective_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-22T19:49:48.612392+00:00
-- url     : https://prove2.me/submissions/c9d79973-5a99-4ecc-bd40-131f7283021d

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_fastPlane_family
import Theorems.Thm_FiniteEnergyPlane_IsReebTrajectory_contDiff
import Theorems.Thm_FiniteEnergyPlane_exists_contDiffOn_lift_of_injective_fderiv
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_dlambdaEnergy_ball_family
import Theorems.Thm_FiniteEnergyPlane_pos_of_hasDerivAt_dlambdaEnergy_ball
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_comp_add_smul
import Theorems.Thm_FiniteEnergyPlane_injective_fderiv_proj_of_fastPlane_family
import Theorems.Thm_FiniteEnergyPlane_rescale_isFiniteEnergyCurve
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_univ_eq_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_ne_top_of_univ_eq_ofReal
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_norm_sub_gt_eq_sub



/-!
# Hryniewicz Lemma 7.3, existence part (`exists_pageFamily_injective_fderiv`): glue

* the family `f` of Lemmas 6.10/6.20 at order `l + 1`;
* a `C^{l+1}` lift `(ζ, τ)` of the Reeb trajectory, `f (ζ t, τ t) = y t`;
* a `C^l` radius `r t` keeping the `dλ`-energy of the disc `B_{r t}(ζ t)` constant;
* `U (t, z) = f (ζ t + r t • z, τ t)`; slices stay in `Λ`, and the immersion property comes from
  the transversality child and the chain rule.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_pageFamily_injective_fderiv_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (t₀ : ℝ) (u₀ : ℂ → V 1) (hu₀ : u₀ ∈ embeddedFastPlaneSet H J P {y t₀} γ)
    (l : ℕ) (hl : 1 ≤ l) :
    ∃ ε > 0, ∃ U : ℝ × ℂ → V 1, IsPageFamilyOn H J P γ y l (ball t₀ ε) U ∧
      (∀ z, U (t₀, z) = u₀ z) ∧
      ∀ p ∈ ball t₀ ε ×ˢ (Set.univ : Set ℂ), Function.Injective (fderiv ℝ (pageMap H U) p) := by
  obtain ⟨⟨hfast₀, hend₀, h0₀, hen₀⟩, hemb₀⟩ := hu₀
  obtain ⟨r₁, hr₁, f, hf, hfinj, hdf, hf0, hslice, -⟩ :=
    exists_fastPlane_family H hH J hJ P hcz u₀ hfast₀ hend₀ hemb₀ (l + 1) (by omega)
  have hf0' : (fun z => f (z, 0)) = u₀ := funext hf0
  have hOo : IsOpen (Set.univ ×ˢ ball (0 : ℂ) r₁ : Set (ℂ × ℂ)) := isOpen_univ.prod isOpen_ball
  have h00 : ((0 : ℂ), (0 : ℂ)) ∈ (Set.univ ×ˢ ball (0 : ℂ) r₁ : Set (ℂ × ℂ)) := ⟨trivial, mem_ball_self hr₁⟩
  have hyc : ContDiff ℝ ∞ y := IsReebTrajectory.contDiff hH hy
  have hfa : y t₀ = f (0, 0) := by rw [hf0]; exact (Set.mem_singleton_iff.1 h0₀).symm
  have hdim : Module.finrank ℝ (ℂ × ℂ) = Module.finrank ℝ (V 1) := by
    rw [Module.finrank_prod, Complex.finrank_real_complex, Module.finrank_fin_fun]
  have hycl : ContDiffOn ℝ (l + 1 : ℕ) y (ball t₀ 1) :=
    (hyc.of_le (by exact_mod_cast le_top)).contDiffOn
  obtain ⟨ε₁, hε₁, c, hc, hc0, hcO⟩ := exists_contDiffOn_lift_of_injective_fderiv hdim
    (n := l + 1) (by omega) hOo hf h00 (hdf _ h00) (t₀ := t₀) one_pos hycl hfa
  set ζ : ℝ → ℂ := fun t => (c t).1 with hζdef
  set τ : ℝ → ℂ := fun t => (c t).2 with hτdef
  have hζ0 : ζ t₀ = 0 := by simp only [hζdef, hc0]
  have hτ0 : τ t₀ = 0 := by simp only [hτdef, hc0]
  have hτO : ∀ t ∈ ball t₀ ε₁, τ t ∈ ball (0 : ℂ) r₁ := fun t ht => (hcO t ht).1.2
  have hcy : ∀ t ∈ ball t₀ ε₁, f (ζ t, τ t) = y t := fun t ht => (hcO t ht).2
  have hζc : ContDiffOn ℝ (l + 1 : ℕ) ζ (ball t₀ ε₁) := contDiff_fst.comp_contDiffOn hc
  have hτc : ContDiffOn ℝ (l + 1 : ℕ) τ (ball t₀ ε₁) := contDiff_snd.comp_contDiffOn hc
  have hle : ((l : ℕ) : WithTop ℕ∞) ≤ ((l + 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast Nat.le_succ l
  have hζl : ContDiffOn ℝ l ζ (ball t₀ ε₁) := hζc.of_le hle
  have hτl : ContDiffOn ℝ l τ (ball t₀ ε₁) := hτc.of_le hle
  -- the energy of discs
  have hsliceFE : ∀ τ' ∈ ball (0 : ℂ) r₁, IsFiniteEnergyCurve H J Set.univ (fun z => f (z, τ')) :=
    fun τ' h => (hslice τ' h).1.1
  have hΦ := contDiffOn_dlambdaEnergy_ball_family H hH J hJ l (ball (0 : ℂ) r₁) isOpen_ball f
    (by exact_mod_cast hf) hsliceFE
  set Φ : ℂ × ℂ × ℝ → ℝ :=
    fun p => (dlambdaEnergy H (ball p.1 p.2.2) (fun z => f (z, p.2.1))).toReal with hΦdef
  set O' : Set (ℝ × ℝ) := ball t₀ ε₁ ×ˢ Set.Ioi 0 with hO'def
  have hO'o : IsOpen O' := isOpen_ball.prod isOpen_Ioi
  have hbase : ((t₀, (1 : ℝ)) : ℝ × ℝ) ∈ O' := ⟨mem_ball_self hε₁, Set.mem_Ioi.2 one_pos⟩
  have hinner : ContDiffOn ℝ l (fun q : ℝ × ℝ => (ζ q.1, τ q.1, q.2)) O' :=
    (hζl.comp contDiffOn_fst fun q hq => hq.1).prodMk
      ((hτl.comp contDiffOn_fst fun q hq => hq.1).prodMk contDiffOn_snd)
  have hmaps : Set.MapsTo (fun q : ℝ × ℝ => (ζ q.1, τ q.1, q.2)) O'
      (Set.univ ×ˢ ball (0 : ℂ) r₁ ×ˢ Set.Ioi 0) :=
    fun q hq => ⟨trivial, hτO q.1 hq.1, hq.2⟩
  have hΦt : ContDiffOn ℝ l (fun q : ℝ × ℝ => Φ (ζ q.1, τ q.1, q.2)) O' := hΦ.comp hinner hmaps
  have hl0 : ((l : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
  have hΦtd : DifferentiableAt ℝ (fun q : ℝ × ℝ => Φ (ζ q.1, τ q.1, q.2)) (t₀, 1) :=
    (hΦt.contDiffAt (hO'o.mem_nhds hbase)).differentiableAt hl0
  set D := fderiv ℝ (fun q : ℝ × ℝ => Φ (ζ q.1, τ q.1, q.2)) (t₀, 1) with hDdef
  -- the radial derivative at the base point is positive
  have hd : HasDerivAt (fun s : ℝ => (dlambdaEnergy H (ball (0 : ℂ) s) u₀).toReal)
      (D ((0 : ℝ), (1 : ℝ))) 1 := by
    have h1 : HasDerivAt (fun s : ℝ => ((t₀, s) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) 1 :=
      (hasDerivAt_const (1 : ℝ) t₀).prodMk (hasDerivAt_id 1)
    have h2 := hΦtd.hasFDerivAt.comp_hasDerivAt (1 : ℝ) h1
    have hfun : ((fun q : ℝ × ℝ => Φ (ζ q.1, τ q.1, q.2)) ∘ fun s : ℝ => ((t₀, s) : ℝ × ℝ)) =
        fun s : ℝ => (dlambdaEnergy H (ball (0 : ℂ) s) u₀).toReal := by
      funext s
      simp only [Function.comp_apply, hΦdef, hζ0, hτ0, hf0']
    rw [hfun] at h2
    exact h2
  have hdpos : 0 < D ((0 : ℝ), (1 : ℝ)) :=
    pos_of_hasDerivAt_dlambdaEnergy_ball H hH J hJ u₀ hfast₀ 0 1 one_pos _ hd
  -- the radius by the curve-lift child applied to `q ↦ (q.1, Φ̃ q - Φ₀)`
  set F : ℝ × ℝ → ℝ × ℝ := fun q => (q.1, Φ (ζ q.1, τ q.1, q.2) - Φ (0, 0, 1)) with hFdef
  have hF : ContDiffOn ℝ l F O' := contDiffOn_fst.prodMk (hΦt.sub contDiffOn_const)
  have hFd : HasFDerivAt F ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod D) (t₀, 1) :=
    hasFDerivAt_fst.prodMk (hΦtd.hasFDerivAt.sub_const _)
  have hFinj : Function.Injective (fderiv ℝ F (t₀, 1)) := by
    rw [hFd.fderiv]
    intro v w h
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hv : v = (v.1, 0) + v.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    have hw : w = (w.1, 0) + w.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    rw [hv, hw, map_add, map_add, map_smul, map_smul, h1] at h2
    have h3 : v.2 * D ((0 : ℝ), (1 : ℝ)) = w.2 * D ((0 : ℝ), (1 : ℝ)) := by
      simpa [smul_eq_mul] using h2
    exact Prod.ext h1 (mul_right_cancel₀ hdpos.ne' h3)
  have hgc : ContDiffOn ℝ l (fun t : ℝ => ((t, (0 : ℝ)) : ℝ × ℝ)) (ball t₀ 1) :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  have hga : (fun t : ℝ => ((t, (0 : ℝ)) : ℝ × ℝ)) t₀ = F (t₀, 1) := by
    simp only [hFdef, hζ0, hτ0, sub_self]
  obtain ⟨ε₂, hε₂, c', hc', hc'0, hc'O⟩ := exists_contDiffOn_lift_of_injective_fderiv
    (E := ℝ × ℝ) (F := ℝ × ℝ) rfl (n := l) hl hO'o hF hbase hFinj (t₀ := t₀) one_pos hgc hga
  set r : ℝ → ℝ := fun t => (c' t).2 with hrdef
  have hc'1 : ∀ t ∈ ball t₀ ε₂, (c' t).1 = t := fun t ht =>
    congrArg Prod.fst (hc'O t ht).2
  have hrpos : ∀ t ∈ ball t₀ ε₂, 0 < r t := fun t ht => (hc'O t ht).1.2
  have hr0 : r t₀ = 1 := by simp only [hrdef, hc'0]
  have hΦeq : ∀ t ∈ ball t₀ ε₂, Φ (ζ t, τ t, r t) = Φ (0, 0, 1) := by
    intro t ht
    have h := congrArg Prod.snd (hc'O t ht).2
    simp only [hFdef] at h
    rw [hc'1 t ht] at h
    exact sub_eq_zero.1 h
  have hrc : ContDiffOn ℝ l r (ball t₀ ε₂) := contDiff_snd.comp_contDiffOn hc'
  -- the family
  set ε := min ε₁ ε₂ with hεdef
  have hball1 : ball t₀ ε ⊆ ball t₀ ε₁ := ball_subset_ball (min_le_left _ _)
  have hball2 : ball t₀ ε ⊆ ball t₀ ε₂ := ball_subset_ball (min_le_right _ _)
  set U : ℝ × ℂ → V 1 := fun p => f (ζ p.1 + r p.1 • p.2, τ p.1) with hUdef
  have htot0 := dlambdaEnergy_univ_eq_of_isNondegenerateEnd H hH J hJ _ hfast₀.1 P hend₀
  have hout0 := dlambdaEnergy_norm_sub_gt_eq_sub H u₀ P.T htot0 0 1
  have hset0 : {x : ℂ | (1 : ℝ) < ‖x - 0‖} = {z : ℂ | 1 < ‖z‖} := by simp
  rw [hset0, hen₀] at hout0
  have hΦ0 : Φ (0, 0, 1) = (dlambdaEnergy H (ball (0 : ℂ) 1) u₀).toReal := by
    simp only [hΦdef, hf0']
  refine ⟨ε, lt_min hε₁ hε₂, U, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- `C^l` on `I × ℂ`
    have h1 : ContDiffOn ℝ l ζ (ball t₀ ε) := hζl.mono hball1
    have h2 : ContDiffOn ℝ l τ (ball t₀ ε) := hτl.mono hball1
    have h3 : ContDiffOn ℝ l r (ball t₀ ε) := hrc.mono hball2
    have hinU : ContDiffOn ℝ l (fun p : ℝ × ℂ => (ζ p.1 + r p.1 • p.2, τ p.1))
        (ball t₀ ε ×ˢ Set.univ) :=
      ((h1.comp contDiffOn_fst fun p hp => hp.1).add
        ((h3.comp contDiffOn_fst fun p hp => hp.1).smul contDiffOn_snd)).prodMk
        (h2.comp contDiffOn_fst fun p hp => hp.1)
    exact (hf.of_le hle).comp hinU (fun p hp => ⟨trivial, hτO p.1 (hball1 hp.1)⟩)
  · -- slices in `Λ({y t}, P)`
    intro t ht
    have ht1 := hball1 ht
    have ht2 := hball2 ht
    obtain ⟨hfa', hea', hema'⟩ := hslice (τ t) (hτO t ht1)
    have hr := hrpos t ht2
    obtain ⟨hF', hE', hEm'⟩ :=
      isFastPlane_comp_add_smul H hH J hJ P _ hfa' hea' hema' (ζ t) (r t) hr
    refine ⟨⟨hF', hE', ?_, ?_⟩, hEm'⟩
    · show f (ζ t + r t • (0 : ℂ), τ t) ∈ ({y t} : Set (V 1))
      rw [smul_zero, add_zero, hcy t ht1]
      exact Set.mem_singleton _
    · have hresc := ((rescale_isFiniteEnergyCurve H hH J hJ Set.univ isOpen_univ _ hfa'.1 (ζ t)
        (r t) hr 1 one_pos).2.2.2 {x | r t < ‖x - ζ t‖} (Set.subset_univ _)
        (measurableSet_lt measurable_const (by fun_prop))).2
      have hset : {w : ℂ | ζ t + r t • w ∈ {x : ℂ | r t < ‖x - ζ t‖}} = {z : ℂ | 1 < ‖z‖} := by
        ext w
        simp only [Set.mem_setOf_eq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hr]
        constructor
        · intro h; nlinarith
        · intro h; nlinarith
      have hfun : (fun w => (1 : ℝ) • (fun z => f (z, τ t)) (ζ t + r t • w)) =
          fun z => U (t, z) := by
        funext w; simp only [one_smul, hUdef]
      rw [hset, hfun] at hresc
      rw [hresc]
      have htot := dlambdaEnergy_univ_eq_of_isNondegenerateEnd H hH J hJ _ hfa'.1 P hea'
      rw [dlambdaEnergy_norm_sub_gt_eq_sub H _ P.T htot, hout0]
      congr 1
      refine (ENNReal.toReal_eq_toReal_iff' (dlambdaEnergy_ne_top_of_univ_eq_ofReal H _ P.T htot _)
        (dlambdaEnergy_ne_top_of_univ_eq_ofReal H _ P.T htot0 _)).1 ?_
      rw [← hΦ0]
      exact hΦeq t ht2
  · -- the slice at `t₀`
    intro z
    show f (ζ t₀ + r t₀ • z, τ t₀) = u₀ z
    rw [hζ0, hτ0, hr0, one_smul, zero_add, hf0]
  · -- injective derivative
    rintro ⟨t, w⟩ ⟨ht, -⟩
    have ht2 := hball2 ht
    have hζd : DifferentiableOn ℝ ζ (ball t₀ ε) := (hζl.differentiableOn hl0).mono hball1
    have hτd : DifferentiableOn ℝ τ (ball t₀ ε) := (hτl.differentiableOn hl0).mono hball1
    have hrd : DifferentiableOn ℝ r (ball t₀ ε) := (hrc.differentiableOn hl0).mono hball2
    have hK := injective_fderiv_proj_of_fastPlane_family H hH J hJ P hcz y hy r₁ f
      (hf.of_le (by exact_mod_cast (by omega : 1 ≤ l + 1))) hfinj hdf hslice (ball t₀ ε)
      isOpen_ball ζ τ hζd hτd (fun t ht => hτO t (hball1 ht)) (fun t ht => hcy t (hball1 ht))
      t ht (ζ t + r t • w)
    set Ψ : ℝ × ℂ → V 1 := fun p => proj H (f (p.2, τ p.1)) with hΨdef
    set ψ : ℝ × ℂ → ℝ × ℂ := fun p => (p.1, ζ p.1 + r p.1 • p.2) with hψdef
    have hK' : Function.Injective (fderiv ℝ Ψ (ψ (t, w))) := hK
    have hcomp : pageMap H U = Ψ ∘ ψ := rfl
    have hΨd : DifferentiableAt ℝ Ψ (ψ (t, w)) := by
      by_contra hnd
      rw [fderiv_zero_of_not_differentiableAt hnd] at hK'
      have := hK' (a₁ := ((1 : ℝ), (0 : ℂ))) (a₂ := 0) (by simp)
      simp at this
    have htn : ball t₀ ε ∈ 𝓝 t := isOpen_ball.mem_nhds ht
    have hfst : HasFDerivAt (Prod.fst : ℝ × ℂ → ℝ) (ContinuousLinearMap.fst ℝ ℝ ℂ) (t, w) :=
      hasFDerivAt_fst
    have hsnd : HasFDerivAt (Prod.snd : ℝ × ℂ → ℂ) (ContinuousLinearMap.snd ℝ ℝ ℂ) (t, w) :=
      hasFDerivAt_snd
    have hζ' := HasFDerivAt.comp (f := (Prod.fst : ℝ × ℂ → ℝ)) (t, w)
      (hζd.differentiableAt htn).hasFDerivAt hfst
    have hr' := HasFDerivAt.comp (f := (Prod.fst : ℝ × ℂ → ℝ)) (t, w)
      (hrd.differentiableAt htn).hasFDerivAt hfst
    have hψ0 := hfst.prodMk (hζ'.add (hr'.smul hsnd))
    have hψ' : HasFDerivAt ψ _ (t, w) := hψ0
    have hinjψ : Function.Injective (fderiv ℝ ψ (t, w)) := by
      rw [hψ'.fderiv]
      refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
      simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply, Prod.mk_eq_zero] at hv
      obtain ⟨h1, h2⟩ := hv
      rw [h1] at h2
      simp only [map_zero, zero_smul, zero_add, add_zero, smul_eq_zero] at h2
      rcases h2 with h2 | h2
      · exact absurd h2 (hrpos t ht2).ne'
      · exact Prod.ext h1 h2
    rw [hcomp, fderiv_comp (t, w) hΨd hψ'.differentiableAt, ContinuousLinearMap.coe_comp']
    exact hK'.comp hinjψ

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (t₀ : ℝ) (u₀ : ℂ → V 1) (hu₀ : u₀ ∈ embeddedFastPlaneSet H J P {y t₀} γ)
    (l : ℕ) (hl : 1 ≤ l) :
    ∃ ε > 0, ∃ U : ℝ × ℂ → V 1, IsPageFamilyOn H J P γ y l (ball t₀ ε) U ∧
      (∀ z, U (t₀, z) = u₀ z) ∧
      ∀ p ∈ ball t₀ ε ×ˢ (Set.univ : Set ℂ), Function.Injective (fderiv ℝ (pageMap H U) p) :=
  FiniteEnergyPlane.exists_pageFamily_injective_fderiv_aux H hH J hJ P hcz γ y hy t₀ u₀ hu₀ l hl
