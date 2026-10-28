-- Prove2me | solution 1 for ChanceStateCtrl.AlmostSure.theorem_3_10
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:25:58.70618+00:00
-- url     : https://prove2.me/submissions/9561ec3f-c805-4827-b839-61520bea0bc5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ChanceStateCtrl_AlmostSure_Setting
import Theorems.Thm_ChanceStateCtrl_AlmostSure_lemma_3_6
import Theorems.Thm_ChanceStateCtrl_AlmostSure_lemma_3_7
import Theorems.Thm_ChanceStateCtrl_AlmostSure_theorem_3_9
import Theorems.Thm_ChanceStateCtrl_AlmostSure_splitting_3_10
import Theorems.Thm_ChanceStateCtrl_AlmostSure_eq_57
import Theorems.Thm_ChanceStateCtrl_AlmostSure_eq_59

open MeasureTheory

namespace ChanceStateCtrl.AlmostSure.Thm310Aux

variable {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace (closure D)]
  {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

theorem Bconst_ae (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ))
    (h : ChanceStateCtrl.PDE.L2 D) :
    ∀ᵐ ω ∂P, (Ainv.compLp (Bconst P h) : Linf D P) ω = Ainv h := by
  filter_upwards [Ainv.coeFn_compLp (Bconst P h), Lp.coeFn_const (p := ⊤) (μ := P) h]
    with ω h1 h2
  rw [h1]
  simp only [Bconst] at *
  rw [h2]; rfl

theorem Ssol_ae (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ))
    (ftil : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P) (u : ChanceStateCtrl.PDE.L2 D) :
    ∀ᵐ ω ∂P, Ssol P Ainv ftil u ω = Ainv (u + ftil ω) := by
  filter_upwards [Ainv.coeFn_compLp (Bconst P u + ftil), Lp.coeFn_add (Bconst P u) ftil,
    Lp.coeFn_const (p := ⊤) (μ := P) u] with ω h1 h2 h3
  simp only [Ssol]
  rw [h1, h2]
  simp only [Pi.add_apply, Bconst]
  rw [h3]; rfl

theorem constLinf_ae (c : C(closure D, ℝ)) :
    ∀ᵐ ω ∂P, (constLinf P c : Linf D P) ω = c := by
  filter_upwards [Lp.coeFn_const (p := ⊤) (μ := P) c] with ω h
  simp only [constLinf]; rw [h]; rfl

theorem Gop_ae (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ))
    (ftil : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P) (α : ℝ) (u : ChanceStateCtrl.PDE.L2 D) :
    ∀ᵐ ω ∂P, Gop P Ainv ftil α u ω =
      Ainv (u + ftil ω) - ContinuousMap.const (closure D) α := by
  filter_upwards [Lp.coeFn_sub (Ssol P Ainv ftil u) (constLinf P (ContinuousMap.const (closure D) α)),
    Ssol_ae P Ainv ftil u, constLinf_ae P (ContinuousMap.const (closure D) α)] with ω h1 h2 h3
  simp only [Gop]
  rw [h1, Pi.sub_apply, h2, h3]

/-- Gradient inequality for a convex differentiable function. -/
theorem convex_grad_ineq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ)
    (hFconv : ConvexOn ℝ Set.univ F) (hFd : Differentiable ℝ F) (x y : E) :
    F x + fderiv ℝ F x (y - x) ≤ F y := by
  set h := y - x
  let g : ℝ → ℝ := fun t => F (x + t • h)
  have hg : ConvexOn ℝ Set.univ g := by
    refine ⟨convex_univ, fun s _ t _ a b ha hb hab => ?_⟩
    have := hFconv.2 (Set.mem_univ (x + s • h)) (Set.mem_univ (x + t • h)) ha hb hab
    obtain rfl : b = 1 - a := by linarith
    simp only [g, smul_eq_mul]
    rw [smul_eq_mul, smul_eq_mul] at this
    convert this using 2
    module
  have hd : HasDerivAt g (fderiv ℝ F x h) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • h) h 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add x
    have h2 : HasFDerivAt F (fderiv ℝ F x) (x + (0 : ℝ) • h) := by
      simpa using (hFd x).hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have := hg.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  simp only [slope_def_field, g] at this
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one, h] at this
  have hxy : x + (y - x) = y := by abel
  rw [hxy] at this
  simp only [h]
  linarith

end ChanceStateCtrl.AlmostSure.Thm310Aux

open ChanceStateCtrl.AlmostSure ChanceStateCtrl.AlmostSure.Thm310Aux

theorem solution {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))}
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (hS : ChanceStateCtrl.PDE.IsClassS D) [CompactSpace (closure D)]
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ)) (hA : IsSolutionOperator D Ainv)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ftil : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P) (α : ℝ) (F : ChanceStateCtrl.PDE.L2 D → ℝ)
    (hFconv : ConvexOn ℝ Set.univ F) (hFdiff : ContDiff ℝ 1 F)
    (hCQ : CQ P Ainv ftil α) (us : ChanceStateCtrl.PDE.L2 D) :
    ChanceStateCtrl.General.IsSolution (feasible P Ainv ftil α) F us ↔
      ∃ lam ∈ Lambda1 C(closure D, ℝ) P, ∃ lamSing : StrongDual ℝ (Linf D P),
        IsSingular P lamSing ∧ ∃ ystar : Linf D P,
          -- (56a)
          (∀ h : ChanceStateCtrl.PDE.L2 D, fderiv ℝ F us h + ∫ ω, lam ω (Ainv h) ∂P
              + lamSing (Ainv.compLp (Bconst P h)) = 0) ∧
          -- (56b)
          (∀ᵐ ω ∂P, ∃ y, ChanceStateCtrl.PDE.IsDirichletSol D (⇑(us + ftil ω)) y ∧ ∀ x : closure D, ystar ω x = y x) ∧
          -- (56c)
          (∀ᵐ ω ∂P, (∀ x : closure D, ystar ω x ≤ α) ∧
              (∀ φ : C(closure D, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ lam ω φ) ∧
              lam ω (ystar ω - ContinuousMap.const (closure D) α) = 0) ∧
          -- (56d)
          lamSing ∈ Kpolar D P ∧
          lamSing (ystar - constLinf P (ContinuousMap.const (closure D) α)) = 0 := by
  constructor
  · intro hsol
    obtain ⟨lamStar, h53a, hfeas, hpol, hcompl⟩ :=
      (lemma_3_7 hDopen hDbdd hd hS Ainv hA P ftil α F hFconv hFdiff hCQ us).1 hsol
    obtain ⟨⟨va, vs, hva, hvs, hsplit, -⟩, -⟩ := theorem_3_9 P (X := C(closure D, ℝ)) lamStar
    obtain ⟨lam, hlam, hrep⟩ := hva
    have h57 := eq_57 P lamStar va vs lam hlam hrep hvs hsplit hpol
    obtain ⟨hnn, ⟨h59s, -, -⟩, hpt⟩ :=
      eq_59 Ainv P ftil α us lamStar va vs lam hlam hrep hvs hsplit h57 hfeas hcompl
    have hspl := splitting_3_10 Ainv P lamStar va vs lam hlam hrep hvs hsplit
    have hGy : ∀ᵐ ω ∂P, Gop P Ainv ftil α us ω =
        Ssol P Ainv ftil us ω - ContinuousMap.const (closure D) α := by
      filter_upwards [Gop_ae P Ainv ftil α us, Ssol_ae P Ainv ftil us] with ω h1 h2
      rw [h1, h2]
    refine ⟨lam, hlam, vs, hvs, Ssol P Ainv ftil us, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      have e1 := hspl h
      have e2 := h53a h
      linarith
    · filter_upwards [Ssol_ae P Ainv ftil us] with ω h1
      obtain ⟨y, hy1, hy2⟩ := hA (us + ftil ω)
      exact ⟨y, hy1, fun x => by rw [h1, hy2]⟩
    · filter_upwards [hGy, hfeas, hnn, hpt] with ω h1 h2 h3 h4
      refine ⟨fun x => ?_, h3, ?_⟩
      · have := h2 x
        rw [h1] at this
        simp at this
        linarith
      · rw [← h1]; exact h4
    · intro y hy; exact (h57 y hy).1
    · exact h59s
  · rintro ⟨lam, hlam, lamSing, hsing, ystar, h56a, h56b, h56c, h56d, h56e⟩
    have huniq := (lemma_3_6 hDopen hDbdd hd hS P).1 us ftil
    have hy : ∀ᵐ ω ∂P, ystar ω = Ainv (us + ftil ω) := by
      filter_upwards [huniq, h56b] with ω ⟨y, _, hy⟩ ⟨y1, hy1, hy1'⟩
      obtain ⟨y2, hy2, hy2'⟩ := hA (us + ftil ω)
      ext x
      rw [hy1', hy2', hy y1 hy1 x x.2, hy y2 hy2 x x.2]
    have hSs : Ssol P Ainv ftil us = ystar := by
      apply Lp.ext
      filter_upwards [Ssol_ae P Ainv ftil us, hy] with ω h1 h2
      rw [h1, h2]
    have hGus : Gop P Ainv ftil α us = ystar - constLinf P (ContinuousMap.const (closure D) α) := by
      simp only [Gop, hSs]
    have hfeas : us ∈ feasible P Ainv ftil α := by
      show Gop P Ainv ftil α us ∈ Kcone D P
      filter_upwards [Gop_ae P Ainv ftil α us, hy, h56c] with ω h1 h2 h3 x
      rw [h1, ← h2]
      simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply]
      linarith [h3.1 x]
    refine ⟨hfeas, fun u hu => ?_⟩
    have hu' : Gop P Ainv ftil α u ∈ Kcone D P := hu
    set h := u - us with hh
    have hdiff : Ainv.compLp (Bconst P h) = Gop P Ainv ftil α u - Gop P Ainv ftil α us := by
      apply Lp.ext
      filter_upwards [Bconst_ae P Ainv h, Lp.coeFn_sub (Gop P Ainv ftil α u) (Gop P Ainv ftil α us),
        Gop_ae P Ainv ftil α u, Gop_ae P Ainv ftil α us] with ω h1 h2 h3 h4
      rw [h1, h2, Pi.sub_apply, h3, h4, hh, map_sub, map_add, map_add]
      abel
    have k1 : lamSing (Ainv.compLp (Bconst P h)) ≤ 0 := by
      rw [hdiff, map_sub, hGus, h56e, sub_zero]
      exact h56d _ hu'
    have k2 : ∫ ω, lam ω (Ainv h) ∂P ≤ 0 := by
      apply integral_nonpos_of_ae
      filter_upwards [Gop_ae P Ainv ftil α u, hy, h56c, hu'] with ω h1 h2 h3 h4
      have e : Ainv h = Gop P Ainv ftil α u ω - (ystar ω - ContinuousMap.const (closure D) α) := by
        rw [h1, h2, hh, map_sub, map_add, map_add]; abel
      have hn : 0 ≤ lam ω (-(Gop P Ainv ftil α u ω)) := h3.2.1 _ (fun x => by
        simp only [ContinuousMap.neg_apply]; linarith [h4 x])
      show lam ω (Ainv h) ≤ 0
      rw [e, map_sub, h3.2.2, sub_zero]
      rw [map_neg] at hn
      linarith
    have hg := convex_grad_ineq F hFconv (hFdiff.differentiable (by norm_num)) us u
    have := h56a h
    linarith
