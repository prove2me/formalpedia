-- Prove2me | solution 1 for ContinuityEqWiki.charge_continuity_of_maxwell
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:19:46.082234+00:00
-- url     : https://prove2.me/submissions/dbb4b153-d91e-4e04-9998-83938f84ea8a

import Mathlib
import Definitions.Def_ContinuityEqWiki_Defs

open ContinuityEqWiki

namespace LUHelpMx

theorem timeDeriv_eq (Φ : ℝ × Space → ℝ) (t : ℝ) (x : Space)
    (h : DifferentiableAt ℝ Φ (t, x)) :
    deriv (fun s => Φ (s, x)) t = fderiv ℝ Φ (t, x) ((1 : ℝ), (0 : Space)) := by
  have h1 : HasDerivAt (Φ ∘ fun s => (s, x)) (fderiv ℝ Φ (t, x) ((1 : ℝ), (0 : Space))) t :=
    h.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  exact h1.deriv

theorem spaceDeriv_eq (Φ : ℝ × Space → ℝ) (t : ℝ) (x : Space)
    (h : DifferentiableAt ℝ Φ (t, x)) (w : Space) :
    fderiv ℝ (fun y => Φ (t, y)) x w = fderiv ℝ Φ (t, x) ((0 : ℝ), w) := by
  have h3 : HasFDerivAt (fun y : Space => ((t, y) : ℝ × Space))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have h4 := h.hasFDerivAt.comp x h3
  rw [show (fun y => Φ (t, y)) = Φ ∘ (fun y : Space => ((t, y) : ℝ × Space)) from rfl, h4.fderiv]
  simp

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem diff_fderiv (f : V → ℝ) (hf : ContDiff ℝ 2 f) : Differentiable ℝ (fderiv ℝ f) :=
  (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero

theorem diff_dir (f : V → ℝ) (hf : ContDiff ℝ 2 f) (b : V) :
    Differentiable ℝ (fun y => fderiv ℝ f y b) := fun y =>
  (diff_fderiv f hf y).clm_apply (differentiableAt_const b)

theorem pd2 (f : V → ℝ) (hf : ContDiff ℝ 2 f) (x a b : V) :
    fderiv ℝ (fun y => fderiv ℝ f y b) x a = fderiv ℝ (fderiv ℝ f) x a b := by
  rw [fderiv_clm_apply (diff_fderiv f hf x) (differentiableAt_const b)]
  simp

theorem sym (f : V → ℝ) (hf : ContDiff ℝ 2 f) (x a b : V) :
    fderiv ℝ (fderiv ℝ f) x a b = fderiv ℝ (fderiv ℝ f) x b a :=
  (hf.contDiffAt.isSymmSndFDerivAt (by simp)) a b

theorem mixed (f : Space → ℝ) (hf : ContDiff ℝ 2 f) (x : Space) (a b : Fin 3) :
    partialDeriv a (fun y => partialDeriv b f y) x =
      partialDeriv b (fun y => partialDeriv a f y) x := by
  unfold partialDeriv
  rw [pd2 f hf, pd2 f hf, sym f hf]

theorem pd_sub (f g : Space → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (a : Fin 3) (x : Space) :
    partialDeriv a (fun y => f y - g y) x = partialDeriv a f x - partialDeriv a g x := by
  unfold partialDeriv
  rw [fderiv_fun_sub (hf x) (hg x)]
  rfl

theorem diff_pd (f : Space → ℝ) (hf : ContDiff ℝ 2 f) (b : Fin 3) :
    Differentiable ℝ (fun y => partialDeriv b f y) :=
  diff_dir f hf _

end LUHelpMx

open LUHelpMx in
theorem solution (H D J : ℝ → Space → Space) (ρ : ℝ → Space → ℝ)
    (hH : ∀ t, ContDiff ℝ 2 (H t)) (hD : ContDiff ℝ 2 (Function.uncurry D))
    (ampere : ∀ t x, curl (H t) x = J t x + timeDeriv D t x)
    (gauss : ∀ t x, div (D t) x = ρ t x) :
    ∀ t x, div (J t) x + timeDeriv ρ t x = 0 := by
  intro t x
  -- components
  set Φ : Fin 3 → ℝ × Space → ℝ := fun i q => Function.uncurry D q i with hΦ
  have hΦc : ∀ i, ContDiff ℝ 2 (Φ i) := fun i => contDiff_pi.1 hD i
  have hΦd : ∀ i, Differentiable ℝ (Φ i) := fun i => (hΦc i).differentiable (by norm_num)
  have hDd : Differentiable ℝ (Function.uncurry D) := hD.differentiable (by norm_num)
  -- time derivative of D, componentwise
  have hTD : ∀ s y i, timeDeriv D s y i = fderiv ℝ (Φ i) (s, y) ((1 : ℝ), (0 : Space)) := by
    intro s y i
    have h1 : HasDerivAt (Function.uncurry D ∘ fun r => (r, y)) (fderiv ℝ (Function.uncurry D) (s, y) ((1 : ℝ), (0 : Space))) s :=
      (hDd _).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))
    have h2 : HasFDerivAt ((fun v : Space => v i) ∘ Function.uncurry D)
        ((ContinuousLinearMap.proj i).comp (fderiv ℝ (Function.uncurry D) (s, y))) (s, y) :=
      (hasFDerivAt_apply i _).comp (s, y) (hDd _).hasFDerivAt
    unfold timeDeriv
    rw [show (fun r => D r y) = Function.uncurry D ∘ fun r => (r, y) from rfl, h1.deriv,
      show Φ i = (fun v : Space => v i) ∘ Function.uncurry D from rfl, h2.fderiv]
    rfl
  -- spatial partial of D components
  have hSD : ∀ s i, partialDeriv i (fun y => D s y i) x =
      fderiv ℝ (Φ i) (s, x) ((0 : ℝ), (Pi.single i 1 : Space)) := by
    intro s i
    unfold partialDeriv
    exact spaceDeriv_eq (Φ i) s x (hΦd i _) _
  -- the key commutation
  have hcomm : ∀ i, partialDeriv i (fun y => timeDeriv D t y i) x =
      deriv (fun s => partialDeriv i (fun y => D s y i) x) t := by
    intro i
    simp_rw [hTD, hSD]
    unfold partialDeriv
    rw [spaceDeriv_eq (fun q => fderiv ℝ (Φ i) q ((1 : ℝ), (0 : Space))) t x
      (diff_dir _ (hΦc i) _ _), pd2 _ (hΦc i), sym _ (hΦc i), ← pd2 _ (hΦc i),
      ← timeDeriv_eq (fun q => fderiv ℝ (Φ i) q ((0 : ℝ), (Pi.single i 1 : Space))) t x
      (diff_dir _ (hΦc i) _ _)]
  -- time derivative of ρ
  have hρ : timeDeriv ρ t x = ∑ i, deriv (fun s => partialDeriv i (fun y => D s y i) x) t := by
    unfold timeDeriv
    have : (fun s => ρ s x) = fun s => ∑ i, partialDeriv i (fun y => D s y i) x := by
      funext s; rw [← gauss]; rfl
    rw [this]
    apply deriv_fun_sum
    intro i _
    simp_rw [hSD]
    have hd := diff_dir _ (hΦc i) ((0 : ℝ), (Pi.single i 1 : Space))
    exact (hd _).comp t ((differentiableAt_id).prodMk (differentiableAt_const x))
  -- differentiability of time-derivative components in space
  have hTDd : ∀ i, Differentiable ℝ (fun y => timeDeriv D t y i) := by
    intro i
    simp_rw [hTD]
    intro y
    exact (diff_dir _ (hΦc i) _ _).comp y ((differentiableAt_const t).prodMk differentiableAt_id)
  have hHc : ∀ k, ContDiff ℝ 2 (fun y => H t y k) := fun k => contDiff_pi.1 (hH t) k
  have hcurld : ∀ i, Differentiable ℝ (fun y => curl (H t) y i) := by
    intro i
    fin_cases i
    · exact (diff_pd _ (hHc 2) 1).sub (diff_pd _ (hHc 1) 2)
    · exact (diff_pd _ (hHc 0) 2).sub (diff_pd _ (hHc 2) 0)
    · exact (diff_pd _ (hHc 1) 0).sub (diff_pd _ (hHc 0) 1)
  have hJ : ∀ i, (fun y => J t y i) = fun y => curl (H t) y i - timeDeriv D t y i := by
    intro i; funext y; rw [ampere]; simp
  have hdivJ : div (J t) x = ∑ i, (partialDeriv i (fun y => curl (H t) y i) x -
      partialDeriv i (fun y => timeDeriv D t y i) x) := by
    unfold div
    apply Finset.sum_congr rfl
    intro i _
    rw [hJ i, pd_sub _ _ (hcurld i) (hTDd i)]
  have hdivcurl : ∑ i, partialDeriv i (fun y => curl (H t) y i) x = 0 := by
    rw [Fin.sum_univ_three]
    have e0 : (fun y => curl (H t) y 0) = fun y =>
        partialDeriv 1 (fun z => H t z 2) y - partialDeriv 2 (fun z => H t z 1) y := rfl
    have e1 : (fun y => curl (H t) y 1) = fun y =>
        partialDeriv 2 (fun z => H t z 0) y - partialDeriv 0 (fun z => H t z 2) y := rfl
    have e2 : (fun y => curl (H t) y 2) = fun y =>
        partialDeriv 0 (fun z => H t z 1) y - partialDeriv 1 (fun z => H t z 0) y := rfl
    rw [e0, e1, e2, pd_sub _ _ (diff_pd _ (hHc 2) 1) (diff_pd _ (hHc 1) 2),
      pd_sub _ _ (diff_pd _ (hHc 0) 2) (diff_pd _ (hHc 2) 0),
      pd_sub _ _ (diff_pd _ (hHc 1) 0) (diff_pd _ (hHc 0) 1),
      mixed _ (hHc 2) x 0 1, mixed _ (hHc 1) x 0 2, mixed _ (hHc 0) x 1 2]
    ring
  rw [hdivJ, Finset.sum_sub_distrib, hdivcurl, hρ]
  simp_rw [hcomm]
  ring
