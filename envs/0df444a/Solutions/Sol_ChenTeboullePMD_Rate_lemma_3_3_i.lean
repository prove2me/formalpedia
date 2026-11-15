-- Prove2me | solution 1 for ChenTeboullePMD.Rate.lemma_3_3_i
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-14T12:32:23.764207+00:00
-- url     : https://prove2.me/submissions/1fd8164a-844c-445a-9488-641ea7ea7402

import Definitions.Def_ChenTeboullePMD_Rate_Setting
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Filter Topology BeckTeboulleMD.EMDA ChenTeboullePMD.Rate

private lemma distance_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (ψ : E → ℝ) (hψ : IsBregmanFunction S ψ)
    (y z : E) (hy : y ∈ closure S) (hz : z ∈ S) : 0 ≤ bregman ψ y z := by
  let d := y-z
  let a : ℝ → E := fun t => z+t • d
  have hdiff : DifferentiableAt ℝ ψ z :=
    (hψ.contDiffOn.differentiableOn (by norm_num) z hz).differentiableAt (hψ.isOpen.mem_nhds hz)
  have hp : HasDerivAt a d 0 := by
    simpa [a] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add z
  have hd : HasDerivAt (fun t => ψ (a t)) (fderiv ℝ ψ z d) 0 := by
    apply hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hp
    simp [a]
  have ht : Tendsto (fun t : ℝ => (ψ (a t)-ψ z)/t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (fderiv ℝ ψ z d)) := by
    simpa [a, smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right
  have he : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), (ψ (a t)-ψ z)/t ≤ ψ y-ψ z := by
    have hs : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), t < 1 :=
      (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hs] with t ht0 ht1
    have hp : 0 < t := ht0
    have hc := hψ.strictConvexOn.convexOn.2 (subset_closure hz) hy
      (by linarith : 0 ≤ 1-t) hp.le (by ring : 1-t+t=1)
    have ha : (1-t) • z+t • y = a t := by
      dsimp [a,d]; module
    rw [ha] at hc
    simp only [smul_eq_mul] at hc
    apply (div_le_iff₀ hp).mpr
    nlinarith
  have hl := le_of_tendsto ht he
  dsimp [d] at hl
  unfold bregman
  linarith

private lemma run_zone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S C : Set E) (ψ f : E → ℝ) (lam : ℕ → ℝ) (x : ℕ → E)
    (hrun : IsPMDRun S C ψ f lam x) (k : ℕ) : x k ∈ S := by
  cases k with
  | zero => exact hrun.1
  | succ k => exact (hrun.2 k).1

private lemma value_decrease {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (ψ : E → ℝ) (hψ : IsBregmanFunction S ψ)
    (C : Set E) (f : E → ℝ) (lam : ℕ → ℝ)
    (hlam : ∀ k, 1 ≤ k → 0 < lam k) (x : ℕ → E)
    (hrun : IsPMDRun S C ψ f lam x) (k : ℕ) (hx : x k ∈ C) :
    (lam (k+1))⁻¹ * bregman ψ (x (k+1)) (x k) ≤ f (x k)-f (x (k+1)) := by
  have hm := (hrun.2 k).2.2 (x k) hx (subset_closure (run_zone S C ψ f lam x hrun k))
  have hself : bregman ψ (x k) (x k) = 0 := by simp [bregman]
  rw [hself, mul_zero, add_zero] at hm
  linarith

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (S : Set E) (ψ : E → ℝ) (hψ : IsBregmanFunction S ψ)
    (C : Set E) (hCne : C.Nonempty) (hCconv : Convex ℝ C)
    (f : E → ℝ) (hf : ConvexOn ℝ C f)
    (hlsc : LowerSemicontinuous (extendTop C f))
    (hri : intrinsicInterior ℝ C ⊆ S)
    (lam : ℕ → ℝ) (hlam : ∀ k, 1 ≤ k → 0 < lam k)
    (x : ℕ → E) (hrun : IsPMDRun S C ψ f lam x) :
    ∀ k : ℕ, x k ∈ C → f (x (k + 1)) ≤ f (x k) := by
  intro k hx
  have hd := value_decrease S ψ hψ C f lam hlam x hrun k hx
  have hn := distance_nonneg S ψ hψ (x (k+1)) (x k)
    (subset_closure (hrun.2 k).1) (run_zone S C ψ f lam x hrun k)
  have hl := hlam (k+1) (Nat.succ_le_succ (Nat.zero_le k))
  have hp := mul_nonneg (inv_nonneg.mpr hl.le) hn
  linarith

#print axioms solution


