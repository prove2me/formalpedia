-- Prove2me | solution 1 for GaussMagnetism.faraday_preserves_divg_B_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:49:32.597774+00:00
-- url     : https://prove2.me/submissions/233044dd-a58a-4cab-99ac-af3b347de00a

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic
import Definitions.Def_TongEM_wave_ops
set_option autoImplicit false
open Larmor TongEM

private theorem pd_diff (f : Vec → ℝ) (hf : ContDiff ℝ 2 f) (i : Fin 3) :
    Differentiable ℝ (pd i f) := by
  exact ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero).clm_apply (differentiable_const _)

private theorem pd_sub (f g : Vec → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin 3) (x : Vec) :
    pd i (fun y => f y - g y) x = pd i f x - pd i g x := by
  unfold pd
  rw [fderiv_fun_sub (hf x) (hg x)]
  rfl

private theorem pd_comm (f : Vec → ℝ) (hf : ContDiff ℝ 2 f)
    (i j : Fin 3) (x : Vec) : pd i (pd j f) x = pd j (pd i f) x := by
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  unfold pd
  rw [fderiv_clm_apply (hd x) (differentiableAt_const _), fderiv_clm_apply (hd x) (differentiableAt_const _)]
  simpa using hf.contDiffAt.isSymmSndFDerivAt (by simp) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)


private theorem partial_eq (F : Vec → Vec) (hF : Differentiable ℝ F) (i j : Fin 3) (x : Vec) :
    Larmor.partialDeriv F i j x = pd i (fun y => F y j) x := by
  have hh := (EuclideanSpace.proj j).hasFDerivAt.comp x (hF x).hasFDerivAt
  change HasFDerivAt (fun y => F y j) _ x at hh
  unfold Larmor.partialDeriv pd
  rw [hh.fderiv]
  rfl

private theorem curl_pd (F : Vec → Vec) (hF : Differentiable ℝ F) :
    curl F = fun x => !₂[pd 1 (fun y => F y 2) x - pd 2 (fun y => F y 1) x,
      pd 2 (fun y => F y 0) x - pd 0 (fun y => F y 2) x,
      pd 0 (fun y => F y 1) x - pd 1 (fun y => F y 0) x] := by
  funext x
  ext i
  fin_cases i <;> simp [curl, partial_eq F hF]

private theorem curl_diff (F : Vec → Vec) (hF : ContDiff ℝ 2 F) :
    Differentiable ℝ (curl F) := by
  have hc (i : Fin 3) : ContDiff ℝ 2 (fun y => F y i) := (contDiff_piLp 2).mp hF i
  rw [curl_pd F (hF.differentiable (by norm_num))]
  apply (differentiable_piLp 2).mpr
  intro i
  fin_cases i
  · exact (pd_diff _ (hc 2) 1).sub (pd_diff _ (hc 1) 2)
  · exact (pd_diff _ (hc 0) 2).sub (pd_diff _ (hc 2) 0)
  · exact (pd_diff _ (hc 1) 0).sub (pd_diff _ (hc 0) 1)

private theorem divcurl (A : Vec → Vec) (hA : ContDiff ℝ 2 A) (x : Vec) :
    divg (curl A) x = 0 := by
  have hc (i : Fin 3) : ContDiff ℝ 2 (fun y => A y i) := (contDiff_piLp 2).mp hA i
  unfold divg
  simp_rw [partial_eq _ (curl_diff A hA)]
  rw [curl_pd A (hA.differentiable (by norm_num))]
  change pd 0 (fun y => pd 1 (fun z => A z 2) y - pd 2 (fun z => A z 1) y) x +
    (pd 1 (fun y => pd 2 (fun z => A z 0) y - pd 0 (fun z => A z 2) y) x +
    (pd 2 (fun y => pd 0 (fun z => A z 1) y - pd 1 (fun z => A z 0) y) x + 0)) = 0
  rw [pd_sub _ _ (pd_diff _ (hc 2) 1) (pd_diff _ (hc 1) 2),
    pd_sub _ _ (pd_diff _ (hc 0) 2) (pd_diff _ (hc 2) 0),
    pd_sub _ _ (pd_diff _ (hc 1) 0) (pd_diff _ (hc 0) 1)]
  rw [pd_comm _ (hc 2) 0 1, pd_comm _ (hc 1) 0 2, pd_comm _ (hc 0) 1 2]
  ring

private theorem space_slice (f : (ℝ × Vec) → ℝ) (hf : Differentiable ℝ f)
    (t : ℝ) (x : Vec) (i : Fin 3) :
    pd i (fun y => f (t,y)) x = fderiv ℝ f (t,x) (0, EuclideanSpace.single i 1) := by
  have hh := (hf (t,x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  unfold pd
  change HasFDerivAt (fun y => f (t,y)) _ x at hh
  rw [hh.fderiv]
  rfl

private theorem time_slice {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : (ℝ × Vec) → V) (hf : Differentiable ℝ f) (t : ℝ) (x : Vec) :
    deriv (fun s => f (s,x)) t = fderiv ℝ f (t,x) (1,0) := by
  have hh := (hf (t,x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  exact hh.deriv

private theorem dir_diff (f : (ℝ × Vec) → ℝ) (hf : ContDiff ℝ 2 f) (v : ℝ × Vec) :
    Differentiable ℝ (fun p => fderiv ℝ f p v) :=
  ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero).clm_apply (differentiable_const _)

private theorem mixed (f : (ℝ × Vec) → ℝ) (hf : ContDiff ℝ 2 f)
    (t : ℝ) (x : Vec) (i : Fin 3) :
    deriv (fun s => pd i (fun y => f (s,y)) x) t =
      pd i (fun y => deriv (fun s => f (s,y)) t) x := by
  have hd := hf.differentiable (by norm_num)
  have hs : (fun s => pd i (fun y => f (s,y)) x) =
      fun s => fderiv ℝ f (s,x) (0, EuclideanSpace.single i 1) := funext fun s => space_slice f hd s x i
  have ht : (fun y => deriv (fun s => f (s,y)) t) =
      fun y => fderiv ℝ f (t,y) (1,0) := funext fun y => time_slice f hd t y
  rw [hs, ht, time_slice _ (dir_diff f hf _), space_slice _ (dir_diff f hf _)]
  have hd' := (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  rw [fderiv_clm_apply (hd' (t,x)) (differentiableAt_const _),
    fderiv_clm_apply (hd' (t,x)) (differentiableAt_const _)]
  simpa using hf.contDiffAt.isSymmSndFDerivAt (by simp) (1,0) (0,EuclideanSpace.single i 1)


private theorem time_diff (F : ℝ → Vec → Vec) (hF : ContDiff ℝ 2 (Function.uncurry F)) (t : ℝ) :
    Differentiable ℝ (fun y => deriv (fun s => F s y) t) := by
  have he : (fun y => deriv (fun s => F s y) t) =
      fun y => fderiv ℝ (Function.uncurry F) (t,y) (1,0) :=
    funext fun y => time_slice _ (hF.differentiable (by norm_num)) t y
  rw [he]
  exact (((hF.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero).clm_apply
    (differentiable_const _)).comp ((differentiable_const t).prodMk differentiable_id)

private theorem time_proj (F : ℝ → Vec → Vec) (hF : ContDiff ℝ 2 (Function.uncurry F))
    (t : ℝ) (x : Vec) (i : Fin 3) :
    (deriv (fun s => F s x) t) i = deriv (fun s => F s x i) t := by
  have ht : DifferentiableAt ℝ (fun s => F s x) t :=
    ((hF.differentiable (by norm_num)).comp (differentiable_id.prodMk (differentiable_const x))).differentiableAt
  have hh := (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt t ht.hasDerivAt
  exact hh.deriv.symm

private theorem div_scalar (F : Vec → Vec) (hF : Differentiable ℝ F) (x : Vec) :
    divg F x = ∑ i, pd i (fun y => F y i) x := by
  unfold divg
  simp_rw [partial_eq F hF]

private theorem div_time_diff (F : ℝ → Vec → Vec) (hF : ContDiff ℝ 2 (Function.uncurry F))
    (x : Vec) : Differentiable ℝ (fun t => divg (F t) x) := by
  have hc (i : Fin 3) : ContDiff ℝ 2 (fun p : ℝ × Vec => F p.1 p.2 i) := (contDiff_piLp 2).mp hF i
  have hs (s : ℝ) : Differentiable ℝ (F s) :=
    (hF.differentiable (by norm_num)).comp ((differentiable_const s).prodMk differentiable_id)
  simp_rw [div_scalar _ (hs _)]
  apply Differentiable.fun_sum
  intro i _
  have he : (fun s => pd i (fun y => F s y i) x) =
      fun s => fderiv ℝ (fun p : ℝ × Vec => F p.1 p.2 i) (s,x) (0,EuclideanSpace.single i 1) :=
    funext fun s => space_slice _ ((hc i).differentiable (by norm_num)) s x i
  rw [he]
  exact (dir_diff _ (hc i) _).comp (differentiable_id.prodMk (differentiable_const x))

private theorem div_time_comm (F : ℝ → Vec → Vec) (hF : ContDiff ℝ 2 (Function.uncurry F))
    (t : ℝ) (x : Vec) :
    deriv (fun s => divg (F s) x) t = divg (fun y => deriv (fun s => F s y) t) x := by
  have hc (i : Fin 3) : ContDiff ℝ 2 (fun p : ℝ × Vec => F p.1 p.2 i) := (contDiff_piLp 2).mp hF i
  have hs (s : ℝ) : Differentiable ℝ (F s) :=
    (hF.differentiable (by norm_num)).comp ((differentiable_const s).prodMk differentiable_id)
  have hd (i : Fin 3) : DifferentiableAt ℝ (fun s => pd i (fun y => F s y i) x) t := by
    have he : (fun s => pd i (fun y => F s y i) x) =
        fun s => fderiv ℝ (fun p : ℝ × Vec => F p.1 p.2 i) (s,x) (0,EuclideanSpace.single i 1) :=
      funext fun s => space_slice _ ((hc i).differentiable (by norm_num)) s x i
    rw [he]
    exact ((dir_diff _ (hc i) _).comp (differentiable_id.prodMk (differentiable_const x))).differentiableAt
  simp_rw [div_scalar _ (hs _)]
  rw [deriv_fun_sum (fun i _ => hd i), div_scalar _ (time_diff F hF t)]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [time_proj F hF t]
  exact mixed _ (hc i) t x i

private theorem div_neg_field (F : Vec → Vec) (hF : Differentiable ℝ F) (x : Vec) :
    divg (fun y => -F y) x = -divg F x := by
  simp [divg, Larmor.partialDeriv, fderiv_fun_neg, Finset.sum_neg_distrib]

theorem solution (E B : ℝ → Vec → Vec)
    (hE : SmoothTV E) (hB : SmoothTV B)
    (hfaraday : ∀ t x, curl (E t) x = -deriv (fun s => B s x) t)
    (hinit : ∀ x, divg (B 0) x = 0) :
    ∀ t x, divg (B t) x = 0 := by
  have hE2 : ContDiff ℝ 2 (Function.uncurry E) := hE.of_le (by change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞); exact WithTop.coe_le_coe.mpr le_top)
  have hB2 : ContDiff ℝ 2 (Function.uncurry B) := hB.of_le (by change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞); exact WithTop.coe_le_coe.mpr le_top)
  intro t x
  have hz (s : ℝ) : deriv (fun u => divg (B u) x) s = 0 := by
    rw [div_time_comm B hB2]
    have he : (fun y => deriv (fun u => B u y) s) = fun y => -curl (E s) y := by
      funext y
      simpa using (congrArg Neg.neg (hfaraday s y)).symm
    rw [he, div_neg_field _ (curl_diff (E s) (hE2.comp ((contDiff_const).prodMk contDiff_id))),
      divcurl (E s) (hE2.comp ((contDiff_const).prodMk contDiff_id)), neg_zero]
  calc divg (B t) x = divg (B 0) x := is_const_of_deriv_eq_zero (div_time_diff B hB2 x) hz t 0
       _ = 0 := hinit x
