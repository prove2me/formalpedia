-- Prove2me | solution 1 for CatSymplectic.Hemistrict.proposition_3_6_2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T22:22:39.054914+00:00
-- url     : https://prove2.me/submissions/913ebd91-4c10-4cbf-9380-df94df11e1c8

import Mathlib
import Definitions.Def_CatSymplectic_Hemistrict_Basic

open ContinuousAlternatingMap CatSymplectic.Hemistrict

namespace CSY362Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma ham_spec (Ω : Form E 3) (F : Form E 1) (hF : F ∈ hamSubmodule Ω) :
    IsHamVF Ω F (hamVF Ω F) := by
  have h : ∃ v, IsHamVF Ω F v := hF.2
  unfold hamVF
  rw [dif_pos h]
  exact h.choose_spec

lemma vec1 (a : E) : (![a] : Fin 1 → E) = fun _ => a := by
  funext i; fin_cases i; rfl

lemma pair_hasFDeriv (G : Form E 1) (v : E → E) (hG : ContDiff ℝ smooth G)
    (hv : ContDiff ℝ smooth v) (x : E) :
    DifferentiableAt ℝ (fun y => G y ![v y]) x ∧ ∀ a,
    fderiv ℝ (fun y => G y ![v y]) x a = fderiv ℝ G x a ![v x] + G x ![fderiv ℝ v x a] := by
  have hGd : DifferentiableAt ℝ G x := hG.differentiable (by simp) x
  have hvd : DifferentiableAt ℝ v x := hv.differentiable (by simp) x
  have e : (fun y => G y ![v y]) = fun y => G y (fun i : Fin 1 => (fun _ : Fin 1 => v) i y) := by
    funext y; rw [vec1]
  rw [e]
  refine ⟨hGd.continuousAlternatingMap_apply (fun _ => hvd), fun a => ?_⟩
  rw [fderiv_continuousAlternatingMap_apply_apply hGd (fun _ => hvd), vec1, vec1]
  simp only [Fin.sum_univ_one]
  congr 2
  funext i; fin_cases i; simp

lemma key (Ω : Form E 3) (F G : Form E 1) (hF : F ∈ hamSubmodule Ω)
    (hG : G ∈ hamSubmodule Ω) (x a : E) :
    hemi Ω F G x ![a] = -(Ω x ![hamVF Ω G x, hamVF Ω F x, a]) +
      fderiv ℝ (fun y => G y ![hamVF Ω F y]) x a := by
  have sF := ham_spec Ω F hF
  have sG := ham_spec Ω G hG
  have hGd : DifferentiableAt ℝ G x := hG.1.differentiable (by simp) x
  obtain ⟨-, hp⟩ := pair_hasFDeriv G (hamVF Ω F) hG.1 sF.1 x
  rw [hp]
  have hd := congrArg (fun φ => φ ![hamVF Ω F x, a]) (sG.2 x)
  simp only [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_two,
    ContinuousAlternatingMap.neg_apply, curryLeft_apply_apply] at hd
  simp only [hemi, lieDeriv1, ContinuousAlternatingMap.add_apply,
    compContinuousLinearMap_apply]
  have r0 : Fin.removeNth 0 ![hamVF Ω F x, a] = ![a] := by
    funext i; fin_cases i; rfl
  have r1 : Fin.removeNth 1 ![hamVF Ω F x, a] = ![hamVF Ω F x] := by
    funext i; fin_cases i; rfl
  have c3 : (Fin.cons (hamVF Ω G x) ![hamVF Ω F x, a] : Fin 3 → E) =
      ![hamVF Ω G x, hamVF Ω F x, a] := by
    funext i; fin_cases i <;> rfl
  rw [Fin.sum_univ_two] at hd
  rw [r0, r1] at hd
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hd
  have e2 : (⇑(fderiv ℝ (hamVF Ω F) x) ∘ ![a]) = ![fderiv ℝ (hamVF Ω F) x a] := by
    funext i; fin_cases i; rfl
  rw [e2]
  linarith

end CSY362Aux

open CSY362Aux

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Ω : Form E 3) (hΩ : IsNPlectic 2 Ω)
    (F G : hamSubmodule Ω) :
    hemi Ω F G + ContWeatherall.grad (alt Ω F G) = -(hemi Ω G F) := by
  funext x
  ext w
  obtain ⟨a, rfl⟩ : ∃ a, w = ![a] := ⟨w 0, by funext i; fin_cases i; rfl⟩
  have sF := ham_spec Ω F F.2
  have sG := ham_spec Ω G G.2
  obtain ⟨d1, -⟩ := pair_hasFDeriv (G : Form E 1) (hamVF Ω F) G.2.1 sF.1 x
  obtain ⟨d2, -⟩ := pair_hasFDeriv (F : Form E 1) (hamVF Ω G) F.2.1 sG.1 x
  have halt : alt Ω F G = fun y => -((fun y => (G : Form E 1) y ![hamVF Ω F y]) y +
      (fun y => (F : Form E 1) y ![hamVF Ω G y]) y) := rfl
  simp only [Pi.add_apply, Pi.neg_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.neg_apply, ContWeatherall.grad_apply, ofSubsingleton_apply_apply]
  rw [key Ω F G F.2 G.2, key Ω G F G.2 F.2, halt, fderiv_fun_neg, fderiv_fun_add d1 d2]
  simp only [_root_.neg_apply, _root_.add_apply,
    Matrix.cons_val_zero]
  have hsw : Ω x ![hamVF Ω F x, hamVF Ω G x, a] = -(Ω x ![hamVF Ω G x, hamVF Ω F x, a]) := by
    have h := AlternatingMap.map_swap (Ω x).toAlternatingMap ![hamVF Ω G x, hamVF Ω F x, a]
      (i := (0 : Fin 3)) (j := 1) (by decide)
    have e : (![hamVF Ω G x, hamVF Ω F x, a] ∘ Equiv.swap (0 : Fin 3) 1) =
        ![hamVF Ω F x, hamVF Ω G x, a] := by
      funext i; fin_cases i <;> rfl
    rw [e] at h
    exact h
  rw [hsw]
  ring
