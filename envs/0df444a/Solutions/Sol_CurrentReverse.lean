-- Prove2me | solution 1 for CurrentReverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:57:58.66636+00:00
-- url     : https://prove2.me/submissions/4c63fcd4-72be-469b-9a25-11e7edc7fc13

import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_CurrentReverse

set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (γ γ' : Curve E) (hlen : γ'.len = γ.len)
    (hrev : ∀ t ∈ Set.Icc (0:ℝ) γ.len, γ'.toFun t = γ.toFun (γ.len - t)) (ω : Form1 E) :
    curveCurrent γ' ω = - curveCurrent γ ω := by
-- BODY
  have hglobal : ∀ t : ℝ, γ'.toFun t = γ.toFun (γ.len - t) := by
    intro t
    rcases lt_or_ge t 0 with ht | ht
    · have hmax : max (0:ℝ) t = 0 := max_eq_left_of_lt ht
      have hmin : min γ'.len (max 0 t) = 0 := by
        rw [hmax]
        exact min_eq_right γ'.len_nonneg
      have h1 : γ'.toFun t = γ'.toFun 0 := by rw [γ'.clamped t, hmin]
      have h2 : γ'.toFun 0 = γ.toFun γ.len := by
        have := hrev 0 ⟨le_refl 0, γ.len_nonneg⟩
        simpa using this
      have h3 : γ.len - t > γ.len := by linarith
      have hmax' : max (0:ℝ) (γ.len - t) = γ.len - t := max_eq_right_of_lt (by linarith [γ.len_nonneg])
      have hmin' : min γ.len (max 0 (γ.len - t)) = γ.len := by
        rw [hmax']; exact min_eq_left (le_of_lt h3)
      have h4 : γ.toFun (γ.len - t) = γ.toFun γ.len := by
        conv_lhs => rw [γ.clamped (γ.len - t), hmin']
      rw [h1, h2, h4]
    · rcases lt_or_ge γ.len t with ht2 | ht2
      · have hmax : max (0:ℝ) t = t := max_eq_right_of_lt (by linarith [γ.len_nonneg])
        have hmin : min γ'.len (max 0 t) = γ.len := by
          rw [hmax, hlen]; exact min_eq_left (le_of_lt ht2)
        have h1 : γ'.toFun t = γ'.toFun γ.len := by rw [γ'.clamped t, hmin]
        have h2 : γ'.toFun γ.len = γ.toFun 0 := by
          have := hrev γ.len ⟨γ.len_nonneg, le_refl γ.len⟩
          simpa using this
        have h3 : γ.len - t < 0 := by linarith
        have hmax' : max (0:ℝ) (γ.len - t) = 0 := max_eq_left_of_lt h3
        have hmin' : min γ.len (max 0 (γ.len - t)) = 0 := by
          rw [hmax']; exact min_eq_right γ.len_nonneg
        have h4 : γ.toFun (γ.len - t) = γ.toFun 0 := by
          conv_lhs => rw [γ.clamped (γ.len - t), hmin']
        rw [h1, h2, h4]
      · exact hrev t ⟨ht, ht2⟩
  have hfun : (ω.pi ∘ γ'.toFun) = fun t => ω.pi (γ.toFun (γ.len - t)) := by
    funext t; simp [hglobal t]
  unfold curveCurrent
  rw [hlen]
  have hderiv : ∀ t : ℝ, deriv (ω.pi ∘ γ'.toFun) t = - deriv (ω.pi ∘ γ.toFun) (γ.len - t) := by
    intro t
    rw [hfun]
    show deriv (fun x => ω.pi (γ.toFun (γ.len - x))) t = - deriv (ω.pi ∘ γ.toFun) (γ.len - t)
    have h := deriv_comp_const_sub (fun u => ω.pi (γ.toFun u)) γ.len t
    rw [show (ω.pi ∘ γ.toFun) = fun u => ω.pi (γ.toFun u) from rfl]
    exact h
  have hcongr : (∫ t in (0:ℝ)..γ.len, ω.f (γ'.toFun t) * deriv (ω.pi ∘ γ'.toFun) t)
      = ∫ t in (0:ℝ)..γ.len, ω.f (γ.toFun (γ.len - t)) * (- deriv (ω.pi ∘ γ.toFun) (γ.len - t)) := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [hglobal t, hderiv t]
  rw [hcongr]
  have hsplit : (∫ t in (0:ℝ)..γ.len, ω.f (γ.toFun (γ.len - t)) * (- deriv (ω.pi ∘ γ.toFun) (γ.len - t)))
      = - ∫ t in (0:ℝ)..γ.len, ω.f (γ.toFun (γ.len - t)) * deriv (ω.pi ∘ γ.toFun) (γ.len - t) := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext t
    ring
  rw [hsplit]
  congr 1
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun t => ω.f (γ.toFun t) * deriv (ω.pi ∘ γ.toFun) t) γ.len (a := (0:ℝ)) (b := γ.len)
  simpa using hsub
