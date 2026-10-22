-- Prove2me | solution 1 for CatSymplectic.Hemistrict.diagram_three
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T22:33:43.552388+00:00
-- url     : https://prove2.me/submissions/8e8ac959-08a0-40c8-9e16-c35064af7d0b

import Mathlib
import Definitions.Def_CatSymplectic_Hemistrict_Basic

open ContinuousAlternatingMap CatSymplectic.Hemistrict

namespace CSY361Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma ham_spec (Ω : Form E 3) (F : Form E 1) (hF : F ∈ hamSubmodule Ω) :
    IsHamVF Ω F (hamVF Ω F) := by
  have h : ∃ v, IsHamVF Ω F v := hF.2
  unfold hamVF
  rw [dif_pos h]
  exact h.choose_spec

lemma vec1 (a : E) : (![a] : Fin 1 → E) = fun _ => a := by
  funext i; fin_cases i; rfl

lemma ex2 (ω : Form E 1) (x a b : E) :
    extDeriv ω x ![a, b] = fderiv ℝ ω x a ![b] - fderiv ℝ ω x b ![a] := by
  simp only [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  simp
  rw [show Fin.removeNth 1 ![a, b] = ![a] from by funext i; fin_cases i; rfl]
  abel

lemma ex3 (β : Form E 2) (x p q r : E) :
    extDeriv β x ![p, q, r] = fderiv ℝ β x p ![q, r] - fderiv ℝ β x q ![p, r] +
      fderiv ℝ β x r ![p, q] := by
  simp only [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  simp
  rw [show Fin.removeNth 1 ![p, q, r] = ![p, r] from by funext i; fin_cases i <;> rfl,
    show Fin.removeNth 2 ![p, q, r] = ![p, q] from by funext i; fin_cases i <;> rfl]
  abel

lemma ex4 (Ω : Form E 3) (x p q r s : E) :
    extDeriv Ω x ![p, q, r, s] = fderiv ℝ Ω x p ![q, r, s] - fderiv ℝ Ω x q ![p, r, s] +
      fderiv ℝ Ω x r ![p, q, s] - fderiv ℝ Ω x s ![p, q, r] := by
  simp only [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  simp
  rw [show Fin.removeNth 1 ![p, q, r, s] = ![p, r, s] from by funext i; fin_cases i <;> rfl,
    show Fin.removeNth 2 ![p, q, r, s] = ![p, q, s] from by funext i; fin_cases i <;> rfl,
    show Fin.removeNth 3 ![p, q, r, s] = ![p, q, r] from by funext i; fin_cases i <;> rfl]
  abel

lemma dpair1 (G : Form E 1) (g : E → E) (x : E) (hG : DifferentiableAt ℝ G x)
    (hg : DifferentiableAt ℝ g x) (u : E) :
    DifferentiableAt ℝ (fun y => G y ![g y]) x ∧
    fderiv ℝ (fun y => G y ![g y]) x u = fderiv ℝ G x u ![g x] + G x ![fderiv ℝ g x u] := by
  have e : (fun y => G y ![g y]) = fun y => G y (fun i : Fin 1 => (fun _ : Fin 1 => g) i y) := by
    funext y; rw [vec1]
  rw [e]
  refine ⟨hG.continuousAlternatingMap_apply (fun _ => hg), ?_⟩
  rw [fderiv_continuousAlternatingMap_apply_apply hG (fun _ => hg), vec1, vec1]
  simp only [Fin.sum_univ_one]
  congr 2
  funext i; fin_cases i; simp

lemma dpair3 (Ω : Form E 3) (g : E → E) (x : E) (hΩ : DifferentiableAt ℝ Ω x)
    (hg : DifferentiableAt ℝ g x) (p q u : E) :
    DifferentiableAt ℝ (fun y => Ω y ![g y, p, q]) x ∧
    fderiv ℝ (fun y => Ω y ![g y, p, q]) x u =
      fderiv ℝ Ω x u ![g x, p, q] + Ω x ![fderiv ℝ g x u, p, q] := by
  set gs : Fin 3 → E → E := ![g, fun _ => p, fun _ => q]
  have hgs : ∀ i, DifferentiableAt ℝ (gs i) x := by
    intro i; fin_cases i
    · exact hg
    · exact differentiableAt_const p
    · exact differentiableAt_const q
  have e : (fun y => Ω y ![g y, p, q]) = fun y => Ω y (fun i => gs i y) := by
    funext y; congr 1; funext i; fin_cases i <;> rfl
  rw [e]
  refine ⟨hΩ.continuousAlternatingMap_apply hgs, ?_⟩
  rw [fderiv_continuousAlternatingMap_apply_apply hΩ hgs]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  have h1 : (fun i => gs i x) = ![g x, p, q] := by funext i; fin_cases i <;> rfl
  rw [h1]
  have z1 : Ω x (Function.update ![g x, p, q] (Fin.succ 0) (fderiv ℝ (gs (Fin.succ 0)) x u)) = 0 := by
    have : fderiv ℝ (gs (Fin.succ 0)) x u = 0 := by simp [gs]
    rw [this]; exact (Ω x).map_update_zero _ _
  have z2 : Ω x (Function.update ![g x, p, q] (Fin.succ 0).succ
      (fderiv ℝ (gs (Fin.succ 0).succ) x u)) = 0 := by
    have : fderiv ℝ (gs (Fin.succ 0).succ) x u = 0 := by simp [gs]
    rw [this]; exact (Ω x).map_update_zero _ _
  rw [z1, z2]
  have h0 : Function.update ![g x, p, q] 0 (fderiv ℝ (gs 0) x u) = ![fderiv ℝ g x u, p, q] := by
    funext i; fin_cases i <;> rfl
  rw [h0]
  ring


lemma sw01 (A : E [⋀^Fin 3]→L[ℝ] ℝ) (p q r : E) : A ![p, q, r] = -A ![q, p, r] := by
  have h := AlternatingMap.map_swap A.toAlternatingMap ![q, p, r] (i := (0 : Fin 3)) (j := 1)
    (by decide)
  have e : (![q, p, r] ∘ Equiv.swap (0 : Fin 3) 1) = ![p, q, r] := by
    funext i; fin_cases i <;> rfl
  rw [e] at h
  exact h

lemma sw12 (A : E [⋀^Fin 3]→L[ℝ] ℝ) (p q r : E) : A ![p, q, r] = -A ![p, r, q] := by
  have h := AlternatingMap.map_swap A.toAlternatingMap ![p, r, q] (i := (1 : Fin 3)) (j := 2)
    (by decide)
  have e : (![p, r, q] ∘ Equiv.swap (1 : Fin 3) 2) = ![p, q, r] := by
    funext i; fin_cases i <;> rfl
  rw [e] at h
  exact h

lemma h2le : minSmoothness ℝ 2 ≤ smooth := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.mpr le_top

lemma one_le : (1 : WithTop ℕ∞) ≤ smooth := WithTop.coe_le_coe.mpr le_top

/-- The Lie derivative of `Ω` along a Hamiltonian field vanishes. -/
lemma lie_omega (Ω : Form E 3) (hΩs : ContDiff ℝ smooth Ω) (hdΩ : extDeriv Ω = 0)
    (F : Form E 1) (hFs : ContDiff ℝ smooth F) (v : E → E) (hv : ContDiff ℝ smooth v)
    (hF : ∀ y, extDeriv F y = -((Ω y).curryLeft (v y))) (x w a b : E) :
    fderiv ℝ Ω x (v x) ![w, a, b] + Ω x ![fderiv ℝ v x w, a, b] +
      Ω x ![w, fderiv ℝ v x a, b] + Ω x ![w, a, fderiv ℝ v x b] = 0 := by
  set β : Form E 2 := fun y => (Ω y).curryLeft (v y) with hβ
  have hβF : β = -(extDeriv F) := by funext y; rw [hβ]; simp [hF y]
  have hdβ : extDeriv β x = 0 := by
    have hdd := ContWeatherall.extDeriv_extDeriv_eq_zero (n := 1) hFs
    have : β = (-1 : ℝ) • extDeriv F := by rw [hβF]; simp
    rw [this, extDeriv_smul, hdd]; simp
  have hβs : ContDiff ℝ smooth β := by
    rw [hβF]; exact (ContWeatherall.extDeriv_contDiff hFs).neg
  have hβd : DifferentiableAt ℝ β x := hβs.differentiable (by simp) x
  have hΩd : DifferentiableAt ℝ Ω x := hΩs.differentiable (by simp) x
  have hvd : DifferentiableAt ℝ v x := hv.differentiable (by simp) x
  have Dβ : ∀ u p q, fderiv ℝ β x u ![p, q] =
      fderiv ℝ Ω x u ![v x, p, q] + Ω x ![fderiv ℝ v x u, p, q] := by
    intro u p q
    rw [← fderiv_continuousAlternatingMap_apply_const_apply hβd]
    have : (fun y => β y ![p, q]) = fun y => Ω y ![v y, p, q] := by
      funext y; simp only [hβ, curryLeft_apply_apply]
    rw [this]
    exact (dpair3 Ω v x hΩd hvd p q u).2
  have e1 := congrArg (fun φ => φ ![w, a, b]) hdβ
  simp only [ex3, Dβ] at e1
  change _ = (0 : ℝ) at e1
  have e2 := congrArg (fun φ => φ x ![v x, w, a, b]) hdΩ
  simp only [ex4] at e2
  change _ = (0 : ℝ) at e2
  have s1 := sw01 (Ω x) (fderiv ℝ v x a) w b
  have s2 := sw01 (Ω x) (fderiv ℝ v x b) w a
  have s3 := sw12 (Ω x) w (fderiv ℝ v x b) a
  linarith

end CSY361Aux

open CSY361Aux

theorem prop361 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Ω : Form E 3) (hΩ : IsNPlectic 2 Ω)
    (F G : hamSubmodule Ω) :
    hemi Ω F G ∈ hamSubmodule Ω ∧
      IsHamVF Ω (hemi Ω F G)
        (VectorField.lieBracket ℝ (hamVF Ω F) (hamVF Ω G)) ∧
      hamVF Ω (hemi Ω F G) =
        VectorField.lieBracket ℝ (hamVF Ω F) (hamVF Ω G) := by
  have sF := ham_spec Ω F F.2
  have sG := ham_spec Ω G G.2
  set v := hamVF Ω F with hvdef
  set w := hamVF Ω G with hwdef
  set g : Form E 1 := (G : Form E 1) with hgdef
  have hGs : ContDiff ℝ smooth g := G.2.1
  have hFs : ContDiff ℝ smooth (F : Form E 1) := F.2.1
  have hv := sF.1
  have hw := sG.1
  have hG1 : ContDiff ℝ smooth (fderiv ℝ g) := hGs.fderiv_right (m := smooth) (by simp)
  have hv1 : ContDiff ℝ smooth (fderiv ℝ v) := hv.fderiv_right (m := smooth) (by simp)
  have hw1 : ContDiff ℝ smooth (fderiv ℝ w) := hw.fderiv_right (m := smooth) (by simp)
  -- smoothness of K
  set K := hemi Ω F G with hK
  let e := ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (ι := Fin 1) 0
  have hcomp : ∀ y, (g y).compContinuousLinearMap (fderiv ℝ v y) =
      e ((e.symm (g y)).comp (fderiv ℝ v y)) := by
    intro y
    conv_lhs => rw [← e.apply_symm_apply (g y)]
    ext m
    rfl
  have hKeq : K = fun y => fderiv ℝ g y (v y) + e ((e.symm (g y)).comp (fderiv ℝ v y)) := by
    funext y; rw [hK, hemi, lieDeriv1, hcomp]
  have hKs : ContDiff ℝ smooth K := by
    rw [hKeq]
    exact (hG1.clm_apply hv).add (e.contDiff.comp ((e.symm.contDiff.comp hGs).clm_comp hv1))
  have hbr : ContDiff ℝ smooth (VectorField.lieBracket ℝ v w) := by
    have : VectorField.lieBracket ℝ v w = fun y => fderiv ℝ w y (v y) - fderiv ℝ v y (w y) := by
      funext y; rfl
    rw [this]
    exact (hw1.clm_apply hv).sub (hv1.clm_apply hw)
  -- the key identity
  have key : ∀ x a b, extDeriv K x ![a, b] =
      -((Ω x).curryLeft (VectorField.lieBracket ℝ v w x) ![a, b]) := by
    intro x a b
    have hKd : DifferentiableAt ℝ K x := hKs.differentiable (by simp) x
    have hgd : ∀ y, DifferentiableAt ℝ g y := fun y => hGs.differentiable (by simp) y
    have hg1d : DifferentiableAt ℝ (fderiv ℝ g) x := hG1.differentiable (by simp) x
    have hvd : DifferentiableAt ℝ v x := hv.differentiable (by simp) x
    have hwd : DifferentiableAt ℝ w x := hw.differentiable (by simp) x
    have hv1d : DifferentiableAt ℝ (fderiv ℝ v) x := hv1.differentiable (by simp) x
    have hΩd : DifferentiableAt ℝ Ω x := hΩ.1.differentiable (by simp) x
    have symG := (hGs.contDiffAt (x := x)).isSymmSndFDerivAt h2le
    have symv := (hv.contDiffAt (x := x)).isSymmSndFDerivAt h2le
    -- derivative of K in direction a, evaluated at b
    have DK : ∀ a b, fderiv ℝ K x a ![b] =
        fderiv ℝ g x (fderiv ℝ v x a) ![b] + fderiv ℝ (fderiv ℝ g) x (v x) a ![b] +
        (fderiv ℝ g x a ![fderiv ℝ v x b] + g x ![fderiv ℝ (fderiv ℝ v) x a b]) := by
      intro a b
      rw [← fderiv_continuousAlternatingMap_apply_const_apply hKd]
      have hfun : (fun y => K y ![b]) =
          fun y => (fun z => fderiv ℝ g z (v z)) y ![b] + g y ![(fun z => fderiv ℝ v z b) y] := by
        funext y
        rw [hK, hemi, lieDeriv1]
        simp only [ContinuousAlternatingMap.add_apply, compContinuousLinearMap_apply]
        congr 2
        funext i; fin_cases i; rfl
      have hΦd : DifferentiableAt ℝ (fun z => fderiv ℝ g z (v z)) x := hg1d.clm_apply hvd
      have hcd : DifferentiableAt ℝ (fun z => fderiv ℝ v z b) x :=
        hv1d.clm_apply (differentiableAt_const b)
      obtain ⟨hpd, hp⟩ := dpair1 g (fun z => fderiv ℝ v z b) x (hgd x) hcd a
      rw [hfun, fderiv_fun_add (hΦd.continuousAlternatingMap_apply_const _) hpd,
        _root_.add_apply, fderiv_continuousAlternatingMap_apply_const_apply hΦd, hp,
        fderiv_clm_apply hg1d hvd, fderiv_clm_apply hv1d (differentiableAt_const b)]
      simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.flip_apply, fderiv_fun_const, Pi.zero_apply, zero_apply,
        _root_.map_zero, zero_add]
      rw [symG a (v x), ContinuousAlternatingMap.add_apply]
    -- E1 identity for g
    have E1 : ∀ y p q, fderiv ℝ g y p ![q] - fderiv ℝ g y q ![p] = -(Ω y ![w y, p, q]) := by
      intro y p q
      rw [← ex2, sG.2 y]
      simp only [ContinuousAlternatingMap.neg_apply, curryLeft_apply_apply]
    -- derivative of E1 along v
    have hS : fderiv ℝ (fderiv ℝ g) x (v x) a ![b] - fderiv ℝ (fderiv ℝ g) x (v x) b ![a] =
        -(fderiv ℝ Ω x (v x) ![w x, a, b] + Ω x ![fderiv ℝ w x (v x), a, b]) := by
      have d1 : ∀ p q, DifferentiableAt ℝ (fun y => fderiv ℝ g y p ![q]) x ∧
          fderiv ℝ (fun y => fderiv ℝ g y p ![q]) x (v x) = fderiv ℝ (fderiv ℝ g) x (v x) p ![q] := by
        intro p q
        have hp : DifferentiableAt ℝ (fun y => fderiv ℝ g y p) x :=
          hg1d.clm_apply (differentiableAt_const p)
        refine ⟨hp.continuousAlternatingMap_apply_const _, ?_⟩
        rw [fderiv_continuousAlternatingMap_apply_const_apply hp,
          fderiv_clm_apply hg1d (differentiableAt_const p)]
        simp
      have hfun : (fun y => fderiv ℝ g y a ![b] - fderiv ℝ g y b ![a]) =
          fun y => -(Ω y ![w y, a, b]) := by funext y; exact E1 y a b
      have := congrArg (fun φ => fderiv ℝ φ x (v x)) hfun
      rw [fderiv_fun_sub (d1 a b).1 (d1 b a).1, fderiv_fun_neg, _root_.sub_apply,
        (d1 a b).2, (d1 b a).2, _root_.neg_apply, (dpair3 Ω w x hΩd hwd a b (v x)).2] at this
      exact this
    have LΩ := lie_omega Ω hΩ.1 hΩ.2.1 F hFs v hv sF.2 x (w x) a b
    have E1a := E1 x (fderiv ℝ v x a) b
    have E1b := E1 x a (fderiv ℝ v x b)
    rw [ex2, DK, DK, symv a b]
    have hR : (Ω x).curryLeft (VectorField.lieBracket ℝ v w x) ![a, b] =
        Ω x ![fderiv ℝ w x (v x), a, b] - Ω x ![fderiv ℝ v x (w x), a, b] := by
      rw [show VectorField.lieBracket ℝ v w x = fderiv ℝ w x (v x) - fderiv ℝ v x (w x) from rfl,
        map_sub, ContinuousAlternatingMap.sub_apply, curryLeft_apply_apply, curryLeft_apply_apply]
    rw [hR]
    linarith
  have hHam : IsHamVF Ω K (VectorField.lieBracket ℝ v w) := by
    refine ⟨hbr, fun x => ?_⟩
    ext m
    obtain ⟨a, b, rfl⟩ : ∃ a b, m = ![a, b] := ⟨m 0, m 1, by funext i; fin_cases i <;> rfl⟩
    rw [key, ContinuousAlternatingMap.neg_apply]
  have hmem : K ∈ hamSubmodule Ω := ⟨hKs, _, hHam⟩
  refine ⟨hmem, hHam, ?_⟩
  have uniq : ∀ u₁ u₂, IsHamVF Ω K u₁ → IsHamVF Ω K u₂ → u₁ = u₂ := by
    intro u₁ u₂ h1 h2
    funext x
    have e : (Ω x).curryLeft (u₁ x) = (Ω x).curryLeft (u₂ x) := by
      have := (h1.2 x).symm.trans (h2.2 x)
      exact neg_injective this
    have : (Ω x).curryLeft (u₁ x - u₂ x) = 0 := by
      rw [map_sub, e, sub_self]
    exact sub_eq_zero.mp (hΩ.2.2 x _ this)
  exact uniq _ _ (ham_spec Ω K hmem) hHam

lemma lin1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E [⋀^Fin 1]→L[ℝ] ℝ) (p q : E) : A ![p - q] = A ![p] - A ![q] := by
  have h := A.toAlternatingMap.map_update_sub ![p] 0 p q
  have e1 : Function.update ![p] 0 (p - q) = ![p - q] := by funext i; fin_cases i; rfl
  have e2 : Function.update ![p] 0 p = ![p] := by funext i; fin_cases i; rfl
  have e3 : Function.update ![p] 0 q = ![q] := by funext i; fin_cases i; rfl
  rw [e1, e2, e3] at h
  exact h

lemma lie1_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E → E) (α : Form E 1) (x u : E) :
    lieDeriv1 v α x ![u] = fderiv ℝ α x (v x) ![u] + α x ![fderiv ℝ v x u] := by
  simp only [lieDeriv1, ContinuousAlternatingMap.add_apply, compContinuousLinearMap_apply]
  congr 2
  funext i; fin_cases i; rfl

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Ω : Form E 3) (hΩ : IsNPlectic 2 Ω)
    (F G H : hamSubmodule Ω) :
    alt Ω (hemi Ω F G) H + alt Ω G (hemi Ω F H) =
      hemiFn Ω F (alt Ω G H) := by
  have sF := ham_spec Ω F F.2
  have sG := ham_spec Ω G G.2
  have sH := ham_spec Ω H H.2
  have hFG := (prop361 Ω hΩ F G).2.2
  have hFH := (prop361 Ω hΩ F H).2.2
  funext x
  have hGd : DifferentiableAt ℝ (G : Form E 1) x := G.2.1.differentiable (by simp) x
  have hHd : DifferentiableAt ℝ (H : Form E 1) x := H.2.1.differentiable (by simp) x
  have hwd : DifferentiableAt ℝ (hamVF Ω G) x := sG.1.differentiable (by simp) x
  have hud : DifferentiableAt ℝ (hamVF Ω H) x := sH.1.differentiable (by simp) x
  obtain ⟨d1, e1⟩ := dpair1 (H : Form E 1) (hamVF Ω G) x hHd hwd (hamVF Ω F x)
  obtain ⟨d2, e2⟩ := dpair1 (G : Form E 1) (hamVF Ω H) x hGd hud (hamVF Ω F x)
  have halt : alt Ω G H = fun y => -((fun y => (H : Form E 1) y ![hamVF Ω G y]) y +
      (fun y => (G : Form E 1) y ![hamVF Ω H y]) y) := rfl
  simp only [Pi.add_apply, hemiFn, lieDerivFn]
  rw [halt, fderiv_fun_neg, fderiv_fun_add d1 d2]
  simp only [_root_.neg_apply, _root_.add_apply]
  rw [e1, e2]
  simp only [alt]
  rw [hFG, hFH]
  simp only [hemi, lie1_apply, VectorField.lieBracket, lin1]
  ring
