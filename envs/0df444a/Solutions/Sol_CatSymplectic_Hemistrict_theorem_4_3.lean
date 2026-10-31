-- Prove2me | solution 1 for CatSymplectic.Hemistrict.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T02:06:31.349506+00:00
-- url     : https://prove2.me/submissions/f3fb2c31-e929-495b-b11c-377f72f7e32f

import Mathlib
import Definitions.Def_CatSymplectic_Hemistrict_Basic
import Theorems.Thm_CatSymplectic_Hemistrict_unique_hamVF
import Theorems.Thm_CatSymplectic_Hemistrict_exact_forms
import Theorems.Thm_CatSymplectic_Hemistrict_proposition_3_6_1
import Theorems.Thm_CatSymplectic_Hemistrict_proposition_3_6_2
import Theorems.Thm_CatSymplectic_Hemistrict_proposition_3_6_3
import Theorems.Thm_CatSymplectic_Hemistrict_hemi_chain_map
import Theorems.Thm_CatSymplectic_Hemistrict_mixed_jacobi
import Theorems.Thm_CatSymplectic_Hemistrict_diagram_three

open ContinuousAlternatingMap CatSymplectic.Hemistrict

namespace CSThm43Aux

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma ham_spec (Ω : Form E 3) (F : Form E 1) (hF : F ∈ hamSubmodule Ω) :
    IsHamVF Ω F (hamVF Ω F) := by
  have h : ∃ v, IsHamVF Ω F v := hF.2
  unfold hamVF
  rw [dif_pos h]
  exact h.choose_spec

lemma vec1 (a : E) : (![a] : Fin 1 → E) = fun _ => a := by
  funext i; fin_cases i; rfl

lemma eta1 (w : Fin 1 → E) : w = ![w 0] := by
  funext i; fin_cases i; rfl

lemma update1 (a b : E) : Function.update (![a] : Fin 1 → E) 0 b = ![b] := by
  funext i; fin_cases i; simp

lemma slot_add (α : E [⋀^Fin 1]→L[ℝ] ℝ) (u v : E) : α ![u + v] = α ![u] + α ![v] := by
  have h := α.toContinuousMultilinearMap.map_update_add (![0] : Fin 1 → E) 0 u v
  simp only [update1] at h
  exact h

lemma slot_smul (α : E [⋀^Fin 1]→L[ℝ] ℝ) (c : ℝ) (u : E) : α ![c • u] = c * α ![u] := by
  have h := α.toContinuousMultilinearMap.map_update_smul (![0] : Fin 1 → E) 0 c u
  simp only [update1, smul_eq_mul] at h
  exact h

lemma slot_zero (α : E [⋀^Fin 1]→L[ℝ] ℝ) : α ![0] = 0 := by
  have h := slot_smul α 0 0
  simpa using h

lemma grad_slot (f : E → ℝ) (x u : E) : ContWeatherall.grad f x ![u] = fderiv ℝ f x u := by
  rw [ContWeatherall.grad_apply]
  simp

/-- The slot-evaluation of a 1-form as a continuous linear functional. -/
noncomputable def ell : (E [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  ((ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).symm :
    (E [⋀^Fin 1]→L[ℝ] ℝ) ≃ₗᵢ[ℝ] (E →L[ℝ] ℝ)).toContinuousLinearEquiv.toContinuousLinearMap

lemma ell_apply (α : E [⋀^Fin 1]→L[ℝ] ℝ) (u : E) : ell α u = α ![u] := by
  have h : α = ofSubsingleton ℝ E ℝ (0 : Fin 1) (ell α) := by
    exact ((ofSubsingleton ℝ E ℝ (0 : Fin 1)).apply_symm_apply α).symm
  conv_rhs => rw [h]
  simp

lemma pair_smooth {F : Form E 1} {v : E → E} (hF : ContDiff ℝ smooth F)
    (hv : ContDiff ℝ smooth v) : ContDiff ℝ smooth (fun x => F x ![v x]) := by
  have e : (fun x => F x ![v x]) = fun x => (ell (F x)) (v x) := by
    funext x; rw [ell_apply]
  rw [e]
  exact (ell.contDiff.comp hF).clm_apply hv

lemma hemiFn_smooth (Ω : Form E 3) {F : Form E 1} (hF : F ∈ hamSubmodule Ω) {f : E → ℝ}
    (hf : ContDiff ℝ smooth f) : ContDiff ℝ smooth (hemiFn Ω F f) := by
  have hfd : ContDiff ℝ smooth (fderiv ℝ f) := (contDiff_infty_iff_fderiv.1 hf).2
  exact hfd.clm_apply (ham_spec Ω F hF).1

lemma alt_smooth (Ω : Form E 3) {F G : Form E 1} (hF : F ∈ hamSubmodule Ω)
    (hG : G ∈ hamSubmodule Ω) : ContDiff ℝ smooth (alt Ω F G) :=
  ((pair_smooth hG.1 (ham_spec Ω F hF).1).add (pair_smooth hF.1 (ham_spec Ω G hG).1)).neg

section Finite

variable [FiniteDimensional ℝ E]

lemma hamVF_add (Ω : Form E 3) (hΩ : IsNPlectic 2 Ω) {F G : Form E 1}
    (hF : F ∈ hamSubmodule Ω) (hG : G ∈ hamSubmodule Ω) :
    hamVF Ω (F + G) = hamVF Ω F + hamVF Ω G := by
  have hsF := ham_spec Ω F hF
  have hsG := ham_spec Ω G hG
  have hv : IsHamVF Ω (F + G) (hamVF Ω F + hamVF Ω G) := by
    refine ⟨hsF.1.add hsG.1, fun x => ?_⟩
    rw [extDeriv_add (hF.1.differentiable (by simp) x) (hG.1.differentiable (by simp) x),
      hsF.2 x, hsG.2 x]
    simp only [Pi.add_apply, ContinuousLinearMap.map_add]
    abel
  exact (unique_hamVF Ω hΩ (F + G) _ _ hv hv).2

lemma hamVF_smul (Ω : Form E 3) (hΩ : IsNPlectic 2 Ω) (c : ℝ) {F : Form E 1}
    (hF : F ∈ hamSubmodule Ω) : hamVF Ω (c • F) = c • hamVF Ω F := by
  have hsF := ham_spec Ω F hF
  have hv : IsHamVF Ω (c • F) (c • hamVF Ω F) := by
    refine ⟨hsF.1.const_smul c, fun x => ?_⟩
    rw [extDeriv_smul, hsF.2 x]
    simp
  exact (unique_hamVF Ω hΩ (c • F) _ _ hv hv).2

end Finite

lemma lieDeriv1_add_right {v : E → E} {G H : Form E 1} (hG : ContDiff ℝ smooth G)
    (hH : ContDiff ℝ smooth H) :
    lieDeriv1 v (G + H) = lieDeriv1 v G + lieDeriv1 v H := by
  funext x
  ext w
  have hG' : DifferentiableAt ℝ G x := hG.differentiable (by simp) x
  have hH' : DifferentiableAt ℝ H x := hH.differentiable (by simp) x
  simp only [lieDeriv1, fderiv_add hG' hH', Pi.add_apply]
  simp
  abel

lemma lieDeriv1_smul_right {v : E → E} (c : ℝ) {G : Form E 1} (hG : ContDiff ℝ smooth G) :
    lieDeriv1 v (c • G) = c • lieDeriv1 v G := by
  funext x
  ext w
  have hG' : DifferentiableAt ℝ G x := hG.differentiable (by simp) x
  simp only [lieDeriv1, Pi.smul_apply]
  rw [fderiv_const_smul hG']
  simp

lemma lieDeriv1_add_left {v v' : E → E} (hv : ContDiff ℝ smooth v) (hv' : ContDiff ℝ smooth v')
    (G : Form E 1) : lieDeriv1 (v + v') G = lieDeriv1 v G + lieDeriv1 v' G := by
  funext x
  ext w
  have h1 : DifferentiableAt ℝ v x := hv.differentiable (by simp) x
  have h2 : DifferentiableAt ℝ v' x := hv'.differentiable (by simp) x
  simp only [lieDeriv1, Pi.add_apply, fderiv_add h1 h2, map_add]
  have key : (G x).compContinuousLinearMap (fderiv ℝ v x + fderiv ℝ v' x) w =
      (G x).compContinuousLinearMap (fderiv ℝ v x) w +
        (G x).compContinuousLinearMap (fderiv ℝ v' x) w := by
    rw [eta1 w]
    simp only [compContinuousLinearMap_apply]
    have e : ∀ A : E →L[ℝ] E, (⇑A ∘ ![w 0]) = ![A (w 0)] := by
      intro A; funext i; fin_cases i; rfl
    rw [e, e, e]
    simpa using slot_add (G x) (fderiv ℝ v x (w 0)) (fderiv ℝ v' x (w 0))
  simp only [ContinuousAlternatingMap.add_apply, key]
  abel

lemma lieDeriv1_smul_left (c : ℝ) {v : E → E} (hv : ContDiff ℝ smooth v) (G : Form E 1) :
    lieDeriv1 (c • v) G = c • lieDeriv1 v G := by
  funext x
  ext w
  have h1 : DifferentiableAt ℝ v x := hv.differentiable (by simp) x
  simp only [lieDeriv1, Pi.smul_apply, fderiv_const_smul h1, map_smul]
  have key : (G x).compContinuousLinearMap (c • fderiv ℝ v x) w =
      c * (G x).compContinuousLinearMap (fderiv ℝ v x) w := by
    rw [eta1 w]
    simp only [compContinuousLinearMap_apply]
    have e : ∀ A : E →L[ℝ] E, (⇑A ∘ ![w 0]) = ![A (w 0)] := by
      intro A; funext i; fin_cases i; rfl
    rw [e, e]
    simpa using slot_smul (G x) c (fderiv ℝ v x (w 0))
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, key,
    smul_eq_mul]
  ring


section Maps

variable [FiniteDimensional ℝ E] (Ω : Form E 3) (hΩ : IsNPlectic 2 Ω)

lemma fn_smooth (f : smoothFns E) : ContDiff ℝ smooth (f : E → ℝ) := f.2

lemma fn_diff (f : smoothFns E) : Differentiable ℝ (f : E → ℝ) :=
  (fn_smooth f).differentiable (by simp)

include hΩ in
lemma grad_mem (f : smoothFns E) : ContWeatherall.grad (f : E → ℝ) ∈ hamSubmodule Ω :=
  (exact_forms Ω hΩ f (fn_smooth f)).1

/-- The differential `d f = df`. -/
noncomputable def dMap : smoothFns E →ₗ[ℝ] hamSubmodule Ω where
  toFun f := ⟨ContWeatherall.grad (f : E → ℝ), grad_mem Ω hΩ f⟩
  map_add' f g := by
    apply Subtype.ext
    exact ContWeatherall.grad_add (fn_diff f) (fn_diff g)
  map_smul' c f := by
    apply Subtype.ext
    funext x
    ext w
    show ContWeatherall.grad (c • (f : E → ℝ)) x w = c * ContWeatherall.grad (f : E → ℝ) x w
    rw [eta1 w, grad_slot, grad_slot, fderiv_const_smul (fn_diff f x)]
    simp

lemma coe_dMap (f : smoothFns E) :
    ((dMap Ω hΩ f : hamSubmodule Ω) : Form E 1) = ContWeatherall.grad (f : E → ℝ) := rfl

lemma hamVF_dMap (f : smoothFns E) :
    hamVF Ω ((dMap Ω hΩ f : hamSubmodule Ω) : Form E 1) = 0 :=
  (exact_forms Ω hΩ f (fn_smooth f)).2

/-- The hemi-bracket on Hamiltonian one-forms. -/
noncomputable def brMap : hamSubmodule Ω →ₗ[ℝ] hamSubmodule Ω →ₗ[ℝ] hamSubmodule Ω :=
  LinearMap.mk₂ ℝ (fun F G => ⟨hemi Ω F G, (proposition_3_6_1 Ω hΩ F G).1⟩)
    (by
      intro F F' G
      apply Subtype.ext
      show lieDeriv1 (hamVF Ω ((F : Form E 1) + F')) G =
        lieDeriv1 (hamVF Ω F) G + lieDeriv1 (hamVF Ω F') G
      rw [hamVF_add Ω hΩ F.2 F'.2,
        lieDeriv1_add_left (ham_spec Ω F F.2).1 (ham_spec Ω F' F'.2).1])
    (by
      intro c F G
      apply Subtype.ext
      show lieDeriv1 (hamVF Ω (c • (F : Form E 1))) G = c • lieDeriv1 (hamVF Ω F) G
      rw [hamVF_smul Ω hΩ c F.2, lieDeriv1_smul_left c (ham_spec Ω F F.2).1])
    (by
      intro F G G'
      apply Subtype.ext
      exact lieDeriv1_add_right G.2.1 G'.2.1)
    (by
      intro c F G
      apply Subtype.ext
      exact lieDeriv1_smul_right c G.2.1)

lemma coe_brMap (F G : hamSubmodule Ω) :
    ((brMap Ω hΩ F G : hamSubmodule Ω) : Form E 1) = hemi Ω F G := rfl

/-- The left action of Hamiltonian one-forms on smooth functions. -/
noncomputable def brLMap : hamSubmodule Ω →ₗ[ℝ] smoothFns E →ₗ[ℝ] smoothFns E :=
  LinearMap.mk₂ ℝ (fun F f => ⟨hemiFn Ω F f, hemiFn_smooth Ω F.2 (fn_smooth f)⟩)
    (by
      intro F F' f
      apply Subtype.ext
      funext x
      show fderiv ℝ (f : E → ℝ) x (hamVF Ω ((F : Form E 1) + F') x) =
        fderiv ℝ (f : E → ℝ) x (hamVF Ω F x) + fderiv ℝ (f : E → ℝ) x (hamVF Ω F' x)
      rw [hamVF_add Ω hΩ F.2 F'.2]
      simp)
    (by
      intro c F f
      apply Subtype.ext
      funext x
      show fderiv ℝ (f : E → ℝ) x (hamVF Ω (c • (F : Form E 1)) x) =
        c • fderiv ℝ (f : E → ℝ) x (hamVF Ω F x)
      rw [hamVF_smul Ω hΩ c F.2]
      simp)
    (by
      intro F f g
      apply Subtype.ext
      funext x
      show fderiv ℝ ((f : E → ℝ) + (g : E → ℝ)) x (hamVF Ω F x) =
        fderiv ℝ (f : E → ℝ) x (hamVF Ω F x) + fderiv ℝ (g : E → ℝ) x (hamVF Ω F x)
      rw [fderiv_add (fn_diff f x) (fn_diff g x)]
      rfl)
    (by
      intro c F f
      apply Subtype.ext
      funext x
      show fderiv ℝ (c • (f : E → ℝ)) x (hamVF Ω F x) =
        c • fderiv ℝ (f : E → ℝ) x (hamVF Ω F x)
      rw [fderiv_const_smul (fn_diff f x)]
      rfl)

lemma coe_brLMap (F : hamSubmodule Ω) (f : smoothFns E) :
    ((brLMap Ω hΩ F f : smoothFns E) : E → ℝ) = hemiFn Ω F f := rfl

/-- The alternator `S_{F,G} = -(ι_{v_F} G + ι_{v_G} F)`. -/
noncomputable def SMap : hamSubmodule Ω →ₗ[ℝ] hamSubmodule Ω →ₗ[ℝ] smoothFns E :=
  LinearMap.mk₂ ℝ (fun F G => ⟨alt Ω F G, alt_smooth Ω F.2 G.2⟩)
    (by
      intro F F' G
      apply Subtype.ext
      funext x
      show -((G : Form E 1) x ![hamVF Ω ((F : Form E 1) + F') x] +
          ((F : Form E 1) x + (F' : Form E 1) x) ![hamVF Ω G x]) =
        -((G : Form E 1) x ![hamVF Ω F x] + (F : Form E 1) x ![hamVF Ω G x]) +
        -((G : Form E 1) x ![hamVF Ω F' x] + (F' : Form E 1) x ![hamVF Ω G x])
      rw [hamVF_add Ω hΩ F.2 F'.2]
      simp only [Pi.add_apply, slot_add, ContinuousAlternatingMap.add_apply]
      ring)
    (by
      intro c F G
      apply Subtype.ext
      funext x
      show -((G : Form E 1) x ![hamVF Ω (c • (F : Form E 1)) x] +
          (c • (F : Form E 1) x) ![hamVF Ω G x]) =
        c * -((G : Form E 1) x ![hamVF Ω F x] + (F : Form E 1) x ![hamVF Ω G x])
      rw [hamVF_smul Ω hΩ c F.2]
      simp only [Pi.smul_apply, slot_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      ring)
    (by
      intro F G G'
      apply Subtype.ext
      funext x
      show -(((G : Form E 1) x + (G' : Form E 1) x) ![hamVF Ω F x] +
          (F : Form E 1) x ![hamVF Ω ((G : Form E 1) + G') x]) =
        -((G : Form E 1) x ![hamVF Ω F x] + (F : Form E 1) x ![hamVF Ω G x]) +
        -((G' : Form E 1) x ![hamVF Ω F x] + (F : Form E 1) x ![hamVF Ω G' x])
      rw [hamVF_add Ω hΩ G.2 G'.2]
      simp only [Pi.add_apply, slot_add, ContinuousAlternatingMap.add_apply]
      ring)
    (by
      intro c F G
      apply Subtype.ext
      funext x
      show -((c • (G : Form E 1) x) ![hamVF Ω F x] +
          (F : Form E 1) x ![hamVF Ω (c • (G : Form E 1)) x]) =
        c * -((G : Form E 1) x ![hamVF Ω F x] + (F : Form E 1) x ![hamVF Ω G x])
      rw [hamVF_smul Ω hΩ c G.2]
      simp only [Pi.smul_apply, slot_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      ring)

lemma coe_SMap (F G : hamSubmodule Ω) :
    ((SMap Ω hΩ F G : smoothFns E) : E → ℝ) = alt Ω F G := rfl

end Maps

end CSThm43Aux

open CSThm43Aux

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Ω : Form E 3) (hΩ : IsNPlectic 2 Ω) :
    ∃ L : Lie2Algebra (hamSubmodule Ω) (smoothFns E),
      L.IsHemistrict ∧
      (∀ f : smoothFns E,
        ((L.d f : hamSubmodule Ω) : Form E 1) = ContWeatherall.grad (f : E → ℝ)) ∧
      (∀ F G : hamSubmodule Ω,
        ((L.br F G : hamSubmodule Ω) : Form E 1) = hemi Ω F G) ∧
      (∀ (F : hamSubmodule Ω) (f : smoothFns E),
        ((L.brL F f : smoothFns E) : E → ℝ) = hemiFn Ω F f) ∧
      (∀ (f : smoothFns E) (F : hamSubmodule Ω), L.brR f F = 0) ∧
      (∀ F G : hamSubmodule Ω,
        ((L.S F G : smoothFns E) : E → ℝ) = alt Ω F G) := by
  have hgrad : ∀ (f : smoothFns E) (x u : E),
      ((dMap Ω hΩ f : hamSubmodule Ω) : Form E 1) x ![u] = fderiv ℝ (f : E → ℝ) x u :=
    fun f x u => grad_slot _ x u
  refine ⟨{ d := dMap Ω hΩ
            br := brMap Ω hΩ
            brL := brLMap Ω hΩ
            brR := 0
            S := SMap Ω hΩ
            J := 0
            chain_L := ?_
            chain_R := ?_
            chain_2 := ?_
            S_0 := ?_
            S_L := ?_
            S_R := ?_
            J_0 := ?_
            J_1 := ?_
            J_2 := ?_
            J_3 := ?_
            diagram_1 := ?_
            diagram_2 := ?_
            diagram_3 := ?_
            diagram_4 := ?_ }, rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
            fun _ _ => rfl, fun _ _ => rfl⟩
  · -- chain_L
    intro F f
    apply Subtype.ext
    exact (hemi_chain_map Ω hΩ F f).1
  · -- chain_R
    intro f F
    apply Subtype.ext
    rw [LinearMap.zero_apply, LinearMap.zero_apply, _root_.map_zero]
    exact (hemi_chain_map Ω hΩ F f).2.symm
  · -- chain_2
    intro f g
    apply Subtype.ext
    funext x
    show fderiv ℝ (g : E → ℝ) x (hamVF Ω ((dMap Ω hΩ f : hamSubmodule Ω) : Form E 1) x) = 0
    rw [hamVF_dMap]
    simp
  · -- S_0
    intro F G
    apply Subtype.ext
    exact proposition_3_6_2 Ω hΩ F G
  · -- S_L
    intro F f
    apply Subtype.ext
    funext x
    show fderiv ℝ (f : E → ℝ) x (hamVF Ω F x) +
        -(((dMap Ω hΩ f : hamSubmodule Ω) : Form E 1) x ![hamVF Ω F x] +
          (F : Form E 1) x ![hamVF Ω ((dMap Ω hΩ f : hamSubmodule Ω) : Form E 1) x]) = -0
    rw [hamVF_dMap, hgrad]
    simp [slot_zero]
  · -- S_R
    intro f F
    apply Subtype.ext
    funext x
    show (0 : ℝ) + -((F : Form E 1) x ![hamVF Ω ((dMap Ω hΩ f : hamSubmodule Ω) : Form E 1) x] +
          ((dMap Ω hΩ f : hamSubmodule Ω) : Form E 1) x ![hamVF Ω F x]) =
        -(fderiv ℝ (f : E → ℝ) x (hamVF Ω F x))
    rw [hamVF_dMap, hgrad]
    simp [slot_zero]
  · -- J_0
    intro F G H
    apply Subtype.ext
    have h := proposition_3_6_3 Ω hΩ F G H
    simp only [LinearMap.zero_apply, _root_.map_zero, add_zero, Submodule.coe_add]
    exact h
  · -- J_1
    intro F G f
    apply Subtype.ext
    have h := mixed_jacobi Ω hΩ F G f
    simp only [LinearMap.zero_apply, add_zero, Submodule.coe_add]
    exact h
  · -- J_2
    intro F f H
    simp
  · -- J_3
    intro f G H
    simp
  · -- diagram_1
    intro w x y z
    simp
  · -- diagram_2
    intro x y z
    simp
  · -- diagram_3
    intro F G H
    apply Subtype.ext
    have h := diagram_three Ω hΩ F G H
    simp only [LinearMap.zero_apply, sub_zero, zero_add, Submodule.coe_add]
    exact h.symm
  · -- diagram_4
    intro F G H
    have hsymm : ∀ A B : hamSubmodule Ω, SMap Ω hΩ A B = SMap Ω hΩ B A := by
      intro A B
      apply Subtype.ext
      funext x
      show -((B : Form E 1) x ![hamVF Ω A x] + (A : Form E 1) x ![hamVF Ω B x]) =
        -((A : Form E 1) x ![hamVF Ω B x] + (B : Form E 1) x ![hamVF Ω A x])
      ring
    show SMap Ω hΩ F _ - SMap Ω hΩ _ F = 0
    rw [hsymm, sub_self]
