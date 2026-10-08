-- Prove2me | solution 1 for ConvexRiskFn.Cont.directional_derivative_props
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T04:16:34.427977+00:00
-- url     : https://prove2.me/submissions/fac1c63a-ddb3-48d5-9b02-9cee05a60d61

import Definitions.Def_ConvexRiskFn_Cont_Setting
set_option autoImplicit false
open Filter Topology Set
namespace RiskDerivative

 theorem realConvexDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : E → EReal) (hρ : ConvexRiskFn.Cont.IsProper ρ)
    (h1 : ConvexRiskFn.Dual.A1 ρ) :
    ConvexOn ℝ (ConvexRiskFn.Dual.dom ρ) (fun x => (ρ x).toReal) := by
  let C := ConvexRiskFn.Dual.dom ρ
  let f := fun x => (ρ x).toReal
  have hfinite (x:E) (hx:x∈C) : (f x : EReal)=ρ x :=
    EReal.coe_toReal (ne_of_lt hx) (ne_of_gt (hρ.1 x))
  have hd : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    have ha1 : a ≤ 1 := by linarith
    have h := h1 x y a ha ha1
    have hb' : 1-a=b := by linarith
    rw [hb',← hfinite x hx,← hfinite y hy,← EReal.coe_mul,← EReal.coe_mul,
      ← EReal.coe_add] at h
    exact lt_of_le_of_lt h (EReal.coe_lt_top _)
  refine ⟨hd,?_⟩
  intro x hx y hy a b ha hb hab
  have h := h1 x y a ha (by linarith)
  have hb' : 1-a=b := by linarith
  rw [hb',← hfinite x hx,← hfinite y hy,← hfinite _ (hd hx hy ha hb hab),
    ← EReal.coe_mul,← EReal.coe_mul,← EReal.coe_add,EReal.coe_le_coe_iff] at h
  exact h

theorem directionalLimit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : E → EReal) (hρ : ConvexRiskFn.Cont.IsProper ρ)
    (h1 : ConvexRiskFn.Dual.A1 ρ) (Xbar : E)
    (hXbar : Xbar ∈ interior (ConvexRiskFn.Dual.dom ρ)) (X : E) :
    ∃ d : ℝ, Tendsto (fun t : ℝ => ((ρ (Xbar+t•X)).toReal-(ρ Xbar).toReal)/t)
      (𝓝[>] 0) (𝓝 d) := by
  let C := ConvexRiskFn.Dual.dom ρ
  let f := fun x => (ρ x).toReal
  let S : Set ℝ := {t | Xbar+t•X ∈ C}
  let g := fun t : ℝ => f (Xbar+t•X)
  have hf := realConvexDomain ρ hρ h1
  have he (s t a b:ℝ) (hab:a+b=1) :
      a•(Xbar+s•X)+b•(Xbar+t•X)=Xbar+(a*s+b*t)•X := by
    calc
      _ = (a+b)•Xbar+(a*s+b*t)•X := by module
      _ = _ := by rw [hab,one_smul]
  have hg : ConvexOn ℝ S g := by
    have hs : Convex ℝ S := by
      intro s hs t ht a b ha hb hab
      have h := hf.1 hs ht ha hb hab
      rw [he s t a b hab] at h
      exact h
    refine ⟨hs,?_⟩
    intro s hs t ht a b ha hb hab
    have h := hf.2 hs ht ha hb hab
    rw [he s t a b hab] at h
    exact h
  have hc : Continuous (fun t : ℝ => Xbar+t•X) := by fun_prop
  have h0 : (0:ℝ) ∈ interior S := by
    apply mem_interior_iff_mem_nhds.mpr
    have hnhds : C ∈ 𝓝 (Xbar+(0:ℝ)•X) := by
      simpa [C] using mem_interior_iff_mem_nhds.mp hXbar
    have h := (hc.continuousAt (x:=0)).preimage_mem_nhds hnhds
    simpa only [Set.preimage,S] using h
  refine ⟨derivWithin g (Ioi 0) 0,?_⟩
  simpa only [slope_fun_def_field,sub_zero,g,f,zero_smul,add_zero] using
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0:ℝ) ∉ Ioi 0)).mp
      (hg.hasDerivWithinAt_rightDeriv_of_mem_interior h0)

end RiskDerivative
#print axioms RiskDerivative.directionalLimit

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : E → EReal) (hρ : ConvexRiskFn.Cont.IsProper ρ)
    (h1 : ConvexRiskFn.Dual.A1 ρ) (Xbar : E)
    (hXbar : Xbar ∈ interior (ConvexRiskFn.Dual.dom ρ)) :
    ∃ δ : E → ℝ,
      (∀ X, Tendsto (fun t : ℝ => ((ρ (Xbar+t•X)).toReal-(ρ Xbar).toReal)/t)
        (𝓝[>] 0) (𝓝 (δ X))) ∧
      (∀ X t, 0<t → δ (t•X)=t*δ X) ∧
      ConvexOn ℝ univ δ ∧
      ∀ X, ρ Xbar+(δ (X-Xbar):EReal)≤ρ X := by
  classical
  let C := ConvexRiskFn.Dual.dom ρ
  let f := fun x => (ρ x).toReal
  let q := fun (X:E) (t:ℝ) => (f (Xbar+t•X)-f Xbar)/t
  have hf := RiskDerivative.realConvexDomain ρ hρ h1
  choose δ hlim using fun X => RiskDerivative.directionalLimit ρ hρ h1 Xbar hXbar X
  have hfinite (x:E) (hx:x∈C) : (f x:EReal)=ρ x :=
    EReal.coe_toReal (ne_of_lt hx) (ne_of_gt (hρ.1 x))
  have hnear (X:E) : ∀ᶠ t : ℝ in 𝓝[>] 0, Xbar+t•X∈C := by
    have hc : Continuous (fun t:ℝ => Xbar+t•X) := by fun_prop
    have hnhds : C ∈ 𝓝 (Xbar+(0:ℝ)•X) := by
      simpa [C] using mem_interior_iff_mem_nhds.mp hXbar
    change ((fun t:ℝ => Xbar+t•X) ⁻¹' C) ∈ 𝓝[>] 0
    exact nhdsWithin_le_nhds ((hc.continuousAt (x:=0)).preimage_mem_nhds hnhds)
  refine ⟨δ,hlim,?_,?_,?_⟩
  · intro X t ht
    have hparam : Tendsto (fun s:ℝ => t*s) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have hid : Tendsto (fun s:ℝ => s) (𝓝[>] 0) (𝓝 (0:ℝ)) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        simpa using (tendsto_const_nhds.mul hid :
          Tendsto (fun s:ℝ => t*s) (𝓝[>] 0) (𝓝 (t*0)))
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact mul_pos ht hs
    have hscaled := ((hlim X).comp hparam).const_mul t
    have heq : (fun s:ℝ => t*q X (t*s)) =ᶠ[𝓝[>] 0] q (t•X) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      dsimp [q]
      rw [smul_smul,mul_comm s t]
      field_simp
    exact tendsto_nhds_unique (hlim (t•X)) (hscaled.congr' heq)
  · refine ⟨convex_univ,?_⟩
    intro X _ Y _ a b ha hb hab
    have hlimR := ((hlim X).const_mul a).add ((hlim Y).const_mul b)
    apply le_of_tendsto_of_tendsto (hlim (a•X+b•Y)) hlimR
    filter_upwards [self_mem_nhdsWithin,hnear X,hnear Y] with t ht hx hy
    have h := hf.2 hx hy ha hb hab
    have he : a•(Xbar+t•X)+b•(Xbar+t•Y)=Xbar+t•(a•X+b•Y) := by
      calc
        _ = (a+b)•Xbar+t•(a•X+b•Y) := by module
        _ = _ := by rw [hab,one_smul]
    rw [he] at h
    dsimp [q,f] at *
    rw [← mul_div_assoc,← mul_div_assoc,← add_div]
    apply (div_le_div_iff_of_pos_right ht).mpr
    have hcancel : a*(ρ Xbar).toReal+b*(ρ Xbar).toReal=(ρ Xbar).toReal := by
      rw [← add_mul,hab,one_mul]
    nlinarith [hcancel]
  · intro X
    by_cases hx : ρ X=⊤
    · simp [hx]
    have hxC : X∈C := lt_of_le_of_ne le_top hx
    have hbound : δ (X-Xbar) ≤ f X-f Xbar := by
      apply le_of_tendsto (hlim (X-Xbar))
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with t ht ht1
      have h := hf.2 (interior_subset hXbar) hxC (sub_nonneg.mpr ht1.le) ht.le (by ring)
      have he : (1-t)•Xbar+t•X=Xbar+t•(X-Xbar) := by module
      rw [he] at h
      change (f (Xbar+t•(X-Xbar))-f Xbar)/t ≤ f X-f Xbar
      apply (div_le_iff₀ ht).mpr
      simp only [smul_eq_mul] at h
      dsimp [f] at *
      nlinarith
    rw [← hfinite Xbar (interior_subset hXbar),← hfinite X hxC,← EReal.coe_add,
      EReal.coe_le_coe_iff]
    linarith

#print axioms solution

open ConvexRiskFn.Cont Filter Topology
namespace ConvexRiskFn.Cont

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : E → EReal) (hρ : IsProper ρ) (h1 : ConvexRiskFn.Dual.A1 ρ) (Xbar : E)
    (hXbar : Xbar ∈ interior (ConvexRiskFn.Dual.dom ρ)) :
    ∃ δ : E → ℝ,
      (∀ X : E, Tendsto (fun t : ℝ => ((ρ (Xbar + t • X)).toReal - (ρ Xbar).toReal) / t)
        (𝓝[>] 0) (𝓝 (δ X))) ∧
      (∀ X : E, ∀ t : ℝ, 0 < t → δ (t • X) = t * δ X) ∧
      ConvexOn ℝ Set.univ δ ∧
      (∀ X : E, ρ Xbar + ((δ (X - Xbar) : ℝ) : EReal) ≤ ρ X) := by
  exact solution ρ hρ h1 Xbar hXbar

end ConvexRiskFn.Cont

#print axioms solution
