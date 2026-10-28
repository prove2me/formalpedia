-- Prove2me | solution 2 for ConvexRiskFn.Cont.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:24:27.464909+00:00
-- url     : https://prove2.me/submissions/f4518691-50b7-4c63-a26f-d29feef322a9

import Mathlib
import Definitions.Def_ConvexRiskFn_Cont_Setting
import Theorems.Thm_ConvexRiskFn_Cont_lsc_of_mem_subdiff
import Theorems.Thm_ConvexRiskFn_Cont_positive_functional_continuous

-- carved verbatim out of submission 9e857c59-e8ff-4c81-b388-38e1881b301a, lines 374-406

section
set_option autoImplicit false
open ConvexRiskFn.Cont Filter Topology Set

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

theorem RiskDerivative.directionalDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
  have hf := realConvexDomain ρ hρ h1
  choose δ hlim using fun X => directionalLimit ρ hρ h1 Xbar hXbar X
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

theorem RiskRoot.algebraicSubgradient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : E → EReal) (hρ : ConvexRiskFn.Cont.IsProper ρ)
    (h1 : ConvexRiskFn.Dual.A1 ρ) (Xbar : E)
    (hXbar : Xbar ∈ interior (ConvexRiskFn.Dual.dom ρ)) :
    ∃ l : E →ₗ[ℝ] ℝ, ConvexRiskFn.Cont.IsAlgSubgradient ρ Xbar l := by
  obtain ⟨δ,_,hhom,hconv,hsupport⟩ :=
    RiskDerivative.directionalDerivative ρ hρ h1 Xbar hXbar
  have hzero : δ 0=0 := by
    have h := hhom 0 2 (by norm_num)
    rw [smul_zero] at h
    linarith
  have hadd : ∀ x y, δ (x+y)≤δ x+δ y := by
    intro x y
    have h := hconv.2 (mem_univ x) (mem_univ y)
      (show 0≤(1/2:ℝ) by norm_num) (show 0≤(1/2:ℝ) by norm_num) (by norm_num)
    have h2 := hhom ((1/2:ℝ)•x+(1/2:ℝ)•y) 2 (by norm_num)
    have he : (2:ℝ)•((1/2:ℝ)•x+(1/2:ℝ)•y)=x+y := by module
    rw [he] at h2
    simp only [smul_eq_mul] at h
    nlinarith
  let p : E →ₗ.[ℝ] ℝ := (0 : E →ₗ[ℝ] ℝ).toPMap ⊥
  have hp : ∀ x : p.domain, p x≤δ x := by
    intro x
    have hx : (x:E)=0 := (Submodule.mem_bot ℝ).mp x.property
    change (0:E →ₗ[ℝ] ℝ) (x:E) ≤ δ (x:E)
    simp [hx,hzero]
  obtain ⟨l,_,hle⟩ := exists_extension_of_le_sublinear p δ
    (fun c hc x => hhom x c hc) hadd hp
  refine ⟨l,?_⟩
  intro X
  exact (add_le_add_right (EReal.coe_le_coe_iff.mpr (hle (X-Xbar))) (ρ Xbar)).trans
    (hsupport X)

theorem RiskRoot.nonneg {E : Type*} [AddCommGroup E] [Module ℝ E] [PartialOrder E]
    [IsOrderedAddMonoid E] (ρ : E → EReal) (h2 : A2 ρ) (Xbar : E)
    (hdom : Xbar ∈ ConvexRiskFn.Dual.dom ρ) (hbot : ⊥ < ρ Xbar) (l : E →ₗ[ℝ] ℝ)
    (hl : IsAlgSubgradient ρ Xbar l) :
    ∀ X : E, 0 ≤ X → 0 ≤ l X := by
  intro X hX
  have hle : Xbar-X ≤ Xbar := sub_le_self Xbar hX
  have hm := h2 (Xbar-X) Xbar hle
  have hs := (hl (Xbar-X)).trans hm
  have he : Xbar-X-Xbar = -X := by abel
  rw [he,map_neg] at hs
  have hfin : ρ Xbar ≠ ⊤ := ne_of_lt (show ρ Xbar < ⊤ from hdom)
  have hnbot : ρ Xbar ≠ ⊥ := ne_of_gt hbot
  have hc : ρ Xbar=(((ρ Xbar).toReal:ℝ):EReal) := (EReal.coe_toReal hfin hnbot).symm
  rw [hc,← EReal.coe_add,EReal.coe_le_coe_iff] at hs
  linarith

private theorem convex_lsc_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {C : Set E} {f : E → ℝ}
    (hC : IsOpen C) (hf : ConvexOn ℝ C f) (hlsc : LowerSemicontinuousOn f C) :
    ContinuousOn f C := by
  classical
  by_cases hne : C.Nonempty
  · let : Nonempty C := hne.to_subtype
    let : BaireSpace C := hC.baireSpace
    let s : ℕ → Set C := fun n => {x | f x ≤ (n : ℝ)}
    have hc : ∀ n, IsClosed (s n) := fun n =>
      (lowerSemicontinuous_restrict_iff.mpr hlsc).isClosed_preimage (n:ℝ)
    have hcover : ⋃ n, s n = univ := by
      apply eq_univ_of_forall
      intro x
      obtain ⟨n,hn⟩ := exists_nat_gt (f x)
      exact mem_iUnion.mpr ⟨n,hn.le⟩
    obtain ⟨n,y,hy⟩ := nonempty_interior_of_iUnion_of_closed hc hcover
    let V : Set E := Subtype.val '' interior (s n)
    have ho : IsOpen V := hC.isOpenMap_subtype_val _ isOpen_interior
    have hyV : (y:E) ∈ V := mem_image_of_mem _ hy
    have hb : ∀ z ∈ V, f z ≤ (n:ℝ) := by
      rintro z ⟨w,hw,rfl⟩
      exact (show w ∈ s n from interior_subset hw)
    apply ((hf.continuousOn_tfae hC hne).out 3 1).mp
    refine ⟨y,y.property,(n:ℝ),?_⟩
    exact (ho.eventually_mem hyV).mono (fun z hz => hb z hz)
  · simp [Set.not_nonempty_iff_eq_empty.mp hne]

theorem RiskRoot.interiorContinuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (ρ : E → EReal) (hρ : ConvexRiskFn.Cont.IsProper ρ)
    (h1 : ConvexRiskFn.Dual.A1 ρ)
    (hlsc : ∀ X ∈ interior (ConvexRiskFn.Dual.dom ρ), LowerSemicontinuousAt ρ X) :
    ContinuousOn ρ (interior (ConvexRiskFn.Dual.dom ρ)) := by
  let C := ConvexRiskFn.Dual.dom ρ
  let f := fun x => (ρ x).toReal
  have hfinite (x:E) (hx:x∈C) : (f x : EReal)=ρ x :=
    EReal.coe_toReal (ne_of_lt hx) (ne_of_gt (hρ.1 x))
  have hconv : ConvexOn ℝ C f := by
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
  have hlow : LowerSemicontinuousOn f (interior C) := by
    intro x hx
    apply LowerSemicontinuousAt.lowerSemicontinuousWithinAt
    rw [lowerSemicontinuousAt_iff]
    intro b hb
    have he : (b:EReal)<ρ x := by
      rw [← hfinite x (interior_subset hx),EReal.coe_lt_coe_iff]
      exact hb
    have h := (lowerSemicontinuousAt_iff.mp (hlsc x hx)) (b:EReal) he
    filter_upwards [h,isOpen_interior.eventually_mem hx] with y hy hyC
    rwa [← hfinite y (interior_subset hyC),EReal.coe_lt_coe_iff] at hy
  have hc := convex_lsc_continuous isOpen_interior (hconv.subset interior_subset hconv.1.interior) hlow
  have hco : ContinuousOn (fun x => (f x:EReal)) (interior C) :=
    continuous_coe_real_ereal.comp_continuousOn hc
  exact hco.congr (fun x hx => (hfinite x (interior_subset hx)).symm)

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]
    (ρ : E → EReal) (hρ : IsProper ρ) (h1 : ConvexRiskFn.Dual.A1 ρ) (h2 : A2 ρ) :
    ContinuousOn ρ (interior (ConvexRiskFn.Dual.dom ρ)) ∧
    ∀ Xbar ∈ interior (ConvexRiskFn.Dual.dom ρ), (subdiff ρ Xbar).Nonempty := by
  have hsub : ∀ Xbar ∈ interior (ConvexRiskFn.Dual.dom ρ), (subdiff ρ Xbar).Nonempty := by
    intro Xbar hXbar
    obtain ⟨l,hl⟩ := RiskRoot.algebraicSubgradient ρ hρ h1 Xbar hXbar
    have hpos := RiskRoot.nonneg ρ h2 Xbar (interior_subset hXbar) (hρ.1 Xbar) l hl
    have hc := ConvexRiskFn.Cont.positive_functional_continuous l hpos
    let L : E →L[ℝ] ℝ := ⟨l,hc⟩
    exact ⟨L,hl⟩
  refine ⟨RiskRoot.interiorContinuous ρ hρ h1 ?_,hsub⟩
  intro Xbar hXbar
  obtain ⟨l,hl⟩ := hsub Xbar hXbar
  exact ConvexRiskFn.Cont.lsc_of_mem_subdiff ρ Xbar l hl

end
