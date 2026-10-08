-- Prove2me | solution 1 for ConvexRiskFn.Dual.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T04:53:58.925349+00:00
-- url     : https://prove2.me/submissions/b77af276-c4a1-47e5-8d45-deab6508df1e

import Definitions.Def_ConvexRiskFn_Dual_Setting
set_option autoImplicit false
open MeasureTheory ConvexRiskFn.Dual Filter Topology Set
namespace RiskDualEpigraph

def epi {E : Type*} (ρ : E → EReal) : Set (E × ℝ) := {p | ρ p.1≤(p.2:EReal)}

theorem convex_epi {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (ρ : E → EReal) (hp : IsProper ρ) (hcvx : A1 ρ) : Convex ℝ (epi ρ) := by
  intro x hx y hy a b ha hb hab
  change ρ x.1≤(x.2:EReal) at hx
  change ρ y.1≤(y.2:EReal) at hy
  have hfinite (z:E) (r:ℝ) (h : ρ z≤(r:EReal)) :
      (((ρ z).toReal:ℝ):EReal)=ρ z :=
    EReal.coe_toReal (ne_of_lt (h.trans_lt (EReal.coe_lt_top _))) (ne_of_gt (hp.1 z))
  have hxreal : (ρ x.1).toReal≤x.2 := by
    rw [← hfinite x.1 x.2 hx,EReal.coe_le_coe_iff] at hx
    exact hx
  have hyreal : (ρ y.1).toReal≤y.2 := by
    rw [← hfinite y.1 y.2 hy,EReal.coe_le_coe_iff] at hy
    exact hy
  have h := hcvx x.1 y.1 a ha (by linarith)
  have hb' : 1-a=b := by linarith
  rw [hb',← hfinite x.1 x.2 hx,← hfinite y.1 y.2 hy,← EReal.coe_mul,
    ← EReal.coe_mul,← EReal.coe_add] at h
  change ρ (a•x.1+b•y.1)≤((a*x.2+b*y.2:ℝ):EReal)
  exact h.trans (EReal.coe_le_coe_iff.mpr (add_le_add
    (mul_le_mul_of_nonneg_left hxreal ha) (mul_le_mul_of_nonneg_left hyreal hb)))

theorem closed_epi {E : Type*} [TopologicalSpace E] (ρ : E → EReal)
    (hlsc : LowerSemicontinuous ρ) : IsClosed (epi ρ) := by
  have hc : Continuous (fun p:E×ℝ => (p.1,(p.2:EReal))) :=
    continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
  exact hlsc.isClosed_epigraph.preimage hc

theorem nonempty_epi {E : Type*} (ρ : E → EReal)
    (hp : (∀ X,⊥<ρ X) ∧ ∃ X,ρ X<⊤) : (epi ρ).Nonempty := by
  obtain ⟨X,hX⟩ := hp.2
  refine ⟨(X,(ρ X).toReal),?_⟩
  exact (EReal.coe_toReal (ne_of_lt hX) (ne_of_gt (hp.1 X))).symm.le

theorem exists_affine_minorant {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] (ρ : E → EReal) (hp : IsProper ρ)
    (hcvx : A1 ρ) (hlsc : LowerSemicontinuous ρ) :
    ∃ (l : E →L[ℝ] ℝ) (b : ℝ), ∀ Y, ((l Y+b:ℝ):EReal)≤ρ Y := by
  obtain ⟨X,hX⟩ := hp.2
  have he : (((ρ X).toReal:ℝ):EReal)=ρ X :=
    EReal.coe_toReal (ne_of_lt hX) (ne_of_gt (hp.1 X))
  have hout : (X,(ρ X).toReal-1)∉epi ρ := by
    change ¬ρ X≤(((ρ X).toReal-1:ℝ):EReal)
    rw [← he,EReal.coe_le_coe_iff]
    simp only [EReal.toReal_coe]
    linarith
  obtain ⟨F,c,hpoint,hon⟩ := geometric_hahn_banach_point_closed
    (convex_epi ρ hp hcvx) (closed_epi ρ hlsc) hout
  have hsplit (Y:E) (t:ℝ) : F (Y,t)=F (Y,0)+t*F (0,1) := by
    have hv : (Y,t)=(Y,0)+t•((0:E),(1:ℝ)) := by simp
    rw [hv,map_add,map_smul,smul_eq_mul]
  have hinside : (X,(ρ X).toReal)∈epi ρ := he.symm.le
  have hpos : 0<F ((0:E),(1:ℝ)) := by
    have h := hon _ hinside
    rw [hsplit] at hpoint h
    nlinarith
  let l : E →L[ℝ] ℝ := -(F (0,1))⁻¹ • (F.comp (ContinuousLinearMap.inl ℝ E ℝ))
  let b : ℝ := c/F (0,1)
  refine ⟨l,b,?_⟩
  intro Y
  by_cases ht : ρ Y=⊤
  · simp [ht]
  have heY : (((ρ Y).toReal:ℝ):EReal)=ρ Y :=
    EReal.coe_toReal ht (ne_of_gt (hp.1 Y))
  have h := hon (Y,(ρ Y).toReal) heY.symm.le
  rw [hsplit] at h
  have hbound : l Y+b≤(ρ Y).toReal := by
    have hid : l Y+b=(c-F (Y,0))/F (0,1) := by
      simp only [l,b,smul_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inl_apply,smul_eq_mul]
      field_simp
      ring
    rw [hid]
    apply (div_le_iff₀ hpos).mpr
    linarith
  rw [← heY,EReal.coe_le_coe_iff]
  exact hbound

theorem exists_affine_minorant_closed_superset {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] (ρ : E → EReal) (hp : IsProper ρ)
    (K : Set (E×ℝ)) (hKcvx : Convex ℝ K) (hKclosed : IsClosed K)
    (hsub : epi ρ ⊆ K) (X : E) (hX : ρ X<⊤) (a : ℝ) (hout : (X,a)∉K) :
    ∃ (l : E →L[ℝ] ℝ) (b : ℝ), ∀ Y, ((l Y+b:ℝ):EReal)≤ρ Y := by
  have he : (((ρ X).toReal:ℝ):EReal)=ρ X :=
    EReal.coe_toReal (ne_of_lt hX) (ne_of_gt (hp.1 X))
  have hb : a<(ρ X).toReal := by
    have h : (a:EReal)<ρ X := lt_of_not_ge (fun h => hout (hsub h))
    rw [← he,EReal.coe_lt_coe_iff] at h
    exact h
  obtain ⟨F,c,hpoint,hon⟩ := geometric_hahn_banach_point_closed
    hKcvx hKclosed hout
  have hsplit (Y:E) (t:ℝ) : F (Y,t)=F (Y,0)+t*F (0,1) := by
    have hv : (Y,t)=(Y,0)+t•((0:E),(1:ℝ)) := by simp
    rw [hv,map_add,map_smul,smul_eq_mul]
  have hinside : (X,(ρ X).toReal)∈epi ρ := he.symm.le
  have hpos : 0<F ((0:E),(1:ℝ)) := by
    have h := hon _ (hsub hinside)
    rw [hsplit] at hpoint h
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (sub_pos.mpr hb).le (le_of_not_gt hn)
    nlinarith
  let l : E →L[ℝ] ℝ := -(F (0,1))⁻¹ • (F.comp (ContinuousLinearMap.inl ℝ E ℝ))
  let b : ℝ := c/F (0,1)
  refine ⟨l,b,?_⟩
  intro Y
  by_cases ht : ρ Y=⊤
  · simp [ht]
  have heY : (((ρ Y).toReal:ℝ):EReal)=ρ Y :=
    EReal.coe_toReal ht (ne_of_gt (hp.1 Y))
  have h := hon (Y,(ρ Y).toReal) (hsub heY.symm.le)
  rw [hsplit] at h
  have hbound : l Y+b≤(ρ Y).toReal := by
    have hid : l Y+b=(c-F (Y,0))/F (0,1) := by
      simp only [l,b,smul_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inl_apply,smul_eq_mul]
      field_simp
      ring
    rw [hid]
    apply (div_le_iff₀ hpos).mpr
    linarith
  rw [← heY,EReal.coe_le_coe_iff]
  exact hbound


theorem affine_minorant_above_closed_superset {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] (ρ : E → EReal) (hp : IsProper ρ)
    (K : Set (E×ℝ)) (hKcvx : Convex ℝ K) (hKclosed : IsClosed K)
    (hsub : epi ρ ⊆ K) (l0 : E →L[ℝ] ℝ) (b0 : ℝ)
    (hm : ∀ Y,((l0 Y+b0:ℝ):EReal)≤ρ Y) (X : E) (a : ℝ)
    (hout : (X,a)∉K) :
    ∃ (l : E →L[ℝ] ℝ) (b : ℝ), a<l X+b ∧ ∀ Y, ((l Y+b:ℝ):EReal)≤ρ Y := by
  obtain ⟨F,c,hpoint,hon⟩ := geometric_hahn_banach_point_closed
    hKcvx hKclosed hout
  have hsplit (Y:E) (t:ℝ) : F (Y,t)=F (Y,0)+t*F (0,1) := by
    have hv : (Y,t)=(Y,0)+t•((0:E),(1:ℝ)) := by simp
    rw [hv,map_add,map_smul,smul_eq_mul]
  have hcoef : 0≤F ((0:E),(1:ℝ)) := by
    by_contra hn
    have hv : F ((0:E),(1:ℝ))<0 := lt_of_not_ge hn
    obtain ⟨Y,hY⟩ := hp.2
    have he : (((ρ Y).toReal:ℝ):EReal)=ρ Y :=
      EReal.coe_toReal (ne_of_lt hY) (ne_of_gt (hp.1 Y))
    obtain ⟨n,hn⟩ := exists_nat_gt ((F (Y,(ρ Y).toReal)-c)/(-F (0,1)))
    have hnum := (div_lt_iff₀ (neg_pos.mpr hv)).mp hn
    have hh : (Y,(ρ Y).toReal+(n:ℝ))∈epi ρ := by
      change ρ Y≤(((ρ Y).toReal+(n:ℝ):ℝ):EReal)
      rw [← he,EReal.coe_le_coe_iff]
      simp only [EReal.toReal_coe]
      exact le_add_of_nonneg_right (Nat.cast_nonneg n)
    have h := hon _ (hsub hh)
    rw [hsplit] at h hnum
    nlinarith
  let D : ℝ := a-l0 X-b0
  let ε : ℝ := (c-F (X,a))/(2*(|D|+1))
  have hε : 0<ε := div_pos (sub_pos.mpr hpoint) (by positivity)
  have hεeq : ε*(2*(|D|+1))=c-F (X,a) := by
    exact div_mul_cancel₀ _ (ne_of_gt (show 0<2*(|D|+1) by positivity))
  have hεD : ε*D<c-F (X,a) := by
    have h := mul_le_mul_of_nonneg_left (le_abs_self D) hε.le
    have hn := abs_nonneg D
    nlinarith
  let G : (E×ℝ) →L[ℝ] ℝ := F+ε•(ContinuousLinearMap.snd ℝ E ℝ-l0.comp (ContinuousLinearMap.fst ℝ E ℝ))
  let r : ℝ := c+ε*b0
  have hGpoint : G (X,a)<r := by
    change F (X,a)+ε*(a-l0 X)<c+ε*b0
    dsimp [D] at hεD
    nlinarith
  have hGon : ∀ p∈epi ρ,r<G p := by
    intro p hp
    have h := hon p (hsub hp)
    have hl : l0 p.1+b0≤p.2 := by
      have he := (hm p.1).trans hp
      exact EReal.coe_le_coe_iff.mp he
    change c+ε*b0<F p+ε*(p.2-l0 p.1)
    have hm := mul_le_mul_of_nonneg_left hl hε.le
    nlinarith
  have hGcoef : 0<G ((0:E),(1:ℝ)) := by
    change 0<F (0,1)+ε*(1-l0 0)
    rw [map_zero,sub_zero]
    linarith
  have hGsplit (Y:E) (t:ℝ) : G (Y,t)=G (Y,0)+t*G (0,1) := by
    have hv : (Y,t)=(Y,0)+t•((0:E),(1:ℝ)) := by simp
    rw [hv,map_add,map_smul,smul_eq_mul]
  let l : E →L[ℝ] ℝ := -(G (0,1))⁻¹ • (G.comp (ContinuousLinearMap.inl ℝ E ℝ))
  let b : ℝ := r/G (0,1)
  have hid (Y:E) : l Y+b=(r-G (Y,0))/G (0,1) := by
    simp only [l,b,smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply,smul_eq_mul]
    field_simp
    ring
  refine ⟨l,b,?_,?_⟩
  · rw [hid]
    apply (lt_div_iff₀ hGcoef).mpr
    rw [hGsplit] at hGpoint
    linarith
  · intro Y
    by_cases ht : ρ Y=⊤
    · simp [ht]
    have he : (((ρ Y).toReal:ℝ):EReal)=ρ Y :=
      EReal.coe_toReal ht (ne_of_gt (hp.1 Y))
    have h := hGon (Y,(ρ Y).toReal) he.symm.le
    rw [hGsplit] at h
    rw [← he,EReal.coe_le_coe_iff,hid]
    apply (div_le_iff₀ hGcoef).mpr
    linarith


theorem not_closure_epi_of_lt_hull {E : Type*} [TopologicalSpace E]
    (ρ : E → EReal) (X : E) (a : ℝ) (ha : (a:EReal)<lscHull ρ X) :
    (X,a)∉closure (epi ρ) := by
  obtain ⟨b,hab,hb⟩ := EReal.lt_iff_exists_real_btwn.mp ha
  have hnear : ∀ᶠ Y in 𝓝 X,(b:EReal)<ρ Y := eventually_lt_of_lt_liminf hb
  obtain ⟨U,hU,hUopen,hX⟩ := mem_nhds_iff.mp hnear
  intro hcl
  have ho : IsOpen (U ×ˢ Iio b) := hUopen.prod isOpen_Iio
  have hx : (X,a)∈U ×ˢ Iio b := ⟨hX,EReal.coe_lt_coe_iff.mp hab⟩
  obtain ⟨p,hp,hpepi⟩ := mem_closure_iff.mp hcl _ ho hx
  have hlow : (b:EReal)<ρ p.1 := hU hp.1
  have hupp : ρ p.1≤(p.2:EReal) := hpepi
  exact lt_asymm (hlow.trans_le hupp) (EReal.coe_lt_coe_iff.mpr hp.2)

end RiskDualEpigraph
#print axioms RiskDualEpigraph.affine_minorant_above_closed_superset
#print axioms RiskDualEpigraph.exists_affine_minorant_closed_superset
#print axioms RiskDualEpigraph.not_closure_epi_of_lt_hull

theorem solution {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    (S : PairedSpaces Ω E) (ρ : E → EReal) (hcvx : A1 ρ) (hp : IsProper ρ)
    (hlscp : ∀ X,⊥<lscHull ρ X) : biconj S ρ=lscHull ρ := by
  have hconjbot (μ:SignedMeasure Ω) : ⊥<conj S ρ μ := by
    obtain ⟨Y,hY⟩ := hp.2
    have he : (((ρ Y).toReal:ℝ):EReal)=ρ Y :=
      EReal.coe_toReal (ne_of_lt hY) (ne_of_gt (hp.1 Y))
    have h : ((pair μ (S.toFun Y):ℝ):EReal)-ρ Y≤conj S ρ μ :=
      le_iSup (fun Z:E => ((pair μ (S.toFun Z):ℝ):EReal)-ρ Z) Y
    rw [← he,← EReal.coe_sub] at h
    exact (EReal.bot_lt_coe _).trans_le h
  let K := closure (RiskDualEpigraph.epi ρ)
  have hKcvx : Convex ℝ K := (RiskDualEpigraph.convex_epi ρ hp hcvx).closure
  have hKclosed : IsClosed K := isClosed_closure
  have hsub : RiskDualEpigraph.epi ρ⊆K := subset_closure
  obtain ⟨Y0,hY0⟩ := hp.2
  obtain ⟨a0,_,ha0⟩ := EReal.lt_iff_exists_real_btwn.mp (hlscp Y0)
  obtain ⟨l0,b0,hbase⟩ := RiskDualEpigraph.exists_affine_minorant_closed_superset
    ρ hp K hKcvx hKclosed hsub Y0 hY0 a0
    (RiskDualEpigraph.not_closure_epi_of_lt_hull ρ Y0 a0 ha0)
  funext X
  apply le_antisymm
  · apply iSup_le
    intro μ
    by_cases ht : conj S ρ μ=⊤
    · simp [ht]
    have hc : (((conj S ρ μ).toReal:ℝ):EReal)=conj S ρ μ :=
      EReal.coe_toReal ht (ne_of_gt (hconjbot μ))
    let p : E → EReal := fun Y => ((pair μ (S.toFun Y)-(conj S ρ μ).toReal:ℝ):EReal)
    have hpρ : ∀ Y,p Y≤ρ Y := by
      intro Y
      by_cases hyt : ρ Y=⊤
      · simp [hyt]
      have he : (((ρ Y).toReal:ℝ):EReal)=ρ Y :=
        EReal.coe_toReal hyt (ne_of_gt (hp.1 Y))
      have h : ((pair μ (S.toFun Y):ℝ):EReal)-ρ Y≤conj S ρ μ :=
        le_iSup (fun Z:E => ((pair μ (S.toFun Z):ℝ):EReal)-ρ Z) Y
      rw [← he,← hc,← EReal.coe_sub,EReal.coe_le_coe_iff] at h
      change (((pair μ (S.toFun Y)-(conj S ρ μ).toReal:ℝ):EReal))≤ρ Y
      rw [← he,EReal.coe_le_coe_iff]
      linarith
    have hpc : Continuous p := continuous_coe_real_ereal.comp
      ((S.continuous_pair μ μ.property).sub continuous_const)
    have hlim : liminf p (𝓝 X)=p X := (hpc.tendsto X).liminf_eq
    have h : p X≤lscHull ρ X := by
      rw [← hlim]
      exact liminf_le_liminf (Eventually.of_forall hpρ)
    rw [← hc,← EReal.coe_sub]
    exact h
  · by_contra hn
    obtain ⟨a,ha,hulla⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
    obtain ⟨l,b,habove,hminor⟩ := RiskDualEpigraph.affine_minorant_above_closed_superset
      ρ hp K hKcvx hKclosed hsub l0 b0 hbase X a
      (RiskDualEpigraph.not_closure_epi_of_lt_hull ρ X a hulla)
    obtain ⟨μ,hμ,hpair⟩ := S.dual_rep l
    have hupper : conj S ρ μ≤((-b:ℝ):EReal) := by
      apply iSup_le
      intro Y
      by_cases ht : ρ Y=⊤
      · simp [ht]
      have he : (((ρ Y).toReal:ℝ):EReal)=ρ Y :=
        EReal.coe_toReal ht (ne_of_gt (hp.1 Y))
      have h := hminor Y
      rw [← he,EReal.coe_le_coe_iff] at h
      rw [← hpair Y,← he,← EReal.coe_sub,EReal.coe_le_coe_iff]
      linarith
    have hterm : (((l X+b:ℝ):EReal))≤((pair μ (S.toFun X):ℝ):EReal)-conj S ρ μ := by
      rw [← hpair X]
      have h := EReal.sub_le_sub (le_refl ((l X:ℝ):EReal)) hupper
      rw [← EReal.coe_sub,sub_neg_eq_add] at h
      exact h
    have hsup : ((pair μ (S.toFun X):ℝ):EReal)-conj S ρ μ≤biconj S ρ X :=
      le_iSup (fun ν:S.Y => ((pair ν (S.toFun X):ℝ):EReal)-conj S ρ ν) ⟨μ,hμ⟩
    exact ha.not_ge ((EReal.coe_lt_coe_iff.mpr habove).le.trans (hterm.trans hsup))

#print axioms solution

open ConvexRiskFn.Dual Filter Topology
namespace ConvexRiskFn.Dual

/-- Theorem 2.1 (Fenchel–Moreau), p. 435: for a convex proper `ρ : 𝒳 → ℝ̄` whose lower
semicontinuous hull never takes the value `−∞`, `ρ** = lsc(ρ)`. -/
example {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [AddCommGroup 𝒳] [Module ℝ 𝒳]
    [TopologicalSpace 𝒳] [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    (S : PairedSpaces Ω 𝒳) (ρ : 𝒳 → EReal) (hcvx : A1 ρ) (hp : IsProper ρ)
    (hlscp : ∀ X, ⊥ < lscHull ρ X) :
    biconj S ρ = lscHull ρ := by
  exact solution S ρ hcvx hp hlscp
end ConvexRiskFn.Dual

#print axioms solution
