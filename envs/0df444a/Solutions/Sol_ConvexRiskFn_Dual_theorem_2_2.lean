-- Prove2me | solution 1 for ConvexRiskFn.Dual.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T04:59:26.245195+00:00
-- url     : https://prove2.me/submissions/5df3b30a-c0ba-494b-b1d0-acf93c12a8ff

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

theorem affine_minorant_above {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] (ρ : E → EReal) (hp : IsProper ρ)
    (hcvx : A1 ρ) (hlsc : LowerSemicontinuous ρ) (X : E) (a : ℝ)
    (ha : (a:EReal)<ρ X) :
    ∃ (l : E →L[ℝ] ℝ) (b : ℝ), a<l X+b ∧ ∀ Y, ((l Y+b:ℝ):EReal)≤ρ Y := by
  obtain ⟨l0,b0,hm⟩ := exists_affine_minorant ρ hp hcvx hlsc
  have hout : (X,a)∉epi ρ := not_le.mpr ha
  obtain ⟨F,c,hpoint,hon⟩ := geometric_hahn_banach_point_closed
    (convex_epi ρ hp hcvx) (closed_epi ρ hlsc) hout
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
    have h := hon _ hh
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
    have h := hon p hp
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

end RiskDualEpigraph

theorem RiskRoot.representation {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    (S : PairedSpaces Ω E) (ρ : E → EReal) (hp : IsProper ρ)
    (hlsc : LowerSemicontinuous ρ) (hcvx : A1 ρ) :
    ∀ X,ρ X=⨆ μ∈dualDom S ρ, ((pair μ (S.toFun X):ℝ):EReal)-conj S ρ μ := by
  have hconjbot (μ:SignedMeasure Ω) : ⊥<conj S ρ μ := by
    obtain ⟨Y,hY⟩ := hp.2
    have he : (((ρ Y).toReal:ℝ):EReal)=ρ Y :=
      EReal.coe_toReal (ne_of_lt hY) (ne_of_gt (hp.1 Y))
    have h : ((pair μ (S.toFun Y):ℝ):EReal)-ρ Y≤conj S ρ μ :=
      le_iSup (fun Z:E => ((pair μ (S.toFun Z):ℝ):EReal)-ρ Z) Y
    rw [← he,← EReal.coe_sub] at h
    exact (EReal.bot_lt_coe _).trans_le h
  intro X
  apply le_antisymm
  · by_contra hn
    obtain ⟨a,ha,hρa⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
    obtain ⟨l,b,habove,hminor⟩ := RiskDualEpigraph.affine_minorant_above ρ hp hcvx hlsc X a hρa
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
    have hdom : μ∈dualDom S ρ := ⟨hμ,hupper.trans_lt (EReal.coe_lt_top _)⟩
    have hterm : (((l X+b:ℝ):EReal))≤((pair μ (S.toFun X):ℝ):EReal)-conj S ρ μ := by
      rw [← hpair X]
      have h := EReal.sub_le_sub (le_refl ((l X:ℝ):EReal)) hupper
      rw [← EReal.coe_sub,sub_neg_eq_add] at h
      exact h
    have hsup : ((pair μ (S.toFun X):ℝ):EReal)-conj S ρ μ≤
        ⨆ ν∈dualDom S ρ, ((pair ν (S.toFun X):ℝ):EReal)-conj S ρ ν :=
      le_iSup_of_le μ (le_iSup_of_le hdom le_rfl)
    exact ha.not_ge ((EReal.coe_lt_coe_iff.mpr habove).le.trans (hterm.trans hsup))
  · apply iSup_le
    intro μ
    apply iSup_le
    intro hμ
    by_cases ht : ρ X=⊤
    · simp [ht]
    have he : (((ρ X).toReal:ℝ):EReal)=ρ X :=
      EReal.coe_toReal ht (ne_of_gt (hp.1 X))
    have hc : (((conj S ρ μ).toReal:ℝ):EReal)=conj S ρ μ :=
      EReal.coe_toReal (ne_of_lt hμ.2) (ne_of_gt (hconjbot μ))
    have h : ((pair μ (S.toFun X):ℝ):EReal)-ρ X≤conj S ρ μ :=
      le_iSup (fun Y:E => ((pair μ (S.toFun Y):ℝ):EReal)-ρ Y) X
    rw [← he,← hc,← EReal.coe_sub,EReal.coe_le_coe_iff] at h
    rw [← he,← hc,← EReal.coe_sub,EReal.coe_le_coe_iff]
    linarith




private theorem pair_nonnegative {Ω : Type*} [MeasurableSpace Ω]
    (μ : SignedMeasure Ω) (hμ : 0 ≤ μ) (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω) :
    0 ≤ pair μ X := by
  let ν := μ.toMeasureOfZeroLE univ MeasurableSet.univ
    ((VectorMeasure.le_restrict_univ_iff_le _ _).mpr hμ)
  let j : JordanDecomposition Ω := ⟨ν,0,Measure.MutuallySingular.zero_right⟩
  have hj : j.toSignedMeasure=μ := by
    simp only [JordanDecomposition.toSignedMeasure,j,Measure.toSignedMeasure_zero,sub_zero]
    exact μ.toMeasureOfZeroLE_toSignedMeasure _
  have he : μ.toJordanDecomposition=j := by
    rw [← hj,JordanDecomposition.toJordanDecomposition_toSignedMeasure]
  unfold pair
  rw [he]
  change 0 ≤ (∫ ω, X ω ∂ν) - (∫ ω, X ω ∂(0:Measure Ω))
  simp only [integral_zero_measure,sub_zero]
  exact integral_nonneg hX

theorem RiskRoot.cone {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [AddCommGroup 𝒳]
    [Module ℝ 𝒳] [TopologicalSpace 𝒳] [IsTopologicalAddGroup 𝒳]
    [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    (S : PairedSpaces Ω 𝒳) (hC : CondC S) :
    Ypos S = {μ | μ ∈ S.Y ∧ ∀ X ∈ Xpos S, 0 ≤ pair μ (S.toFun X)} := by
  ext μ
  constructor
  · rintro ⟨hY,hμ⟩
    refine ⟨hY,?_⟩
    intro X hX
    exact pair_nonnegative μ hμ _ hX
  · rintro ⟨hY,h⟩
    refine ⟨hY,?_⟩
    by_contra hn
    obtain ⟨X,hX,hneg⟩ := hC μ hY hn
    exact (not_lt_of_ge (h X hX)) hneg



namespace RiskDual

theorem integrable_pos {Ω : Type*} [MeasurableSpace Ω] (μ : SignedMeasure Ω)
    (f : Ω → ℝ) (hf : Integrable f μ.totalVariation) :
    Integrable f μ.toJordanDecomposition.posPart := by
  apply hf.mono_measure
  rw [SignedMeasure.totalVariation]
  exact Measure.le_add_right le_rfl

theorem integrable_neg {Ω : Type*} [MeasurableSpace Ω] (μ : SignedMeasure Ω)
    (f : Ω → ℝ) (hf : Integrable f μ.totalVariation) :
    Integrable f μ.toJordanDecomposition.negPart := by
  apply hf.mono_measure
  rw [SignedMeasure.totalVariation]
  exact Measure.le_add_left le_rfl

theorem pair_add {Ω : Type*} [MeasurableSpace Ω] (μ : SignedMeasure Ω)
    (f g : Ω → ℝ) (hf : Integrable f μ.totalVariation) (hg : Integrable g μ.totalVariation) :
    pair μ (f+g)=pair μ f+pair μ g := by
  unfold pair
  simp only [Pi.add_apply]
  rw [integral_add (integrable_pos μ f hf) (integrable_pos μ g hg),
    integral_add (integrable_neg μ f hf) (integrable_neg μ g hg)]
  ring

theorem pair_smul {Ω : Type*} [MeasurableSpace Ω] (μ : SignedMeasure Ω)
    (a : ℝ) (f : Ω → ℝ) : pair μ (a•f)=a*pair μ f := by
  unfold pair
  simp only [Pi.smul_apply,smul_eq_mul,integral_const_mul]
  ring

theorem pair_const {Ω : Type*} [MeasurableSpace Ω] (μ : SignedMeasure Ω) (a : ℝ) :
    pair μ (fun _ => a)=a*μ Set.univ := by
  unfold pair
  rw [SignedMeasure.apply_eq_posPart_real_sub_negPart_real μ MeasurableSet.univ]
  simp only [integral_const,smul_eq_mul,MeasureTheory.measureReal_def]
  ring

noncomputable def pairingLinear {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (S : PairedSpaces Ω E) (μ : SignedMeasure Ω) (hμ : μ ∈ S.Y) : E →ₗ[ℝ] ℝ where
  toFun X := pair μ (S.toFun X)
  map_add' X Y := by
    rw [map_add,pair_add μ _ _ (S.integrable μ hμ X) (S.integrable μ hμ Y)]
  map_smul' a X := by
    rw [map_smul,pair_smul,smul_eq_mul]
    rfl

end RiskDual

theorem RiskRoot.nonnegInf {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    (S : PairedSpaces Ω E) (hC : CondC S) (ρ : E → EReal)
    (hp : IsProper ρ) (hA2 : A2 S ρ) (μ : SignedMeasure Ω) (hμ : μ ∈ S.Y)
    (hneg : ¬ (0≤μ)) : conj S ρ μ=⊤ := by
  obtain ⟨X,hX⟩ := hp.2
  obtain ⟨Z,hZ,hn⟩ := hC μ hμ hneg
  let l := RiskDual.pairingLinear S μ hμ
  have hnL : l Z<0 := hn
  have he : (((ρ X).toReal:ℝ):EReal)=ρ X := EReal.coe_toReal (ne_of_lt hX) (ne_of_gt (hp.1 X))
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro b
  let k := l X-(ρ X).toReal
  let t := max 0 ((b+1-k)/(-l Z))
  have ht : 0≤t := le_max_left _ _
  have hb : b+1≤k-t*l Z := by
    have h := (div_le_iff₀ (neg_pos.mpr hnL)).mp (le_max_right 0 ((b+1-k)/(-l Z)))
    change b+1-k≤t*(-l Z) at h
    nlinarith
  have hm : ρ (X-t•Z)≤ρ X := by
    apply hA2
    intro ω
    simp only [map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    exact sub_le_self _ (mul_nonneg ht (hZ ω))
  have heT : (((ρ (X-t•Z)).toReal:ℝ):EReal)=ρ (X-t•Z) :=
    EReal.coe_toReal (ne_of_lt (hm.trans_lt hX)) (ne_of_gt (hp.1 _))
  have hr : (ρ (X-t•Z)).toReal≤(ρ X).toReal := by
    rw [← he,← heT,EReal.coe_le_coe_iff] at hm
    exact hm
  have hterm : ((k-t*l Z:ℝ):EReal) ≤
      ((pair μ (S.toFun (X-t•Z)):ℝ):EReal)-ρ (X-t•Z) := by
    rw [← heT,← EReal.coe_sub,EReal.coe_le_coe_iff]
    change k-t*l Z≤l (X-t•Z)-(ρ (X-t•Z)).toReal
    rw [map_sub,map_smul,smul_eq_mul]
    dsimp [k]
    linarith
  have hle : ((b+1:ℝ):EReal)≤conj S ρ μ :=
    (EReal.coe_le_coe_iff.mpr hb).trans (hterm.trans
      (le_iSup (fun Y:E => ((pair μ (S.toFun Y):ℝ):EReal)-ρ Y) (X-t•Z)))
  exact (EReal.coe_lt_coe_iff.mpr (by linarith : b<b+1)).trans_le hle



theorem RiskRoot.massInf {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    (S : PairedSpaces Ω E) (one : E) (hone : S.toFun one=fun _ => 1)
    (ρ : E → EReal) (hp : IsProper ρ) (hA3 : A3 one ρ)
    (μ : SignedMeasure Ω) (hμ : μ ∈ S.Y) (hmass : μ Set.univ ≠ 1) :
    conj S ρ μ=⊤ := by
  obtain ⟨X,hX⟩ := hp.2
  have he : (((ρ X).toReal:ℝ):EReal)=ρ X := EReal.coe_toReal (ne_of_lt hX) (ne_of_gt (hp.1 X))
  let l := RiskDual.pairingLinear S μ hμ
  have honeL : l one=μ Set.univ := by
    change pair μ (S.toFun one)=μ Set.univ
    rw [hone]
    simpa using RiskDual.pair_const μ 1
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro b
  let k : ℝ := l X-(ρ X).toReal
  let a : ℝ := (b+1-k)/(μ Set.univ-1)
  have hv : ρ (X+a•one)=(((ρ X).toReal+a:ℝ):EReal) := by
    rw [hA3,← he,← EReal.coe_add]
    simp only [EReal.toReal_coe]
  have hterm : ((pair μ (S.toFun (X+a•one)):ℝ):EReal)-ρ (X+a•one)=
      ((k+a*(μ Set.univ-1):ℝ):EReal) := by
    rw [hv,← EReal.coe_sub]
    congr 1
    change l (X+a•one)-((ρ X).toReal+a)=k+a*(μ Set.univ-1)
    rw [map_add,map_smul,honeL,smul_eq_mul]
    dsimp [k]
    ring
  have ha : k+a*(μ Set.univ-1)=b+1 := by
    dsimp [a]
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hmass)]
    ring
  have hle : ((b+1:ℝ):EReal)≤conj S ρ μ := by
    rw [← ha,← hterm]
    exact le_iSup (fun Y:E => ((pair μ (S.toFun Y):ℝ):EReal)-ρ Y) (X+a•one)
  exact (EReal.coe_lt_coe_iff.mpr (by linarith : b<b+1)).trans_le hle



theorem RiskRoot.indicator {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    (S : PairedSpaces Ω E) (ρ : E → EReal) (hp : IsProper ρ)
    (hlsc : LowerSemicontinuous ρ) (_hcvx : A1 ρ) (hA4 : A4 ρ) :
    ∀ μ ∈ S.Y,
      ((∀ X, ((pair μ (S.toFun X):ℝ):EReal)≤ρ X) → conj S ρ μ=0) ∧
      ((¬ ∀ X, ((pair μ (S.toFun X):ℝ):EReal)≤ρ X) → conj S ρ μ=⊤) := by
  have hzero : ρ 0=0 := by
    obtain ⟨X,hX⟩ := hp.2
    have he : (((ρ X).toReal:ℝ):EReal)=ρ X :=
      EReal.coe_toReal (ne_of_lt hX) (ne_of_gt (hp.1 X))
    have hc : ContinuousAt (fun t:ℝ => t•X) 0 := by fun_prop
    have hsc : LowerSemicontinuousAt (fun t:ℝ => ρ (t•X)) 0 := by
      have h : LowerSemicontinuousAt ρ ((fun t:ℝ => t•X) 0) := by simpa using hlsc (0:E)
      exact h.comp (g:=fun t:ℝ => t•X) hc
    have hreal : Tendsto (fun t:ℝ => t*(ρ X).toReal) (𝓝[>] 0) (𝓝 (0*(ρ X).toReal)) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).mul tendsto_const_nhds
    have hco : Tendsto (fun t:ℝ => ((t*(ρ X).toReal:ℝ):EReal)) (𝓝[>] 0) (𝓝 (0:EReal)) := by
      simpa only [Function.comp_def,zero_mul,EReal.coe_zero] using
        (continuous_coe_real_ereal.tendsto _).comp hreal
    have hlim : Tendsto (fun t:ℝ => ρ (t•X)) (𝓝[>] 0) (𝓝 (0:EReal)) := by
      apply hco.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hA4 t X ht,← he,← EReal.coe_mul]
      simp only [EReal.toReal_coe]
    have hle : ρ (0:E)≤0 := by
      have h := (hsc.lowerSemicontinuousWithinAt (Set.Ioi (0:ℝ))).le_liminf
      simpa [hlim.liminf_eq] using h
    have he0 : (((ρ (0:E)).toReal:ℝ):EReal)=ρ 0 :=
      EReal.coe_toReal (ne_of_lt (hle.trans_lt (by simp))) (ne_of_gt (hp.1 0))
    have h := hA4 2 (0:E) (by norm_num)
    rw [smul_zero,← he0,← EReal.coe_mul,EReal.coe_eq_coe_iff] at h
    have hr : (ρ (0:E)).toReal=0 := by linarith
    rw [← he0,hr,EReal.coe_zero]
  intro μ hμ
  let l := RiskDual.pairingLinear S μ hμ
  constructor
  · intro hdom
    apply le_antisymm
    · apply iSup_le
      intro X
      exact EReal.sub_nonpos.mpr (hdom X)
    · have h : ((pair μ (S.toFun (0:E)):ℝ):EReal)-ρ (0:E)≤conj S ρ μ :=
        le_iSup (fun X:E => ((pair μ (S.toFun X):ℝ):EReal)-ρ X) (0:E)
      have hpzero : pair μ (S.toFun (0:E))=0 := by simp [pair]
      simpa only [hpzero,hzero,EReal.coe_zero,sub_zero] using h
  · intro hbad
    push Not at hbad
    obtain ⟨X,hX⟩ := hbad
    have he : (((ρ X).toReal:ℝ):EReal)=ρ X :=
      EReal.coe_toReal (ne_of_lt (hX.trans (EReal.coe_lt_top _))) (ne_of_gt (hp.1 X))
    have hd : 0<l X-(ρ X).toReal := by
      rw [← he,EReal.coe_lt_coe_iff] at hX
      exact sub_pos.mpr hX
    apply (EReal.eq_top_iff_forall_lt _).mpr
    intro b
    let t := max 1 ((b+1)/(l X-(ρ X).toReal))
    have ht : 0<t := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)
    have hb : b+1≤t*(l X-(ρ X).toReal) :=
      (div_le_iff₀ hd).mp (le_max_right 1 _)
    have hterm : ((pair μ (S.toFun (t•X)):ℝ):EReal)-ρ (t•X)=
        ((t*(l X-(ρ X).toReal):ℝ):EReal) := by
      rw [hA4 t X ht,← he,← EReal.coe_mul,← EReal.coe_sub]
      congr 1
      change l (t•X)-t*(ρ X).toReal=t*(l X-(ρ X).toReal)
      rw [map_smul,smul_eq_mul]
      ring
    have hle : ((b+1:ℝ):EReal)≤conj S ρ μ :=
      (EReal.coe_le_coe_iff.mpr hb).trans (hterm.symm.le.trans
        (le_iSup (fun Y:E => ((pair μ (S.toFun Y):ℝ):EReal)-ρ Y) (t•X)))
    exact (EReal.coe_lt_coe_iff.mpr (by linarith : b<b+1)).trans_le hle



private theorem sup_add_real {ι : Type*} (A : Set ι) (f : ι → EReal) (a : ℝ) :
    (⨆ i∈A,f i)+(a:EReal)=⨆ i∈A,f i+(a:EReal) := by
  apply le_antisymm
  · apply (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot a)) (.inl (EReal.coe_ne_top a))).mp
    apply iSup_le
    intro i
    apply iSup_le
    intro hi
    apply (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot a)) (.inl (EReal.coe_ne_top a))).mpr
    exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)
  · apply iSup_le
    intro i
    apply iSup_le
    intro hi
    exact add_le_add (le_iSup_of_le i (le_iSup_of_le hi le_rfl)) le_rfl

private theorem sup_mul_real {ι : Type*} (A : Set ι) (f : ι → EReal) (a : ℝ) (ha : 0<a) :
    (a:EReal)*(⨆ i∈A,f i)=⨆ i∈A,(a:EReal)*f i := by
  apply le_antisymm
  · rw [mul_comm]
    apply (EReal.le_div_iff_mul_le (EReal.coe_pos.mpr ha) (EReal.coe_ne_top a)).mp
    apply iSup_le
    intro i
    apply iSup_le
    intro hi
    apply (EReal.le_div_iff_mul_le (EReal.coe_pos.mpr ha) (EReal.coe_ne_top a)).mpr
    rw [mul_comm]
    exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)
  · apply iSup_le
    intro i
    apply iSup_le
    intro hi
    exact mul_le_mul_of_nonneg_left (le_iSup_of_le i (le_iSup_of_le hi le_rfl))
      (EReal.coe_nonneg.mpr ha.le)

theorem solution {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    (S : PairedSpaces Ω E) (hC : CondC S) (ρ : E → EReal)
    (hp : IsProper ρ) (hlsc : LowerSemicontinuous ρ) (hcvx : A1 ρ) :
    (∀ X,ρ X=⨆ μ∈dualDom S ρ,((pair μ (S.toFun X):ℝ):EReal)-conj S ρ μ) ∧
    (A2 S ρ ↔ ∀ μ∈dualDom S ρ,0≤μ) ∧
    (∀ one:E,S.toFun one=(fun _ => 1) →
      (A3 one ρ ↔ ∀ μ∈dualDom S ρ,μ Set.univ=1)) ∧
    (A4 ρ ↔ ∀ X,ρ X=⨆ μ∈dualDom S ρ,((pair μ (S.toFun X):ℝ):EReal)) := by
  have hrep := RiskRoot.representation S ρ hp hlsc hcvx
  have hconjbot (μ:SignedMeasure Ω) : ⊥<conj S ρ μ := by
    obtain ⟨Y,hY⟩ := hp.2
    have he : (((ρ Y).toReal:ℝ):EReal)=ρ Y :=
      EReal.coe_toReal (ne_of_lt hY) (ne_of_gt (hp.1 Y))
    have h : ((pair μ (S.toFun Y):ℝ):EReal)-ρ Y≤conj S ρ μ :=
      le_iSup (fun Z:E => ((pair μ (S.toFun Z):ℝ):EReal)-ρ Z) Y
    rw [← he,← EReal.coe_sub] at h
    exact (EReal.bot_lt_coe _).trans_le h
  refine ⟨hrep,⟨?_,?_⟩,?_,⟨?_,?_⟩⟩
  · intro hm μ hμ
    by_contra hn
    have h := RiskRoot.nonnegInf S hC ρ hp hm μ hμ.1 hn
    have hlt := hμ.2
    rw [h] at hlt
    exact (lt_irrefl _ hlt)
  · intro hm X Y hXY
    rw [hrep X,hrep Y]
    apply iSup_le
    intro μ
    apply iSup_le
    intro hμ
    have hpos : 0≤pair μ (S.toFun (Y-X)) := pair_nonnegative μ (hm μ hμ) _ (by
      intro ω
      simp only [map_sub,Pi.sub_apply]
      exact sub_nonneg.mpr (hXY ω))
    let l := RiskDual.pairingLinear S μ hμ.1
    have hle : pair μ (S.toFun X)≤pair μ (S.toFun Y) := by
      change l X≤l Y
      change 0≤l (Y-X) at hpos
      rw [map_sub] at hpos
      linarith
    exact (EReal.sub_le_sub (EReal.coe_le_coe_iff.mpr hle) le_rfl).trans
      (le_iSup_of_le μ (le_iSup_of_le hμ le_rfl))
  · intro one hone
    constructor
    · intro hm μ hμ
      by_contra hn
      have h := RiskRoot.massInf S one hone ρ hp hm μ hμ.1 hn
      have hlt := hμ.2
      rw [h] at hlt
      exact (lt_irrefl _ hlt)
    · intro hm a X
      rw [hrep (X+a•one),hrep X,sup_add_real]
      apply iSup_congr
      intro μ
      apply iSup_congr
      intro hμ
      let l := RiskDual.pairingLinear S μ hμ.1
      have honeL : l one=1 := by
        change pair μ (S.toFun one)=1
        rw [hone]
        simpa [hm μ hμ] using RiskDual.pair_const μ 1
      have hpair : pair μ (S.toFun (X+a•one))=pair μ (S.toFun X)+a := by
        change l (X+a•one)=l X+a
        rw [map_add,map_smul,honeL,smul_eq_mul,mul_one]
      have hc : (((conj S ρ μ).toReal:ℝ):EReal)=conj S ρ μ :=
        EReal.coe_toReal (ne_of_lt hμ.2) (ne_of_gt (hconjbot μ))
      rw [hpair,← hc,← EReal.coe_sub,← EReal.coe_sub,← EReal.coe_add]
      congr 1
      ring
  · intro hhom X
    rw [hrep X]
    apply iSup_congr
    intro μ
    apply iSup_congr
    intro hμ
    have hzero : conj S ρ μ=0 := by
      by_cases hbound : ∀ Y,((pair μ (S.toFun Y):ℝ):EReal)≤ρ Y
      · exact (RiskRoot.indicator S ρ hp hlsc hcvx hhom μ hμ.1).1 hbound
      · have h := (RiskRoot.indicator S ρ hp hlsc hcvx hhom μ hμ.1).2 hbound
        have hlt := hμ.2
        rw [h] at hlt
        exact False.elim (lt_irrefl _ hlt)
    simp [hzero]
  · intro hsup t X ht
    rw [hsup (t•X),hsup X,sup_mul_real _ _ t ht]
    apply iSup_congr
    intro μ
    apply iSup_congr
    intro hμ
    let l := RiskDual.pairingLinear S μ hμ.1
    have hpair : pair μ (S.toFun (t•X))=t*pair μ (S.toFun X) := by
      change l (t•X)=t*l X
      rw [map_smul,smul_eq_mul]
    rw [hpair,EReal.coe_mul]

#print axioms solution

open ConvexRiskFn.Dual Filter Topology
namespace ConvexRiskFn.Dual

/-- Theorem 2.2, p. 435: let `ρ : 𝒳 → ℝ̄` be proper, lower semicontinuous and convex, and let
`𝒜 = dom(ρ*)`. Then `ρ(X) = sup_{μ ∈ 𝒜} {⟨μ, X⟩ − ρ*(μ)}` for all `X` (2.6), and
(i) (A2) holds iff every `μ ∈ 𝒜` is nonnegative; (ii) (A3) holds iff `μ(Ω) = 1` for every
`μ ∈ 𝒜`; (iii) (A4) holds iff `ρ(X) = sup_{μ ∈ 𝒜} ⟨μ, X⟩` for all `X` (2.7).
Condition (C) is the standing assumption of §2. Part (ii) is stated for every `one ∈ 𝒳` that is
the constant function `1` (needed for (A3) to make sense); parts (2.6), (i), (iii) do not need
constants in `𝒳`. -/
example {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [AddCommGroup 𝒳] [Module ℝ 𝒳]
    [TopologicalSpace 𝒳] [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    (S : PairedSpaces Ω 𝒳) (hC : CondC S)
    (ρ : 𝒳 → EReal) (hp : IsProper ρ) (hlsc : LowerSemicontinuous ρ) (hcvx : A1 ρ) :
    (∀ X, ρ X = ⨆ μ ∈ dualDom S ρ, ((pair μ (S.toFun X) : ℝ) : EReal) - conj S ρ μ) ∧
    (A2 S ρ ↔ ∀ μ ∈ dualDom S ρ, 0 ≤ μ) ∧
    (∀ one : 𝒳, S.toFun one = (fun _ => 1) →
      (A3 one ρ ↔ ∀ μ ∈ dualDom S ρ, μ Set.univ = 1)) ∧
    (A4 ρ ↔ ∀ X, ρ X = ⨆ μ ∈ dualDom S ρ, ((pair μ (S.toFun X) : ℝ) : EReal)) := by
  exact solution S hC ρ hp hlsc hcvx
end ConvexRiskFn.Dual

#print axioms solution
