-- Prove2me | solution 1 for BregmanPPA.IneqMult.lemmaA2
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T20:20:21.520018+00:00
-- url     : https://prove2.me/submissions/a6e8dd64-09cb-4189-a58e-d89c98be8613

import Definitions.Def_BregmanPPA_IneqMult_Program
set_option autoImplicit false
section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult
namespace BregmanIneqMultCodex
variable {m : ℕ}

theorem original_conjugate_support_bound (F : E m → EReal) (hp : IsProperFn F)
    (u v : E m) (hs : IsSubgradient F u v) :
    conjE F v ≤ (((inner ℝ u v-(F u).toReal : ℝ)) : EReal) := by
  have eu := EReal.coe_toReal hs.1 (hp.1 u)
  apply iSup_le
  intro q
  by_cases hqt : F q=⊤
  · simp only [hqt,EReal.sub_top]; exact bot_le
  have eq := EReal.coe_toReal hqt (hp.1 q)
  have hi := hs.2 q
  rw [← eu,← eq,← EReal.coe_add] at hi
  have hir := EReal.coe_le_coe_iff.mp hi
  rw [← eq,← EReal.coe_sub]
  apply EReal.coe_le_coe_iff.mpr
  simp only [inner_sub_right] at hir
  have hqv : inner ℝ v q=inner ℝ q v := real_inner_comm _ _
  have huv : inner ℝ v u=inner ℝ u v := real_inner_comm _ _
  rw [hqv,huv] at hir
  linarith

theorem original_monoconj_proper (F : E m → EReal) (hp : IsProperFn F)
    (hu : ∃ u : E m, u ∈ posOrthant m ∧ F u ≠ ⊤ ∧ ∃ v : E m, IsSubgradient F u v) :
    IsProperFn (monoConjE F) := by
  obtain ⟨u,hu,hut,v,hv⟩ := hu
  have hun : u ∈ nonnegOrthant m := fun i => (hu i).le
  have eu := EReal.coe_toReal hut (hp.1 u)
  refine ⟨?_,v,?_⟩
  · intro z
    have hi : ((inner ℝ u z : ℝ) : EReal)-F u ≤ monoConjE F z :=
      le_iSup_of_le u (le_iSup_of_le hun le_rfl)
    rw [← eu,← EReal.coe_sub] at hi
    exact ne_of_gt ((EReal.bot_lt_coe _).trans_le hi)
  · have hbound : monoConjE F v ≤ conjE F v := by
      apply iSup_le
      intro q
      apply iSup_le
      intro hq
      exact le_iSup (fun q => ((inner ℝ q v : ℝ) : EReal)-F q) q
    exact ne_of_lt ((hbound.trans (original_conjugate_support_bound F hp u v hv)).trans_lt (EReal.coe_lt_top _))

theorem original_monoconj_lsc (F : E m → EReal) (hp : IsProperFn F) :
    LowerSemicontinuous (monoConjE F) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  have he : (monoConjE F) ⁻¹' Set.Iic a =
      ⋂ q, ⋂ (_ : q ∈ nonnegOrthant m), {z | ((inner ℝ q z : ℝ) : EReal)-F q ≤ a} := by
    ext z
    simp only [Set.mem_preimage,Set.mem_Iic,Set.mem_iInter,Set.mem_ofPred_eq,monoConjE,iSup_le_iff]
  rw [he]
  apply isClosed_iInter
  intro q
  apply isClosed_iInter
  intro hq
  by_cases hqt : F q=⊤
  · simp only [hqt,EReal.sub_top,bot_le,Set.ofPred_true]
    exact isClosed_univ
  · rw [← EReal.coe_toReal hqt (hp.1 q)]
    simp only [← EReal.coe_sub]
    have hc : Continuous (fun z : E m => (((inner ℝ q z-(F q).toReal : ℝ)) : EReal)) :=
      continuous_coe_real_ereal.comp ((continuous_const.inner continuous_id).sub continuous_const)
    exact isClosed_le hc continuous_const

theorem original_monoconj_convex (F : E m → EReal) (hp : IsProperFn F) :
    IsConvexFn (monoConjE F) := by
  intro u hu v hv α β hα hβ hab
  change monoConjE F (α • u.1+β • v.1) ≤ ((α*u.2+β*v.2 : ℝ) : EReal)
  apply iSup_le
  intro q
  apply iSup_le
  intro hq
  by_cases hqt : F q=⊤
  · simp only [hqt,EReal.sub_top]; exact bot_le
  have hb (z : E m) : ((inner ℝ q z : ℝ) : EReal)-F q ≤ monoConjE F z :=
    le_iSup_of_le q (le_iSup_of_le hq le_rfl)
  have eu := (hb u.1).trans hu
  have ev := (hb v.1).trans hv
  have ef := EReal.coe_toReal hqt (hp.1 q)
  rw [← ef,← EReal.coe_sub] at eu ev ⊢
  have ru := EReal.coe_le_coe_iff.mp eu
  have rv := EReal.coe_le_coe_iff.mp ev
  apply EReal.coe_le_coe_iff.mpr
  simp only [inner_add_right,inner_smul_right]
  have hfcomb : α*(F q).toReal+β*(F q).toReal=(F q).toReal := by
    rw [← add_mul,hab,one_mul]
  nlinarith [hfcomb,mul_nonneg hα (sub_nonneg.mpr ru),mul_nonneg hβ (sub_nonneg.mpr rv)]
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult Filter Topology
namespace BregmanIneqMultCodex
variable {m : ℕ}
noncomputable def slaterCost (F : E m → EReal) (z q : E m) : ℝ :=
  (F q).toReal-inner ℝ z q

def slaterSet (F : E m → EReal) (z : E m) : Set (E m × ℝ) :=
  {a | ∃ q : E m, F q ≠ ⊤ ∧ (∀ i, a.1 i < q i) ∧ slaterCost F z q < a.2}

theorem slaterSet_open (F : E m → EReal) (z : E m) : IsOpen (slaterSet F z) := by
  have he : slaterSet F z = ⋃ q : E m, ⋃ (_ : F q ≠ ⊤),
      {a : E m × ℝ | (∀ i, a.1 i < q i) ∧ slaterCost F z q < a.2} := by
    ext a; simp only [slaterSet,Set.mem_ofPred_eq,Set.mem_iUnion,exists_prop]
  rw [he]
  apply isOpen_iUnion
  intro q
  apply isOpen_iUnion
  intro hq
  have h1 : IsOpen {a : E m × ℝ | ∀ i, a.1 i < q i} := by
    have he : {a : E m × ℝ | ∀ i, a.1 i < q i} =
        ⋂ i : Fin m, {a : E m × ℝ | a.1 i < q i} := by ext a; simp
    rw [he]
    apply isOpen_iInter_of_finite
    intro i
    have hcoord : Continuous (fun a : E m × ℝ => a.1 i) := by fun_prop
    exact isOpen_lt hcoord continuous_const
  exact h1.inter (isOpen_lt continuous_const continuous_snd)

theorem slaterSet_convex (F : E m → EReal) (hp : IsProperFn F)
    (hc : IsConvexFn F) (z : E m) : Convex ℝ (slaterSet F z) := by
  intro a ha b hb α β hα hβ hab
  obtain ⟨q,hqt,hqa,hqa'⟩ := ha
  obtain ⟨r,hrt,hrb,hrb'⟩ := hb
  let s := α • q+β • r
  have eq := EReal.coe_toReal hqt (hp.1 q)
  have er := EReal.coe_toReal hrt (hp.1 r)
  have hqe : (q,(F q).toReal) ∈ {p : E m × ℝ | F p.1 ≤ (p.2 : EReal)} := by
    change F q ≤ ((F q).toReal : EReal); rw [eq]
  have hre : (r,(F r).toReal) ∈ {p : E m × ℝ | F p.1 ≤ (p.2 : EReal)} := by
    change F r ≤ ((F r).toReal : EReal); rw [er]
  have hs := hc hqe hre hα hβ hab
  change F s ≤ ((α*(F q).toReal+β*(F r).toReal : ℝ) : EReal) at hs
  have hst : F s ≠ ⊤ := ne_of_lt (hs.trans_lt (EReal.coe_lt_top _))
  have es := EReal.coe_toReal hst (hp.1 s)
  rw [← es] at hs
  have hsr := EReal.coe_le_coe_iff.mp hs
  refine ⟨s,hst,?_,?_⟩
  · intro i
    change α*a.1 i+β*b.1 i < α*q i+β*r i
    have h1 := hqa i
    have h2 := hrb i
    rcases eq_or_lt_of_le hα with hα0 | hαp
    · have hβ1 : β=1 := by linarith
      rw [← hα0,hβ1]; simpa using h2
    · nlinarith [mul_pos hαp (sub_pos.mpr h1),mul_nonneg hβ (sub_nonneg.mpr h2.le)]
  · change (F s).toReal-inner ℝ z s < α*a.2+β*b.2
    dsimp [slaterCost] at hqa' hrb'
    change (F s).toReal-inner ℝ z (α • q+β • r) < α*a.2+β*b.2
    simp only [inner_add_right,inner_smul_right]
    rcases eq_or_lt_of_le hα with hα0 | hαp
    · have hβ1 : β=1 := by linarith
      rw [← hα0,hβ1] at hsr ⊢
      simp only [zero_mul,one_mul,zero_add] at hsr ⊢
      linarith
    · nlinarith [mul_pos hαp (sub_pos.mpr hqa'),mul_nonneg hβ (sub_nonneg.mpr hrb'.le)]

theorem slaterSet_nonempty (F : E m → EReal) (z u : E m)
    (hu : u ∈ posOrthant m) (hut : F u ≠ ⊤) :
    (0,slaterCost F z u+1) ∈ slaterSet F z := by
  refine ⟨u,hut,?_,?_⟩
  · intro i; simpa using hu i
  · simp

theorem slater_value_not_mem (F : E m → EReal) (hp : IsProperFn F)
    (z : E m) (hz : monoConjE F z ≠ ⊤) (hb : monoConjE F z ≠ ⊥) :
    (0,-(monoConjE F z).toReal) ∉ slaterSet F z := by
  rintro ⟨q,hqt,hq,hcost⟩
  have hqn : q ∈ nonnegOrthant m := fun i => (hq i).le
  have hi : ((inner ℝ q z : ℝ) : EReal)-F q ≤ monoConjE F z :=
    le_iSup_of_le q (le_iSup_of_le hqn le_rfl)
  rw [← EReal.coe_toReal hqt (hp.1 q),← EReal.coe_toReal hz hb,← EReal.coe_sub] at hi
  have hir := EReal.coe_le_coe_iff.mp hi
  dsimp [slaterCost] at hcost
  have hqz : inner ℝ q z=inner ℝ z q := real_inner_comm _ _
  rw [hqz] at hir
  linarith
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult Filter Topology
namespace BregmanIneqMultCodex
variable {m : ℕ}

theorem product_functional_eval (L : StrongDual ℝ (E m × ℝ)) (q : E m) (r : ℝ) :
    L (q,r) = (L.comp (ContinuousLinearMap.inl ℝ (E m) ℝ)) q+r*L (0,1) := by
  have he : (q,r)=(q,0)+r • ((0,1) : E m × ℝ) := by ext <;> simp
  rw [he,map_add,map_smul]
  rfl

theorem slater_separator_vertical_pos (F : E m → EReal) (z u : E m)
    (hu : u ∈ posOrthant m) (hut : F u ≠ ⊤) (γ : ℝ)
    (hn : (0,-γ) ∉ slaterSet F z) (L : StrongDual ℝ (E m × ℝ))
    (hL : ∀ a ∈ slaterSet F z, L (0,-γ) < L a) : 0 < L (0,1) := by
  have hcost : -γ ≤ slaterCost F z u := by
    by_contra h
    apply hn
    exact ⟨u,hut,hu,lt_of_not_ge h⟩
  have hs := hL _ (slaterSet_nonempty F z u hu hut)
  rw [product_functional_eval L 0 (-γ),product_functional_eval L 0 (slaterCost F z u+1)] at hs
  simp only [map_zero,zero_add] at hs
  by_contra hn'
  have ha : L (0,1) ≤ 0 := le_of_not_gt hn'
  have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ slaterCost F z u+1+γ by linarith) ha
  nlinarith

theorem slater_separator_horizontal_nonpos (F : E m → EReal) (z u : E m)
    (hu : u ∈ posOrthant m) (hut : F u ≠ ⊤) (γ : ℝ)
    (L : StrongDual ℝ (E m × ℝ)) (hL : ∀ a ∈ slaterSet F z, L (0,-γ) < L a)
    (d : E m) (hd : d ∈ nonnegOrthant m) :
    (L.comp (ContinuousLinearMap.inl ℝ (E m) ℝ)) d ≤ 0 := by
  let A := L.comp (ContinuousLinearMap.inl ℝ (E m) ℝ)
  let r := slaterCost F z u+1
  have hbase := hL (0,r) (slaterSet_nonempty F z u hu hut)
  let D := L (0,r)-L (0,-γ)
  have hD : 0 < D := sub_pos.mpr hbase
  by_contra hn
  have hpos : 0 < A d := lt_of_not_ge hn
  let α := (D+1)/(A d)
  have hα : 0 < α := div_pos (by linarith) hpos
  have hαe : α*(A d)=D+1 := div_mul_cancel₀ _ (ne_of_gt hpos)
  have ht : (-α • d,r) ∈ slaterSet F z := by
    refine ⟨u,hut,?_,?_⟩
    · intro i
      change (-α)*d i < u i
      have hm := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα.le) (hd i)
      exact hm.trans_lt (hu i)
    · dsimp [r]; linarith
  have hi := hL _ ht
  rw [product_functional_eval L (-α • d) r] at hi
  change L (0,-γ) < A (-α • d)+r*L (0,1) at hi
  rw [map_smul] at hi
  change L (0,-γ) < (-α)*(A d)+r*L (0,1) at hi
  have he : L (0,r)=r*L (0,1) := by
    rw [product_functional_eval L 0 r,map_zero,zero_add]
  dsimp [D] at hαe
  rw [he] at hαe
  nlinarith

theorem slater_separator_epigraph (F : E m → EReal) (z u : E m)
    (hu : u ∈ posOrthant m) (γ : ℝ) (L : StrongDual ℝ (E m × ℝ))
    (hL : ∀ a ∈ slaterSet F z, L (0,-γ) < L a)
    (q : E m) (hqt : F q ≠ ⊤) : L (0,-γ) ≤ L (q,slaterCost F z q) := by
  have hc : Continuous (fun t : ℝ => L (q-t • u,slaterCost F z q+t)) := by fun_prop
  have ht : Tendsto (fun t : ℝ => L (q-t • u,slaterCost F z q+t)) (𝓝[>] (0 : ℝ))
      (𝓝 (L (q,slaterCost F z q))) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  have hp : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [hp] with t ht
  apply (hL _ ?_).le
  refine ⟨q,hqt,?_,?_⟩
  · intro i
    change q i-t*u i < q i
    have hm := mul_pos ht (hu i)
    linarith
  · linarith
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult
namespace BregmanIneqMultCodex
variable {m : ℕ}

theorem original_monoconj_upper_argument (F : E m → EReal) (hp : IsProperFn F)
    (z w : E m) (hw : ∀ i, z i ≤ w i) : monoConjE F z ≤ conjE F w := by
  apply iSup_le
  intro p
  apply iSup_le
  intro hpn
  have hi : inner ℝ p z ≤ inner ℝ p w := by
    have hn : 0 ≤ inner ℝ p (w-z) := by
      rw [PiLp.inner_apply]
      simp only [RCLike.inner_apply,conj_trivial]
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (sub_nonneg.mpr (hw i)) (hpn i)
    rw [inner_sub_right] at hn
    linarith
  have ht : ((inner ℝ p z : ℝ) : EReal)-F p ≤ ((inner ℝ p w : ℝ) : EReal)-F p := by
    by_cases hpt : F p=⊤
    · rw [hpt]; exact le_rfl
    rw [← EReal.coe_toReal hpt (hp.1 p),← EReal.coe_sub,← EReal.coe_sub]
    exact EReal.coe_le_coe_iff.mpr (sub_le_sub_right hi _)
  exact ht.trans (le_iSup (fun p => ((inner ℝ p w : ℝ) : EReal)-F p) p)

theorem original_monoconj_attainment_of_positive_finite (F : E m → EReal) (hp : IsProperFn F)
    (hc : IsConvexFn F) (u : E m) (hu : u ∈ posOrthant m) (hut : F u ≠ ⊤)
    (z : E m) (hz : monoConjE F z ≠ ⊤) :
    ∃ w : E m, (∀ i, z i ≤ w i) ∧ monoConjE F z = conjE F w := by
  have hun : u ∈ nonnegOrthant m := fun i => (hu i).le
  have hlower : ((inner ℝ u z : ℝ) : EReal)-F u ≤ monoConjE F z :=
    le_iSup_of_le u (le_iSup_of_le hun le_rfl)
  rw [← EReal.coe_toReal hut (hp.1 u),← EReal.coe_sub] at hlower
  have hb : monoConjE F z ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe _).trans_le hlower)
  let γ := (monoConjE F z).toReal
  have eγ := EReal.coe_toReal hz hb
  have hn : (0,-γ) ∉ slaterSet F z := slater_value_not_mem F hp z hz hb
  obtain ⟨L,hL⟩ := geometric_hahn_banach_point_open (slaterSet_convex F hp hc z)
    (slaterSet_open F z) hn
  let a := L (0,1)
  have ha : 0 < a := slater_separator_vertical_pos F z u hu hut γ hn L hL
  let A := L.comp (ContinuousLinearMap.inl ℝ (E m) ℝ)
  let v := (InnerProductSpace.toDual ℝ (E m)).symm A
  have hev (q : E m) : inner ℝ v q=A q := InnerProductSpace.toDual_symm_apply
  have hvn (i : Fin m) : v i ≤ 0 := by
    have hd : EuclideanSpace.single i (1 : ℝ) ∈ nonnegOrthant m := by
      intro j
      simp only [PiLp.single_apply]
      split_ifs <;> norm_num
    have hs := slater_separator_horizontal_nonpos F z u hu hut γ L hL _ hd
    have he := hev (EuclideanSpace.single i (1 : ℝ))
    simp only [EuclideanSpace.inner_single_right,conj_trivial,one_mul] at he
    rw [← he] at hs
    exact hs
  let w := z-a⁻¹ • v
  have hw (i : Fin m) : z i ≤ w i := by
    change z i ≤ z i-a⁻¹*v i
    have hn := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ha.le) (hvn i)
    linarith
  have hupper : conjE F w ≤ monoConjE F z := by
    apply iSup_le
    intro q
    by_cases hqt : F q=⊤
    · rw [hqt,EReal.sub_top]; exact bot_le
    have hi := slater_separator_epigraph F z u hu γ L hL q hqt
    rw [product_functional_eval L 0 (-γ),product_functional_eval L q (slaterCost F z q)] at hi
    simp only [map_zero,zero_add] at hi
    change -γ*a ≤ A q+slaterCost F z q*a at hi
    rw [← hev q] at hi
    dsimp [slaterCost] at hi
    rw [← EReal.coe_toReal hqt (hp.1 q),← eγ,← EReal.coe_sub]
    apply EReal.coe_le_coe_iff.mpr
    change inner ℝ q (z-a⁻¹ • v)-(F q).toReal ≤ γ
    have hqz : inner ℝ q z=inner ℝ z q := real_inner_comm _ _
    have hqv : inner ℝ q v=inner ℝ v q := real_inner_comm _ _
    rw [inner_sub_right,inner_smul_right,hqz,hqv]
    apply (mul_le_mul_iff_right₀ ha).mp
    have he : a*(inner ℝ z q-a⁻¹*inner ℝ v q-(F q).toReal)=
        a*inner ℝ z q-inner ℝ v q-a*(F q).toReal := by
      rw [mul_sub,mul_sub,← mul_assoc,mul_inv_cancel₀ (ne_of_gt ha),one_mul]
    rw [he]
    nlinarith
  exact ⟨w,hw,le_antisymm (original_monoconj_upper_argument F hp z w hw) hupper⟩
theorem original_monoconj_attainment (F : E m → EReal) (hp : IsProperFn F)
    (hc : IsConvexFn F)
    (hu : ∃ u : E m, u ∈ posOrthant m ∧ F u ≠ ⊤ ∧ ∃ v : E m, IsSubgradient F u v)
    (z : E m) (hz : monoConjE F z ≠ ⊤) :
    ∃ w : E m, (∀ i, z i ≤ w i) ∧ monoConjE F z = conjE F w := by
  obtain ⟨u,hu,hut,hv⟩ := hu
  exact original_monoconj_attainment_of_positive_finite F hp hc u hu hut z hz
end BregmanIneqMultCodex


end

set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult

/-- Lemma A2, p. 223: closedness, convexity, properness and attainment of the
restricted conjugate's infimum representation. -/
theorem solution {m : ℕ} (F : E m → EReal)
    (hproper : IsProperFn F) (hconvex : IsConvexFn F)
    (hclosed : LowerSemicontinuous F)
    (hu : ∃ u : E m, u ∈ posOrthant m ∧ F u ≠ ⊤ ∧
      ∃ v : E m, IsSubgradient F u v) :
    LowerSemicontinuous (monoConjE F) ∧
    IsProperFn (monoConjE F) ∧
    IsConvexFn (monoConjE F) ∧
    (∀ z : E m, monoConjE F z ≠ ⊤ →
      ∃ w : E m, (∀ i, z i ≤ w i) ∧ monoConjE F z = conjE F w) := by
  exact ⟨BregmanIneqMultCodex.original_monoconj_lsc F hproper,
    BregmanIneqMultCodex.original_monoconj_proper F hproper hu,
    BregmanIneqMultCodex.original_monoconj_convex F hproper,
    fun z hz => BregmanIneqMultCodex.original_monoconj_attainment F hproper hconvex hu z hz⟩



#print axioms solution
