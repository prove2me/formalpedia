-- Prove2me | solution 1 for BregmanPPA.ProxMult.theorem8_existence
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T01:29:19.847091+00:00
-- url     : https://prove2.me/submissions/458801eb-630f-4117-a7dc-f5aa00adadff

import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_IneqMult_Program
import Definitions.Def_BregmanPPA_ProxMult_Saddle
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Mathlib
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

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult
namespace BregmanIneqMultCodex
variable {m : ℕ}

theorem original_monoconj_finite (F : E m → EReal) (hp : IsProperFn F)
    (hfinite : ∀ p : E m, p ∈ posOrthant m → F p ≠ ⊤)
    (him : ∀ z : E m, z ∈ posOrthant m → ∃ p : E m, IsSubgradient F p z) :
    ∀ z : E m, monoConjE F z ≠ ⊤ ∧ monoConjE F z ≠ ⊥ := by
  intro z
  let w : E m := (WithLp.equiv 2 _).symm (fun i => max (z i) 0+1)
  have hw : w ∈ posOrthant m := by
    intro i
    change 0 < max (z i) 0+1
    have h0 := le_max_right (z i) 0
    linarith
  have hzw (i : Fin m) : z i ≤ w i := by
    change z i ≤ max (z i) 0+1
    have hi := le_max_left (z i) 0
    linarith
  obtain ⟨p,hp'⟩ := him w hw
  have hupper := (original_monoconj_upper_argument F hp z w hzw).trans
    (original_conjugate_support_bound F hp p w hp')
  have hzt : monoConjE F z ≠ ⊤ := ne_of_lt (hupper.trans_lt (EReal.coe_lt_top _))
  let u : E m := (WithLp.equiv 2 _).symm (fun _ => (1 : ℝ))
  have hup : u ∈ posOrthant m := by intro i; change 0 < (1 : ℝ); norm_num
  have hun : u ∈ nonnegOrthant m := fun i => (hup i).le
  have hut := hfinite u hup
  have hlower : ((inner ℝ u z : ℝ) : EReal)-F u ≤ monoConjE F z :=
    le_iSup_of_le u (le_iSup_of_le hun le_rfl)
  rw [← EReal.coe_toReal hut (hp.1 u),← EReal.coe_sub] at hlower
  exact ⟨hzt,ne_of_gt ((EReal.bot_lt_coe _).trans_le hlower)⟩
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult Filter Topology
namespace BregmanIneqMultCodex
variable {m : ℕ}
noncomputable def linearCost (F : E m → EReal) (z q : E m) : EReal :=
  F q-((inner ℝ z q : ℝ) : EReal)

def linearLevel (F : E m → EReal) (z : E m) (r : ℝ) : Set (E m) :=
  {q | q ∈ nonnegOrthant m ∧ F q ≤ ((r+inner ℝ z q : ℝ) : EReal)}

theorem linearCost_ne_bot (F : E m → EReal) (hp : IsProperFn F) (z q : E m) :
    linearCost F z q ≠ ⊥ := by
  by_cases hqt : F q=⊤
  · rw [linearCost,hqt,EReal.top_sub_coe]; exact top_ne_bot
  · rw [linearCost,← EReal.coe_toReal hqt (hp.1 q),← EReal.coe_sub]
    exact EReal.coe_ne_bot _

theorem linearLevel_cost_iff (F : E m → EReal) (z q : E m) (r : ℝ) :
    q ∈ linearLevel F z r ↔ q ∈ nonnegOrthant m ∧ linearCost F z q ≤ (r : EReal) := by
  simp only [linearLevel,Set.mem_ofPred_eq,linearCost]
  rw [EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _)),← EReal.coe_add]

theorem linearCost_lsc (F : E m → EReal) (hp : IsProperFn F)
    (hf : LowerSemicontinuous F) (z : E m) : LowerSemicontinuous (linearCost F z) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  by_cases hat : a=⊤
  · subst a; simp
  by_cases hab : a=⊥
  · subst a
    have he : (linearCost F z) ⁻¹' Set.Iic ⊥ = ∅ := by
      ext q
      simp only [Set.mem_preimage,Set.mem_Iic,le_bot_iff,Set.mem_empty_iff_false]
      exact iff_false_intro (linearCost_ne_bot F hp z q)
    rw [he]; exact isClosed_empty
  have ea := EReal.coe_toReal hat hab
  have he : (linearCost F z) ⁻¹' Set.Iic a =
      (fun q => (q,(((a.toReal+inner ℝ z q : ℝ)) : EReal))) ⁻¹'
        {p : E m × EReal | F p.1 ≤ p.2} := by
    ext q
    simp only [Set.mem_preimage,Set.mem_Iic,Set.mem_ofPred_eq,linearCost]
    rw [← ea,EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _)),← EReal.coe_add]
    simp only [EReal.toReal_coe]
  rw [he]
  apply hf.isClosed_epigraph.preimage
  exact continuous_id.prodMk (continuous_coe_real_ereal.comp (continuous_const.add (continuous_const.inner continuous_id)))

theorem nonnegOrthant_closed : IsClosed (nonnegOrthant m) := by
  have he : nonnegOrthant m = ⋂ i : Fin m, {q : E m | 0 ≤ q i} := by ext q; simp [nonnegOrthant]
  rw [he]
  apply isClosed_iInter
  intro i
  have hi : Continuous (fun q : E m => q i) := by fun_prop
  exact isClosed_le continuous_const hi

theorem linearLevel_closed (F : E m → EReal) (hf : LowerSemicontinuous F)
    (z : E m) (r : ℝ) : IsClosed (linearLevel F z r) := by
  have he : linearLevel F z r = nonnegOrthant m ∩
      (fun q => (q,(((r+inner ℝ z q : ℝ)) : EReal))) ⁻¹'
        {p : E m × EReal | F p.1 ≤ p.2} := rfl
  rw [he]
  apply nonnegOrthant_closed.inter
  apply hf.isClosed_epigraph.preimage
  exact continuous_id.prodMk (continuous_coe_real_ereal.comp (continuous_const.add (continuous_const.inner continuous_id)))

theorem linearLevel_compact_of_support (F : E m → EReal) (hp : IsProperFn F)
    (hf : LowerSemicontinuous F) (z p w : E m) (hs : IsSubgradient F p w)
    (hw : ∀ i, 1 ≤ w i-z i) (r : ℝ) : IsCompact (linearLevel F z r) := by
  let D := r+inner ℝ w p-(F p).toReal
  let R := max D 0
  have hbound (q : E m) (hq : q ∈ linearLevel F z r) (i : Fin m) : q i ≤ R := by
    have hqt : F q ≠ ⊤ := ne_of_lt (hq.2.trans_lt (EReal.coe_lt_top _))
    have eq := EReal.coe_toReal hqt (hp.1 q)
    have ep := EReal.coe_toReal hs.1 (hp.1 p)
    have hi := hs.2 q
    rw [← ep,← eq,← EReal.coe_add] at hi
    have hir := EReal.coe_le_coe_iff.mp hi
    have hqr := hq.2
    rw [← eq] at hqr
    have hqrr := EReal.coe_le_coe_iff.mp hqr
    have hg : inner ℝ (w-z) q ≤ D := by
      simp only [inner_sub_left,inner_sub_right] at hir ⊢
      dsimp [D]
      linarith
    have hsum : (∑ j : Fin m, q j) ≤ inner ℝ (w-z) q := by
      rw [PiLp.inner_apply]
      simp only [RCLike.inner_apply,conj_trivial]
      apply Finset.sum_le_sum
      intro j hj
      change q j ≤ q j*(w j-z j)
      have hm := mul_nonneg (hq.1 j) (sub_nonneg.mpr (hw j))
      nlinarith
    have hqi : q i ≤ ∑ j : Fin m, q j := Finset.single_le_sum (fun j hj => hq.1 j) (Finset.mem_univ i)
    exact ((hqi.trans hsum).trans hg).trans (le_max_left D 0)
  let H := PiLp.homeomorph 2 (fun _ : Fin m => ℝ)
  have hbox : IsCompact (Set.pi Set.univ (fun _ : Fin m => Set.Icc (0 : ℝ) R)) :=
    by simpa only [Set.pi,Set.mem_univ,forall_const] using
      (isCompact_pi_infinite fun _ : Fin m => (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) R)))
  have hc := H.isCompact_preimage.mpr hbox
  apply hc.of_isClosed_subset (linearLevel_closed F hf z r)
  intro q hq
  change (fun i => q i) ∈ Set.pi Set.univ (fun _ : Fin m => Set.Icc (0 : ℝ) R)
  simp only [Set.mem_pi,Set.mem_univ,forall_const,Set.mem_Icc]
  exact fun i => ⟨hq.1 i,hbound q hq i⟩
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult
namespace BregmanIneqMultCodex
variable {m : ℕ}

theorem original_monoconj_maximizer (F : E m → EReal) (hp : IsProperFn F)
    (hf : LowerSemicontinuous F)
    (hfinite : ∀ p : E m, p ∈ posOrthant m → F p ≠ ⊤)
    (him : ∀ z : E m, z ∈ posOrthant m → ∃ p : E m, IsSubgradient F p z)
    (z : E m) : ∃ q : E m, q ∈ nonnegOrthant m ∧ F q ≠ ⊤ ∧
      monoConjE F z = (((inner ℝ q z-(F q).toReal : ℝ)) : EReal) := by
  let w : E m := (WithLp.equiv 2 _).symm (fun i => max (z i) 0+2)
  have hw : w ∈ posOrthant m := by
    intro i
    change 0 < max (z i) 0+2
    have h0 := le_max_right (z i) 0
    linarith
  have hgap (i : Fin m) : 1 ≤ w i-z i := by
    change 1 ≤ max (z i) 0+2-z i
    have hi := le_max_left (z i) 0
    linarith
  obtain ⟨p,hs⟩ := him w hw
  let u : E m := (WithLp.equiv 2 _).symm (fun _ => (1 : ℝ))
  have hup : u ∈ posOrthant m := by intro i; change 0 < (1 : ℝ); norm_num
  have hun : u ∈ nonnegOrthant m := fun i => (hup i).le
  have hut := hfinite u hup
  let r := slaterCost F z u
  have eu := EReal.coe_toReal hut (hp.1 u)
  have hul : u ∈ linearLevel F z r := by
    refine ⟨hun,?_⟩
    rw [← eu]
    change ((F u).toReal : EReal) ≤ (((F u).toReal-inner ℝ z u+inner ℝ z u : ℝ) : EReal)
    rw [sub_add_cancel]
  have hk := linearLevel_compact_of_support F hp hf z p w hs hgap r
  have hls := (linearCost_lsc F hp hf z).lowerSemicontinuousOn (linearLevel F z r)
  obtain ⟨q,hql,hmin⟩ := LowerSemicontinuousOn.exists_isMinOn ⟨u,hul⟩ hk hls
  have hqt : F q ≠ ⊤ := ne_of_lt (hql.2.trans_lt (EReal.coe_lt_top _))
  have hminall (t : E m) (ht : t ∈ nonnegOrthant m) : linearCost F z q ≤ linearCost F z t := by
    by_cases htl : t ∈ linearLevel F z r
    · exact hmin htl
    · have hn : ¬ linearCost F z t ≤ (r : EReal) := by
        intro h
        exact htl ((linearLevel_cost_iff F z t r).mpr ⟨ht,h⟩)
      exact ((linearLevel_cost_iff F z q r).mp hql).2.trans (le_of_not_ge hn)
  have eq := EReal.coe_toReal hqt (hp.1 q)
  have hlo : (((inner ℝ q z-(F q).toReal : ℝ)) : EReal) ≤ monoConjE F z := by
    have hi : ((inner ℝ q z : ℝ) : EReal)-F q ≤ monoConjE F z :=
      le_iSup_of_le q (le_iSup_of_le hql.1 le_rfl)
    rw [← eq,← EReal.coe_sub] at hi
    exact hi
  have hup' : monoConjE F z ≤ (((inner ℝ q z-(F q).toReal : ℝ)) : EReal) := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    by_cases htt : F t=⊤
    · rw [htt,EReal.sub_top]; exact bot_le
    have et := EReal.coe_toReal htt (hp.1 t)
    have hi := hminall t ht
    dsimp [linearCost] at hi
    rw [← eq,← et,← EReal.coe_sub,← EReal.coe_sub] at hi
    have hir := EReal.coe_le_coe_iff.mp hi
    rw [← et,← EReal.coe_sub]
    apply EReal.coe_le_coe_iff.mpr
    have htz : inner ℝ t z=inner ℝ z t := real_inner_comm _ _
    have hqz : inner ℝ q z=inner ℝ z q := real_inner_comm _ _
    rw [htz,hqz]
    linarith
  exact ⟨q,hql.1,hqt,le_antisymm hup' hlo⟩
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult
namespace BregmanIneqMultCodex
variable {m : ℕ}
def monoMaxSet (F : E m → EReal) (z : E m) : Set (E m) :=
  {q | q ∈ nonnegOrthant m ∧ F q ≠ ⊤ ∧
    monoConjE F z = (((inner ℝ q z-(F q).toReal : ℝ)) : EReal)}

theorem monoMax_cost (F : E m → EReal) (z q : E m) (hq : q ∈ monoMaxSet F z) :
    (F q).toReal-inner ℝ z q = -(monoConjE F z).toReal := by
  have he := congrArg EReal.toReal hq.2.2
  simp only [EReal.toReal_coe] at he
  have hqz : inner ℝ q z=inner ℝ z q := real_inner_comm _ _
  rw [hqz] at he
  linarith

theorem nonneg_inner_mono (p z w : E m) (hp : p ∈ nonnegOrthant m)
    (hw : ∀ i, z i ≤ w i) : inner ℝ p z ≤ inner ℝ p w := by
  have hn : 0 ≤ inner ℝ p (w-z) := by
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply,conj_trivial]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (sub_nonneg.mpr (hw i)) (hp i)
  rw [inner_sub_right] at hn
  linarith

theorem monoMax_subgradient (F : E m → EReal) (hp : IsProperFn F)
    (z w q : E m) (hw : ∀ i, z i ≤ w i)
    (he : monoConjE F z=conjE F w) (hq : q ∈ monoMaxSet F z) : IsSubgradient F q w := by
  have eq := EReal.coe_toReal hq.2.1 (hp.1 q)
  have hi : ((inner ℝ q w : ℝ) : EReal)-F q ≤ conjE F w :=
    le_iSup (fun t => ((inner ℝ t w : ℝ) : EReal)-F t) q
  rw [← he,hq.2.2,← eq,← EReal.coe_sub] at hi
  simp only [EReal.toReal_coe] at hi
  have hir := EReal.coe_le_coe_iff.mp hi
  have hm := nonneg_inner_mono q z w hq.1 hw
  have hqz : inner ℝ q z=inner ℝ z q := real_inner_comm _ _
  have hqw : inner ℝ q w=inner ℝ w q := real_inner_comm _ _
  have hval : inner ℝ w q-(F q).toReal=(monoConjE F z).toReal := by
    have hc := monoMax_cost F z q hq
    rw [hqz,hqw] at hir hm
    linarith
  refine ⟨hq.2.1,?_⟩
  intro t
  by_cases htt : F t=⊤
  · rw [htt]; exact le_top
  have et := EReal.coe_toReal htt (hp.1 t)
  have ht : ((inner ℝ t w : ℝ) : EReal)-F t ≤ conjE F w :=
    le_iSup (fun t => ((inner ℝ t w : ℝ) : EReal)-F t) t
  rw [← he,hq.2.2,← et,← EReal.coe_sub] at ht
  have htr := EReal.coe_le_coe_iff.mp ht
  rw [← eq,← et,← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  have htw : inner ℝ t w=inner ℝ w t := real_inner_comm _ _
  rw [htw,hqz] at htr
  have hc := monoMax_cost F z q hq
  simp only [inner_sub_right]
  linarith

theorem monoMaxSet_convex (F : E m → EReal) (hp : IsProperFn F)
    (hc : IsConvexFn F) (z : E m) : Convex ℝ (monoMaxSet F z) := by
  intro q hq r hr α β hα hβ hab
  let s := α • q+β • r
  have hn : s ∈ nonnegOrthant m := by
    intro i
    change 0 ≤ α*q i+β*r i
    exact add_nonneg (mul_nonneg hα (hq.1 i)) (mul_nonneg hβ (hr.1 i))
  have hqe : (q,(F q).toReal) ∈ {p : E m × ℝ | F p.1 ≤ (p.2 : EReal)} := by
    change F q ≤ ((F q).toReal : EReal); rw [EReal.coe_toReal hq.2.1 (hp.1 q)]
  have hre : (r,(F r).toReal) ∈ {p : E m × ℝ | F p.1 ≤ (p.2 : EReal)} := by
    change F r ≤ ((F r).toReal : EReal); rw [EReal.coe_toReal hr.2.1 (hp.1 r)]
  have hs := hc hqe hre hα hβ hab
  change F s ≤ ((α*(F q).toReal+β*(F r).toReal : ℝ) : EReal) at hs
  have hst : F s ≠ ⊤ := ne_of_lt (hs.trans_lt (EReal.coe_lt_top _))
  have es := EReal.coe_toReal hst (hp.1 s)
  rw [← es] at hs
  have hsr := EReal.coe_le_coe_iff.mp hs
  have eM : (((monoConjE F z).toReal : ℝ) : EReal)=monoConjE F z := by
    rw [hq.2.2]; simp only [EReal.toReal_coe]
  have hi : ((inner ℝ s z : ℝ) : EReal)-F s ≤ monoConjE F z :=
    le_iSup_of_le s (le_iSup_of_le hn le_rfl)
  rw [← es,← eM,← EReal.coe_sub] at hi
  have hir := EReal.coe_le_coe_iff.mp hi
  have hqv := monoMax_cost F z q hq
  have hrv := monoMax_cost F z r hr
  have hsz : inner ℝ s z=inner ℝ z s := real_inner_comm _ _
  rw [hsz] at hir
  have hsum : α*(monoConjE F z).toReal+β*(monoConjE F z).toReal=(monoConjE F z).toReal := by
    rw [← add_mul,hab,one_mul]
  have hvalue : (F s).toReal-inner ℝ z s=-(monoConjE F z).toReal := by
    change (F s).toReal-inner ℝ z (α • q+β • r)=-(monoConjE F z).toReal
    simp only [inner_add_right,inner_smul_right]
    simp only [s,inner_add_right,inner_smul_right] at hir
    nlinarith
  refine ⟨hn,hst,?_⟩
  rw [← eM]
  congr 1
  rw [hsz]
  linarith

theorem original_monoconj_maximizer_unique (F : E m → EReal) (hp : IsProperFn F)
    (hc : IsConvexFn F) (hstrict : EssentiallyStrictlyConvex F)
    (hfinite : ∀ p : E m, p ∈ posOrthant m → F p ≠ ⊤)
    (z q r : E m) (hq : q ∈ monoMaxSet F z) (hr : r ∈ monoMaxSet F z) : q=r := by
  let u : E m := (WithLp.equiv 2 _).symm (fun _ => (1 : ℝ))
  have hu : u ∈ posOrthant m := by intro i; change 0 < (1 : ℝ); norm_num
  have hz : monoConjE F z ≠ ⊤ := by rw [hq.2.2]; exact EReal.coe_ne_top _
  obtain ⟨w,hw,he⟩ := original_monoconj_attainment_of_positive_finite F hp hc u hu (hfinite u hu) z hz
  have hs := monoMaxSet_convex F hp hc z
  have hdom : monoMaxSet F z ⊆ ThreeOpSplitting.Convergence.dom (BregmanPPA.Convergence.subdiffOp F) := by
    intro t ht
    exact ⟨w,monoMax_subgradient F hp z w t hw he ht⟩
  have hf := hstrict (monoMaxSet F z) hs hdom
  have hl : ConcaveOn ℝ (monoMaxSet F z) (fun t => inner ℝ z t) := by
    refine ⟨hs,?_⟩
    intro x _ y _ a b _ _ _
    simp only [inner_add_right,inner_smul_right,smul_eq_mul]
    exact le_rfl
  have hcost := hf.sub_concaveOn hl
  have hqmin : IsMinOn (fun t => (F t).toReal-inner ℝ z t) (monoMaxSet F z) q := by
    intro t ht
    change (F q).toReal-inner ℝ z q ≤ (F t).toReal-inner ℝ z t
    rw [monoMax_cost F z q hq,monoMax_cost F z t ht]
  have hrmin : IsMinOn (fun t => (F t).toReal-inner ℝ z t) (monoMaxSet F z) r := by
    intro t ht
    change (F r).toReal-inner ℝ z r ≤ (F t).toReal-inner ℝ z t
    rw [monoMax_cost F z r hr,monoMax_cost F z t ht]
  exact hcost.eq_of_isMinOn hqmin hrmin hq hr
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult Filter Topology
namespace BregmanIneqMultCodex
variable {m : ℕ}

theorem monoMax_min_cost (F : E m → EReal) (hp : IsProperFn F)
    (z q : E m) (hq : q ∈ monoMaxSet F z) (y : E m) (hy : y ∈ nonnegOrthant m) :
    linearCost F z q ≤ linearCost F z y := by
  by_cases hyt : F y=⊤
  · change linearCost F z q ≤ F y-((inner ℝ z y : ℝ) : EReal)
    rw [hyt,EReal.top_sub_coe]; exact le_top
  have ey := EReal.coe_toReal hyt (hp.1 y)
  have eq := EReal.coe_toReal hq.2.1 (hp.1 q)
  have hi : ((inner ℝ y z : ℝ) : EReal)-F y ≤ monoConjE F z :=
    le_iSup_of_le y (le_iSup_of_le hy le_rfl)
  rw [hq.2.2,← ey,← EReal.coe_sub] at hi
  have hir := EReal.coe_le_coe_iff.mp hi
  rw [linearCost,linearCost,← eq,← ey,← EReal.coe_sub,← EReal.coe_sub]
  apply EReal.coe_le_coe_iff.mpr
  have hyz : inner ℝ y z=inner ℝ z y := real_inner_comm _ _
  have hqz : inner ℝ q z=inner ℝ z q := real_inner_comm _ _
  rw [hyz,hqz] at hir
  linarith

theorem monoMax_of_min_cost (F : E m → EReal) (hp : IsProperFn F)
    (z q : E m) (hqn : q ∈ nonnegOrthant m) (hqt : F q ≠ ⊤)
    (hmin : ∀ y ∈ nonnegOrthant m, linearCost F z q ≤ linearCost F z y) :
    q ∈ monoMaxSet F z := by
  have eq := EReal.coe_toReal hqt (hp.1 q)
  have hlo : (((inner ℝ q z-(F q).toReal : ℝ)) : EReal) ≤ monoConjE F z := by
    have hi : ((inner ℝ q z : ℝ) : EReal)-F q ≤ monoConjE F z :=
      le_iSup_of_le q (le_iSup_of_le hqn le_rfl)
    rw [← eq,← EReal.coe_sub] at hi
    exact hi
  refine ⟨hqn,hqt,le_antisymm ?_ hlo⟩
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  by_cases htt : F t=⊤
  · rw [htt,EReal.sub_top]; exact bot_le
  have et := EReal.coe_toReal htt (hp.1 t)
  have hi := hmin t ht
  dsimp [linearCost] at hi
  rw [← eq,← et,← EReal.coe_sub,← EReal.coe_sub] at hi
  have hir := EReal.coe_le_coe_iff.mp hi
  rw [← et,← EReal.coe_sub]
  apply EReal.coe_le_coe_iff.mpr
  have htz : inner ℝ t z=inner ℝ z t := real_inner_comm _ _
  have hqz : inner ℝ q z=inner ℝ z q := real_inner_comm _ _
  rw [htz,hqz]
  linarith

theorem monoMax_graph_limit {α : Type*} (l : Filter α) [NeBot l]
    (F : E m → EReal) (hp : IsProperFn F) (hf : LowerSemicontinuous F)
    (u : E m) (hun : u ∈ nonnegOrthant m) (hut : F u ≠ ⊤)
    (zs qs : α → E m) (z q : E m) (hz : Tendsto zs l (𝓝 z))
    (hq : Tendsto qs l (𝓝 q)) (hs : ∀ᶠ a in l, qs a ∈ monoMaxSet F (zs a)) :
    q ∈ monoMaxSet F z := by
  have hqn : q ∈ nonnegOrthant m := nonnegOrthant_closed.mem_of_tendsto hq (hs.mono fun a ha => ha.1)
  have hbound (y : E m) (hyn : y ∈ nonnegOrthant m) (hyt : F y ≠ ⊤) :
      F q ≤ (((F y).toReal+inner ℝ z (q-y) : ℝ) : EReal) := by
    have ht : Tendsto (fun a => (F y).toReal+inner ℝ (zs a) (qs a-y)) l
        (𝓝 ((F y).toReal+inner ℝ z (q-y))) :=
      tendsto_const_nhds.add (hz.inner (hq.sub tendsto_const_nhds))
    have he := (continuous_coe_real_ereal.tendsto _).comp ht
    change (q,(((F y).toReal+inner ℝ z (q-y) : ℝ) : EReal)) ∈ {p : E m × EReal | F p.1 ≤ p.2}
    apply hf.isClosed_epigraph.mem_of_tendsto (hq.prodMk_nhds he)
    filter_upwards [hs] with a ha
    have hi := monoMax_min_cost F hp (zs a) (qs a) ha y hyn
    have ea := EReal.coe_toReal ha.2.1 (hp.1 (qs a))
    have ey := EReal.coe_toReal hyt (hp.1 y)
    dsimp [linearCost] at hi
    rw [← ea,← ey,← EReal.coe_sub,← EReal.coe_sub] at hi
    have hir := EReal.coe_le_coe_iff.mp hi
    change F (qs a) ≤ (((F y).toReal+inner ℝ (zs a) (qs a-y) : ℝ) : EReal)
    rw [← ea]
    apply EReal.coe_le_coe_iff.mpr
    simp only [inner_sub_right]
    linarith
  have hqt : F q ≠ ⊤ := ne_of_lt ((hbound u hun hut).trans_lt (EReal.coe_lt_top _))
  apply monoMax_of_min_cost F hp z q hqn hqt
  intro y hyn
  by_cases hyt : F y=⊤
  · change linearCost F z q ≤ F y-((inner ℝ z y : ℝ) : EReal)
    rw [hyt,EReal.top_sub_coe]; exact le_top
  have hi := hbound y hyn hyt
  have eq := EReal.coe_toReal hqt (hp.1 q)
  have ey := EReal.coe_toReal hyt (hp.1 y)
  rw [← eq] at hi
  have hir := EReal.coe_le_coe_iff.mp hi
  rw [linearCost,linearCost,← eq,← ey,← EReal.coe_sub,← EReal.coe_sub]
  apply EReal.coe_le_coe_iff.mpr
  simp only [inner_sub_right] at hir
  linarith
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult Filter Topology
namespace BregmanIneqMultCodex
variable {m : ℕ}
theorem linearLevel_coordinate_bound (F : E m → EReal) (hp : IsProperFn F)
    (z p w : E m) (hs : IsSubgradient F p w) (hw : ∀ i, 1 ≤ w i-z i)
    (r : ℝ) (q : E m) (hq : q ∈ linearLevel F z r) (i : Fin m) :
    q i ≤ max (r+inner ℝ w p-(F p).toReal) 0 := by
    let D := r+inner ℝ w p-(F p).toReal
    have hqt : F q ≠ ⊤ := ne_of_lt (hq.2.trans_lt (EReal.coe_lt_top _))
    have eq := EReal.coe_toReal hqt (hp.1 q)
    have ep := EReal.coe_toReal hs.1 (hp.1 p)
    have hi := hs.2 q
    rw [← ep,← eq,← EReal.coe_add] at hi
    have hir := EReal.coe_le_coe_iff.mp hi
    have hqr := hq.2
    rw [← eq] at hqr
    have hqrr := EReal.coe_le_coe_iff.mp hqr
    have hg : inner ℝ (w-z) q ≤ D := by
      simp only [inner_sub_left,inner_sub_right] at hir ⊢
      dsimp [D]
      linarith
    have hsum : (∑ j : Fin m, q j) ≤ inner ℝ (w-z) q := by
      rw [PiLp.inner_apply]
      simp only [RCLike.inner_apply,conj_trivial]
      apply Finset.sum_le_sum
      intro j hj
      change q j ≤ q j*(w j-z j)
      have hm := mul_nonneg (hq.1 j) (sub_nonneg.mpr (hw j))
      nlinarith
    have hqi : q i ≤ ∑ j : Fin m, q j := Finset.single_le_sum (fun j hj => hq.1 j) (Finset.mem_univ i)
    exact ((hqi.trans hsum).trans hg).trans (le_max_left D 0)

theorem monoMax_local_compact (F : E m → EReal) (hp : IsProperFn F)
    (hfinite : ∀ p : E m, p ∈ posOrthant m → F p ≠ ⊤)
    (him : ∀ z : E m, z ∈ posOrthant m → ∃ p : E m, IsSubgradient F p z)
    (z₀ : E m) : ∃ K : Set (E m), IsCompact K ∧ ∀ᶠ z in 𝓝 z₀, monoMaxSet F z ⊆ K := by
  let w : E m := (WithLp.equiv 2 _).symm (fun i => max (z₀ i) 0+2)
  have hw : w ∈ posOrthant m := by
    intro i
    change 0 < max (z₀ i) 0+2
    have hi := le_max_right (z₀ i) 0
    linarith
  have hgap (i : Fin m) : z₀ i < w i-1 := by
    change z₀ i < max (z₀ i) 0+2-1
    have hi := le_max_left (z₀ i) 0
    linarith
  obtain ⟨p,hs⟩ := him w hw
  let u : E m := (WithLp.equiv 2 _).symm (fun _ => (1 : ℝ))
  have hup : u ∈ posOrthant m := by intro i; change 0 < (1 : ℝ); norm_num
  have hun : u ∈ nonnegOrthant m := fun i => (hup i).le
  have hut := hfinite u hup
  let r := slaterCost F z₀ u+1
  let R := max (r+inner ℝ w p-(F p).toReal) 0
  let H := PiLp.homeomorph 2 (fun _ : Fin m => ℝ)
  let K := H ⁻¹' Set.pi Set.univ (fun _ : Fin m => Set.Icc (0 : ℝ) R)
  have hbox : IsCompact (Set.pi Set.univ (fun _ : Fin m => Set.Icc (0 : ℝ) R)) := by
    simpa only [Set.pi,Set.mem_univ,forall_const] using
      (isCompact_pi_infinite fun _ : Fin m => (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) R)))
  refine ⟨K,H.isCompact_preimage.mpr hbox,?_⟩
  have hcoord : ∀ᶠ z in 𝓝 z₀, ∀ i, z i < w i-1 := by
    have hopen : IsOpen {z : E m | ∀ i, z i < w i-1} := by
      have he : {z : E m | ∀ i, z i < w i-1}=⋂ i : Fin m, {z : E m | z i < w i-1} := by ext z; simp
      rw [he]
      apply isOpen_iInter_of_finite
      intro i
      have hi : Continuous (fun z : E m => z i) := by fun_prop
      exact isOpen_lt hi continuous_const
    exact hopen.mem_nhds hgap
  have hc : Continuous (fun z : E m => slaterCost F z u) := by dsimp [slaterCost]; fun_prop
  have hcost : ∀ᶠ z in 𝓝 z₀, slaterCost F z u < r :=
    (hc.tendsto z₀).eventually (Iio_mem_nhds (show slaterCost F z₀ u < r by dsimp [r]; linarith))
  filter_upwards [hcoord,hcost] with z hz hz'
  intro q hq
  have hmin := monoMax_min_cost F hp z q hq u hun
  have heu : linearCost F z u=(slaterCost F z u : EReal) := by
    rw [linearCost,← EReal.coe_toReal hut (hp.1 u),← EReal.coe_sub]
    rfl
  have hqc : linearCost F z q ≤ (r : EReal) := by
    rw [heu] at hmin
    exact hmin.trans (EReal.coe_le_coe_iff.mpr hz'.le)
  have hql := (linearLevel_cost_iff F z q r).mpr ⟨hq.1,hqc⟩
  have hzg (i : Fin m) : 1 ≤ w i-z i := by have hi := hz i; linarith
  change (fun i => q i) ∈ Set.pi Set.univ (fun _ : Fin m => Set.Icc (0 : ℝ) R)
  simp only [Set.mem_pi,Set.mem_univ,forall_const,Set.mem_Icc]
  exact fun i => ⟨hq.1 i,linearLevel_coordinate_bound F hp z p w hs hzg r q hql i⟩
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult Filter Topology
namespace BregmanIneqMultCodex
variable {m : ℕ}

noncomputable def monoOptimizer (F : E m → EReal) (hp : IsProperFn F)
    (hf : LowerSemicontinuous F)
    (hfinite : ∀ p : E m, p ∈ posOrthant m → F p ≠ ⊤)
    (him : ∀ z : E m, z ∈ posOrthant m → ∃ p : E m, IsSubgradient F p z)
    (z : E m) : E m := Classical.choose (original_monoconj_maximizer F hp hf hfinite him z)

theorem monoOptimizer_mem (F : E m → EReal) (hp : IsProperFn F)
    (hf : LowerSemicontinuous F)
    (hfinite : ∀ p : E m, p ∈ posOrthant m → F p ≠ ⊤)
    (him : ∀ z : E m, z ∈ posOrthant m → ∃ p : E m, IsSubgradient F p z)
    (z : E m) : monoOptimizer F hp hf hfinite him z ∈ monoMaxSet F z :=
  Classical.choose_spec (original_monoconj_maximizer F hp hf hfinite him z)

theorem monoOptimizer_continuous (F : E m → EReal) (hp : IsProperFn F)
    (hc : IsConvexFn F) (hf : LowerSemicontinuous F) (hstrict : EssentiallyStrictlyConvex F)
    (hfinite : ∀ p : E m, p ∈ posOrthant m → F p ≠ ⊤)
    (him : ∀ z : E m, z ∈ posOrthant m → ∃ p : E m, IsSubgradient F p z) :
    Continuous (monoOptimizer F hp hf hfinite him) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨K,hK,hmem⟩ := monoMax_local_compact F hp hfinite him z
  apply hK.tendsto_nhds_of_unique_mapClusterPt
  · filter_upwards [hmem] with t ht
    exact ht (monoOptimizer_mem F hp hf hfinite him t)
  · intro q hq hx
    obtain ⟨U,hU,hT⟩ := mapClusterPt_iff_ultrafilter.mp hx
    let u : E m := (WithLp.equiv 2 _).symm (fun _ => (1 : ℝ))
    have hup : u ∈ posOrthant m := by intro i; change 0 < (1 : ℝ); norm_num
    have hun : u ∈ nonnegOrthant m := fun i => (hup i).le
    have hz : Tendsto (fun t : E m => t) (U : Filter (E m)) (𝓝 z) := tendsto_id.mono_left hU
    have hgraph := monoMax_graph_limit (U : Filter (E m)) F hp hf u hun (hfinite u hup)
      (fun t : E m => t) (monoOptimizer F hp hf hfinite him) z q hz hT
      (Eventually.of_forall (monoOptimizer_mem F hp hf hfinite him))
    exact original_monoconj_maximizer_unique F hp hc hstrict hfinite z q
      (monoOptimizer F hp hf hfinite him z) hgraph (monoOptimizer_mem F hp hf hfinite him z)
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult Filter Topology
namespace BregmanIneqMultCodex
variable {m : ℕ}
noncomputable def monoConjReal (F : E m → EReal) (z : E m) : ℝ := (monoConjE F z).toReal

theorem monoConj_support (F : E m → EReal) (hp : IsProperFn F) (hf : LowerSemicontinuous F)
    (hfinite : ∀ p : E m, p ∈ posOrthant m → F p ≠ ⊤)
    (him : ∀ z : E m, z ∈ posOrthant m → ∃ p : E m, IsSubgradient F p z)
    (z y : E m) : inner ℝ (monoOptimizer F hp hf hfinite him z) (y-z) ≤
      monoConjReal F y-monoConjReal F z := by
  let q := monoOptimizer F hp hf hfinite him z
  have hq := monoOptimizer_mem F hp hf hfinite him z
  have hy := original_monoconj_finite F hp hfinite him y
  have ey := EReal.coe_toReal hy.1 hy.2
  have eq := EReal.coe_toReal hq.2.1 (hp.1 q)
  have hi : ((inner ℝ q y : ℝ) : EReal)-F q ≤ monoConjE F y :=
    le_iSup_of_le q (le_iSup_of_le hq.1 le_rfl)
  rw [← ey,← eq,← EReal.coe_sub] at hi
  have hir := EReal.coe_le_coe_iff.mp hi
  have ez := congrArg EReal.toReal hq.2.2
  simp only [EReal.toReal_coe] at ez
  change inner ℝ q (y-z) ≤ (monoConjE F y).toReal-(monoConjE F z).toReal
  rw [inner_sub_right]
  linarith

theorem monoConj_hasFDerivAt (F : E m → EReal) (hp : IsProperFn F)
    (hc : IsConvexFn F) (hf : LowerSemicontinuous F) (hstrict : EssentiallyStrictlyConvex F)
    (hfinite : ∀ p : E m, p ∈ posOrthant m → F p ≠ ⊤)
    (him : ∀ z : E m, z ∈ posOrthant m → ∃ p : E m, IsSubgradient F p z)
    (z : E m) : HasFDerivAt (monoConjReal F)
      ((InnerProductSpace.toDual ℝ _) (monoOptimizer F hp hf hfinite him z)) z := by
  apply hasFDerivAt_iff_isLittleO.mpr
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hj : Tendsto (monoOptimizer F hp hf hfinite him) (𝓝 z)
      (𝓝 (monoOptimizer F hp hf hfinite him z)) :=
    (monoOptimizer_continuous F hp hc hf hstrict hfinite him).continuousAt.tendsto
  have ht : Tendsto (fun y => ‖monoOptimizer F hp hf hfinite him y-monoOptimizer F hp hf hfinite him z‖)
      (𝓝 z) (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hj.sub_const (monoOptimizer F hp hf hfinite him z)).norm
  filter_upwards [ht.eventually (Iio_mem_nhds hε)] with y hy
  have hl := monoConj_support F hp hf hfinite him z y
  have hu := monoConj_support F hp hf hfinite him y z
  rw [← neg_sub y z,inner_neg_right] at hu
  have hpos : 0 ≤ monoConjReal F y-monoConjReal F z-inner ℝ (monoOptimizer F hp hf hfinite him z) (y-z) := by linarith
  have hb : monoConjReal F y-monoConjReal F z-inner ℝ (monoOptimizer F hp hf hfinite him z) (y-z) ≤
      inner ℝ (monoOptimizer F hp hf hfinite him y-monoOptimizer F hp hf hfinite him z) (y-z) := by
    rw [inner_sub_left]; linarith
  simp only [InnerProductSpace.toDual_apply_apply]
  rw [Real.norm_of_nonneg hpos]
  exact hb.trans ((real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hy.le (norm_nonneg _)))
theorem monoConj_gradient (F : E m → EReal) (hp : IsProperFn F)
    (hc : IsConvexFn F) (hf : LowerSemicontinuous F) (hstrict : EssentiallyStrictlyConvex F)
    (hfinite : ∀ p : E m, p ∈ posOrthant m → F p ≠ ⊤)
    (him : ∀ z : E m, z ∈ posOrthant m → ∃ p : E m, IsSubgradient F p z)
    (z : E m) : gradient (monoConjReal F) z=monoOptimizer F hp hf hfinite him z := by
  have hd := (monoConj_hasFDerivAt F hp hc hf hstrict hfinite him z).fderiv
  change (InnerProductSpace.toDual ℝ _).symm (fderiv ℝ (monoConjReal F) z)=_
  rw [hd]
  exact (InnerProductSpace.toDual ℝ _).symm_apply_apply _
end BregmanIneqMultCodex


end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- First-order support at a point in the original open zone, including boundary test points. -/
theorem gradient_support (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h)
    {y z : H} (hy : y ∈ S) (hz : z ∈ closure S) :
    inner ℝ (gradient h y) (z-y) ≤ h z-h y := by
  have hd : DifferentiableAt ℝ h y :=
    ((hh.contDiffOn.differentiableOn (by simp)) y hy).differentiableAt (hh.isOpen.mem_nhds hy)
  let l : ℝ →ᵃ[ℝ] H := AffineMap.lineMap y z
  have hcv := hh.strictConvexOn.convexOn.comp_affineMap l
  have h0 : (0 : ℝ) ∈ l ⁻¹' closure S := by simpa [l] using subset_closure hy
  have h1 : (1 : ℝ) ∈ l ⁻¹' closure S := by simpa [l] using hz
  have hder : HasDerivAt (h ∘ l) (fderiv ℝ h y (z-y)) 0 := by
    apply hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap (a := y) (b := z) (x := (0 : ℝ)))
    simp [l]
  have hs := hcv.le_slope_of_hasDerivAt h0 h1 (by norm_num) hder
  simpa [l,slope,inner_gradient_left] using hs

theorem bregman_nonneg (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h)
    {x y : H} (hx : x ∈ closure S) (hy : y ∈ S) : 0 ≤ bregmanD h x y := by
  have hs := gradient_support S h hh hy hx
  dsimp [bregmanD]; linarith
end BregmanPPACodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.Convergence Filter Topology
namespace BregmanIneqMultCodex
variable {m : ℕ}

theorem nonneg_subset_closure_of_pos_subset (S : Set (E m)) (hS : posOrthant m ⊆ S) :
    nonnegOrthant m ⊆ closure S := by
  intro p hp
  let u : E m := (WithLp.equiv 2 _).symm (fun _ => (1 : ℝ))
  have hc : Continuous (fun t : ℝ => p+t • u) := by fun_prop
  have ht : Tendsto (fun t : ℝ => p+t • u) (𝓝[>] (0 : ℝ)) (𝓝 p) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply isClosed_closure.mem_of_tendsto ht
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [hpos] with t ht
  apply subset_closure
  apply hS
  intro i
  change 0 < p i+t*1
  have hi := hp i
  linarith

theorem extendedH_gradient_subgradient (S : Set (E m)) (h : E m → ℝ)
    (hh : IsBregmanFunction S h) (p : E m) (hp : p ∈ S) :
    IsSubgradient (extendedH S h) p (gradient h p) := by
  classical
  have hpc : p ∈ closure S := subset_closure hp
  refine ⟨?_,?_⟩
  · simp only [extendedH,if_pos hpc]; exact EReal.coe_ne_top _
  · intro q
    by_cases hqc : q ∈ closure S
    · simp only [extendedH,if_pos hpc,if_pos hqc,← EReal.coe_add]
      apply EReal.coe_le_coe_iff.mpr
      have hi := BregmanPPACodex.gradient_support S h hh hp hqc
      linarith
    · simp only [extendedH,if_neg hqc]; exact le_top

theorem monoConj_extendedH_eq (S : Set (E m)) (h : E m → ℝ)
    (hS : posOrthant m ⊆ S) : monoConjE (extendedH S h)=monoConj h := by
  classical
  funext z
  apply iSup_congr
  intro q
  apply iSup_congr
  intro hq
  have hqc := nonneg_subset_closure_of_pos_subset S hS hq
  simp only [extendedH,if_pos hqc,← EReal.coe_sub]

theorem extendedH_positive_finite (S : Set (E m)) (h : E m → ℝ) (hS : posOrthant m ⊆ S)
    (p : E m) (hp : p ∈ posOrthant m) : extendedH S h p ≠ ⊤ := by
  classical
  have hpc := subset_closure (hS hp)
  simp only [extendedH,if_pos hpc]
  exact EReal.coe_ne_top _

theorem extendedH_positive_subgradient_image (S : Set (E m)) (h : E m → ℝ)
    (hh : IsBregmanFunction S h) (him : posOrthant m ⊆ gradient h '' S)
    (z : E m) (hz : z ∈ posOrthant m) : ∃ p, IsSubgradient (extendedH S h) p z := by
  obtain ⟨p,hp,hz'⟩ := him hz
  exact ⟨p,hz' ▸ extendedH_gradient_subgradient S h hh p hp⟩
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.Convergence
namespace BregmanIneqMultCodex
variable {m : ℕ}

theorem extendedH_epi_iff (S : Set (E m)) (h : E m → ℝ) (p : E m) (r : ℝ) :
    extendedH S h p ≤ (r : EReal) ↔ p ∈ closure S ∧ h p ≤ r := by
  classical
  by_cases hp : p ∈ closure S
  · simp [extendedH,hp,EReal.coe_le_coe_iff]
  · simp [extendedH,hp,top_le_iff]

theorem extendedH_proper (S : Set (E m)) (h : E m → ℝ) (hS : posOrthant m ⊆ S) :
    IsProperFn (extendedH S h) := by
  classical
  refine ⟨?_,?_⟩
  · intro p
    by_cases hp : p ∈ closure S
    · simp only [extendedH,if_pos hp]; exact EReal.coe_ne_bot _
    · simp only [extendedH,if_neg hp]; exact top_ne_bot
  · let u : E m := (WithLp.equiv 2 _).symm (fun _ => (1 : ℝ))
    have hu : u ∈ posOrthant m := by intro i; change 0 < (1 : ℝ); norm_num
    exact ⟨u,extendedH_positive_finite S h hS u hu⟩

theorem extendedH_convex (S : Set (E m)) (h : E m → ℝ) (hh : IsBregmanFunction S h) :
    IsConvexFn (extendedH S h) := by
  intro p hp q hq α β hα hβ hab
  have hpc := (extendedH_epi_iff S h p.1 p.2).mp hp
  have hqc := (extendedH_epi_iff S h q.1 q.2).mp hq
  apply (extendedH_epi_iff S h _ _).mpr
  refine ⟨hh.strictConvexOn.1 hpc.1 hqc.1 hα hβ hab,?_⟩
  change h (α • p.1+β • q.1) ≤ α*p.2+β*q.2
  have hi := hh.strictConvexOn.convexOn.2 hpc.1 hqc.1 hα hβ hab
  change h (α • p.1+β • q.1) ≤ α*h p.1+β*h q.1 at hi
  nlinarith [mul_le_mul_of_nonneg_left hpc.2 hα,mul_le_mul_of_nonneg_left hqc.2 hβ]

theorem extendedH_lsc (S : Set (E m)) (h : E m → ℝ) (hh : IsBregmanFunction S h) :
    LowerSemicontinuous (extendedH S h) := by
  classical
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  by_cases ha : a=⊤
  · subst a; simp
  have he : (extendedH S h) ⁻¹' Set.Iic a=
      closure S ∩ (fun p => (h p : EReal)) ⁻¹' Set.Iic a := by
    ext p
    by_cases hp : p ∈ closure S
    · simp [extendedH,hp]
    · simp [extendedH,hp,top_le_iff,ha]
  rw [he]
  have hc := continuous_coe_real_ereal.comp_continuousOn hh.continuousOn
  exact hc.preimage_isClosed_of_isClosed isClosed_closure isClosed_Iic

theorem extendedH_essential_strict (S : Set (E m)) (h : E m → ℝ) (hh : IsBregmanFunction S h) :
    EssentiallyStrictlyConvex (extendedH S h) := by
  classical
  intro s hs hdom
  have hsub : s ⊆ closure S := by
    intro p hp
    obtain ⟨g,hg⟩ := hdom hp
    have hpt : extendedH S h p ≠ ⊤ := hg.1
    by_contra hn
    apply hpt
    simp only [extendedH,if_neg hn]
  apply (hh.strictConvexOn.subset hsub hs).congr
  intro p hp
  simp only [extendedH,if_pos (hsub hp),EReal.toReal_coe]
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult
namespace BregmanIneqMultCodex
variable {m : ℕ}

theorem conjugate_ne_bot (F : E m → EReal) (hp : IsProperFn F) (z : E m) : conjE F z ≠ ⊥ := by
  obtain ⟨u,hut⟩ := hp.2
  have hi : ((inner ℝ u z : ℝ) : EReal)-F u ≤ conjE F z :=
    le_iSup (fun u => ((inner ℝ u z : ℝ) : EReal)-F u) u
  rw [← EReal.coe_toReal hut (hp.1 u),← EReal.coe_sub] at hi
  exact ne_of_gt ((EReal.bot_lt_coe _).trans_le hi)

theorem monoConjE_indicator_representation (F : E m → EReal) (hp : IsProperFn F) (z : E m) :
    monoConjE F z=conjE (fun p => F p+indicatorPos m p) z := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro p
    apply iSup_le
    intro hn
    have hi : ((inner ℝ p z : ℝ) : EReal)-(F p+indicatorPos m p) ≤
        conjE (fun p => F p+indicatorPos m p) z :=
      le_iSup (fun p => ((inner ℝ p z : ℝ) : EReal)-(F p+indicatorPos m p)) p
    simpa only [indicatorPos,if_pos hn,add_zero] using hi
  · apply iSup_le
    intro p
    by_cases hn : p ∈ nonnegOrthant m
    · have hi : ((inner ℝ p z : ℝ) : EReal)-F p ≤ monoConjE F z :=
        le_iSup_of_le p (le_iSup_of_le hn le_rfl)
      simpa only [indicatorPos,if_pos hn,add_zero] using hi
    · simp only [indicatorPos,if_neg hn,EReal.add_top_of_ne_bot (hp.1 p),EReal.sub_top]
      exact bot_le

theorem monoConjE_upper_infimum (F : E m → EReal) (hp : IsProperFn F)
    (hc : IsConvexFn F) (u : E m) (hu : u ∈ posOrthant m) (hut : F u ≠ ⊤) (z : E m) :
    monoConjE F z=⨅ w ∈ {w : E m | ∀ i, z i ≤ w i}, conjE F w := by
  apply le_antisymm
  · apply le_iInf
    intro w
    apply le_iInf
    intro hw
    exact original_monoconj_upper_argument F hp z w hw
  · by_cases hz : monoConjE F z=⊤
    · rw [hz]; exact le_top
    obtain ⟨w,hw,he⟩ := original_monoconj_attainment_of_positive_finite F hp hc u hu hut z hz
    exact iInf_le_of_le w (iInf_le_of_le hw he.ge)

theorem infConv_indicatorNeg_representation (G : E m → EReal)
    (hG : ∀ w, G w ≠ ⊥) (z : E m) :
    infConv G (indicatorNeg m) z=⨅ w ∈ {w : E m | ∀ i, z i ≤ w i}, G w := by
  classical
  apply le_antisymm
  · apply le_iInf
    intro w
    apply le_iInf
    intro hw
    have hn : ∀ i, (z-w) i ≤ 0 := by
      intro i; change z i-w i ≤ 0; exact sub_nonpos.mpr (hw i)
    have hi : infConv G (indicatorNeg m) z ≤ G (z-(z-w))+indicatorNeg m (z-w) :=
      iInf_le (fun y => G (z-y)+indicatorNeg m y) (z-w)
    have he : z-(z-w)=w := by abel
    simpa only [he,indicatorNeg,if_pos hn,add_zero] using hi
  · apply le_iInf
    intro y
    by_cases hn : ∀ i, y i ≤ 0
    · have hw : ∀ i, z i ≤ (z-y) i := by
        intro i; change z i ≤ z i-y i; have hi := hn i; linarith
      have hi : (⨅ w ∈ {w : E m | ∀ i, z i ≤ w i}, G w) ≤ G (z-y) :=
        iInf_le_of_le (z-y) (iInf_le_of_le hw le_rfl)
      simpa only [indicatorNeg,if_pos hn,add_zero] using hi
    · simp only [indicatorNeg,if_neg hn,EReal.add_top_of_ne_bot (hG (z-y))]
      exact le_top

theorem monoConjE_monotone (F : E m → EReal) (hp : IsProperFn F)
    (z y : E m) (hzy : ∀ i, z i ≤ y i) : monoConjE F z ≤ monoConjE F y := by
  apply iSup_le
  intro p
  apply iSup_le
  intro hn
  have hi := nonneg_inner_mono p z y hn hzy
  have ht : ((inner ℝ p z : ℝ) : EReal)-F p ≤ ((inner ℝ p y : ℝ) : EReal)-F p := by
    by_cases hpt : F p=⊤
    · rw [hpt,EReal.sub_top,EReal.sub_top]
    · rw [← EReal.coe_toReal hpt (hp.1 p),← EReal.coe_sub,← EReal.coe_sub]
      exact EReal.coe_le_coe_iff.mpr (sub_le_sub_right hi _)
  exact ht.trans (le_iSup_of_le p (le_iSup_of_le hn le_rfl))
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB
namespace BregmanEqMultCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Necessary subgradient condition for the original extended-real convex objective. -/
theorem convex_smooth_min_subgradient (F : H → EReal) (hp : IsProperFn F)
    (hc : IsConvexFn F) (G : H → ℝ) (z g : H)
    (hd : HasFDerivAt G ((InnerProductSpace.toDual ℝ H) g) z)
    (hmin : ∀ y, F z+(G z : EReal) ≤ F y+(G y : EReal)) :
    IsSubgradient F z (-g) := by
  have hz : F z ≠ ⊤ := by
    obtain ⟨y,hy⟩ := hp.2
    have hey := EReal.coe_toReal hy (hp.1 y)
    intro hzt
    have hm := hmin y
    rw [hzt,EReal.top_add_coe,← hey,← EReal.coe_add] at hm
    exact EReal.coe_ne_top _ (top_le_iff.mp hm)
  refine ⟨hz,?_⟩
  intro y
  by_cases hy : F y=⊤
  · rw [hy]; exact le_top
  have ez := EReal.coe_toReal hz (hp.1 z)
  have ey := EReal.coe_toReal hy (hp.1 y)
  rw [← ez,← ey,← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  let l : ℝ →ᵃ[ℝ] H := AffineMap.lineMap z y
  have hder : HasDerivAt (G ∘ l) (inner ℝ g (y-z)) 0 := by
    simpa only [l,InnerProductSpace.toDual_apply_apply] using
      hd.comp_hasDerivAt_of_eq (0 : ℝ)
        (AffineMap.hasDerivAt_lineMap (a := z) (b := y) (x := (0 : ℝ))) (by simp)
  have hb : ∀ t : ℝ, 0 < t → t < 1 →
      (F z).toReal-(F y).toReal ≤ t⁻¹*(G (l t)-G z) := by
    intro t ht ht1
    have hez : (z,(F z).toReal) ∈ {p : H × ℝ | F p.1 ≤ (p.2 : EReal)} := by
      change F z ≤ ((F z).toReal : EReal); rw [ez]
    have hey : (y,(F y).toReal) ∈ {p : H × ℝ | F p.1 ≤ (p.2 : EReal)} := by
      change F y ≤ ((F y).toReal : EReal); rw [ey]
    have hcv := hc hez hey (show 0 ≤ 1-t by linarith) ht.le (show (1-t)+t=1 by ring)
    change F ((1-t) • z+t • y) ≤ (((1-t)*(F z).toReal+t*(F y).toReal : ℝ) : EReal) at hcv
    have hl : l t=(1-t) • z+t • y := by simp [l,AffineMap.lineMap_apply_module]
    rw [← hl] at hcv
    have hft : F (l t) ≠ ⊤ := ne_of_lt (hcv.trans_lt (EReal.coe_lt_top _))
    have eft := EReal.coe_toReal hft (hp.1 (l t))
    have hm := hmin (l t)
    rw [← ez,← eft,← EReal.coe_add,← EReal.coe_add] at hm
    have hmr := EReal.coe_le_coe_iff.mp hm
    rw [← eft] at hcv
    have hcvr := EReal.coe_le_coe_iff.mp hcv
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ ht).mpr
    change ((F z).toReal-(F y).toReal)*t ≤ G (l t)-G z
    nlinarith
  have hs := hder.tendsto_slope_zero_right
  have hlow : (F z).toReal-(F y).toReal ≤ inner ℝ g (y-z) := by
    apply ge_of_tendsto hs
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    simpa only [l,Function.comp_def,zero_add,smul_eq_mul,AffineMap.lineMap_apply_zero] using hb t ht ht1
  rw [inner_neg_left]
  linarith
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.Convergence
namespace BregmanIneqMultCodex
variable {m : ℕ}

theorem indicatorPos_epi_iff (p : E m) (r : ℝ) :
    indicatorPos m p ≤ (r : EReal) ↔ p ∈ nonnegOrthant m ∧ 0 ≤ r := by
  classical
  by_cases hp : p ∈ nonnegOrthant m
  · simp [indicatorPos,hp]
  · simp [indicatorPos,hp,top_le_iff]

theorem indicatorPos_proper : IsProperFn (indicatorPos m) := by
  classical
  refine ⟨?_,0,?_⟩
  · intro p
    by_cases hp : p ∈ nonnegOrthant m
    · simp only [indicatorPos,if_pos hp]; exact EReal.zero_ne_bot
    · simp only [indicatorPos,if_neg hp]; exact top_ne_bot
  · have hn : (0 : E m) ∈ nonnegOrthant m := by intro i; simp
    simp only [indicatorPos,if_pos hn]; exact EReal.zero_ne_top

theorem indicatorPos_convex : IsConvexFn (indicatorPos m) := by
  intro p hp q hq α β hα hβ hab
  have hp' := (indicatorPos_epi_iff p.1 p.2).mp hp
  have hq' := (indicatorPos_epi_iff q.1 q.2).mp hq
  apply (indicatorPos_epi_iff _ _).mpr
  constructor
  · intro i
    change 0 ≤ α*p.1 i+β*q.1 i
    exact add_nonneg (mul_nonneg hα (hp'.1 i)) (mul_nonneg hβ (hq'.1 i))
  · change 0 ≤ α*p.2+β*q.2
    exact add_nonneg (mul_nonneg hα hp'.2) (mul_nonneg hβ hq'.2)

theorem monoConj_gradient_value (S : Set (E m)) (h : E m → ℝ)
    (hh : IsBregmanFunction S h) (hS : posOrthant m ⊆ S)
    (him : posOrthant m ⊆ gradient h '' S) (z : E m) :
    let p := gradient (fun z => (monoConj h z).toReal) z
    p ∈ nonnegOrthant m ∧ monoConj h z=(((inner ℝ p z-h p : ℝ)) : EReal) := by
  let F := extendedH S h
  have hp := extendedH_proper S h hS
  have hc := extendedH_convex S h hh
  have hf := extendedH_lsc S h hh
  have hs := extendedH_essential_strict S h hh
  have hfinite := extendedH_positive_finite S h hS
  have hsub := extendedH_positive_subgradient_image S h hh him
  have he : monoConjE F=monoConj h := monoConj_extendedH_eq S h hS
  have hre : monoConjReal F=(fun z => (monoConj h z).toReal) := by
    funext z; exact congrArg EReal.toReal (congrFun he z)
  have hg := monoConj_gradient F hp hc hf hs hfinite hsub z
  rw [hre] at hg
  have hq := monoOptimizer_mem F hp hf hfinite hsub z
  rw [← hg] at hq
  have hqc := nonneg_subset_closure_of_pos_subset S hS hq.1
  refine ⟨hq.1,?_⟩
  have hv := hq.2.2
  rw [he] at hv
  simpa only [F,extendedH,if_pos hqc,EReal.toReal_coe] using hv

theorem monoConj_projected_stationarity (S : Set (E m)) (h : E m → ℝ)
    (hh : IsBregmanFunction S h) (hS : posOrthant m ⊆ S)
    (him : posOrthant m ⊆ gradient h '' S) (z : E m)
    (hpS : gradient (fun z => (monoConj h z).toReal) z ∈ S) :
    z-gradient h (gradient (fun z => (monoConj h z).toReal) z) ∈
      normalCone (nonnegOrthant m) (gradient (fun z => (monoConj h z).toReal) z) := by
  classical
  let p := gradient (fun z => (monoConj h z).toReal) z
  have hval := monoConj_gradient_value S h hh hS him z
  have hpn : p ∈ nonnegOrthant m := hval.1
  have hpv : monoConj h z=(((inner ℝ p z-h p : ℝ)) : EReal) := hval.2
  let G : E m → ℝ := fun q => h q-inner ℝ z q
  have hd : DifferentiableAt ℝ h p :=
    ((hh.contDiffOn.differentiableOn (by simp)) p hpS).differentiableAt (hh.isOpen.mem_nhds hpS)
  have hdh := hd.hasGradientAt.hasFDerivAt
  have hdG : HasFDerivAt G ((InnerProductSpace.toDual ℝ _) (gradient h p-z)) p := by
    rw [map_sub]
    convert hdh.sub ((InnerProductSpace.toDual ℝ _) z).hasFDerivAt using 1 <;>
      first | rfl | (ext q; simp [G])
  have hmin : ∀ q, indicatorPos m p+(G p : EReal) ≤ indicatorPos m q+(G q : EReal) := by
    intro q
    simp only [indicatorPos,if_pos hpn,zero_add]
    by_cases hqn : q ∈ nonnegOrthant m
    · simp only [if_pos hqn,zero_add]
      apply EReal.coe_le_coe_iff.mpr
      have hi : (((inner ℝ q z-h q : ℝ)) : EReal) ≤ monoConj h z :=
        le_iSup_of_le q (le_iSup_of_le hqn le_rfl)
      rw [hpv] at hi
      have hir := EReal.coe_le_coe_iff.mp hi
      have hqz : inner ℝ q z=inner ℝ z q := real_inner_comm _ _
      have hpz : inner ℝ p z=inner ℝ z p := real_inner_comm _ _
      rw [hqz,hpz] at hir
      dsimp [G]; linarith
    · simp only [if_neg hqn,EReal.top_add_coe]; exact le_top
  have hg := BregmanEqMultCodex.convex_smooth_min_subgradient (indicatorPos m)
    indicatorPos_proper indicatorPos_convex G p (gradient h p-z) hdG hmin
  refine ⟨hval.1,?_⟩
  intro q hqn
  have hi := hg.2 q
  simp only [indicatorPos,if_pos hpn,if_pos hqn,zero_add] at hi
  have hir : inner ℝ (-(gradient h p-z)) (q-p) ≤ 0 := by
    exact EReal.coe_le_coe_iff.mp (by simpa only [EReal.coe_zero] using hi)
  simpa only [neg_sub] using hir
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.Convergence
namespace BregmanIneqMultCodex
variable {n m : ℕ}

theorem finite_convex_toReal (C : Set (E n)) (F : E n → EReal)
    (hp : IsProperFn F) (hc : IsConvexFn F) (hC : Convex ℝ C)
    (hf : ∀ x ∈ C, F x ≠ ⊤) : ConvexOn ℝ C (fun x => (F x).toReal) := by
  refine ⟨hC,?_⟩
  intro x hx y hy a b ha hb hab
  have ex := EReal.coe_toReal (hf x hx) (hp.1 x)
  have ey := EReal.coe_toReal (hf y hy) (hp.1 y)
  have hz := hC hx hy ha hb hab
  have ez := EReal.coe_toReal (hf _ hz) (hp.1 _)
  have hx' : (x,(F x).toReal) ∈ {p : E n × ℝ | F p.1 ≤ (p.2 : EReal)} := by
    change F x ≤ ((F x).toReal : EReal); rw [ex]
  have hy' : (y,(F y).toReal) ∈ {p : E n × ℝ | F p.1 ≤ (p.2 : EReal)} := by
    change F y ≤ ((F y).toReal : EReal); rw [ey]
  have hi := hc hx' hy' ha hb hab
  change F (a • x+b • y) ≤ (((a*(F x).toReal+b*(F y).toReal : ℝ)) : EReal) at hi
  rw [← ez] at hi
  exact EReal.coe_le_coe_iff.mp hi

/-- Segment optimality for a coordinatewise monotone smooth outer penalty. -/
theorem monotone_penalty_lagrangian_min (C : Set (E n)) (f : E n → ℝ)
    (g : E n → E m) (M : E m → ℝ) (a : E m) (c : ℝ) (x : E n)
    (hf : ConvexOn ℝ C f) (hg : ∀ i, ConvexOn ℝ C (fun x => g x i))
    (hM : ∀ z w, (∀ i, z i ≤ w i) → M z ≤ M w) (hc : 0 < c) (hx : x ∈ C)
    (hd : HasFDerivAt M ((InnerProductSpace.toDual ℝ _) (gradient M (a+c • g x))) (a+c • g x))
    (hmin : ∀ y ∈ C, f x+c⁻¹*M (a+c • g x) ≤ f y+c⁻¹*M (a+c • g y)) :
    ∀ y ∈ C, f x+inner ℝ (gradient M (a+c • g x)) (g x) ≤
      f y+inner ℝ (gradient M (a+c • g x)) (g y) := by
  intro y hy
  let z := a+c • g x
  let d := c • (g y-g x)
  let l : ℝ →ᵃ[ℝ] E m := AffineMap.lineMap z (z+d)
  have hder : HasDerivAt (M ∘ l) (inner ℝ (gradient M z) d) 0 := by
    simpa only [sub_self,add_sub_cancel_left,InnerProductSpace.toDual_apply_apply] using
      hd.comp_hasDerivAt_of_eq (0 : ℝ)
        (AffineMap.hasDerivAt_lineMap (a := z) (b := z+d) (x := (0 : ℝ))) (by simp [l,z])
  have hb : ∀ t : ℝ, 0 < t → t < 1 →
      c*(f x-f y) ≤ t⁻¹*(M (l t)-M z) := by
    intro t ht ht1
    let xt := (1-t) • x+t • y
    have hxt := hf.1 hx hy (show 0 ≤ 1-t by linarith) ht.le (show (1-t)+t=1 by ring)
    have hfx := hf.2 hx hy (show 0 ≤ 1-t by linarith) ht.le (show (1-t)+t=1 by ring)
    have hgv : ∀ i, (a+c • g xt) i ≤ (l t) i := by
      intro i
      have hi := (hg i).2 hx hy (show 0 ≤ 1-t by linarith) ht.le (show (1-t)+t=1 by ring)
      have he : (l t) i=a i+c*((1-t)*g x i+t*g y i) := by
        simp only [l,AffineMap.lineMap_apply_module,z,d,PiLp.add_apply,PiLp.smul_apply,
          PiLp.sub_apply,smul_eq_mul]
        ring
      rw [he]
      change a i+c*g xt i ≤ a i+c*((1-t)*g x i+t*g y i)
      simpa only [xt,smul_eq_mul,add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_left hi hc.le) (a i)
    have hm := hmin xt hxt
    have houter := hM _ _ hgv
    have hbound := mul_le_mul_of_nonneg_left houter (inv_nonneg.mpr hc.le)
    have hright : f x+c⁻¹*M z ≤ (1-t)*f x+t*f y+c⁻¹*M (l t) := by
      dsimp only [xt] at hm
      change f x+c⁻¹*M z ≤ _ at hm
      exact hm.trans (add_le_add hfx hbound)
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ ht).mpr
    have he : c*(c⁻¹*M (l t)-c⁻¹*M z)=M (l t)-M z := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hright hc.le]
  have hl : c*(f x-f y) ≤ inner ℝ (gradient M z) d := by
    apply ge_of_tendsto hder.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    simpa only [Function.comp_def,zero_add,smul_eq_mul,l,AffineMap.lineMap_apply_zero] using hb t ht ht1
  simp only [d,inner_smul_right,inner_sub_right] at hl
  have hi : f x-f y ≤ inner ℝ (gradient M z) (g y)-inner ℝ (gradient M z) (g x) := by
    nlinarith [hl]
  dsimp only [z] at hi
  linarith
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.ProxMult
namespace BregmanProxMultCodex

theorem indicator_support {m : ℕ} (p u : E m) (hp : p ∈ nonnegOrthant m) :
    IsSubgradient (indicatorPos m) p u ↔
      ∀ q ∈ nonnegOrthant m, inner ℝ u (q-p) ≤ 0 := by
  classical
  constructor
  · rintro ⟨_,h⟩ q hq
    simpa [indicatorPos,hp,hq] using h q
  · intro h
    refine ⟨by simp [indicatorPos,hp],?_⟩
    intro q
    by_cases hq : q ∈ nonnegOrthant m
    · simpa [indicatorPos,hp,hq] using h q hq
    · simp [indicatorPos,hp,hq]

theorem lagr_finite_rep {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (x : E n) (hx : x ∈ C) (q : E m) (hq : q ∈ nonnegOrthant m) :
    lagr C f g x q = ((f x).toReal + inner ℝ q (gvec g x) : ℝ) := by
  classical
  simp only [lagr,if_pos hx,if_pos hq]
  rw [← EReal.coe_toReal (hP.f_finite x hx) (hP.f_proper.1 x),← EReal.coe_add]
  congr 1
  simp [PiLp.inner_apply,gvec,mul_comm]

theorem super_support {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (x : E n) (hx : x ∈ C) (p v : E m) (hp : p ∈ nonnegOrthant m) :
    v ∈ supdiffP C f g x p ↔
      ∀ q ∈ nonnegOrthant m, inner ℝ (gvec g x-v) (q-p) ≤ 0 := by
  classical
  constructor
  · rintro ⟨_,hs⟩ q hq
    have hi := hs q
    dsimp only at hi
    rw [lagr_finite_rep C f g hP x hx p hp,lagr_finite_rep C f g hP x hx q hq] at hi
    have hr : -((f x).toReal+inner ℝ p (gvec g x))+
        inner ℝ (-v) (q-p) ≤ -((f x).toReal+inner ℝ q (gvec g x)) := by
      simpa only [← EReal.coe_neg,← EReal.coe_add,EReal.coe_le_coe_iff] using hi
    rw [inner_sub_left,inner_sub_right,real_inner_comm q (gvec g x),
      real_inner_comm p (gvec g x)]
    rw [inner_neg_left] at hr
    linarith
  · intro hs
    change IsSubgradient (fun q => -lagr C f g x q) p (-v)
    refine ⟨?_,?_⟩
    · change -lagr C f g x p ≠ ⊤
      rw [lagr_finite_rep C f g hP x hx p hp,← EReal.coe_neg]
      exact EReal.coe_ne_top _
    · intro q
      dsimp only
      by_cases hq : q ∈ nonnegOrthant m
      · rw [lagr_finite_rep C f g hP x hx p hp,lagr_finite_rep C f g hP x hx q hq]
        have hr := hs q hq
        rw [inner_sub_left,inner_sub_right,real_inner_comm q (gvec g x),
          real_inner_comm p (gvec g x)] at hr
        simp only [← EReal.coe_neg,← EReal.coe_add,EReal.coe_le_coe_iff,inner_neg_left]
        linarith
      · simp [lagr,hx,hq]
end BregmanProxMultCodex

namespace BregmanProxMultCodex

theorem original_supdiff_formula {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g) :
    ∀ x ∈ C, ∀ p ∈ nonnegOrthant m,
      supdiffP C f g x p =
        {v | ∃ u ∈ BregmanPPA.Convergence.subdiffOp (indicatorPos m) p,
          v = gvec g x-u} := by
  intro x hx p hp
  ext v
  change v ∈ supdiffP C f g x p ↔
    ∃ u, IsSubgradient (indicatorPos m) p u ∧ v = gvec g x-u
  rw [super_support C f g hP x hx p v hp]
  constructor
  · intro hs
    exact ⟨gvec g x-v,(indicator_support p (gvec g x-v) hp).mpr hs,by abel⟩
  · rintro ⟨u,hu,hv⟩ q hq
    have he : gvec g x-v=u := by rw [hv]; abel
    rw [he]
    exact (indicator_support p u hp).mp hu q hq
end BregmanProxMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.ProxMult BregmanPPA.Convergence
namespace BregmanProxMultCodex
variable {n m : ℕ}

theorem lagr_real_convex (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (p : E m) (hp : p ∈ nonnegOrthant m) :
    ConvexOn ℝ C (fun y => (f y).toReal+inner ℝ p (gvec g y)) := by
  have hf := BregmanIneqMultCodex.finite_convex_toReal C f hP.f_proper hP.f_convex hP.convex hP.f_finite
  refine ⟨hP.convex,?_⟩
  intro x hx y hy a b ha hb hab
  have hfx := hf.2 hx hy ha hb hab
  have hgg : ∑ i, p i*(g i (a • x+b • y)).toReal ≤
      a*(∑ i, p i*(g i x).toReal)+b*(∑ i, p i*(g i y).toReal) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hg := BregmanIneqMultCodex.finite_convex_toReal C (g i) (hP.g_proper i)
      (hP.g_convex i) hP.convex (hP.g_finite i)
    have hi := mul_le_mul_of_nonneg_left (hg.2 hx hy ha hb hab) (hp i)
    simpa only [smul_eq_mul,mul_add,mul_left_comm] using hi
  simp only [PiLp.inner_apply,Real.inner_apply,gvec,WithLp.equiv_symm_apply,
    smul_eq_mul] at hfx hgg ⊢
  linarith

theorem lagr_epi_iff (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (p : E m) (hp : p ∈ nonnegOrthant m) (x : E n) (r : ℝ) :
    lagr C f g x p ≤ (r : EReal) ↔
      x ∈ C ∧ (f x).toReal+inner ℝ p (gvec g x) ≤ r := by
  classical
  by_cases hx : x ∈ C
  · rw [lagr_finite_rep C f g hP x hx p hp]
    simp only [hx,true_and,EReal.coe_le_coe_iff]
  · simp [lagr,hx,top_le_iff,EReal.coe_ne_top]

theorem lagr_proper_convex (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (p : E m) (hp : p ∈ nonnegOrthant m) :
    IsProperFn (fun y => lagr C f g y p) ∧ IsConvexFn (fun y => lagr C f g y p) := by
  classical
  have hr := lagr_real_convex C f g hP p hp
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro x
    dsimp only
    by_cases hx : x ∈ C
    · rw [lagr_finite_rep C f g hP x hx p hp]; exact EReal.coe_ne_bot _
    · simp [lagr,hx]
  · obtain ⟨x,hx⟩ := hP.nonempty
    refine ⟨x,?_⟩
    dsimp only
    rw [lagr_finite_rep C f g hP x hx p hp]; exact EReal.coe_ne_top _
  · intro x hx y hy a b ha hb hab
    have hx' := (lagr_epi_iff C f g hP p hp x.1 x.2).mp hx
    have hy' := (lagr_epi_iff C f g hP p hp y.1 y.2).mp hy
    apply (lagr_epi_iff C f g hP p hp _ _).mpr
    refine ⟨hP.convex hx'.1 hy'.1 ha hb hab,?_⟩
    have hi := hr.2 hx'.1 hy'.1 ha hb hab
    change _ ≤ a*x.2+b*y.2
    exact hi.trans (add_le_add (mul_le_mul_of_nonneg_left hx'.2 ha)
      (mul_le_mul_of_nonneg_left hy'.2 hb))

theorem bregman_convex_on (C S : Set (E n)) (h : E n → ℝ)
    (hh : IsBregmanFunction S h) (hC : Convex ℝ C) (hS : C ⊆ S) (xk : E n) :
    ConvexOn ℝ C (fun y => bregmanD h y xk) := by
  refine ⟨hC,?_⟩
  intro x hx y hy a b ha hb hab
  have hi := hh.strictConvexOn.convexOn.2
    (subset_closure (hS hx)) (subset_closure (hS hy)) ha hb hab
  have he : inner ℝ (gradient h xk) (a • x+b • y-xk) =
      a*inner ℝ (gradient h xk) (x-xk)+b*inner ℝ (gradient h xk) (y-xk) := by
    rw [inner_sub_right,inner_add_right,inner_smul_right,inner_smul_right,
      inner_sub_right,inner_sub_right]
    have habx : a*inner ℝ (gradient h xk) xk+b*inner ℝ (gradient h xk) xk = inner ℝ (gradient h xk) xk := by
      rw [← add_mul,hab,one_mul]
    nlinarith [habx]
  simp only [bregmanD,smul_eq_mul]
  rw [he]
  simp only [smul_eq_mul] at hi
  have habh : a*h xk+b*h xk=h xk := by rw [← add_mul,hab,one_mul]
  nlinarith [habh]

theorem bregman_penalty_derivative (S : Set (E n)) (h : E n → ℝ)
    (hh : IsBregmanFunction S h) (c : ℝ) (xk z : E n) (hz : z ∈ S) :
    HasFDerivAt (fun y => c⁻¹*bregmanD h y xk)
      ((InnerProductSpace.toDual ℝ _) (c⁻¹ • (gradient h z-gradient h xk))) z := by
  have hd : DifferentiableAt ℝ h z :=
    ((hh.contDiffOn.differentiableOn (by simp)) z hz).differentiableAt (hh.isOpen.mem_nhds hz)
  let L := (InnerProductSpace.toDual ℝ (E n)) (gradient h xk)
  have hl : HasFDerivAt (fun y => L y-L xk) L z := L.hasFDerivAt.sub_const (L xk)
  have he := ((hd.hasGradientAt.hasFDerivAt.sub_const (h xk)).sub hl).const_smul c⁻¹
  rw [map_smul,map_sub]
  convert he using 1 <;>
    first | rfl | (ext y; simp [bregmanD,L,InnerProductSpace.toDual_apply_apply,inner_sub_right,smul_eq_mul])

end BregmanProxMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.Convergence
namespace BregmanIneqMultCodex
variable {n m : ℕ}

theorem monoConj_real_properties (S : Set (E m)) (h : E m → ℝ)
    (hh : IsBregmanFunction S h) (hS : posOrthant m ⊆ S)
    (him : posOrthant m ⊆ gradient h '' S) :
    (∀ z, monoConj h z ≠ ⊤ ∧ monoConj h z ≠ ⊥) ∧
    Differentiable ℝ (fun z => (monoConj h z).toReal) ∧
    (∀ z w, (∀ i, z i ≤ w i) → (monoConj h z).toReal ≤ (monoConj h w).toReal) := by
  let F := extendedH S h
  have hp := extendedH_proper S h hS
  have hc := extendedH_convex S h hh
  have hf := extendedH_lsc S h hh
  have hs := extendedH_essential_strict S h hh
  have hfinite := extendedH_positive_finite S h hS
  have hsub := extendedH_positive_subgradient_image S h hh him
  have he : monoConjE F=monoConj h := monoConj_extendedH_eq S h hS
  have hv := original_monoconj_finite F hp hfinite hsub
  have hd : Differentiable ℝ (fun z => (monoConjE F z).toReal) := fun z =>
    (monoConj_hasFDerivAt F hp hc hf hs hfinite hsub z).differentiableAt
  have hmon := monoConjE_monotone F hp
  rw [he] at hv hd hmon
  refine ⟨hv,hd,?_⟩
  intro z w hzw
  exact EReal.toReal_le_toReal (hmon z w hzw) (hv z).2 (hv w).1

end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.ProxMult BregmanPPA.Convergence
namespace BregmanProxMultCodex
variable {n m : ℕ}

theorem primal_step {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (Sx : Set (E n)) (hx : E n → ℝ)
    (Sp : Set (E m)) (hp : E m → ℝ) (c : ℝ) (xk z : E n) (pk q : E m)
    (hP : IsConvexProgram C f g) (hc : 0 < c)
    (hhx : IsBregmanFunction Sx hx) (hSx : C ⊆ Sx)
    (hhp : IsBregmanFunction Sp hp) (hSp : nonnegOrthant m ⊆ Sp)
    (him : gradient hp '' Sp = Set.univ) (hz : z ∈ C)
    (hmin : ∀ y ∈ C, proxMultObj f g hx hp c xk pk z ≤ proxMultObj f g hx hp c xk pk y)
    (hq : q=gradient (fun w => (monoConj hp w).toReal) (gradient hp pk+c • gvec g z)) :
    q ∈ nonnegOrthant m ∧ c⁻¹ • (gradient hx xk-gradient hx z) ∈ subdiffX C f g z q := by
  have hpos : posOrthant m ⊆ Sp := fun p h => hSp (fun i => (h i).le)
  have himpos : posOrthant m ⊆ gradient hp '' Sp := by rw [him]; exact Set.subset_univ _
  have hqn : q ∈ nonnegOrthant m := by
    rw [hq]
    exact (BregmanIneqMultCodex.monoConj_gradient_value Sp hp hhp hpos himpos _).1
  refine ⟨hqn,?_⟩
  let G : E n → ℝ := fun y => c⁻¹*bregmanD hx y xk
  let A : E n → ℝ := fun y => (f y).toReal+G y
  let M : E m → ℝ := fun w => (monoConj hp w).toReal
  have hf := BregmanIneqMultCodex.finite_convex_toReal C f hP.f_proper hP.f_convex hP.convex hP.f_finite
  have hG := bregman_convex_on C Sx hx hhx hP.convex hSx xk
  have hGc : ConvexOn ℝ C G := by
    refine ⟨hP.convex,?_⟩
    intro u hu v hv a b ha hb hab
    have hi := mul_le_mul_of_nonneg_left (hG.2 hu hv ha hb hab) (inv_nonneg.mpr hc.le)
    dsimp only [G]
    simp only [smul_eq_mul] at hi ⊢
    nlinarith
  have hA : ConvexOn ℝ C A := hf.add hGc
  have hg : ∀ i, ConvexOn ℝ C (fun y => gvec g y i) := by
    intro i
    exact BregmanIneqMultCodex.finite_convex_toReal C (g i) (hP.g_proper i)
      (hP.g_convex i) hP.convex (hP.g_finite i)
  have hM := BregmanIneqMultCodex.monoConj_real_properties Sp hp hhp hpos himpos
  have hminimum : ∀ y ∈ C, A z+c⁻¹*M (gradient hp pk+c • gvec g z) ≤
      A y+c⁻¹*M (gradient hp pk+c • gvec g y) := by
    intro y hy
    have hi := hmin y hy
    simp only [proxMultObj] at hi
    rw [← EReal.coe_toReal (hP.f_finite z hz) (hP.f_proper.1 z),
      ← EReal.coe_toReal (hP.f_finite y hy) (hP.f_proper.1 y),
      ← EReal.coe_add,← EReal.coe_add] at hi
    have hr := EReal.coe_le_coe_iff.mp hi
    dsimp only [A,G,M]
    linarith
  have hd := (hM.2.1 (gradient hp pk+c • gvec g z)).hasGradientAt.hasFDerivAt
  have hlag := BregmanIneqMultCodex.monotone_penalty_lagrangian_min C A (gvec g) M
    (gradient hp pk) c z hA hg hM.2.2 hc hz hd hminimum
  rw [← hq] at hlag
  have hF := lagr_proper_convex C f g hP q hqn
  have hFG : ∀ y, lagr C f g z q+(G z : EReal) ≤ lagr C f g y q+(G y : EReal) := by
    intro y
    classical
    by_cases hy : y ∈ C
    · rw [lagr_finite_rep C f g hP z hz q hqn,lagr_finite_rep C f g hP y hy q hqn,
        ← EReal.coe_add,← EReal.coe_add]
      apply EReal.coe_le_coe_iff.mpr
      have hi := hlag y hy
      dsimp only [A] at hi
      linarith
    · simp [lagr,hy,EReal.top_add_coe]
  have hdG := bregman_penalty_derivative Sx hx hhx c xk z (hSx hz)
  have hs := BregmanEqMultCodex.convex_smooth_min_subgradient
    (fun y => lagr C f g y q) hF.1 hF.2 G z
    (c⁻¹ • (gradient hx z-gradient hx xk)) hdG hFG
  change IsSubgradient (fun y => lagr C f g y q) z _
  have he : -(c⁻¹ • (gradient hx z-gradient hx xk)) =
      c⁻¹ • (gradient hx xk-gradient hx z) := by module
  rw [he] at hs
  exact hs
end BregmanProxMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.Convergence
namespace BregmanProxMultCodex

theorem conjugate_gradient_of_normal {m : ℕ} (S : Set (E m)) (h : E m → ℝ)
    (hh : IsBregmanFunction S h) (hS : nonnegOrthant m ⊆ S)
    (him : gradient h '' S=Set.univ) (z p : E m) (hp : p ∈ nonnegOrthant m)
    (hnormal : ∀ q ∈ nonnegOrthant m, inner ℝ (z-gradient h p) (q-p) ≤ 0) :
    p=gradient (fun w => (monoConj h w).toReal) z := by
  classical
  have hpos : posOrthant m ⊆ S := fun q hq => hS (fun i => (hq i).le)
  have himpos : posOrthant m ⊆ gradient h '' S := by rw [him]; exact Set.subset_univ _
  let q := gradient (fun w => (monoConj h w).toReal) z
  have hv := BregmanIneqMultCodex.monoConj_gradient_value S h hh hpos himpos z
  have hqn : q ∈ nonnegOrthant m := hv.1
  have hcost : inner ℝ q z-h q ≤ inner ℝ p z-h p := by
    have hs := BregmanPPACodex.gradient_support S h hh (hS hp) (subset_closure (hS hqn))
    have hn := hnormal q hqn
    rw [inner_sub_left] at hn
    have hi : inner ℝ z (q-p) ≤ h q-h p := by linarith
    have hqz : inner ℝ z q=inner ℝ q z := real_inner_comm _ _
    have hpz : inner ℝ z p=inner ℝ p z := real_inner_comm _ _
    rw [inner_sub_right,hqz,hpz] at hi
    linarith
  have hpval : monoConj h z=(((inner ℝ p z-h p:ℝ)):EReal) := by
    apply le_antisymm
    · rw [hv.2]
      exact EReal.coe_le_coe_iff.mpr hcost
    · exact le_iSup_of_le p (le_iSup_of_le hp le_rfl)
  let F := extendedH S h
  have hpc : p ∈ closure S := subset_closure (hS hp)
  have hqc : q ∈ closure S := subset_closure (hS hqn)
  have he := BregmanIneqMultCodex.monoConj_extendedH_eq S h hpos
  have hpmax : p ∈ BregmanIneqMultCodex.monoMaxSet F z := by
    refine ⟨hp,?_,?_⟩
    · simp only [F,extendedH,if_pos hpc]; exact EReal.coe_ne_top _
    · rw [congrFun he z]
      simpa only [F,extendedH,if_pos hpc,EReal.toReal_coe] using hpval
  have hqmax : q ∈ BregmanIneqMultCodex.monoMaxSet F z := by
    refine ⟨hqn,?_,?_⟩
    · simp only [F,extendedH,if_pos hqc]; exact EReal.coe_ne_top _
    · rw [congrFun he z]
      simpa only [F,extendedH,if_pos hqc,EReal.toReal_coe] using hv.2
  exact BregmanIneqMultCodex.original_monoconj_maximizer_unique F
    (BregmanIneqMultCodex.extendedH_proper S h hpos)
    (BregmanIneqMultCodex.extendedH_convex S h hh)
    (BregmanIneqMultCodex.extendedH_essential_strict S h hh)
    (BregmanIneqMultCodex.extendedH_positive_finite S h hpos) z p q hpmax hqmax
end BregmanProxMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.ProxMult BregmanPPA.Convergence
namespace BregmanProxMultCodex

theorem original_objective_min_of_support {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (Sx : Set (E n)) (hx : E n → ℝ) (hhx : IsBregmanFunction Sx hx) (hSx : C ⊆ Sx)
    (Sp : Set (E m)) (hp : E m → ℝ) (hhp : IsBregmanFunction Sp hp)
    (hSp : nonnegOrthant m ⊆ Sp) (him : gradient hp '' Sp=Set.univ)
    (c : ℝ) (hc : 0 < c) (xk z : E n) (pk q : E m) (hz : z ∈ C)
    (hq : q=gradient (fun w => (monoConj hp w).toReal) (gradient hp pk+c • gvec g z))
    (hsg : c⁻¹ • (gradient hx xk-gradient hx z) ∈ subdiffX C f g z q) :
    ∀ y ∈ C, proxMultObj f g hx hp c xk pk z ≤ proxMultObj f g hx hp c xk pk y := by
  have hpos : posOrthant m ⊆ Sp := fun p h => hSp (fun i => (h i).le)
  have himpos : posOrthant m ⊆ gradient hp '' Sp := by rw [him]; exact Set.subset_univ _
  have hM := BregmanIneqMultCodex.monoConj_real_properties Sp hp hhp hpos himpos
  have hval := BregmanIneqMultCodex.monoConj_gradient_value Sp hp hhp hpos himpos
    (gradient hp pk+c • gvec g z)
  rw [← hq] at hval
  intro y hy
  have hL := hsg.2 y
  dsimp only at hL
  rw [lagr_finite_rep C f g hP z hz q hval.1,
    lagr_finite_rep C f g hP y hy q hval.1,← EReal.coe_add] at hL
  have hLr := EReal.coe_le_coe_iff.mp hL
  rw [inner_smul_left,inner_sub_left] at hLr
  simp only [RCLike.conj_to_real] at hLr
  have hB := BregmanPPACodex.gradient_support Sx hx hhx (hSx hz) (subset_closure (hSx hy))
  have hD : inner ℝ (gradient hx z-gradient hx xk) (y-z) ≤
      bregmanD hx y xk-bregmanD hx z xk := by
    simp only [bregmanD,inner_sub_left,inner_sub_right] at hB ⊢
    linarith
  have hDc := mul_le_mul_of_nonneg_left hD (inv_nonneg.mpr hc.le)
  rw [inner_sub_left] at hDc
  have htest : (((inner ℝ q (gradient hp pk+c • gvec g y)-hp q:ℝ)):EReal) ≤
      monoConj hp (gradient hp pk+c • gvec g y) :=
    le_iSup_of_le q (le_iSup_of_le hval.1 le_rfl)
  rw [← EReal.coe_toReal (hM.1 _).1 (hM.1 _).2] at htest
  have htestR := EReal.coe_le_coe_iff.mp htest
  have hvalueR := congrArg EReal.toReal hval.2
  simp only [EReal.toReal_coe] at hvalueR
  simp only [inner_add_right,inner_smul_right] at htestR hvalueR
  have houter : c*(inner ℝ q (gvec g y)-inner ℝ q (gvec g z)) ≤
      (monoConj hp (gradient hp pk+c • gvec g y)).toReal-
        (monoConj hp (gradient hp pk+c • gvec g z)).toReal := by linarith
  have houterc := mul_le_mul_of_nonneg_left houter (inv_nonneg.mpr hc.le)
  rw [← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul] at houterc
  simp only [proxMultObj]
  rw [← EReal.coe_toReal (hP.f_finite z hz) (hP.f_proper.1 z),
    ← EReal.coe_toReal (hP.f_finite y hy) (hP.f_proper.1 y),← EReal.coe_add,← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  nlinarith
end BregmanProxMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.ProxMult BregmanPPA.Convergence
namespace BregmanProxMultCodex

theorem sum_gradient_pair {n m : ℕ} (hx : E n → ℝ) (hp : E m → ℝ)
    (x : E n) (p : E m) (hdx : DifferentiableAt ℝ hx x)
    (hdp : DifferentiableAt ℝ hp p) :
    gradient (sumFn hx hp) (pair x p) = pair (gradient hx x) (gradient hp p) := by
  let F : PD n m →L[ℝ] E n := WithLp.fstL 2 ℝ (E n) (E m)
  let G : PD n m →L[ℝ] E m := WithLp.sndL 2 ℝ (E n) (E m)
  have hx' := hdx.hasGradientAt.hasFDerivAt.comp (pair x p) F.hasFDerivAt
  have hp' := hdp.hasGradientAt.hasFDerivAt.comp (pair x p) G.hasFDerivAt
  have he := hx'.add hp'
  have hd : HasFDerivAt (sumFn hx hp)
      ((InnerProductSpace.toDual ℝ _) (pair (gradient hx x) (gradient hp p))) (pair x p) := by
    convert he using 1 <;>
      first | rfl | (ext z; simp [sumFn,F,G,pair,WithLp.prod_inner_apply,InnerProductSpace.toDual_apply_apply])
  exact (hasGradientAt_iff_hasFDerivAt.mpr hd).gradient
end BregmanProxMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.ProxMult ThreeOpSplitting.Convergence
namespace BregmanProxMultCodex

theorem opK_point_in_program {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (z w : PD n m) (hw : w ∈ opK C f g z) :
    z.ofLp.1 ∈ C ∧ z.ofLp.2 ∈ nonnegOrthant m := by
  classical
  have ht := hw.1.1
  change lagr C f g z.ofLp.1 z.ofLp.2 ≠ ⊤ at ht
  have hx : z.ofLp.1 ∈ C := by
    by_contra hn
    exact ht (by simp only [lagr,if_neg hn])
  refine ⟨hx,?_⟩
  have hb := hw.2.1
  change -lagr C f g z.ofLp.1 z.ofLp.2 ≠ ⊤ at hb
  by_contra hn
  exact hb (by simp only [lagr,if_pos hx,if_neg hn,EReal.neg_bot])

theorem opK_dom_subset {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) :
    dom (opK C f g) ⊆ prodZone C (nonnegOrthant m) := by
  rintro z ⟨w,hw⟩
  exact opK_point_in_program C f g z w hw
theorem nonnegOrthant_closed {m : ℕ} : IsClosed (nonnegOrthant m) := by
  have he : nonnegOrthant m = ⋂ i : Fin m, {p : E m | 0 ≤ p i} := by
    ext p
    simp [nonnegOrthant]
  rw [he]
  apply isClosed_iInter
  intro i
  exact isClosed_le continuous_const (by fun_prop)

theorem opK_closure_subset {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (Sx : Set (E n)) (Sp : Set (E m))
    (hC : IsClosed C) (hSx : C ⊆ Sx) (hSp : nonnegOrthant m ⊆ Sp) :
    closure (dom (opK C f g)) ⊆ prodZone Sx Sp := by
  have hclosed : IsClosed (prodZone C (nonnegOrthant m)) := by
    change IsClosed ((fun z : PD n m => z.ofLp.1) ⁻¹' C ∩
      (fun z : PD n m => z.ofLp.2) ⁻¹' nonnegOrthant m)
    exact (hC.preimage (by fun_prop)).inter (nonnegOrthant_closed.preimage (by fun_prop))
  have hb := closure_minimal (opK_dom_subset C f g) hclosed
  intro z hz
  have hi := hb hz
  exact ⟨hSx hi.1,hSp hi.2⟩
end BregmanProxMultCodex


end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.ProxMult BregmanPPA.Convergence
namespace BregmanProxMultCodex

theorem original_run_of_product {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (Sx : Set (E n)) (hx : E n → ℝ)
    (Sp : Set (E m)) (hp : E m → ℝ) (c : ℕ → ℝ) (x : ℕ → E n) (p : ℕ → E m)
    (hP : IsConvexProgram C f g) (hc : ∀ k, 0 < c k)
    (hhx : IsBregmanFunction Sx hx) (hSx : C ⊆ Sx)
    (hhp : IsBregmanFunction Sp hp) (hSp : nonnegOrthant m ⊆ Sp)
    (him : gradient hp '' Sp=Set.univ)
    (hrun : IsBregmanPPARun (prodZone Sx Sp) (sumFn hx hp) (opK C f g) c
      (fun k => pair (x k) (p k))) : IsProxMultRun C f g Sx hx Sp hp c x p := by
  have hzone (k : ℕ) : x k ∈ Sx ∧ p k ∈ Sp := (hrun k).1
  have hxD (k : ℕ) : DifferentiableAt ℝ hx (x k) :=
    ((hhx.contDiffOn.differentiableOn (by simp)) (x k) (hzone k).1).differentiableAt
      (hhx.isOpen.mem_nhds (hzone k).1)
  have hpD (k : ℕ) : DifferentiableAt ℝ hp (p k) :=
    ((hhp.contDiffOn.differentiableOn (by simp)) (p k) (hzone k).2).differentiableAt
      (hhp.isOpen.mem_nhds (hzone k).2)
  refine ⟨(hzone 0).1,?_⟩
  intro k
  have hi := (hrun k).2
  have hd := opK_point_in_program C f g _ _ hi
  have hnC : x (k+1) ∈ C := hd.1
  have hnN : p (k+1) ∈ nonnegOrthant m := hd.2
  rw [sum_gradient_pair hx hp (x k) (p k) (hxD k) (hpD k),
    sum_gradient_pair hx hp (x (k+1)) (p (k+1)) (hxD (k+1)) (hpD (k+1))] at hi
  change (c k)⁻¹ • (gradient hx (x k)-gradient hx (x (k+1))) ∈
      subdiffX C f g (x (k+1)) (p (k+1)) ∧
    -((c k)⁻¹ • (gradient hp (p k)-gradient hp (p (k+1)))) ∈
      supdiffP C f g (x (k+1)) (p (k+1)) at hi
  have hs := hi.2
  rw [original_supdiff_formula C f g hP (x (k+1)) hnC (p (k+1)) hnN] at hs
  obtain ⟨u,hu,he⟩ := hs
  have hscale := congrArg (fun a : E m => c k • a) he
  simp only [smul_neg,smul_smul,mul_inv_cancel₀ (hc k).ne',one_smul,smul_sub] at hscale
  have hdiff : gradient hp (p (k+1))-gradient hp (p k) = c k • gvec g (x (k+1))-c k • u := by
    simpa only [neg_sub] using hscale
  let outer := gradient hp (p k)+c k • gvec g (x (k+1))
  have hnormal : ∀ q ∈ nonnegOrthant m,
      inner ℝ (outer-gradient hp (p (k+1))) (q-p (k+1)) ≤ 0 := by
    have heq : outer-gradient hp (p (k+1))=c k • u := by
      calc
        outer-gradient hp (p (k+1)) = c k • gvec g (x (k+1))-
            (gradient hp (p (k+1))-gradient hp (p k)) := by dsimp only [outer]; abel
        _ = c k • u := by rw [hdiff]; abel
    intro q hq
    have h := (indicator_support (p (k+1)) u hnN).mp hu q hq
    rw [heq,inner_smul_left]
    simpa only [RCLike.conj_to_real] using mul_nonpos_of_nonneg_of_nonpos (hc k).le h
  have hupdate := conjugate_gradient_of_normal Sp hp hhp hSp him outer (p (k+1)) hnN hnormal
  refine ⟨(hzone k).2,hnC,?_,hupdate⟩
  exact original_objective_min_of_support C f g hP Sx hx hhx hSx Sp hp hhp hSp him
    (c k) (hc k) (x k) (x (k+1)) (p k) (p (k+1)) hnC hupdate hi.1
end BregmanProxMultCodex

end

section
set_option autoImplicit false
open Filter Topology BregmanPPA.Convergence
namespace BregmanProxMultCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
noncomputable def quadratic (x : H) : ℝ := (1/2:ℝ)*‖x‖^2

theorem quadratic_gradient (x : H) : gradient (quadratic (H:=H)) x=x := by
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_smul (1/2:ℝ)
  convert hd using 1 <;>
    first | rfl | (ext y; simp [InnerProductSpace.toDual_apply_apply,smul_eq_mul])

theorem quadratic_distance (x y : H) :
    bregmanD (quadratic (H:=H)) x y=(1/2:ℝ)*‖x-y‖^2 := by
  rw [bregmanD,quadratic_gradient]
  simp only [quadratic,norm_sub_sq_real,inner_sub_right,real_inner_self_eq_norm_sq]
  rw [real_inner_comm y x]
  ring

omit [FiniteDimensional ℝ H] in
theorem quadratic_strict : StrictConvexOn ℝ (Set.univ : Set H) quadratic := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ hxy a b ha hb hab
  have hn : 0 < ‖x-y‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))
  have hp : 0 < a*b*‖x-y‖^2 := mul_pos (mul_pos ha hb) hn
  have he : a*‖x‖^2+b*‖y‖^2-‖a • x+b • y‖^2 = a*b*‖x-y‖^2 := by
    rw [norm_add_sq_real,norm_smul,norm_smul,inner_smul_left,inner_smul_right]
    simp only [Real.norm_eq_abs,abs_of_pos ha,abs_of_pos hb,norm_sub_sq_real,RCLike.conj_to_real]
    have hba : b=1-a := by linarith
    rw [hba]
    ring
  simp only [quadratic,smul_eq_mul]
  nlinarith

theorem quadratic_level_bound (α : ℝ) (x y : H)
    (h : bregmanD quadratic x y ≤ α) : ‖x-y‖ ≤ 2*max α 1 := by
  rw [quadratic_distance] at h
  have h1 : 1 ≤ max α 1 := le_max_right _ _
  have h2 : α ≤ max α 1 := le_max_left _ _
  have hn := norm_nonneg (x-y)
  nlinarith [sq_nonneg (‖x-y‖-max α 1)]

theorem quadratic_bregman : IsBregmanFunction (Set.univ : Set H) quadratic := by
  have hd : ContDiff ℝ 1 (quadratic (H:=H)) :=
    (contDiff_norm_sq ℝ).const_smul (1/2:ℝ)
  refine ⟨isOpen_univ,hd.contDiffOn,?_,hd.continuous.continuousOn,?_,?_,?_,?_⟩
  · simpa only [closure_univ] using (quadratic_strict (H:=H))
  · intro α y _
    apply (Metric.isBounded_closedBall (x:=y) (r:=2*max α 1)).subset
    intro x hx
    rw [Metric.mem_closedBall,dist_eq_norm]
    exact quadratic_level_bound α x y hx.2
  · intro α x _
    apply (Metric.isBounded_closedBall (x:=x) (r:=2*max α 1)).subset
    intro y hy
    rw [Metric.mem_closedBall,dist_comm,dist_eq_norm]
    exact quadratic_level_bound α x y hy.2
  · intro y y' _ hy
    simp_rw [quadratic_distance]
    have hc : Tendsto (fun _ : ℕ => y') atTop (𝓝 y') := tendsto_const_nhds
    have ht := ((hc.sub hy).norm.pow 2).const_mul (1/2:ℝ)
    simpa using ht
  · intro x y y' _ _ hy _ _ hD
    simp_rw [quadratic_distance] at hD
    have ht : Tendsto (fun k => ‖x k-y k‖^2) atTop (𝓝 0) := by
      have he := hD.const_mul 2
      simpa only [← mul_assoc,show (2:ℝ)*(1/2)=1 by norm_num,one_mul,mul_zero] using he
    have hn : Tendsto (fun k => ‖x k-y k‖) atTop (𝓝 0) := by
      have he := Real.continuous_sqrt.continuousAt.tendsto.comp ht
      simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using he
    have hs : Tendsto (fun k => x k-y k) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr hn
    have he := hs.add hy
    simpa only [sub_add_cancel,zero_add] using he

theorem quadratic_image : gradient (quadratic (H:=H)) '' Set.univ=Set.univ := by
  ext y
  simp only [Set.mem_image,Set.mem_univ,true_and,iff_true]
  exact ⟨y,quadratic_gradient y⟩
end BregmanProxMultCodex

end

section

namespace RockafellarMaxMono.Shared

/-- Rockafellar (1970), p. 209: a *proper convex function* on a real normed space `V` is a
function `f : V → (−∞, +∞]`, not identically `+∞`, such that
`f((1 − λ)x + λy) ≤ (1 − λ)f(x) + λf(y)` whenever `x, y ∈ V` and `0 < λ < 1`.
The value set `(−∞, +∞]` is encoded as `EReal` together with the requirement that `f`
never takes the value `⊥ = −∞`. -/
def ProperConvex {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : V → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ (∃ x, f x ≠ ⊤) ∧
    ∀ (x y : V) (t : ℝ), 0 < t → t < 1 →
      f ((1 - t) • x + t • y) ≤ ((1 - t : ℝ) : EReal) * f x + ((t : ℝ) : EReal) * f y

end RockafellarMaxMono.Shared


namespace RockafellarMaxMono.Shared

/-- Rockafellar (1970), p. 209: the *subdifferential* of `f : V → (−∞, +∞]` at `x` is
`∂f(x) = {x* ∈ V* | f(y) ≥ f(x) + ⟨y − x, x*⟩ for all y ∈ V}`, a subset of the
(strong) dual `V* = StrongDual ℝ V`; the pairing `⟨y − x, x*⟩` is `x' (y - x)`. -/
def subdiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : V → EReal) (x : V) :
    Set (StrongDual ℝ V) :=
  {x' | ∀ y : V, f x + ((x' (y - x) : ℝ) : EReal) ≤ f y}

end RockafellarMaxMono.Shared


namespace RockafellarMaxMono.Maximality

/-- Rockafellar (1970), p. 209: a multivalued mapping `T : V → V*` (encoded as
`V → Set (StrongDual ℝ V)`) is a *monotone operator* if
`⟨x₀ − x₁, x₀* − x₁*⟩ ≥ 0` whenever `x₀* ∈ T(x₀)` and `x₁* ∈ T(x₁)`. -/
def IsMonotoneOp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V → Set (StrongDual ℝ V)) : Prop :=
  ∀ (x₀ x₁ : V) (x₀' x₁' : StrongDual ℝ V), x₀' ∈ T x₀ → x₁' ∈ T x₁ →
    0 ≤ (x₀' - x₁') (x₀ - x₁)

/-- Rockafellar (1970), p. 209: a monotone operator `T : V → V*` is *maximal monotone* if its
graph `G(T) = {(x, x*) | x* ∈ T(x)}` is not properly contained in the graph of any other
monotone operator `T' : V → V*`; equivalently, every monotone `T'` whose graph contains the
graph of `T` coincides with `T`. -/
def IsMaximalMonotone {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V → Set (StrongDual ℝ V)) : Prop :=
  IsMonotoneOp T ∧
    ∀ T' : V → Set (StrongDual ℝ V), IsMonotoneOp T' → (∀ x, T x ⊆ T' x) → ∀ x, T' x = T x

end RockafellarMaxMono.Maximality

set_option autoImplicit false

/-- Ekeland's variational principle (weak form, with control of the value). -/
theorem rmm_ekeland {X : Type*} [MetricSpace X] [CompleteSpace X] (H : X → ℝ)
    (hH : LowerSemicontinuous H) (m : ℝ) (hm : ∀ x, m ≤ H x) (δ : ℝ) (hδ : 0 < δ) (x₁ : X) :
    ∃ x, H x ≤ H x₁ ∧ ∀ y, H x ≤ H y + δ * dist y x := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : X → Set X, ∀ z y, y ∈ S z ↔ H y + δ * dist y z ≤ H z :=
    ⟨fun z => {y | H y + δ * dist y z ≤ H z}, fun _ _ => Iff.rfl⟩
  have hself : ∀ z, z ∈ S z := by intro z; rw [hS]; simp
  have htrans : ∀ z y w, y ∈ S z → w ∈ S y → w ∈ S z := by
    intro z y w hy hw
    rw [hS] at hy hw ⊢
    have := dist_triangle w y z
    nlinarith
  have hclosed : ∀ z, IsClosed (S z) := by
    intro z
    have h1 : LowerSemicontinuous (fun y => H y + δ * dist y z) :=
      hH.add (Continuous.lowerSemicontinuous (by fun_prop))
    have h2 : S z = (fun y => H y + δ * dist y z) ⁻¹' Set.Iic (H z) := by
      ext y; rw [hS]; rfl
    rw [h2]
    exact h1.isClosed_preimage (H z)
  have hnext : ∀ z, ∃ y ∈ S z, ∀ w ∈ S y, δ * dist w y ≤ H z - H y := by
    intro z
    have hne : (H '' S z).Nonempty := ⟨H z, z, hself z, rfl⟩
    have hbdd : BddBelow (H '' S z) := ⟨m, by rintro _ ⟨y, -, rfl⟩; exact hm y⟩
    have hμ : sInf (H '' S z) ≤ H z := csInf_le hbdd ⟨z, hself z, rfl⟩
    obtain ⟨y, hy, hyμ⟩ : ∃ y ∈ S z, 2 * H y - H z ≤ sInf (H '' S z) := by
      rcases eq_or_lt_of_le hμ with h | h
      · exact ⟨z, hself z, by linarith⟩
      · obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne
          (show sInf (H '' S z) < (H z + sInf (H '' S z)) / 2 by linarith)
        exact ⟨y, hy, by linarith⟩
    refine ⟨y, hy, fun w hw => ?_⟩
    have hwz : w ∈ S z := htrans z y w hy hw
    have hw' : sInf (H '' S z) ≤ H w := csInf_le hbdd ⟨w, hwz, rfl⟩
    rw [hS] at hw
    linarith
  choose nxt hnxtS hnxt using hnext
  obtain ⟨z, hz0, hzs⟩ : ∃ z : ℕ → X, z 0 = x₁ ∧ ∀ n, z (n + 1) = nxt (z n) :=
    ⟨fun n => Nat.rec x₁ (fun _ p => nxt p) n, rfl, fun _ => rfl⟩
  have hstep : ∀ n, z (n + 1) ∈ S (z n) := fun n => by rw [hzs]; exact hnxtS _
  have hnest : ∀ n k, n ≤ k → S (z k) ⊆ S (z n) := by
    intro n k hnk
    induction k, hnk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hnk ih => exact fun w hw => ih (htrans _ _ _ (hstep k) hw)
  have hmem : ∀ n k, n ≤ k → z k ∈ S (z n) := fun n k hnk => hnest n k hnk (hself _)
  have hanti : Antitone (fun n => H (z n)) := by
    refine antitone_nat_of_succ_le fun n => ?_
    have h1 := hstep n
    rw [hS] at h1
    have := dist_nonneg (x := z (n + 1)) (y := z n)
    nlinarith
  have hbddz : BddBelow (Set.range fun n => H (z n)) := ⟨m, by rintro _ ⟨n, rfl⟩; exact hm _⟩
  have hlimH := tendsto_atTop_ciInf hanti hbddz
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = ⨅ n, H (z n) := ⟨_, rfl⟩
  rw [← hL] at hlimH
  have hLle : ∀ n, L ≤ H (z n) := fun n => hL ▸ ciInf_le hbddz n
  have hgap : ∀ n, ∀ w ∈ S (z (n + 1)), δ * dist w (z (n + 1)) ≤ H (z n) - L := by
    intro n w hw
    have h1 := hnxt (z n) w (by rw [← hzs]; exact hw)
    rw [← hzs] at h1
    linarith [hLle (n + 1)]
  have he : Filter.Tendsto (fun n => H (z n) - L) Filter.atTop (nhds 0) := by
    simpa using hlimH.sub_const L
  have hcauchy : CauchySeq z := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hev := he.eventually (gt_mem_nhds (show (0:ℝ) < δ * ε by positivity))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    refine ⟨N + 1, fun n hn => ?_⟩
    have h1 := hgap N (z n) (hmem (N + 1) n hn)
    have h2 := hN N le_rfl
    have h3 : δ * dist (z n) (z (N + 1)) < δ * ε := by linarith
    exact lt_of_mul_lt_mul_left h3 hδ.le
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hxS : ∀ n, x ∈ S (z n) := fun n =>
    (hclosed _).mem_of_tendsto hx (Filter.eventually_atTop.2 ⟨n, fun k hk => hmem n k hk⟩)
  refine ⟨x, ?_, fun y => ?_⟩
  · have h1 := hxS 0
    rw [hS, hz0] at h1
    have := dist_nonneg (x := x) (y := x₁)
    nlinarith
  · by_contra hlt
    push Not at hlt
    have hyx : y ∈ S x := by rw [hS]; exact hlt.le
    have hbound : ∀ n, δ * dist y x ≤ 2 * (H (z n) - L) := by
      intro n
      have h1 := hgap n y (htrans _ _ _ (hxS (n + 1)) hyx)
      have h2 := hgap n x (hxS (n + 1))
      have h3 := dist_triangle y (z (n + 1)) x
      rw [dist_comm (z (n + 1)) x] at h3
      nlinarith
    have h0 : δ * dist y x ≤ 0 := by
      have h4 := he.const_mul 2
      simp only [mul_zero] at h4
      exact ge_of_tendsto' h4 hbound
    have hd : dist y x = 0 :=
      le_antisymm (by nlinarith [dist_nonneg (x := y) (y := x)]) dist_nonneg
    rw [dist_eq_zero] at hd
    subst hd
    simp at hlt

open RockafellarMaxMono in
theorem rmm_le_coe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (y : E) (r : ℝ) :
    f y ≤ (r : EReal) ↔ f y ≠ ⊤ ∧ (f y).toReal ≤ r := by
  constructor
  · intro h
    have hne : f y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top r) h
    refine ⟨hne, ?_⟩
    rw [← EReal.coe_le_coe_iff, EReal.coe_toReal hne (hf.1 y)]
    exact h
  · rintro ⟨hne, h⟩
    rw [← EReal.coe_toReal hne (hf.1 y)]
    exact EReal.coe_le_coe_iff.2 h

open RockafellarMaxMono in
theorem rmm_conv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (x y : E) (r s a b : ℝ) (hx : f x ≤ (r : EReal))
    (hy : f y ≤ (s : EReal)) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    f (a • x + b • y) ≤ ((a * r + b * s : ℝ) : EReal) := by
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · subst hb0
    have ha1 : a = 1 := by linarith
    subst ha1
    simpa using hx
  rcases eq_or_lt_of_le (show b ≤ 1 by linarith) with hb1 | hb1
  · subst hb1
    have ha0 : a = 0 := by linarith
    subst ha0
    simpa using hy
  have ha' : a = 1 - b := by linarith
  subst ha'
  obtain ⟨hx1, hx2⟩ := (rmm_le_coe f hf x r).1 hx
  obtain ⟨hy1, hy2⟩ := (rmm_le_coe f hf y s).1 hy
  obtain ⟨p, hp, hpr⟩ : ∃ p : ℝ, f x = p ∧ p ≤ r :=
    ⟨_, (EReal.coe_toReal hx1 (hf.1 x)).symm, hx2⟩
  obtain ⟨q, hq, hqs⟩ : ∃ q : ℝ, f y = q ∧ q ≤ s :=
    ⟨_, (EReal.coe_toReal hy1 (hf.1 y)).symm, hy2⟩
  have hc := hf.2.2 x y b hbpos hb1
  rw [hp, hq, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hc
  refine hc.trans (EReal.coe_le_coe_iff.2 ?_)
  have h1 : 0 ≤ 1 - b := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hpr h1, mul_le_mul_of_nonneg_left hqs hbpos.le]

open RockafellarMaxMono in
theorem rmm_epi_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (ψ : StrongDual ℝ E) (κ : ℝ) :
    Convex ℝ {p : E × ℝ | f p.1 ≤ ((p.2 + ψ p.1 + κ : ℝ) : EReal)} := by
  intro p hp q hq a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hp hq ⊢
  have h := rmm_conv_le f hf p.1 q.1 _ _ a b hp hq ha hb hab
  have heq : (a • p + b • q).2 + ψ (a • p + b • q).1 + κ
      = a * (p.2 + ψ p.1 + κ) + b * (q.2 + ψ q.1 + κ) := by
    simp only [Prod.snd_add, Prod.fst_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_add,
      map_smul]
    linear_combination (-κ) * hab
  rw [heq]
  simpa only [Prod.fst_add, Prod.smul_fst] using h

theorem rmm_epi_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hlsc : LowerSemicontinuous f) :
    IsClosed {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
  have h := hlsc.isClosed_epigraph
  exact h.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))

open RockafellarMaxMono in
theorem rmm_minorant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∃ (a : StrongDual ℝ E) (b : ℝ), ∀ x, f x ≠ ⊤ → a x + b ≤ (f x).toReal := by
  obtain ⟨x1, hx1⟩ := hf.2.1
  have hconv : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    have := rmm_epi_convex f hf 0 0
    simpa using this
  have hnot : ((x1, (f x1).toReal - 1) : E × ℝ) ∉ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    intro h
    simp only [Set.mem_ofPred_eq] at h
    rw [rmm_le_coe f hf] at h
    linarith [h.2]
  obtain ⟨ℓ, u, hℓ0, hℓ⟩ := geometric_hahn_banach_point_closed hconv (rmm_epi_closed f hlsc) hnot
  have hdec : ∀ (y : E) (r : ℝ), ℓ (y, r) = ℓ (y, 0) + r * ℓ (0, 1) := by
    intro y r
    have : ((y, r) : E × ℝ) = (y, 0) + r • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  have hmem : ∀ y, f y ≠ ⊤ →
      ((y, (f y).toReal) : E × ℝ) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    intro y hy
    simp only [Set.mem_ofPred_eq]
    rw [EReal.coe_toReal hy (hf.1 y)]
  have h1 := hℓ _ (hmem x1 hx1)
  rw [hdec] at h1 hℓ0
  have hc : 0 < ℓ (0, 1) := by nlinarith
  refine ⟨-(ℓ (0, 1))⁻¹ • ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ), u / ℓ (0, 1), fun x hx => ?_⟩
  have h2 := hℓ _ (hmem x hx)
  rw [hdec] at h2
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, smul_eq_mul]
  have e : -(ℓ (0, 1))⁻¹ * ℓ (x, 0) + u / ℓ (0, 1) = (u - ℓ (x, 0)) / ℓ (0, 1) := by
    field_simp
    ring
  rw [e, div_le_iff₀ hc]
  linarith

open RockafellarMaxMono in
theorem rmm_subdiff_fin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (x : E) (x' : StrongDual ℝ E) (h : x' ∈ Shared.subdiff f x) :
    f x ≠ ⊤ := by
  intro hx
  obtain ⟨z, hz⟩ := hf.2.1
  have h1 := (show ∀ y, f x + ((x' (y - x) : ℝ) : EReal) ≤ f y from h) z
  rw [hx, EReal.top_add_coe] at h1
  exact hz (top_le_iff.1 h1)

open RockafellarMaxMono in
theorem rmm_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f)
    (x0 : E) (x0' : StrongDual ℝ E)
    (hrel : ∀ x, ∀ u ∈ Shared.subdiff f x, 0 ≤ (u - x0') (x - x0))
    (η : ℝ) (hη : 0 < η) :
    f x0 ≠ ⊤ ∧ ∀ y, f y ≠ ⊤ →
      (f x0).toReal + x0' (y - x0) - η * (2 * ‖y - x0‖ + ‖y - x0‖ ^ 2) ≤ (f y).toReal := by
  classical
  obtain ⟨a, b, hab⟩ := rmm_minorant f hf hlsc
  obtain ⟨x1, hx1⟩ := hf.2.1
  have hfF : ∀ x, f x ≠ ⊤ → f x = (((f x).toReal : ℝ) : EReal) :=
    fun x hx => (EReal.coe_toReal hx (hf.1 x)).symm
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = η / 2 := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨k, hk⟩ : ∃ k : E → ℝ, ∀ x, k x = η * ‖x - x0‖ + η * ‖x - x0‖ ^ 2 :=
    ⟨_, fun _ => rfl⟩
  have hkcont : Continuous k := by
    have : k = fun x => η * ‖x - x0‖ + η * ‖x - x0‖ ^ 2 := funext hk
    rw [this]; fun_prop
  obtain ⟨g, hg⟩ : ∃ g : E → ℝ, ∀ x, g x = (f x).toReal - x0' (x - x0) := ⟨_, fun _ => rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = g x1 + k x1 + 1 := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : E → ℝ, ∀ x, H x = if f x = ⊤ then M else min (g x + k x) M :=
    ⟨_, fun _ => rfl⟩
  -- lower semicontinuity of the truncated function
  have hHlsc : LowerSemicontinuous H := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro c
    by_cases hc : M ≤ c
    · have : H ⁻¹' Set.Iic c = Set.univ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
        rw [hH]
        split_ifs
        · exact hc
        · exact (min_le_right _ _).trans hc
      rw [this]; exact isClosed_univ
    · push Not at hc
      have : H ⁻¹' Set.Iic c = (fun x => ((x, c + x0' (x - x0) - k x) : E × ℝ)) ⁻¹'
          {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_ofPred_eq]
        rw [rmm_le_coe f hf, hH]
        split_ifs with hx
        · simp only [hx, ne_eq, not_true_eq_false, false_and, iff_false, not_le]
          exact hc
        · rw [min_le_iff, hg]
          constructor
          · rintro (h | h)
            · exact ⟨hx, by linarith⟩
            · linarith
          · rintro ⟨-, h⟩
            left; linarith
      rw [this]
      exact (rmm_epi_closed f hlsc).preimage (continuous_id.prodMk
        ((continuous_const.add (x0'.continuous.comp (continuous_id.sub continuous_const))).sub
          hkcont))
  -- lower bound
  have hHbdd : ∀ x, min (a x0 + b - ‖a - x0'‖ ^ 2 / (4 * η)) M ≤ H x := by
    intro x
    rw [hH x]
    split_ifs with hx
    · exact min_le_right _ _
    · refine min_le_min_right _ ?_
      have h1 := hab x hx
      rw [hg, hk]
      have h2 := (a - x0').le_opNorm (x - x0)
      have h3 := neg_abs_le ((a - x0') (x - x0))
      rw [← Real.norm_eq_abs] at h3
      have h4 : (a - x0') (x - x0) = a x - a x0 - x0' (x - x0) := by
        rw [ContinuousLinearMap.sub_apply, map_sub]
      have hβ : ‖a - x0'‖ ^ 2 / (4 * η) * (4 * η) = ‖a - x0'‖ ^ 2 := by
        field_simp
      have ht := norm_nonneg (x - x0)
      have hC := norm_nonneg (a - x0')
      nlinarith [sq_nonneg (2 * η * ‖x - x0‖ - ‖a - x0'‖), mul_nonneg hη.le ht]
  -- Ekeland point
  obtain ⟨x, hxH, hxE⟩ := rmm_ekeland H hHlsc _ hHbdd δ hδpos x1
  have hH1 : H x1 = g x1 + k x1 := by
    rw [hH, if_neg hx1, min_eq_left (by rw [hM]; linarith)]
  rw [hH1] at hxH
  have hxfin : f x ≠ ⊤ := by
    intro hx
    rw [hH, if_pos hx] at hxH
    rw [hM] at hxH
    linarith
  have hHx : H x = g x + k x := by
    have hxH' := hxH
    rw [hH, if_neg hxfin] at hxH' ⊢
    rcases min_choice (g x + k x) M with h | h
    · exact h
    · rw [h] at hxH'; rw [hM] at hxH'; linarith
  have hEk : ∀ y, f y ≠ ⊤ → g x + k x ≤ g y + k y + δ * ‖y - x‖ := by
    intro y hy
    have h1 := hxE y
    rw [hHx, dist_eq_norm] at h1
    have h2 : H y ≤ g y + k y := by rw [hH, if_neg hy]; exact min_le_left _ _
    linarith
  -- the perturbation
  obtain ⟨K, hK⟩ : ∃ K : E → ℝ, ∀ y, K y = k y + δ * ‖y - x‖ := ⟨_, fun _ => rfl⟩
  have hKcont : Continuous K := by
    have : K = fun y => k y + δ * ‖y - x‖ := funext hK
    rw [this]; fun_prop
  have hKx : K x = k x := by rw [hK, sub_self, norm_zero, mul_zero, add_zero]
  have hnc : ∀ (u v : E) (s t : ℝ), 0 ≤ s → 0 ≤ t → ‖s • u + t • v‖ ≤ s * ‖u‖ + t * ‖v‖ := by
    intro u v s t hs ht
    calc ‖s • u + t • v‖ ≤ ‖s • u‖ + ‖t • v‖ := norm_add_le _ _
      _ = s * ‖u‖ + t * ‖v‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
  have hKconv : ∀ (y z : E) (s t : ℝ), 0 ≤ s → 0 ≤ t → s + t = 1 →
      K (s • y + t • z) ≤ s * K y + t * K z := by
    intro y z s t hs ht hst
    have e1 : s • y + t • z - x0 = s • (y - x0) + t • (z - x0) := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hst, one_smul]
    have e2 : s • y + t • z - x = s • (y - x) + t • (z - x) := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hst, one_smul]
    rw [hK, hK, hK, hk, hk, hk, e1, e2]
    have n1 := hnc (y - x0) (z - x0) s t hs ht
    have n2 := hnc (y - x) (z - x) s t hs ht
    have n0 := norm_nonneg (s • (y - x0) + t • (z - x0))
    have hsq : ‖s • (y - x0) + t • (z - x0)‖ ^ 2 ≤ s * ‖y - x0‖ ^ 2 + t * ‖z - x0‖ ^ 2 := by
      have h1 : ‖s • (y - x0) + t • (z - x0)‖ ^ 2 ≤ (s * ‖y - x0‖ + t * ‖z - x0‖) ^ 2 :=
        pow_le_pow_left₀ n0 n1 2
      have h2 : (s * ‖y - x0‖ + t * ‖z - x0‖) ^ 2 ≤ s * ‖y - x0‖ ^ 2 + t * ‖z - x0‖ ^ 2 := by
        have ht' : t = 1 - s := by linarith
        subst ht'
        nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (‖y - x0‖ - ‖z - x0‖))]
      linarith
    have m1 := mul_le_mul_of_nonneg_left n1 hη.le
    have m2 := mul_le_mul_of_nonneg_left hsq hη.le
    have m3 := mul_le_mul_of_nonneg_left n2 hδpos.le
    nlinarith
  -- the two convex sets
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = g x - x0' x0 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Set (E × ℝ), A = {p : E × ℝ | f p.1 ≤ ((p.2 + x0' p.1 + κ : ℝ) : EReal)} :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Set (E × ℝ), B = {p : E × ℝ | p.2 < -(K p.1 - K x)} := ⟨_, rfl⟩
  have hAconv : Convex ℝ A := hA ▸ rmm_epi_convex f hf x0' κ
  have hBopen : IsOpen B := by
    rw [hB]
    exact isOpen_lt continuous_snd (((hKcont.comp continuous_fst).sub continuous_const).neg)
  have hBconv : Convex ℝ B := by
    rw [hB]
    intro p hp q hq s t hs ht hst
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hp hq ⊢
    have hc := hKconv p.1 q.1 s t hs ht hst
    have hd1 : 0 < -(K p.1 - K x) - p.2 := by linarith
    have hd2 : 0 < -(K q.1 - K x) - q.2 := by linarith
    have hkey : 0 < s * (-(K p.1 - K x) - p.2) + t * (-(K q.1 - K x) - q.2) := by
      rcases eq_or_lt_of_le hs with hs0 | hspos
      · subst hs0
        have ht1 : t = 1 := by linarith
        subst ht1
        linarith
      · have := mul_pos hspos hd1
        have := mul_nonneg ht hd2.le
        linarith
    have hKx' : K x = s * K x + t * K x := by rw [← add_mul, hst, one_mul]
    nlinarith
  have hdisj : Disjoint B A := by
    rw [Set.disjoint_left]
    intro p hpB hpA
    rw [hB] at hpB
    rw [hA] at hpA
    simp only [Set.mem_ofPred_eq] at hpB hpA
    rw [rmm_le_coe f hf] at hpA
    obtain ⟨hp1, hp2⟩ := hpA
    have h1 := hEk p.1 hp1
    rw [hK p.1, hKx] at hpB
    rw [hg p.1, hg x] at h1
    rw [hκ, hg x] at hp2
    simp only [map_sub] at h1 hp2
    linarith
  obtain ⟨ℓ, u, hℓB, hℓA⟩ := geometric_hahn_banach_open hBconv hBopen hAconv hdisj
  have hdec : ∀ (y : E) (r : ℝ), ℓ (y, r) = ℓ (y, 0) + r * ℓ (0, 1) := by
    intro y r
    have : ((y, r) : E × ℝ) = (y, 0) + r • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  have hlin : ∀ y z : E, ℓ (y - z, 0) = ℓ (y, 0) - ℓ (z, 0) := by
    intro y z
    have : ((y - z, (0 : ℝ)) : E × ℝ) = (y, 0) - (z, 0) := by ext <;> simp
    rw [this, map_sub]
  have hxA : ((x, 0) : E × ℝ) ∈ A := by
    rw [hA]
    simp only [Set.mem_ofPred_eq]
    rw [rmm_le_coe f hf]
    refine ⟨hxfin, ?_⟩
    rw [hκ, hg, map_sub]
    linarith
  have hxB : ((x, -1) : E × ℝ) ∈ B := by
    rw [hB]
    simp only [Set.mem_ofPred_eq, sub_self, neg_zero]
    norm_num
  have hu1 := hℓA _ hxA
  have hu2 := hℓB _ hxB
  rw [hdec] at hu2
  have hc : 0 < ℓ (0, 1) := by linarith
  have hu : u = ℓ (x, 0) := by
    by_contra hne
    have hlt : u < ℓ (x, 0) := lt_of_le_of_ne hu1 hne
    have hB' : ((x, (u - ℓ (x, 0)) / ℓ (0, 1)) : E × ℝ) ∈ B := by
      rw [hB]
      simp only [Set.mem_ofPred_eq, sub_self, neg_zero]
      exact div_neg_of_neg_of_pos (by linarith) hc
    have h1 := hℓB _ hB'
    rw [hdec, div_mul_cancel₀ _ hc.ne'] at h1
    linarith
  obtain ⟨ψ, hψ⟩ : ∃ ψ : StrongDual ℝ E, ∀ v, ψ v = -(ℓ (v, 0)) / ℓ (0, 1) :=
    ⟨-(ℓ (0, 1))⁻¹ • ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ), fun v => by
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inl_apply, smul_eq_mul]
      field_simp⟩
  have hS1 : ∀ y, f y ≠ ⊤ → ψ (y - x) ≤ g y - g x := by
    intro y hy
    have hyA : ((y, g y - g x) : E × ℝ) ∈ A := by
      rw [hA]
      simp only [Set.mem_ofPred_eq]
      rw [rmm_le_coe f hf]
      refine ⟨hy, ?_⟩
      rw [hκ, hg y, hg x, map_sub, map_sub]
      linarith
    have h1 := hℓA _ hyA
    rw [hdec] at h1
    rw [hψ, hlin, div_le_iff₀ hc]
    linarith
  have hS2 : ∀ y, -ψ (y - x) ≤ K y - K x := by
    intro y
    by_contra hlt
    push Not at hlt
    have hyB : ((y, ψ (y - x)) : E × ℝ) ∈ B := by
      rw [hB]
      simp only [Set.mem_ofPred_eq]
      linarith
    have h1 := hℓB _ hyB
    rw [hdec, hψ, hlin, div_mul_cancel₀ _ hc.ne'] at h1
    linarith
  have hsub : ψ + x0' ∈ Shared.subdiff f x := by
    show ∀ y, f x + (((ψ + x0') (y - x) : ℝ) : EReal) ≤ f y
    intro y
    by_cases hy : f y = ⊤
    · rw [hy]; exact le_top
    · rw [hfF x hxfin, hfF y hy, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have h1 := hS1 y hy
      rw [hg, hg] at h1
      simp only [ContinuousLinearMap.add_apply, map_sub] at h1 ⊢
      linarith
  have hmono := hrel x _ hsub
  simp only [add_sub_cancel_right] at hmono
  have hx0 : x = x0 := by
    have h := hS2 x0
    have e1 : K x0 = δ * ‖x - x0‖ := by
      rw [hK, hk, sub_self, norm_zero, norm_sub_rev]; ring
    have e2 : K x = η * ‖x - x0‖ + η * ‖x - x0‖ ^ 2 := by rw [hKx, hk]
    rw [e1, e2, map_sub] at h
    rw [map_sub] at hmono
    have ht := norm_nonneg (x - x0)
    have h0 : ‖x - x0‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖x - x0‖ := lt_of_le_of_ne ht (Ne.symm hne)
      have := mul_pos hη hpos
      nlinarith [sq_nonneg ‖x - x0‖]
    rwa [norm_eq_zero, sub_eq_zero] at h0
  refine ⟨hx0 ▸ hxfin, fun y hy => ?_⟩
  have h1 := hS1 y hy
  have h2 := hS2 y
  rw [hK y, hKx, hk, hk] at h2
  rw [hx0] at h1 h2
  rw [hg, hg, sub_self, map_zero, sub_zero] at h1
  rw [sub_self, norm_zero] at h2
  have hw := norm_nonneg (y - x0)
  nlinarith [mul_nonneg hη.le hw]

open RockafellarMaxMono in
theorem rmm_key {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f)
    (x0 : E) (x0' : StrongDual ℝ E)
    (hrel : ∀ x, ∀ u ∈ Shared.subdiff f x, 0 ≤ (u - x0') (x - x0)) :
    x0' ∈ Shared.subdiff f x0 := by
  have hfin := (rmm_step f hf hlsc x0 x0' hrel 1 one_pos).1
  show ∀ y, f x0 + ((x0' (y - x0) : ℝ) : EReal) ≤ f y
  intro y
  by_cases hy : f y = ⊤
  · rw [hy]; exact le_top
  rw [← EReal.coe_toReal hfin (hf.1 x0), ← EReal.coe_toReal hy (hf.1 y), ← EReal.coe_add,
    EReal.coe_le_coe_iff]
  apply le_of_forall_pos_le_add
  intro ε hε
  have hw : 0 ≤ ‖y - x0‖ := norm_nonneg _
  have hden : 0 < 2 * ‖y - x0‖ + ‖y - x0‖ ^ 2 + 1 := by positivity
  have h := (rmm_step f hf hlsc x0 x0' hrel (ε / (2 * ‖y - x0‖ + ‖y - x0‖ ^ 2 + 1))
    (div_pos hε hden)).2 y hy
  have h3 : ε / (2 * ‖y - x0‖ + ‖y - x0‖ ^ 2 + 1) * (2 * ‖y - x0‖ + ‖y - x0‖ ^ 2) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith
  linarith

open RockafellarMaxMono RockafellarMaxMono.Maximality in
theorem bregman_existence_accepted_subdiff_maximal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    IsMaximalMonotone (Shared.subdiff f) := by
  have hmono : IsMonotoneOp (Shared.subdiff f) := by
    intro x₀ x₁ x₀' x₁' h0 h1
    have hfin0 := rmm_subdiff_fin f hf x₀ x₀' h0
    have hfin1 := rmm_subdiff_fin f hf x₁ x₁' h1
    have a0 := (show ∀ y, f x₀ + ((x₀' (y - x₀) : ℝ) : EReal) ≤ f y from h0) x₁
    have a1 := (show ∀ y, f x₁ + ((x₁' (y - x₁) : ℝ) : EReal) ≤ f y from h1) x₀
    rw [← EReal.coe_toReal hfin0 (hf.1 x₀), ← EReal.coe_toReal hfin1 (hf.1 x₁),
      ← EReal.coe_add, EReal.coe_le_coe_iff] at a0 a1
    simp only [ContinuousLinearMap.sub_apply, map_sub] at a0 a1 ⊢
    linarith
  refine ⟨hmono, fun T' hT' hsub x => ?_⟩
  ext x'
  constructor
  · intro hx'
    exact rmm_key f hf hlsc x x' fun z u hu => hT' z x u x' (hsub z hu) hx'
  · intro hx'
    exact hsub x hx'


end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open InertialFB.IFB
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Transport the original extended-real subgradient inequality only at verified finite points. -/
theorem subgradient_real_comparison (f : H → EReal) (hproper : IsProperFn f)
    {u v g : H} (hu : IsSubgradient f u g) (hv : f v ≠ ⊤) :
    (f u).toReal+inner ℝ g (v-u) ≤ (f v).toReal := by
  have heu := EReal.coe_toReal hu.1 (hproper.1 u)
  have hev := EReal.coe_toReal hv (hproper.1 v)
  have hg := hu.2 v
  rw [← heu,← hev,← EReal.coe_add] at hg
  exact EReal.coe_le_coe_iff.mp hg

theorem zero_subgradient_real_min (f : H → EReal) (hproper : IsProperFn f)
    {z v : H} (hz : IsSubgradient f z 0) (hv : f v ≠ ⊤) :
    (f z).toReal ≤ (f v).toReal := by
  simpa using subgradient_real_comparison f hproper hz hv

theorem zero_subgradient_of_min (f : H → EReal) {p : H} (hp : f p ≠ ⊤)
    (hmin : ∀ v : H, f p ≤ f v) : IsSubgradient f p 0 := by
  exact ⟨hp,fun v => by simpa using hmin v⟩

/-- Lower semicontinuity passes a verified objective-value limit to a boundary point. -/
theorem lsc_objective_limit (f : H → EReal) (hf : LowerSemicontinuous f)
    (x : ℕ → H) (p : H) (m : EReal) (hx : Tendsto x atTop (𝓝 p))
    (hm : Tendsto (fun k => f (x k)) atTop (𝓝 m)) : f p ≤ m := by
  by_contra hn
  have hmp : m < f p := lt_of_not_ge hn
  obtain ⟨a,hma,hap⟩ := exists_between hmp
  have hl : ∀ᶠ k in atTop, a < f (x k) := hx.eventually (hf p a hap)
  have hu : ∀ᶠ k in atTop, f (x k) < a := hm.eventually (Iio_mem_nhds hma)
  obtain ⟨k,hk⟩ := (hl.and hu).exists
  exact lt_asymm hk.1 hk.2
end BregmanPPACodex

end

section
set_option autoImplicit false
open InertialFB.IFB ThreeOpSplitting.Convergence
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

lemma positive_coe_mul_ne_bot (a : ℝ) (ha : 0 ≤ a) (v : EReal) (hv : v ≠ ⊥) :
    (a : EReal)*v ≠ ⊥ :=
  (EReal.mul_ne_bot _ _).mpr ⟨Or.inl (EReal.coe_ne_bot _),Or.inr hv,
    Or.inl (EReal.coe_ne_top _),Or.inl (EReal.coe_nonneg.mpr ha)⟩

/-- Bridge the original epigraph predicate to the inspected convex-combination helper. -/
theorem epigraph_proper_convex (f : H → EReal) (hp : IsProperFn f) (hc : IsConvexFn f) :
    RockafellarMaxMono.Shared.ProperConvex f := by
  refine ⟨hp.1,hp.2,?_⟩
  intro x y t ht ht1
  by_cases hx : f x=⊤
  · rw [hx,EReal.coe_mul_top_of_pos (sub_pos.mpr ht1),
      EReal.top_add_of_ne_bot (positive_coe_mul_ne_bot t ht.le (f y) (hp.1 y))]
    exact le_top
  by_cases hy : f y=⊤
  · rw [hy,EReal.coe_mul_top_of_pos ht,
      EReal.add_top_of_ne_bot (positive_coe_mul_ne_bot (1-t) (sub_nonneg.mpr ht1.le) (f x) (hp.1 x))]
    exact le_top
  have hxe : (x,(f x).toReal) ∈ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    change f x ≤ ((f x).toReal : EReal)
    rw [EReal.coe_toReal hx (hp.1 x)]
  have hye : (y,(f y).toReal) ∈ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    change f y ≤ ((f y).toReal : EReal)
    rw [EReal.coe_toReal hy (hp.1 y)]
  have hm := hc hxe hye (a := 1-t) (b := t) (sub_nonneg.mpr ht1.le) ht.le (by ring)
  change f ((1-t) • x+t • y) ≤ (((1-t)*(f x).toReal+t*(f y).toReal : ℝ) : EReal) at hm
  rw [EReal.coe_add,EReal.coe_mul,EReal.coe_mul,
    EReal.coe_toReal hx (hp.1 x),EReal.coe_toReal hy (hp.1 y)] at hm
  exact hm

/-- The original Hilbert subgradient is exactly the inspected dual predicate under Riesz. -/
theorem subgradient_riesz_iff (f : H → EReal)
    (hf : RockafellarMaxMono.Shared.ProperConvex f) (x g : H) :
    IsSubgradient f x g ↔ (InnerProductSpace.toDual ℝ H) g ∈ RockafellarMaxMono.Shared.subdiff f x := by
  constructor
  · intro h
    simpa only [RockafellarMaxMono.Shared.subdiff,Set.mem_setOf_eq,
      InnerProductSpace.toDual_apply_apply] using h.2
  · intro h
    refine ⟨rmm_subdiff_fin f hf x ((InnerProductSpace.toDual ℝ H) g) h,?_⟩
    simpa only [RockafellarMaxMono.Shared.subdiff,Set.mem_setOf_eq,
      InnerProductSpace.toDual_apply_apply] using h

/-- Maximal subdifferentials, with the exact original graph-inclusion and epigraph predicates. -/
theorem original_subdiff_maximal (f : H → EReal) (hp : IsProperFn f)
    (hc : IsConvexFn f) (hl : LowerSemicontinuous f) :
    IsMaximalMonotone (BregmanPPA.Convergence.subdiffOp f) := by
  have hf := epigraph_proper_convex f hp hc
  have hmono : IsMonotoneOp (BregmanPPA.Convergence.subdiffOp f) := by
    intro x y g v hg hv
    have h1 := BregmanPPACodex.subgradient_real_comparison f hp hg hv.1
    have h2 := BregmanPPACodex.subgradient_real_comparison f hp hv hg.1
    simp only [inner_sub_left,inner_sub_right] at h1 h2 ⊢
    simp only [real_inner_comm] at h1 h2 ⊢
    linarith
  refine ⟨hmono,?_⟩
  intro T' hT' hsub
  funext x
  ext g
  constructor
  · intro hg
    have hdual : (InnerProductSpace.toDual ℝ H) g ∈ RockafellarMaxMono.Shared.subdiff f x := by
      apply rmm_key f hf hl x ((InnerProductSpace.toDual ℝ H) g)
      intro z u hu
      have huf : IsSubgradient f z ((InnerProductSpace.toDual ℝ H).symm u) :=
        (subgradient_riesz_iff f hf z _).mpr (by simpa using hu)
      have hpair := hT' z x ((InnerProductSpace.toDual ℝ H).symm u) g (hsub z huf) hg
      have he : (u-(InnerProductSpace.toDual ℝ H) g) (z-x) =
          inner ℝ (z-x) ((InnerProductSpace.toDual ℝ H).symm u-g) := by
        rw [ContinuousLinearMap.sub_apply,← InnerProductSpace.toDual_symm_apply,
          InnerProductSpace.toDual_apply_apply]
        rw [← inner_sub_left,real_inner_comm]
      rw [he]
      exact hpair
    exact (subgradient_riesz_iff f hf x g).mpr hdual
  · intro hg; exact hsub x hg
end BregmanExistenceCodex

end

section

open InnerProductSpace

namespace DouglasRachfordPPA.GenDR

/-! Operators on `H` are subsets of `H × H`, encoded as `T : H → Set H` with graph
`{(x, y) | y ∈ T x}` (Eckstein–Bertsekas, pp. 3–5). Monotonicity, maximality, `dom` and `zer`
are the published `ThreeOpSplitting.Convergence` notions. -/

/-- The identity operator `I = {(x, x) | x ∈ H}`. -/
def opId {H : Type*} : H → Set H := fun x => {x}

/-- The scaled operator `cT = {(x, c y) | (x, y) ∈ T}`. -/
def opSmul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (c : ℝ) (T : H → Set H) : H → Set H :=
  fun x => {w | ∃ y ∈ T x, w = c • y}

/-- The sum `A + B = {(x, y + z) | (x, y) ∈ A, (x, z) ∈ B}`; its domain is `dom A ∩ dom B`. -/
def opAdd {H : Type*} [Add H] (A B : H → Set H) : H → Set H :=
  fun x => {w | ∃ y ∈ A x, ∃ z ∈ B x, w = y + z}

/-- The inverse `T⁻¹ = {(y, x) | (x, y) ∈ T}`. -/
def opInv {H : Type*} (T : H → Set H) : H → Set H := fun y => {x | y ∈ T x}

/-- The image (range) `im T = {y | ∃ x, (x, y) ∈ T}`. -/
def imOp {H : Type*} (T : H → Set H) : Set H := {y | ∃ x, y ∈ T x}

/-- The resolvent `J_{cT} = (I + cT)⁻¹`, as an operator (a graph, possibly multivalued and
not everywhere defined). -/
def opResolvent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (c : ℝ) (T : H → Set H) : H → Set H :=
  opInv (opAdd opId (opSmul c T))

/-- An operator `T` is single-valued if `T x` has at most one element for every `x`. -/
def IsSingleValuedOp {H : Type*} (T : H → Set H) : Prop :=
  ∀ x y y' : H, y ∈ T x → y' ∈ T x → y = y'

/-- An operator `C` is nonexpansive if `‖y' - y‖ ≤ ‖x' - x‖` for all `(x, y), (x', y') ∈ C`. -/
def IsNonexpansiveOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : H → Set H) : Prop :=
  ∀ x x' y y' : H, y ∈ C x → y' ∈ C x' → ‖y' - y‖ ≤ ‖x' - x‖

/-- An operator `J` is firmly nonexpansive if `‖y' - y‖² ≤ ⟪x' - x, y' - y⟫` for all
`(x, y), (x', y') ∈ J`. -/
def IsFirmlyNonexpansiveOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : H → Set H) : Prop :=
  ∀ x x' y y' : H, y ∈ J x → y' ∈ J x' → ‖y' - y‖ ^ 2 ≤ ⟪x' - x, y' - y⟫_ℝ

end DouglasRachfordPPA.GenDR

end

section

open InnerProductSpace ThreeOpSplitting.Convergence
open Filter Topology

namespace DouglasRachfordPPA.GenDR

lemma gdr_g_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (a b x : H) :
    ⟪x - a, x - b⟫_ℝ = ‖x - (1/2:ℝ) • (a + b)‖ ^ 2 - ‖(1/2:ℝ) • (a - b)‖ ^ 2 := by
  have h1 : x - a = (x - (1/2:ℝ) • (a + b)) - (1/2:ℝ) • (a - b) := by module
  have h2 : x - b = (x - (1/2:ℝ) • (a + b)) + (1/2:ℝ) • (a - b) := by module
  rw [h1, h2, inner_sub_left, inner_add_right, inner_add_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_comm (x - (1/2:ℝ) • (a + b))]
  ring

lemma gdr_g_pert {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (a b x d : H) (t : ℝ) :
    ⟪(x - t • d) - a, (x - t • d) - b⟫_ℝ = ⟪x - a, x - b⟫_ℝ
      - 2 * t * ⟪x - (1/2:ℝ) • (a + b), d⟫_ℝ + t ^ 2 * ‖d‖ ^ 2 := by
  rw [gdr_g_eq, gdr_g_eq]
  have : x - t • d - (1/2:ℝ) • (a + b) = (x - (1/2:ℝ) • (a + b)) - t • d := by module
  rw [this, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- Weighted inequality: the key algebraic step. -/
lemma gdr_weighted {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (a b : ι → H) (hmono : ∀ i j, 0 ≤ ⟪a i - a j, b j - b i⟫_ℝ) :
    ∑ i, w i * ⟪(∑ j, w j • ((1/2:ℝ) • (a j + b j))) - a i,
        (∑ j, w j • ((1/2:ℝ) • (a j + b j))) - b i⟫_ℝ ≤ 0 := by
  set A := ∑ j, w j • a j
  set B := ∑ j, w j • b j
  have hx : ∑ j, w j • ((1/2:ℝ) • (a j + b j)) = (1/2:ℝ) • (A + B) := by
    simp only [A, B, Finset.smul_sum, ← Finset.sum_add_distrib, smul_add, smul_comm (w _) (1/2:ℝ)]
  rw [hx]
  set x := (1/2:ℝ) • (A + B)
  have e1 : ∀ i, ⟪x - a i, x - b i⟫_ℝ = ‖x‖^2 - ⟪x, b i⟫_ℝ - ⟪a i, x⟫_ℝ + ⟪a i, b i⟫_ℝ := by
    intro i
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq]; ring
  simp_rw [e1]
  have hs : ∑ i, w i * (‖x‖^2 - ⟪x, b i⟫_ℝ - ⟪a i, x⟫_ℝ + ⟪a i, b i⟫_ℝ)
      = ‖x‖^2 - ⟪x, B⟫_ℝ - ⟪A, x⟫_ℝ + ∑ i, w i * ⟪a i, b i⟫_ℝ := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hw1, one_mul, A, B, inner_sum, sum_inner, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  rw [hs]
  -- double sum
  have hD : 0 ≤ ∑ i, ∑ j, w i * w j * ⟪a i - a j, b j - b i⟫_ℝ :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hw0 i) (hw0 j)) (hmono i j)
  have hAB : ⟪A, B⟫_ℝ = ∑ i, ∑ j, w i * w j * ⟪a i, b j⟫_ℝ := by
    simp only [A, B, sum_inner, inner_sum, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
      Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  have hBA : ⟪A, B⟫_ℝ = ∑ i, ∑ j, w i * w j * ⟪a j, b i⟫_ℝ := by
    rw [hAB, Finset.sum_comm]; simp only [mul_comm (w _) (w _)]
  have hd1 : ∑ i, ∑ j, w i * w j * ⟪a i, b i⟫_ℝ = ∑ i, w i * ⟪a i, b i⟫_ℝ := by
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_mul, ← Finset.mul_sum, hw1, mul_one]
  have hd2 : ∑ i, ∑ j, w i * w j * ⟪a j, b j⟫_ℝ = ∑ i, w i * ⟪a i, b i⟫_ℝ := by
    rw [Finset.sum_comm]; simp only [mul_comm (w _) (w _)]; exact hd1
  have hexp : ∑ i, ∑ j, w i * w j * ⟪a i - a j, b j - b i⟫_ℝ =
      (∑ i, ∑ j, w i * w j * ⟪a i, b j⟫_ℝ) - (∑ i, ∑ j, w i * w j * ⟪a i, b i⟫_ℝ)
      - (∑ i, ∑ j, w i * w j * ⟪a j, b j⟫_ℝ) + (∑ i, ∑ j, w i * w j * ⟪a j, b i⟫_ℝ) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    rw [inner_sub_left, inner_sub_right, inner_sub_right]; ring
  rw [hexp, ← hAB, ← hBA, hd1, hd2] at hD
  have hx2 : ‖x‖^2 = (1/4:ℝ) * (‖A‖^2 + 2 * ⟪A, B⟫_ℝ + ‖B‖^2) := by
    simp only [x, norm_smul, mul_pow, norm_add_sq_real]; norm_num
  have hxB : ⟪x, B⟫_ℝ = (1/2:ℝ) * (⟪A, B⟫_ℝ + ‖B‖^2) := by
    simp only [x, inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq, RCLike.conj_to_real]
  have hAx : ⟪A, x⟫_ℝ = (1/2:ℝ) * (‖A‖^2 + ⟪A, B⟫_ℝ) := by
    simp only [x, inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq]
  have hAmB : 0 ≤ ‖A - B‖^2 := sq_nonneg _
  rw [norm_sub_sq_real] at hAmB
  rw [hx2, hxB, hAx]
  nlinarith


/-- projection variational inequality onto a compact convex set -/
lemma gdr_proj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : Set H) (hK : Convex ℝ K) (x q : H) (hq : q ∈ K)
    (hmin : ∀ y ∈ K, ‖x - q‖ ≤ ‖x - y‖) : ∀ z ∈ K, ⟪x - q, z - q⟫_ℝ ≤ 0 := by
  intro z hz
  by_contra hcon
  push_neg at hcon
  set ε := ⟪x - q, z - q⟫_ℝ
  set N := ‖z - q‖ ^ 2
  have hN : 0 ≤ N := sq_nonneg _
  set t := min 1 (ε / (N + 1))
  have ht0 : 0 < t := lt_min one_pos (div_pos hcon (by linarith))
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ ε / (N + 1) := min_le_right _ _
  have htN : t * N < 2 * ε := by
    have : t * (N + 1) ≤ ε := by rwa [le_div_iff₀ (by linarith)] at ht2
    nlinarith
  have hmem : q + t • (z - q) ∈ K := by
    have := hK hq hz (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
    convert this using 1; module
  have h1 := hmin _ hmem
  have h2 : ‖x - (q + t • (z - q))‖ ^ 2 = ‖x - q‖ ^ 2 - 2 * t * ε + t ^ 2 * N := by
    have : x - (q + t • (z - q)) = (x - q) - t • (z - q) := by module
    rw [this, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have h3 : ‖x - q‖ ^ 2 ≤ ‖x - (q + t • (z - q))‖ ^ 2 := by
    gcongr
  rw [h2] at h3
  nlinarith

lemma gdr_finite {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s : Finset (H × H)) (hs : s.Nonempty)
    (hmono : ∀ p ∈ s, ∀ q ∈ s, 0 ≤ ⟪p.1 - q.1, q.2 - p.2⟫_ℝ) :
    ∃ x : H, ∀ p ∈ s, ⟪x - p.1, x - p.2⟫_ℝ ≤ 0 := by
  classical
  set cen : H × H → H := fun p => (1/2:ℝ) • (p.1 + p.2) with hcen
  set g : H × H → H → ℝ := fun p x => ⟪x - p.1, x - p.2⟫_ℝ with hg
  have gcont : ∀ p, Continuous (g p) := fun p => by
    simp only [hg]; fun_prop
  set K := convexHull ℝ (cen '' (s : Set (H × H)))
  have hKc : IsCompact K := (s.finite_toSet.image cen).isCompact_convexHull ℝ
  obtain ⟨p0, hp0⟩ := hs
  have hKne : K.Nonempty := ⟨cen p0, subset_convexHull ℝ _ ⟨p0, hp0, rfl⟩⟩
  set φ : H → ℝ := fun x => s.sup' ⟨p0, hp0⟩ (fun p => g p x)
  have hφc : Continuous φ := Continuous.finset_sup'_apply _ (fun p _ => gcont p)
  obtain ⟨xs, hxsK, hxmin⟩ := hKc.exists_isMinOn hKne hφc.continuousOn
  set m := φ xs
  have hgm : ∀ p ∈ s, g p xs ≤ m := fun p hp => Finset.le_sup' (fun p => g p xs) hp
  suffices hm : m ≤ 0 from ⟨xs, fun p hp => (hgm p hp).trans hm⟩
  set I := s.filter (fun p => g p xs = m)
  have hIs : I ⊆ s := Finset.filter_subset _ _
  obtain ⟨pm, hpm, hpmeq⟩ := Finset.exists_mem_eq_sup' ⟨p0, hp0⟩ (fun p => g p xs)
  have hpmI : pm ∈ I := Finset.mem_filter.2 ⟨hpm, hpmeq.symm⟩
  set KI := convexHull ℝ (cen '' (I : Set (H × H)))
  have hKIK : KI ⊆ K := convexHull_mono (Set.image_mono (by exact_mod_cast hIs))
  have hxsKI : xs ∈ KI := by
    by_contra hnot
    have hKIc : IsCompact KI := (I.finite_toSet.image cen).isCompact_convexHull ℝ
    have hKIne : KI.Nonempty := ⟨cen pm, subset_convexHull ℝ _ ⟨pm, hpmI, rfl⟩⟩
    obtain ⟨q, hqKI, hqmin⟩ := hKIc.exists_isMinOn hKIne
      (continuous_const.sub continuous_id).norm.continuousOn (f := fun y => ‖xs - y‖)
    have hvi := gdr_proj KI (convex_convexHull ℝ _) xs q hqKI (fun y hy => hqmin hy)
    set d := xs - q
    have hd : d ≠ 0 := by
      intro h; apply hnot; rw [show xs = q from sub_eq_zero.1 h]; exact hqKI
    have hdpos : 0 < ‖d‖ ^ 2 := by positivity
    have hact : ∀ p ∈ I, ‖d‖ ^ 2 ≤ ⟪xs - cen p, d⟫_ℝ := by
      intro p hp
      have := hvi (cen p) (subset_convexHull ℝ _ ⟨p, hp, rfl⟩)
      have e : xs - cen p = d - (cen p - q) := by simp only [d]; abel
      rw [e, inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm]
      linarith
    -- find t
    have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
        0 < t ∧ t ≤ 1 ∧ ∀ p ∈ s, p ∉ I → g p (xs - t • d) < m := by
      refine (Filter.Eventually.and self_mem_nhdsWithin ?_)
      refine Filter.Eventually.and ?_ ?_
      · exact nhdsWithin_le_nhds (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
      · rw [Filter.eventually_all_finset]
        intro p hp
        by_cases hpI : p ∈ I
        · exact Filter.Eventually.of_forall fun _ h => absurd hpI h
        · have hlt : g p xs < m := by
            refine lt_of_le_of_ne (hgm p hp) ?_
            intro h; exact hpI (Finset.mem_filter.2 ⟨hp, h⟩)
          have hc : Continuous (fun t : ℝ => g p (xs - t • d)) :=
            (gcont p).comp (continuous_const.sub (continuous_id.smul continuous_const))
          have ht := hc.tendsto 0
          simp only [zero_smul, sub_zero] at ht
          exact nhdsWithin_le_nhds ((ht.eventually (gt_mem_nhds hlt)).mono fun _ h _ => h)
    obtain ⟨t, ht0, ht1, htI⟩ := hev.exists
    have hmemK : xs - t • d ∈ K := by
      have := (convex_convexHull ℝ (cen '' (s : Set (H × H)))) hxsK (hKIK hqKI)
        (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
      convert this using 1; simp only [d]; module
    have hlt : φ (xs - t • d) < m := by
      obtain ⟨p, hp, hpeq⟩ := Finset.exists_mem_eq_sup' ⟨p0, hp0⟩ (fun p => g p (xs - t • d))
      show s.sup' _ (fun p => g p (xs - t • d)) < m
      rw [hpeq]
      by_cases hpI : p ∈ I
      · have hgp : g p xs = m := (Finset.mem_filter.1 hpI).2
        have := gdr_g_pert p.1 p.2 xs d t
        have ha := hact p hpI
        simp only [hg] at hgp ⊢
        rw [this, hgp]
        have : 0 < t * ‖d‖ ^ 2 * (2 - t) :=
          mul_pos (mul_pos ht0 hdpos) (by linarith)
        nlinarith
      · exact htI p hp hpI
    exact absurd (hxmin hmemK) (not_le.2 hlt)
  -- now xs is a convex combination of active centers
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hxs⟩ := mem_convexHull_iff_exists_fintype.1 hxsKI
  choose pz hpzI hpzc using fun i => (hz i)
  have key := gdr_weighted w hw0 hw1 (fun i => (pz i).1) (fun i => (pz i).2)
    (fun i j => hmono _ (hIs (hpzI i)) _ (hIs (hpzI j)))
  have hxs' : ∑ j, w j • ((1/2:ℝ) • ((pz j).1 + (pz j).2)) = xs := by
    rw [← hxs]; apply Finset.sum_congr rfl; intro j _; rw [← hpzc j]
  rw [hxs'] at key
  have hall : ∀ i, ⟪xs - (pz i).1, xs - (pz i).2⟫_ℝ = m := fun i =>
    (Finset.mem_filter.1 (hpzI i)).2
  simp only [hall, ← Finset.sum_mul, hw1, one_mul] at key
  exact key

lemma gdr_real_ulim {ι : Type*} (f : ι → ℝ) (M : ℝ) (hM : ∀ k, |f k| ≤ M) (U : Ultrafilter ι) :
    ∃ a, Tendsto f U (𝓝 a) := by
  have hc : IsCompact (Set.Icc (-M) M) := isCompact_Icc
  obtain ⟨a, -, ha⟩ := hc.ultrafilter_le_nhds (U.map f) (by
    rw [Filter.le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
    exact Filter.univ_mem' (fun k => abs_le.1 (hM k)))
  exact ⟨a, ha⟩

lemma gdr_exists_ulim {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {ι : Type*} (u : ι → H) (M : ℝ) (hM : ∀ k, ‖u k‖ ≤ M) (U : Ultrafilter ι) :
    ∃ w : H, ∀ y, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 (inner ℝ w y)) := by
  have hb : ∀ y k, |inner ℝ (u k) y| ≤ M * ‖y‖ := fun y k =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM k) (norm_nonneg _))
  have hex : ∀ y, ∃ a, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 a) :=
    fun y => gdr_real_ulim _ _ (hb y) U
  set L : H → ℝ := fun y => limUnder (U : Filter ι) (fun k => inner ℝ (u k) y) with hL
  have hLt : ∀ y, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 (L y)) :=
    fun y => tendsto_nhds_limUnder (hex y)
  have hadd : ∀ y y', L (y + y') = L y + L y' := by
    intro y y'
    have h1 := hLt (y + y')
    have h2 := (hLt y).add (hLt y')
    simp only [inner_add_right] at h1
    exact tendsto_nhds_unique h1 h2
  have hsmul : ∀ (c : ℝ) y, L (c • y) = c * L y := by
    intro c y
    have h1 := hLt (c • y)
    have h2 := (hLt y).const_mul c
    simp only [real_inner_smul_right] at h1
    exact tendsto_nhds_unique h1 h2
  let Ll : H →ₗ[ℝ] ℝ :=
    { toFun := L, map_add' := hadd, map_smul' := fun c y => by simp [hsmul] }
  have hbd : ∀ y, ‖Ll y‖ ≤ M * ‖y‖ := by
    intro y
    show |L y| ≤ M * ‖y‖
    have := (hLt y)
    have hmem : ∀ᶠ k in (U : Filter ι), inner ℝ (u k) y ∈ Set.Icc (-(M * ‖y‖)) (M * ‖y‖) :=
      Filter.Eventually.of_forall (fun k => abs_le.1 (hb y k))
    exact abs_le.2 (isClosed_Icc.mem_of_tendsto this hmem)
  let Lc : StrongDual ℝ H := Ll.mkContinuous M hbd
  refine ⟨(InnerProductSpace.toDual ℝ H).symm Lc, fun y => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  exact hLt y

lemma gdr_weak_closed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {ι : Type*} (U : Filter ι) [U.NeBot] (u : ι → H) (w a b : H)
    (hw : ∀ y, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 (inner ℝ w y)))
    (hev : ∀ᶠ k in U, ⟪u k - a, u k - b⟫_ℝ ≤ 0) : ⟪w - a, w - b⟫_ℝ ≤ 0 := by
  set c := (1/2:ℝ) • (a + b)
  set r := ‖(1/2:ℝ) • (a - b)‖
  have hr : 0 ≤ r := norm_nonneg _
  have hev2 : ∀ᶠ k in U, ⟪u k - c, w - c⟫_ℝ ≤ r * ‖w - c‖ := by
    filter_upwards [hev] with k hk
    rw [gdr_g_eq] at hk
    have h1 : ‖u k - c‖ ≤ r := by
      have : ‖u k - c‖ ^ 2 ≤ r ^ 2 := by linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr two_ne_zero).1 this
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
  have hlim : Tendsto (fun k => ⟪u k - c, w - c⟫_ℝ) U (𝓝 (‖w - c‖ ^ 2)) := by
    have := (hw (w - c)).sub (tendsto_const_nhds (x := ⟪c, w - c⟫_ℝ))
    simp only [← inner_sub_left, real_inner_self_eq_norm_sq] at this
    exact this
  have hle : ‖w - c‖ ^ 2 ≤ r * ‖w - c‖ := le_of_tendsto hlim hev2
  have hle2 : ‖w - c‖ ≤ r := by
    by_contra h; push_neg at h
    have : 0 < ‖w - c‖ := lt_of_le_of_lt hr h
    nlinarith
  rw [gdr_g_eq]
  have := norm_nonneg (w - c)
  nlinarith

lemma gdr_inf {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : Set (H × H)) (hmono : ∀ p ∈ S, ∀ q ∈ S, 0 ≤ ⟪p.1 - q.1, q.2 - p.2⟫_ℝ) :
    ∃ x : H, ∀ p ∈ S, ⟪x - p.1, x - p.2⟫_ℝ ≤ 0 := by
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨p0, hp0⟩
  · exact ⟨0, fun p hp => by simp [hS] at hp⟩
  set F' : Finset (H × H) → Finset (H × H) := fun F => insert p0 (F.filter (· ∈ S))
  have hF'S : ∀ F, ∀ p ∈ F' F, p ∈ S := by
    intro F p hp
    rcases Finset.mem_insert.1 hp with h | h
    · rw [h]; exact hp0
    · exact (Finset.mem_filter.1 h).2
  have hex : ∀ F, ∃ x : H, ∀ p ∈ F' F, ⟪x - p.1, x - p.2⟫_ℝ ≤ 0 := fun F =>
    gdr_finite (F' F) ⟨p0, Finset.mem_insert_self _ _⟩
      (fun p hp q hq => hmono p (hF'S F p hp) q (hF'S F q hq))
  choose xF hxF using hex
  set c0 := (1/2:ℝ) • (p0.1 + p0.2)
  set r0 := ‖(1/2:ℝ) • (p0.1 - p0.2)‖
  have hbd : ∀ F, ‖xF F‖ ≤ ‖c0‖ + r0 := by
    intro F
    have h := hxF F p0 (Finset.mem_insert_self _ _)
    rw [gdr_g_eq] at h
    have h1 : ‖xF F - c0‖ ≤ r0 := by
      have : ‖xF F - c0‖ ^ 2 ≤ r0 ^ 2 := by linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
    calc ‖xF F‖ = ‖(xF F - c0) + c0‖ := by rw [sub_add_cancel]
      _ ≤ ‖xF F - c0‖ + ‖c0‖ := norm_add_le _ _
      _ ≤ ‖c0‖ + r0 := by linarith
  set U : Ultrafilter (Finset (H × H)) := Ultrafilter.of (atTop : Filter (Finset (H × H)))
  obtain ⟨w, hw⟩ := gdr_exists_ulim xF _ hbd U
  refine ⟨w, fun p hp => ?_⟩
  apply gdr_weak_closed (U : Filter (Finset (H × H))) xF w p.1 p.2 hw
  have hat : ∀ᶠ F in (atTop : Filter (Finset (H × H))), ⟪xF F - p.1, xF F - p.2⟫_ℝ ≤ 0 := by
    filter_upwards [eventually_ge_atTop {p}] with F hF
    apply hxF F p
    apply Finset.mem_insert_of_mem
    exact Finset.mem_filter.2 ⟨hF (Finset.mem_singleton_self p), hp⟩
  exact Ultrafilter.of_le _ hat

lemma gdr_minty_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → Set H) (hT : IsMaximalMonotone T) (c : ℝ) (hc : 0 < c) (w : H) :
    ∃ x y, y ∈ T x ∧ w = x + c • y := by
  set S : Set (H × H) := {p | c⁻¹ • (w - p.2) ∈ T p.1}
  have hmono : ∀ p ∈ S, ∀ q ∈ S, 0 ≤ ⟪p.1 - q.1, q.2 - p.2⟫_ℝ := by
    intro p hp q hq
    have h := hT.1 _ _ _ _ hp hq
    have e : q.2 - p.2 = c • (c⁻¹ • (w - p.2) - c⁻¹ • (w - q.2)) := by
      rw [smul_sub, smul_smul, smul_smul, mul_inv_cancel₀ hc.ne', one_smul, one_smul]; abel
    rw [e, inner_smul_right]
    exact mul_nonneg hc.le h
  obtain ⟨x, hx⟩ := gdr_inf S hmono
  set y0 := c⁻¹ • (w - x)
  set T' : H → Set H := fun z => {y | y ∈ T z ∨ (z = x ∧ y = y0)}
  have hsub : ∀ z, T z ⊆ T' z := fun z y hy => Or.inl hy
  have key : ∀ z y, y ∈ T z → 0 ≤ ⟪z - x, y - y0⟫_ℝ := by
    intro z y hy
    have hp : (z, w - c • y) ∈ S := by
      show c⁻¹ • (w - (w - c • y)) ∈ T z
      rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]; exact hy
    have h := hx _ hp
    simp only at h
    have e : y - y0 = c⁻¹ • (x - (w - c • y)) := by
      simp only [y0]
      rw [smul_sub, smul_sub, smul_sub, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]; abel
    rw [e, inner_smul_right]
    have : ⟪z - x, x - (w - c • y)⟫_ℝ = -⟪x - z, x - (w - c • y)⟫_ℝ := by
      rw [← inner_neg_left, neg_sub]
    rw [this]
    exact mul_nonneg (inv_nonneg.2 hc.le) (by linarith)
  have hT'mono : IsMonotoneOp T' := by
    intro z1 z2 u1 u2 h1 h2
    rcases h1 with h1 | ⟨rfl, rfl⟩ <;> rcases h2 with h2 | ⟨rfl, rfl⟩
    · exact hT.1 _ _ _ _ h1 h2
    · exact key _ _ h1
    · have := key _ _ h2
      rw [← neg_sub z2, ← neg_sub u2, inner_neg_neg]; exact this
    · simp
  have hEq := hT.2 T' hT'mono hsub
  have hy0 : y0 ∈ T x := by
    have : y0 ∈ T' x := Or.inr ⟨rfl, rfl⟩
    rw [hEq] at this; exact this
  refine ⟨x, y0, hy0, ?_⟩
  simp only [y0]
  rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]; abel

lemma gdr_max_iff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → Set H) (hT : IsMonotoneOp T) (c : ℝ) (hc : 0 < c) :
    IsMaximalMonotone T ↔ ∀ w, ∃ x y, y ∈ T x ∧ w = x + c • y := by
  constructor
  · intro h w; exact gdr_minty_core T h c hc w
  · intro hsurj
    refine ⟨hT, fun T' hT' hsub => ?_⟩
    funext z
    apply Set.Subset.antisymm _ (hsub z)
    intro u hu
    obtain ⟨x, y, hy, hw⟩ := hsurj (z + c • u)
    have hm := hT' z x u y hu (hsub x hy)
    have e : z - x = c • (y - u) := by
      rw [smul_sub]; linear_combination (norm := module) hw
    rw [e, inner_smul_left, RCLike.conj_to_real, ← neg_sub u y, inner_neg_left,
      real_inner_self_eq_norm_sq] at hm
    have hn : ‖u - y‖ ^ 2 ≤ 0 := by nlinarith
    have : u - y = 0 := by
      have := pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 (le_antisymm hn (sq_nonneg _))
      exact norm_eq_zero.1 this
    have huy : u = y := sub_eq_zero.1 this
    have hzx : z = x := by
      have : z - x = 0 := by rw [e, huy, sub_self, smul_zero]
      exact sub_eq_zero.1 this
    rw [huy, hzx]; exact hy

lemma gdr_mem_res {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (c : ℝ) (T : H → Set H) (w x : H) :
    x ∈ opResolvent c T w ↔ ∃ y ∈ T x, w = x + c • y := by
  simp only [opResolvent, opInv, opAdd, opId, opSmul, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, rfl, b, ⟨y, hy, rfl⟩, h⟩; exact ⟨y, hy, h⟩
  · rintro ⟨y, hy, h⟩; exact ⟨x, rfl, c • y, ⟨y, hy, rfl⟩, h⟩

theorem minty_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → Set H) (hT : IsMonotoneOp T) :
    IsMaximalMonotone T ↔ imOp (opAdd opId T) = Set.univ := by
  rw [gdr_max_iff T hT 1 one_pos, Set.eq_univ_iff_forall]
  simp only [imOp, opAdd, opId, Set.mem_setOf_eq, Set.mem_singleton_iff, one_smul]
  constructor
  · intro h w
    obtain ⟨x, y, hy, hw⟩ := h w
    exact ⟨x, x, rfl, y, hy, hw⟩
  · intro h w
    obtain ⟨x, a, rfl, y, hy, hw⟩ := h w
    exact ⟨a, y, hy, hw⟩

lemma gdr_fne_iff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (c : ℝ) (hc : 0 < c) (T : H → Set H) :
    IsMonotoneOp T ↔ IsFirmlyNonexpansiveOp (opResolvent c T) := by
  have expand : ∀ x x' y y' : H, ⟪(x' + c • y') - (x + c • y), x' - x⟫_ℝ
      = ‖x' - x‖ ^ 2 + c * ⟪x' - x, y' - y⟫_ℝ := by
    intro x x' y y'
    have : (x' + c • y') - (x + c • y) = (x' - x) + c • (y' - y) := by module
    rw [this, inner_add_left, real_inner_self_eq_norm_sq, inner_smul_left, RCLike.conj_to_real,
      real_inner_comm]
  constructor
  · intro hT w w' x x' hx hx'
    obtain ⟨y, hy, rfl⟩ := (gdr_mem_res c T w x).1 hx
    obtain ⟨y', hy', rfl⟩ := (gdr_mem_res c T w' x').1 hx'
    rw [expand]
    have := hT x' x y' y hy' hy
    nlinarith
  · intro hF x x' y y' hy hy'
    have h := hF (x' + c • y') (x + c • y) x' x ((gdr_mem_res c T _ _).2 ⟨y', hy', rfl⟩)
      ((gdr_mem_res c T _ _).2 ⟨y, hy, rfl⟩)
    rw [expand] at h
    have : 0 ≤ c * ⟪x - x', y - y'⟫_ℝ := by linarith
    exact nonneg_of_mul_nonneg_right (by linarith) hc |> fun h' => by
      by_contra hneg; push_neg at hneg; nlinarith

theorem resolvent_fne_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (c : ℝ) (hc : 0 < c) (T : H → Set H) :
    (IsMonotoneOp T ↔ IsFirmlyNonexpansiveOp (opResolvent c T)) ∧
    (IsMaximalMonotone T ↔
      IsFirmlyNonexpansiveOp (opResolvent c T) ∧ dom (opResolvent c T) = Set.univ) := by
  refine ⟨gdr_fne_iff c hc T, ?_⟩
  have hdom : dom (opResolvent c T) = Set.univ ↔ ∀ w, ∃ x y, y ∈ T x ∧ w = x + c • y := by
    rw [Set.eq_univ_iff_forall]
    simp only [dom, Set.mem_setOf_eq, Set.Nonempty, gdr_mem_res]
  constructor
  · intro hM
    exact ⟨(gdr_fne_iff c hc T).1 hM.1, hdom.2 ((gdr_max_iff T hM.1 c hc).1 hM)⟩
  · rintro ⟨hF, hD⟩
    have hT := (gdr_fne_iff c hc T).2 hF
    exact (gdr_max_iff T hT c hc).2 (hdom.1 hD)

lemma gdr_mem_M {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : H → Set H) (y u : H) :
    u ∈ opAdd (opInv K) (opSmul (-1) opId) y ↔ y ∈ K (u + y) := by
  simp only [opAdd, opInv, opSmul, opId, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ha, b, ⟨z, hz, hb⟩, hu⟩
    rw [hu, hb, hz]
    have : a + (-1:ℝ) • y + y = a := by module
    rw [this]; exact ha
  · intro h
    refine ⟨u + y, h, (-1:ℝ) • y, ⟨y, rfl, rfl⟩, ?_⟩
    module

theorem fne_inv_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : H → Set H) :
    (IsFirmlyNonexpansiveOp K ↔ IsMonotoneOp (opAdd (opInv K) (opSmul (-1) opId))) ∧
    (IsFirmlyNonexpansiveOp K ∧ dom K = Set.univ ↔
      IsMaximalMonotone (opAdd (opInv K) (opSmul (-1) opId))) := by
  set M := opAdd (opInv K) (opSmul (-1) opId)
  have p1 : IsFirmlyNonexpansiveOp K ↔ IsMonotoneOp M := by
    constructor
    · intro hF y y' u u' hu hu'
      rw [gdr_mem_M] at hu hu'
      have h := hF _ _ _ _ hu' hu
      have e : (u + y) - (u' + y') = (u - u') + (y - y') := by abel
      rw [e, inner_add_left, real_inner_self_eq_norm_sq] at h
      have e2 : ⟪u - u', y - y'⟫_ℝ = ⟪y - y', u - u'⟫_ℝ := real_inner_comm _ _
      rw [norm_sub_rev] at h
      linarith
    · intro hM x x' y y' hy hy'
      have h1 : (x - y) ∈ M y := (gdr_mem_M K y _).2 (by rw [sub_add_cancel]; exact hy)
      have h2 : (x' - y') ∈ M y' := (gdr_mem_M K y' _).2 (by rw [sub_add_cancel]; exact hy')
      have h := hM _ _ _ _ h2 h1
      rw [real_inner_comm] at h
      have e : x' - x = ((x' - y') - (x - y)) + (y' - y) := by abel
      rw [e, inner_add_left, real_inner_self_eq_norm_sq]
      linarith
  refine ⟨p1, ?_⟩
  have hdom : dom K = Set.univ ↔ ∀ w, ∃ x y, y ∈ M x ∧ w = x + (1:ℝ) • y := by
    rw [Set.eq_univ_iff_forall]
    simp only [dom, Set.Nonempty, one_smul]
    constructor
    · intro h w
      obtain ⟨y, hy⟩ := h w
      refine ⟨y, w - y, (gdr_mem_M K y _).2 (by rw [sub_add_cancel]; exact hy), by abel⟩
    · intro h w
      obtain ⟨x, y, hy, rfl⟩ := h w
      rw [gdr_mem_M] at hy
      exact ⟨x, by rw [add_comm]; exact hy⟩
  constructor
  · rintro ⟨hF, hD⟩
    have hM := p1.1 hF
    exact (gdr_max_iff M hM 1 one_pos).2 (hdom.1 hD)
  · intro hMax
    exact ⟨p1.2 hMax.1, hdom.2 ((gdr_max_iff M hMax.1 1 one_pos).1 hMax)⟩

lemma gdr_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (c : ℝ) (hc : 0 < c) (T : H → Set H) (hT : IsMonotoneOp T) :
    IsSingleValuedOp (opResolvent c T) := by
  intro w x x' hx hx'
  have h := (gdr_fne_iff c hc T).1 hT w w x x' hx hx'
  rw [sub_self, inner_zero_left] at h
  have : ‖x' - x‖ = 0 := by
    have := sq_nonneg ‖x' - x‖
    exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (le_antisymm h this)
  exact (sub_eq_zero.1 (norm_eq_zero.1 this)).symm

theorem resolvent_sv_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (c : ℝ) (hc : 0 < c) (T : H → Set H) :
    (IsMonotoneOp T → IsSingleValuedOp (opResolvent c T)) ∧
    (IsMaximalMonotone T → dom (opResolvent c T) = Set.univ) ∧
    (IsMaximalMonotone T → ∃! J : H → H, IsResolvent c T J) := by
  refine ⟨gdr_single c hc T, fun hM => ((resolvent_fne_core c hc T).2.1 hM).2, fun hM => ?_⟩
  have hex : ∀ w, ∃ x, x ∈ opResolvent c T w := by
    intro w
    obtain ⟨x, y, hy, hw⟩ := gdr_minty_core T hM c hc w
    exact ⟨x, (gdr_mem_res c T w x).2 ⟨y, hy, hw⟩⟩
  choose J hJ using hex
  have hres : ∀ J : H → H, IsResolvent c T J ↔ ∀ w, J w ∈ opResolvent c T w := by
    intro J
    constructor
    · intro h w
      refine (gdr_mem_res c T w (J w)).2 ⟨_, h w, ?_⟩
      rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]; abel
    · intro h w
      obtain ⟨y, hy, hw⟩ := (gdr_mem_res c T w (J w)).1 (h w)
      have : c⁻¹ • (w - J w) = y := by
        rw [sub_eq_of_eq_add' hw, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      rw [this]; exact hy
  refine ⟨J, (hres J).2 hJ, fun J' hJ' => ?_⟩
  funext w
  exact gdr_single c hc T hM.1 w _ _ (hJ w) ((hres J').1 hJ' w) |>.symm

theorem representation_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (c : ℝ) (hc : 0 < c) (T : H → Set H) (hT : IsMonotoneOp T) :
    (∀ z x y x' y' : H, y ∈ T x → y' ∈ T x' → z = x + c • y → z = x' + c • y' →
      x = x' ∧ y = y') ∧
    (IsMaximalMonotone T → ∀ z : H, ∃! p : H × H, p.2 ∈ T p.1 ∧ z = p.1 + c • p.2) := by
  have p1 : ∀ z x y x' y' : H, y ∈ T x → y' ∈ T x' → z = x + c • y → z = x' + c • y' →
      x = x' ∧ y = y' := by
    intro z x y x' y' hy hy' hz hz'
    have hxx := gdr_single c hc T hT z x x' ((gdr_mem_res c T z x).2 ⟨y, hy, hz⟩)
      ((gdr_mem_res c T z x').2 ⟨y', hy', hz'⟩)
    refine ⟨hxx, ?_⟩
    rw [hz, hxx] at hz'
    have := add_left_cancel hz'
    exact smul_right_injective H hc.ne' this
  refine ⟨p1, fun hM z => ?_⟩
  obtain ⟨x, y, hy, hz⟩ := gdr_minty_core T hM c hc z
  refine ⟨(x, y), ⟨hy, hz⟩, fun p hp => ?_⟩
  obtain ⟨h1, h2⟩ := p1 z p.1 p.2 x y hp.1 hy hp.2 hz
  exact Prod.ext h1 h2

end DouglasRachfordPPA.GenDR

open DouglasRachfordPPA.GenDR


theorem bregman_existence_accepted_minty {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → Set H) (hT : IsMonotoneOp T) :
    IsMaximalMonotone T ↔ imOp (opAdd opId T) = Set.univ := by
  exact minty_core T hT


end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.ProxMult
namespace BregmanProxMultCodex

theorem finite_toReal_lscWithin {n : ℕ} (C : Set (E n)) (F : E n → EReal)
    (hp : IsProperFn F) (hl : LowerSemicontinuous F) (hf : ∀ x ∈ C, F x ≠ ⊤)
    (x : E n) (hx : x ∈ C) :
    LowerSemicontinuousWithinAt (fun y => (F y).toReal) C x := by
  intro a ha
  have he : (a : EReal) < F x := by
    rw [← EReal.coe_toReal (hf x hx) (hp.1 x)]
    exact EReal.coe_lt_coe_iff.mpr ha
  have hh : ∀ᶠ y in 𝓝[C] x, (a : EReal) < F y :=
    (hl x (a : EReal) he).filter_mono nhdsWithin_le_nhds
  filter_upwards [hh,self_mem_nhdsWithin] with y hy hCy
  rw [← EReal.coe_toReal (hf y hCy) (hp.1 y)] at hy
  exact EReal.coe_lt_coe_iff.mp hy

theorem lagr_real_lscWithin {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (p : E m) (hp : p ∈ nonnegOrthant m) (x : E n) (hx : x ∈ C) :
    LowerSemicontinuousWithinAt (fun y => (f y).toReal+inner ℝ p (gvec g y)) C x := by
  have hf := finite_toReal_lscWithin C f hP.f_proper hP.f_lsc hP.f_finite x hx
  have hg (i : Fin m) : LowerSemicontinuousWithinAt (fun y => p i*(g i y).toReal) C x := by
    have hi := finite_toReal_lscWithin C (g i) (hP.g_proper i) (hP.g_lsc i) (hP.g_finite i) x hx
    have hcont : ContinuousAt (fun t : ℝ => p i*t) ((g i x).toReal) := by fun_prop
    exact hcont.comp_lowerSemicontinuousWithinAt (f := fun y : E n => (g i y).toReal)
      (s := C) (x := x) hi (fun _ _ h => mul_le_mul_of_nonneg_left h (hp i))
  have hs := lowerSemicontinuousWithinAt_sum (a := Finset.univ) (fun i _ => hg i)
  convert hf.add hs using 1 <;>
    first | rfl | (ext y; simp [PiLp.inner_apply,gvec,mul_comm])

theorem lagr_lsc {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (p : E m) (hp : p ∈ nonnegOrthant m) :
    LowerSemicontinuous (fun y => lagr C f g y p) := by
  classical
  intro x a ha
  dsimp only at ha ⊢
  by_cases hx : x ∈ C
  · have hr := lagr_real_lscWithin C f g hP p hp x hx
    have hxv := lagr_finite_rep C f g hP x hx p hp
    rw [hxv] at ha
    by_cases hab : a=⊥
    · subst a
      exact Filter.Eventually.of_forall fun y => by
        by_cases hy : y ∈ C
        · rw [lagr_finite_rep C f g hP y hy p hp]
          exact EReal.bot_lt_coe _
        · simp [lagr,hy]
    have hat : a ≠ ⊤ := ne_top_of_lt ha
    have hac := EReal.coe_toReal hat hab
    have har : a.toReal < (f x).toReal+inner ℝ p (gvec g x) := by
      rw [← hac] at ha
      exact EReal.coe_lt_coe_iff.mp ha
    have he := hr a.toReal har
    have hU : ∀ᶠ y in 𝓝 x, y ∈ C → a.toReal < (f y).toReal+inner ℝ p (gvec g y) := by
      exact eventually_nhdsWithin_iff.mp he
    filter_upwards [hU] with y hy
    by_cases hCy : y ∈ C
    · rw [lagr_finite_rep C f g hP y hCy p hp,← hac]
      exact EReal.coe_lt_coe_iff.mpr (hy hCy)
    · simp only [lagr,if_neg hCy]
      exact lt_top_iff_ne_top.mpr hat
  · have hU : Cᶜ ∈ 𝓝 x := hP.closed.isOpen_compl.mem_nhds hx
    filter_upwards [hU] with y hy
    simp only [Set.mem_compl_iff] at hy
    simpa only [lagr,if_neg hx,if_neg hy] using ha

/-- Each finite shifted Lagrangian is closed, convex and proper. -/
theorem shifted_lagr_properties {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (p : E m) (hp : p ∈ nonnegOrthant m) (r : ℝ) :
    IsProperFn (fun y => lagr C f g y p+(r:EReal)) ∧
    IsConvexFn (fun y => lagr C f g y p+(r:EReal)) ∧
    LowerSemicontinuous (fun y => lagr C f g y p+(r:EReal)) := by
  classical
  have he (x : E n) (t : ℝ) : lagr C f g x p+(r:EReal) ≤ (t:EReal) ↔
      x ∈ C ∧ (f x).toReal+inner ℝ p (gvec g x)+r ≤ t := by
    by_cases hx : x ∈ C
    · rw [lagr_finite_rep C f g hP x hx p hp,← EReal.coe_add]
      simp only [EReal.coe_le_coe_iff,hx,true_and]
    · simp [lagr,hx]
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro x
    dsimp only
    by_cases hx : x ∈ C
    · rw [lagr_finite_rep C f g hP x hx p hp,← EReal.coe_add]
      exact EReal.coe_ne_bot _
    · simp [lagr,hx]
  · obtain ⟨x,hx⟩ := hP.nonempty
    refine ⟨x,?_⟩
    dsimp only
    rw [lagr_finite_rep C f g hP x hx p hp,← EReal.coe_add]
    exact EReal.coe_ne_top _
  · have hr := (lagr_real_convex C f g hP p hp).add_const r
    intro x hx y hy a b ha hb hab
    have hx' := (he x.1 x.2).mp hx
    have hy' := (he y.1 y.2).mp hy
    apply (he _ _).mpr
    refine ⟨hP.convex hx'.1 hy'.1 ha hb hab,?_⟩
    exact (hr.2 hx'.1 hy'.1 ha hb hab).trans
      (add_le_add (smul_le_smul_of_nonneg_left hx'.2 ha)
        (smul_le_smul_of_nonneg_left hy'.2 hb))
  · exact (lagr_lsc C f g hP p hp).add' lowerSemicontinuous_const
      (fun _ => EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot r))
        (Or.inr (EReal.coe_ne_top r)))

/-- The guarded primal conjugate penalty, as an exact supremum of shifted Lagrangians. -/
noncomputable def primal_sup {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (h : E m → ℝ) (p0 : E m) (x : E n) : EReal :=
  ⨆ p : {p : E m // p ∈ nonnegOrthant m},
    lagr C f g x p.val+((inner ℝ p.val p0-h p.val : ℝ):EReal)

theorem primal_sup_closed_convex {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (h : E m → ℝ) (p0 : E m) :
    IsConvexFn (primal_sup C f g h p0) ∧
    LowerSemicontinuous (primal_sup C f g h p0) := by
  have hs (p : {p : E m // p ∈ nonnegOrthant m}) :=
    shifted_lagr_properties C f g hP p.val p.property (inner ℝ p.val p0-h p.val)
  constructor
  · intro x hx y hy a b ha hb hab
    change (⨆ p : {p : E m // p ∈ nonnegOrthant m},
      lagr C f g (a • x+b • y).1 p.val+
        ((inner ℝ p.val p0-h p.val : ℝ):EReal)) ≤ ((a • x+b • y).2:EReal)
    apply iSup_le
    intro p
    have hx' := (le_iSup (fun q : {q : E m // q ∈ nonnegOrthant m} =>
      lagr C f g x.1 q.val+((inner ℝ q.val p0-h q.val : ℝ):EReal)) p).trans hx
    have hy' := (le_iSup (fun q : {q : E m // q ∈ nonnegOrthant m} =>
      lagr C f g y.1 q.val+((inner ℝ q.val p0-h q.val : ℝ):EReal)) p).trans hy
    exact (hs p).2.1 hx' hy' ha hb hab
  · exact lowerSemicontinuous_iSup fun p => (hs p).2.2

theorem primal_sup_proper {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (h : E m → ℝ) (p0 : E m)
    (hfinite : ∀ z, monoConj h z ≠ ⊤ ∧ monoConj h z ≠ ⊥) :
    IsProperFn (primal_sup C f g h p0) := by
  have hz : (0:E m) ∈ nonnegOrthant m := by intro i; simp
  constructor
  · intro x
    have ht := (shifted_lagr_properties C f g hP (0:E m) hz
      (inner ℝ (0:E m) p0-h 0)).1.1 x
    exact ne_of_gt ((bot_lt_iff_ne_bot.mpr ht).trans_le
      (le_iSup (fun p : {p : E m // p ∈ nonnegOrthant m} =>
        lagr C f g x p.val+((inner ℝ p.val p0-h p.val : ℝ):EReal)) ⟨0,hz⟩))
  · obtain ⟨x,hx⟩ := hP.nonempty
    refine ⟨x,?_⟩
    have hb : primal_sup C f g h p0 x ≤
        (((f x).toReal+(monoConj h (p0+gvec g x)).toReal:ℝ):EReal) := by
      apply iSup_le
      intro p
      have hl : ((inner ℝ p.val (p0+gvec g x)-h p.val:ℝ):EReal) ≤
          monoConj h (p0+gvec g x) :=
        le_iSup_of_le p.val (le_iSup_of_le p.property le_rfl)
      rw [← EReal.coe_toReal (hfinite _).1 (hfinite _).2] at hl
      have hr := EReal.coe_le_coe_iff.mp hl
      rw [lagr_finite_rep C f g hP x hx p.val p.property,← EReal.coe_add]
      apply EReal.coe_le_coe_iff.mpr
      rw [inner_add_right] at hr
      linarith
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hb

theorem ereal_coe_add_iSup {ι : Type*} (a : ℝ) (F : ι → EReal) :
    (a:EReal)+(⨆ i, F i) = ⨆ i, (a:EReal)+F i := by
  apply le_antisymm
  · have h : (⨆ i, F i) ≤ (-a:EReal)+(⨆ i, (a:EReal)+F i) := by
      apply iSup_le
      intro i
      have hi := add_le_add (show (-a:EReal) ≤ (-a:EReal) from le_rfl) (le_iSup (fun i => (a:EReal)+F i) i)
      simpa only [← add_assoc,← EReal.coe_neg,← EReal.coe_add,neg_add_cancel,EReal.coe_zero,zero_add] using hi
    have hh := add_le_add (show (a:EReal) ≤ (a:EReal) from le_rfl) h
    simpa only [← add_assoc,← EReal.coe_neg,← EReal.coe_add,add_neg_cancel,EReal.coe_zero,zero_add] using hh
  · exact iSup_le fun i => add_le_add le_rfl (le_iSup F i)

theorem primal_sup_value {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (h : E m → ℝ) (p0 : E m) (x : E n) (hx : x ∈ C) :
    primal_sup C f g h p0 x =
      ((f x).toReal:EReal)+monoConj h (p0+gvec g x) := by
  have he (p : {p : E m // p ∈ nonnegOrthant m}) :
      lagr C f g x p.val+((inner ℝ p.val p0-h p.val:ℝ):EReal) =
      ((f x).toReal:EReal)+((inner ℝ p.val (p0+gvec g x)-h p.val:ℝ):EReal) := by
    rw [lagr_finite_rep C f g hP x hx p.val p.property]
    simp only [← EReal.coe_add,inner_add_right]
    congr 1
    ring
  unfold primal_sup
  simp_rw [he]
  rw [← ereal_coe_add_iSup]
  simp only [monoConj,iSup_subtype]

theorem primal_sup_top_off {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (h : E m → ℝ) (p0 : E m)
    (x : E n) (hx : x ∉ C) : primal_sup C f g h p0 x = ⊤ := by
  classical
  have hz : (0:E m) ∈ nonnegOrthant m := by intro i; simp
  apply top_le_iff.mp
  have hl := le_iSup (fun p : {p : E m // p ∈ nonnegOrthant m} =>
    lagr C f g x p.val+((inner ℝ p.val p0-h p.val:ℝ):EReal)) ⟨0,hz⟩
  simpa only [primal_sup,lagr,if_neg hx,EReal.top_add_coe] using hl

theorem primal_sup_minty {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (h : E m → ℝ) (p0 : E m)
    (hfinite : ∀ z, monoConj h z ≠ ⊤ ∧ monoConj h z ≠ ⊥) (x0 : E n) :
    ∃ x ∈ C, IsSubgradient (primal_sup C f g h p0) x (x0-x) := by
  have hc := primal_sup_closed_convex C f g hP h p0
  have hm := BregmanExistenceCodex.original_subdiff_maximal
    (primal_sup C f g h p0) (primal_sup_proper C f g hP h p0 hfinite) hc.1 hc.2
  have hi := (bregman_existence_accepted_minty
    (BregmanPPA.Convergence.subdiffOp (primal_sup C f g h p0)) hm.1).mp hm
  have hx0 : x0 ∈ DouglasRachfordPPA.GenDR.imOp
      (DouglasRachfordPPA.GenDR.opAdd DouglasRachfordPPA.GenDR.opId
        (BregmanPPA.Convergence.subdiffOp (primal_sup C f g h p0))) := by
    rw [hi]; trivial
  obtain ⟨x,a,ha,v,hv,he⟩ := hx0
  have hax : a=x := ha
  subst a
  have hev : x0-x=v := by rw [he]; abel
  have hs : IsSubgradient (primal_sup C f g h p0) x (x0-x) := by rw [hev]; exact hv
  refine ⟨x,?_,hs⟩
  by_contra hx
  exact hs.1 (primal_sup_top_off C f g h p0 x hx)

theorem primal_quadratic_minimizer {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (h : E m → ℝ) (p0 : E m)
    (hfinite : ∀ z, monoConj h z ≠ ⊤ ∧ monoConj h z ≠ ⊥) (x0 : E n) :
    ∃ x ∈ C, ∀ y ∈ C,
      (f x).toReal+(monoConj h (p0+gvec g x)).toReal+(1/2:ℝ)*‖x-x0‖^2 ≤
      (f y).toReal+(monoConj h (p0+gvec g y)).toReal+(1/2:ℝ)*‖y-x0‖^2 := by
  obtain ⟨x,hx,hs⟩ := primal_sup_minty C f g hP h p0 hfinite x0
  have hv (z : E n) (hz : z ∈ C) : primal_sup C f g h p0 z =
      (((f z).toReal+(monoConj h (p0+gvec g z)).toReal:ℝ):EReal) := by
    rw [primal_sup_value C f g hP h p0 z hz,
      ← EReal.coe_toReal (hfinite _).1 (hfinite _).2,← EReal.coe_add]
    simp only [EReal.toReal_coe]
  refine ⟨x,hx,?_⟩
  intro y hy
  have hi := hs.2 y
  rw [hv x hx,hv y hy,← EReal.coe_add] at hi
  have hr := EReal.coe_le_coe_iff.mp hi
  have he : (1/2:ℝ)*‖y-x0‖^2-(1/2:ℝ)*‖x-x0‖^2+
      inner ℝ (x0-x) (y-x) = (1/2:ℝ)*‖y-x‖^2 := by
    simp only [norm_sub_sq_real,inner_sub_left,inner_sub_right,real_inner_self_eq_norm_sq]
    simp only [real_inner_comm]
    ring
  nlinarith [sq_nonneg ‖y-x‖]

end BregmanProxMultCodex





end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.ProxMult ThreeOpSplitting.Convergence
namespace BregmanProxMultCodex

theorem opK_monotone {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g) :
    IsMonotoneOp (opK C f g) := by
  intro x y u v hu hv
  have hx := opK_point_in_program C f g x u hu
  have hy := opK_point_in_program C f g y v hv
  have ha := hu.1.2 y.ofLp.1
  have hb := hv.1.2 x.ofLp.1
  have hc := hu.2.2 y.ofLp.2
  have hd := hv.2.2 x.ofLp.2
  dsimp only at ha hb hc hd
  simp only [neg_neg] at hc hd
  rw [lagr_finite_rep C f g hP x.ofLp.1 hx.1 x.ofLp.2 hx.2,
    lagr_finite_rep C f g hP y.ofLp.1 hy.1 x.ofLp.2 hx.2] at ha
  rw [lagr_finite_rep C f g hP y.ofLp.1 hy.1 y.ofLp.2 hy.2,
    lagr_finite_rep C f g hP x.ofLp.1 hx.1 y.ofLp.2 hy.2] at hb
  rw [lagr_finite_rep C f g hP x.ofLp.1 hx.1 x.ofLp.2 hx.2,
    lagr_finite_rep C f g hP x.ofLp.1 hx.1 y.ofLp.2 hy.2] at hc
  rw [lagr_finite_rep C f g hP y.ofLp.1 hy.1 y.ofLp.2 hy.2,
    lagr_finite_rep C f g hP y.ofLp.1 hy.1 x.ofLp.2 hx.2] at hd
  simp only [← EReal.coe_neg,← EReal.coe_add,EReal.coe_le_coe_iff] at ha hb hc hd
  rw [real_inner_comm]
  change 0 ≤ inner ℝ (u.ofLp.1-v.ofLp.1) (x.ofLp.1-y.ofLp.1)+
    inner ℝ (u.ofLp.2-v.ofLp.2) (x.ofLp.2-y.ofLp.2)
  simp only [inner_sub_left,inner_sub_right] at ha hb hc hd ⊢
  linarith
end BregmanProxMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.ProxMult BregmanPPA.Convergence
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
namespace BregmanProxMultCodex

theorem opK_minty_point {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (x0 : E n) (p0 : E m) :
    ∃ x p, pair x0 p0-pair x p ∈ opK C f g (pair x p) := by
  have hpos : posOrthant m ⊆ (Set.univ : Set (E m)) := Set.subset_univ _
  have himpos : posOrthant m ⊆ gradient (quadratic (H:=E m)) '' Set.univ := by
    rw [quadratic_image]; exact Set.subset_univ _
  have hM := BregmanIneqMultCodex.monoConj_real_properties Set.univ quadratic
    quadratic_bregman hpos himpos
  obtain ⟨x,hx,hmin⟩ := primal_quadratic_minimizer C f g hP quadratic p0 hM.1 x0
  let p := gradient (fun z => (monoConj (quadratic (H:=E m)) z).toReal) (p0+gvec g x)
  have hminimum : ∀ y ∈ C,
      proxMultObj f g quadratic quadratic 1 x0 p0 x ≤
      proxMultObj f g quadratic quadratic 1 x0 p0 y := by
    intro y hy
    simp only [proxMultObj,inv_one,one_mul,quadratic_gradient,one_smul,quadratic_distance]
    rw [← EReal.coe_toReal (hP.f_finite x hx) (hP.f_proper.1 x),
      ← EReal.coe_toReal (hP.f_finite y hy) (hP.f_proper.1 y),← EReal.coe_add,← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    simpa only [add_assoc] using hmin y hy
  have hpr := primal_step C f g Set.univ quadratic Set.univ quadratic 1 x0 x p0 p
    hP (by norm_num) quadratic_bregman (Set.subset_univ C) quadratic_bregman
    (Set.subset_univ _) quadratic_image hx hminimum (by simp only [quadratic_gradient,one_smul]; rfl)
  simp only [inv_one,one_smul,quadratic_gradient] at hpr
  have hstation := BregmanIneqMultCodex.monoConj_projected_stationarity
    Set.univ quadratic quadratic_bregman hpos himpos (p0+gvec g x) (Set.mem_univ _)
  change p0+gvec g x-gradient quadratic p ∈ normalCone (nonnegOrthant m) p at hstation
  rw [quadratic_gradient] at hstation
  have hu : IsSubgradient (indicatorPos m) p (p0+gvec g x-p) :=
    (indicator_support p _ hpr.1).mpr hstation.2
  refine ⟨x,p,?_⟩
  change x0-x ∈ subdiffX C f g x p ∧ -(p0-p) ∈ supdiffP C f g x p
  refine ⟨hpr.2,?_⟩
  rw [original_supdiff_formula C f g hP x hx p hpr.1]
  refine ⟨p0+gvec g x-p,hu,?_⟩
  module

theorem original_K_maximal {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g) :
    IsMaximalMonotone (opK C f g) := by
  apply (bregman_existence_accepted_minty (opK C f g) (opK_monotone C f g hP)).mpr
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨x,p,hw⟩ := opK_minty_point C f g hP z.ofLp.1 z.ofLp.2
  refine ⟨pair x p,pair x p,rfl,z-pair x p,?_,?_⟩
  · exact hw
  · abel
end BregmanProxMultCodex

end

section
set_option autoImplicit false
open BregmanPPA.IneqMult BregmanPPA.ProxMult BregmanPPA.Convergence
namespace BregmanProxMultCodex

theorem sum_bregman_pair {n m : ℕ} (hx : E n → ℝ) (hp : E m → ℝ)
    (x y : E n) (p q : E m) (hdy : DifferentiableAt ℝ hx y)
    (hdq : DifferentiableAt ℝ hp q) :
    bregmanD (sumFn hx hp) (pair x p) (pair y q) =
      bregmanD hx x y+bregmanD hp p q := by
  rw [bregmanD,sum_gradient_pair hx hp y q hdy hdq]
  simp only [bregmanD,sumFn,pair,WithLp.prod_inner_apply]
  change hx x+hp p-(hx y+hp q)-
      (inner ℝ (gradient hx y) (x-y)+inner ℝ (gradient hp q) (p-q)) =
    hx x-hx y-inner ℝ (gradient hx y) (x-y)+
      (hp p-hp q-inner ℝ (gradient hp q) (p-q))
  ring
end BregmanProxMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.ProxMult BregmanPPA.Convergence
namespace BregmanProxMultCodex
variable {n m : ℕ}

theorem prodZone_closure (Sx : Set (E n)) (Sp : Set (E m)) :
    closure (prodZone Sx Sp) = prodZone (closure Sx) (closure Sp) := by
  let e := WithLp.homeomorphProd 2 (E n) (E m)
  change closure (e ⁻¹' (Sx ×ˢ Sp)) = e ⁻¹' (closure Sx ×ˢ closure Sp)
  rw [← e.preimage_closure,closure_prod_eq]

theorem prodZone_open (Sx : Set (E n)) (Sp : Set (E m))
    (hx : IsOpen Sx) (hp : IsOpen Sp) : IsOpen (prodZone Sx Sp) := by
  change IsOpen ((fun z : PD n m => z.ofLp.1) ⁻¹' Sx ∩
    (fun z : PD n m => z.ofLp.2) ⁻¹' Sp)
  exact (hx.preimage (by fun_prop)).inter (hp.preimage (by fun_prop))

theorem packed_bounded_iff (s : Set (PD n m)) :
    Bornology.IsBounded s ↔
      Bornology.IsBounded ((fun z => z.ofLp.1) '' s) ∧
      Bornology.IsBounded ((fun z => z.ofLp.2) '' s) := by
  change @Bornology.IsBounded _ (Bornology.induced (@WithLp.ofLp 2 (E n × E m))) s ↔ _
  rw [Bornology.isBounded_induced,← Bornology.isBounded_image_fst_and_snd]
  simp only [Set.image_image,Function.comp_def]

theorem prodZone_bounded (Sx : Set (E n)) (Sp : Set (E m))
    (hx : Bornology.IsBounded Sx) (hp : Bornology.IsBounded Sp) :
    Bornology.IsBounded (prodZone Sx Sp) := by
  apply (packed_bounded_iff _).mpr
  constructor
  · apply hx.subset
    rintro _ ⟨z,hz,rfl⟩
    exact hz.1
  · apply hp.subset
    rintro _ ⟨z,hz,rfl⟩
    exact hz.2

theorem sum_contDiffOn (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp) :
    ContDiffOn ℝ 1 (sumFn hx hp) (prodZone Sx Sp) := by
  let F : PD n m →L[ℝ] E n := WithLp.fstL 2 ℝ (E n) (E m)
  let G : PD n m →L[ℝ] E m := WithLp.sndL 2 ℝ (E n) (E m)
  exact (hhx.contDiffOn.comp F.contDiff.contDiffOn (fun z hz => hz.1)).add
    (hhp.contDiffOn.comp G.contDiff.contDiffOn (fun z hz => hz.2))

theorem sum_continuousOn (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp) :
    ContinuousOn (sumFn hx hp) (closure (prodZone Sx Sp)) := by
  rw [prodZone_closure]
  exact (hhx.continuousOn.comp (by fun_prop) (fun z hz => hz.1)).add
    (hhp.continuousOn.comp (by fun_prop) (fun z hz => hz.2))

theorem sum_strictConvexOn (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp) :
    StrictConvexOn ℝ (closure (prodZone Sx Sp)) (sumFn hx hp) := by
  rw [prodZone_closure]
  refine ⟨?_,?_⟩
  · intro x hx' y hy' a b ha hb hab
    exact ⟨hhx.strictConvexOn.1 hx'.1 hy'.1 ha hb hab,
      hhp.strictConvexOn.1 hx'.2 hy'.2 ha hb hab⟩
  · intro x hx' y hy' hne a b ha hb hab
    have hxc := hhx.strictConvexOn.convexOn.2 hx'.1 hy'.1 ha.le hb.le hab
    have hpc := hhp.strictConvexOn.convexOn.2 hx'.2 hy'.2 ha.le hb.le hab
    by_cases he : x.ofLp.1=y.ofLp.1
    · have hn : x.ofLp.2 ≠ y.ofLp.2 := by
        intro hn
        apply hne
        apply WithLp.ofLp_injective
        exact Prod.ext he hn
      have hps := hhp.strictConvexOn.2 hx'.2 hy'.2 hn ha hb hab
      change hx (a • x.ofLp.1+b • y.ofLp.1)+hp (a • x.ofLp.2+b • y.ofLp.2) <
        a*(hx x.ofLp.1+hp x.ofLp.2)+b*(hx y.ofLp.1+hp y.ofLp.2)
      simp only [smul_eq_mul] at hxc hps
      linarith
    · have hxs := hhx.strictConvexOn.2 hx'.1 hy'.1 he ha hb hab
      change hx (a • x.ofLp.1+b • y.ofLp.1)+hp (a • x.ofLp.2+b • y.ofLp.2) <
        a*(hx x.ofLp.1+hp x.ofLp.2)+b*(hx y.ofLp.1+hp y.ofLp.2)
      simp only [smul_eq_mul] at hxs hpc
      linarith

theorem sum_distance (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp)
    (x y : PD n m) (hy : y ∈ prodZone Sx Sp) :
    bregmanD (sumFn hx hp) x y =
      bregmanD hx x.ofLp.1 y.ofLp.1+bregmanD hp x.ofLp.2 y.ofLp.2 := by
  have hdx : DifferentiableAt ℝ hx y.ofLp.1 :=
    ((hhx.contDiffOn.differentiableOn (by simp)) _ hy.1).differentiableAt (hhx.isOpen.mem_nhds hy.1)
  have hdp : DifferentiableAt ℝ hp y.ofLp.2 :=
    ((hhp.contDiffOn.differentiableOn (by simp)) _ hy.2).differentiableAt (hhp.isOpen.mem_nhds hy.2)
  exact sum_bregman_pair hx hp x.ofLp.1 y.ofLp.1 x.ofLp.2 y.ofLp.2 hdx hdp
end BregmanProxMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.ProxMult BregmanPPA.Convergence
namespace BregmanProxMultCodex
variable {n m : ℕ}

theorem sum_component_bounds (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp)
    (x y : PD n m) (hxC : x ∈ closure (prodZone Sx Sp)) (hy : y ∈ prodZone Sx Sp)
    (α : ℝ) (hb : bregmanD (sumFn hx hp) x y ≤ α) :
    bregmanD hx x.ofLp.1 y.ofLp.1 ≤ α ∧ bregmanD hp x.ofLp.2 y.ofLp.2 ≤ α := by
  rw [prodZone_closure] at hxC
  have hn1 := BregmanPPACodex.bregman_nonneg Sx hx hhx hxC.1 hy.1
  have hn2 := BregmanPPACodex.bregman_nonneg Sp hp hhp hxC.2 hy.2
  rw [sum_distance Sx Sp hx hp hhx hhp x y hy] at hb
  constructor <;> linarith

theorem sum_bounded_L1 (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp)
    (α : ℝ) (y : PD n m) (hy : y ∈ prodZone Sx Sp) :
    Bornology.IsBounded {x | x ∈ closure (prodZone Sx Sp) ∧ bregmanD (sumFn hx hp) x y ≤ α} := by
  have hb := prodZone_bounded
    {x | x ∈ closure Sx ∧ bregmanD hx x y.ofLp.1 ≤ α}
    {p | p ∈ closure Sp ∧ bregmanD hp p y.ofLp.2 ≤ α}
    (hhx.bounded_L₁ α y.ofLp.1 hy.1) (hhp.bounded_L₁ α y.ofLp.2 hy.2)
  apply hb.subset
  rintro x ⟨hxC,hD⟩
  have hs := sum_component_bounds Sx Sp hx hp hhx hhp x y hxC hy α hD
  rw [prodZone_closure] at hxC
  exact ⟨⟨hxC.1,hs.1⟩,⟨hxC.2,hs.2⟩⟩

theorem sum_bounded_L2 (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp)
    (α : ℝ) (x : PD n m) (hxC : x ∈ closure (prodZone Sx Sp)) :
    Bornology.IsBounded {y | y ∈ prodZone Sx Sp ∧ bregmanD (sumFn hx hp) x y ≤ α} := by
  have hC := hxC
  rw [prodZone_closure] at hC
  have hb := prodZone_bounded
    {y | y ∈ Sx ∧ bregmanD hx x.ofLp.1 y ≤ α}
    {q | q ∈ Sp ∧ bregmanD hp x.ofLp.2 q ≤ α}
    (hhx.bounded_L₂ α x.ofLp.1 hC.1) (hhp.bounded_L₂ α x.ofLp.2 hC.2)
  apply hb.subset
  rintro y ⟨hy,hD⟩
  have hs := sum_component_bounds Sx Sp hx hp hhx hhp x y hxC hy α hD
  exact ⟨⟨hy.1,hs.1⟩,⟨hy.2,hs.2⟩⟩

theorem sum_tendsto_zero (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp)
    (y : ℕ → PD n m) (y' : PD n m) (hy : ∀ k, y k ∈ prodZone Sx Sp)
    (ht : Tendsto y atTop (𝓝 y')) :
    Tendsto (fun k => bregmanD (sumFn hx hp) y' (y k)) atTop (𝓝 0) := by
  have hxT := (show Continuous (fun z : PD n m => z.ofLp.1) by fun_prop).tendsto y' |>.comp ht
  have hpT := (show Continuous (fun z : PD n m => z.ofLp.2) by fun_prop).tendsto y' |>.comp ht
  have h1 := hhx.tendsto_zero (fun k => (y k).ofLp.1) y'.ofLp.1 (fun k => (hy k).1) hxT
  have h2 := hhp.tendsto_zero (fun k => (y k).ofLp.2) y'.ofLp.2 (fun k => (hy k).2) hpT
  have he : (fun k => bregmanD (sumFn hx hp) y' (y k)) =
      (fun k => bregmanD hx y'.ofLp.1 (y k).ofLp.1+bregmanD hp y'.ofLp.2 (y k).ofLp.2) := by
    funext k
    exact sum_distance Sx Sp hx hp hhx hhp y' (y k) (hy k)
  rw [he]
  simpa using h1.add h2

theorem sum_tendsto_of_zero (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp)
    (x y : ℕ → PD n m) (y' : PD n m)
    (hxC : ∀ k, x k ∈ closure (prodZone Sx Sp)) (hy : ∀ k, y k ∈ prodZone Sx Sp)
    (hyT : Tendsto y atTop (𝓝 y')) (hyC : y' ∈ closure (prodZone Sx Sp))
    (hB : Bornology.IsBounded (Set.range x))
    (hD : Tendsto (fun k => bregmanD (sumFn hx hp) (x k) (y k)) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 y') := by
  have hC (k : ℕ) : (x k).ofLp.1 ∈ closure Sx ∧ (x k).ofLp.2 ∈ closure Sp := by
    have hi := hxC k
    rw [prodZone_closure] at hi
    exact hi
  have hnn1 (k : ℕ) : 0 ≤ bregmanD hx (x k).ofLp.1 (y k).ofLp.1 :=
    BregmanPPACodex.bregman_nonneg Sx hx hhx (hC k).1 (hy k).1
  have hnn2 (k : ℕ) : 0 ≤ bregmanD hp (x k).ofLp.2 (y k).ofLp.2 :=
    BregmanPPACodex.bregman_nonneg Sp hp hhp (hC k).2 (hy k).2
  have hd1 : Tendsto (fun k => bregmanD hx (x k).ofLp.1 (y k).ofLp.1) atTop (𝓝 0) := by
    apply squeeze_zero hnn1 _ hD
    intro k
    rw [sum_distance Sx Sp hx hp hhx hhp (x k) (y k) (hy k)]
    linarith [hnn2 k]
  have hd2 : Tendsto (fun k => bregmanD hp (x k).ofLp.2 (y k).ofLp.2) atTop (𝓝 0) := by
    apply squeeze_zero hnn2 _ hD
    intro k
    rw [sum_distance Sx Sp hx hp hhx hhp (x k) (y k) (hy k)]
    linarith [hnn1 k]
  have hyT1 := (show Continuous (fun z : PD n m => z.ofLp.1) by fun_prop).tendsto y' |>.comp hyT
  have hyT2 := (show Continuous (fun z : PD n m => z.ofLp.2) by fun_prop).tendsto y' |>.comp hyT
  have hb := (packed_bounded_iff (Set.range x)).mp hB
  have hb1 : Bornology.IsBounded (Set.range (fun k => (x k).ofLp.1)) := by
    apply hb.1.subset
    rintro _ ⟨k,rfl⟩
    exact ⟨x k,⟨k,rfl⟩,rfl⟩
  have hb2 : Bornology.IsBounded (Set.range (fun k => (x k).ofLp.2)) := by
    apply hb.2.subset
    rintro _ ⟨k,rfl⟩
    exact ⟨x k,⟨k,rfl⟩,rfl⟩
  rw [prodZone_closure] at hyC
  have ht1 := hhx.tendsto_of_zero (fun k => (x k).ofLp.1) (fun k => (y k).ofLp.1) y'.ofLp.1
    (fun k => (hC k).1) (fun k => (hy k).1) hyT1 hyC.1 hb1 hd1
  have ht2 := hhp.tendsto_of_zero (fun k => (x k).ofLp.2) (fun k => (y k).ofLp.2) y'.ofLp.2
    (fun k => (hC k).2) (fun k => (hy k).2) hyT2 hyC.2 hb2 hd2
  exact (WithLp.prod_continuous_toLp 2 (E n) (E m)).tendsto (y'.ofLp) |>.comp (ht1.prodMk_nhds ht2)
end BregmanProxMultCodex

end

section
set_option autoImplicit false
open BregmanPPA.IneqMult BregmanPPA.ProxMult BregmanPPA.Convergence
namespace BregmanProxMultCodex

theorem product_bregman {n m : ℕ} (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp) :
    IsBregmanFunction (prodZone Sx Sp) (sumFn hx hp) where
  isOpen := prodZone_open Sx Sp hhx.isOpen hhp.isOpen
  contDiffOn := sum_contDiffOn Sx Sp hx hp hhx hhp
  strictConvexOn := sum_strictConvexOn Sx Sp hx hp hhx hhp
  continuousOn := sum_continuousOn Sx Sp hx hp hhx hhp
  bounded_L₁ := sum_bounded_L1 Sx Sp hx hp hhx hhp
  bounded_L₂ := sum_bounded_L2 Sx Sp hx hp hhx hhp
  tendsto_zero := sum_tendsto_zero Sx Sp hx hp hhx hhp
  tendsto_of_zero := sum_tendsto_of_zero Sx Sp hx hp hhx hhp
end BregmanProxMultCodex

end

section

open InertialFB.IFB

namespace BregmanPPA.Existence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The extended function `ĥ` of the closing note of Definition 1 (p. 205): `ĥ = h` on `S̄` and
`ĥ = +∞` off `S̄`. Its subdifferential `subdiffOp (extendedFn S h)` is the paper's `∂h`. -/
noncomputable def extendedFn (S : Set H) (h : H → ℝ) : H → EReal := by
  classical
  exact fun x => if x ∈ closure S then ((h x : ℝ) : EReal) else ⊤

/-- The gradient `∇h` as an operator with domain `dom ∇h = S`: `x ↦ {∇h(x)}` for `x ∈ S` and
`x ↦ ∅` off `S`. Its image `imOp (gradOp S h)` is `im ∇h = ∇h(S)`. -/
noncomputable def gradOp (S : Set H) (h : H → ℝ) : H → Set H :=
  fun x => {g | x ∈ S ∧ g = gradient h x}

/-- A run of recursion (3), `x^{k+1} = (∇h + c_k T)⁻¹(∇h(x^k))`, in its equivalent form (4)
(p. 207): every iterate lies in `S = dom ∇h`, and
`(1/c_k)(∇h(x^k) − ∇h(x^{k+1})) ∈ T(x^{k+1})` for every `k`. -/
def IsBregmanPPARun (S : Set H) (h : H → ℝ) (T : H → Set H) (c : ℕ → ℝ) (x : ℕ → H) : Prop :=
  ∀ k, x k ∈ S ∧ (c k)⁻¹ • (gradient h (x k) - gradient h (x (k + 1))) ∈ T (x (k + 1))

end BregmanPPA.Existence

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open ThreeOpSplitting.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Adjoining a related point to the exact original graph cannot extend a maximal operator. -/
theorem maximal_related_point (T : H → Set H) (hT : IsMaximalMonotone T) (z u : H)
    (hrel : ∀ v w : H, w ∈ T v → 0 ≤ inner ℝ (z-v) (u-w)) : u ∈ T z := by
  let U : H → Set H := fun x => T x ∪ {v | x=z ∧ v=u}
  have hU : IsMonotoneOp U := by
    intro x y v w hv hw
    rcases hv with hv | ⟨hx,hv⟩
    · rcases hw with hw | ⟨hy,hw⟩
      · exact hT.1 x y v w hv hw
      · rw [hy,hw]
        have he : inner ℝ (x-z) (v-u) = inner ℝ (z-x) (u-v) := by
          rw [← neg_sub z x,← neg_sub u v,inner_neg_left,inner_neg_right,neg_neg]
        rw [he]; exact hrel x v hv
    · rcases hw with hw | ⟨hy,hw⟩
      · rw [hx,hv]; exact hrel y w hw
      · rw [hx,hv,hy,hw]; simp
  have hEq : U=T := hT.2 U hU (fun x => Set.subset_union_left)
  have hu : u ∈ U z := Or.inr ⟨rfl,rfl⟩
  rwa [hEq] at hu

/-- Norm limits of graph points remain in the exact original maximal monotone graph. -/
theorem maximal_graph_limit (T : H → Set H) (hT : IsMaximalMonotone T)
    (x u : ℕ → H) (z v : H) (hx : Tendsto x atTop (𝓝 z)) (hu : Tendsto u atTop (𝓝 v))
    (hmem : ∀ k, u k ∈ T (x k)) : v ∈ T z := by
  apply maximal_related_point T hT z v
  intro y w hw
  have ht : Tendsto (fun k => inner ℝ (x k-y) (u k-w)) atTop (𝓝 (inner ℝ (z-y) (v-w))) :=
    (hx.sub_const y).inner (hu.sub_const w)
  exact (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).mem_of_tendsto ht
    (Eventually.of_forall (fun k => hT.1 (x k) y (u k) w (hmem k) hw))
end BregmanPPACodex

end

section
set_option autoImplicit false
section

open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

namespace BregmanPPA.Existence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A trimonotone (3-cyclically monotone) operator, in the sense of Brézis–Haraux [5]: for all
`(x₀, y₀), (x₁, y₁), (x₂, y₂)` in the graph of `R`,
`⟪x₁ − x₀, y₀⟫ + ⟪x₂ − x₁, y₁⟫ + ⟪x₀ − x₂, y₂⟫ ≤ 0`. -/
def IsTrimonotone (R : H → Set H) : Prop :=
  ∀ x₀ x₁ x₂ y₀ y₁ y₂ : H, y₀ ∈ R x₀ → y₁ ∈ R x₁ → y₂ ∈ R x₂ →
    inner ℝ (x₁ - x₀) y₀ + inner ℝ (x₂ - x₁) y₁ + inner ℝ (x₀ - x₂) y₂ ≤ 0

/-- Definition 2 (p. 208): a monotone operator `R` has the L-property if, for all `u ∈ dom R`
and `v ∈ im R`, `inf {⟪x − u, y − v⟫ | x ∈ dom R, y ∈ R x} > −∞`. -/
def HasLProperty (R : H → Set H) : Prop :=
  IsMonotoneOp R ∧ ∀ u ∈ dom R, ∀ v ∈ imOp R,
    BddBelow {t : ℝ | ∃ x y, y ∈ R x ∧ t = inner ℝ (x - u) (y - v)}

end BregmanPPA.Existence

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open scoped Pointwise
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

/-- A lower bound on graph pairings gives norm approximation by graph outputs. -/
theorem range_closure_of_pairing_bound (C : H → Set H) (hC : IsMaximalMonotone C)
    (r u : H) (M : ℝ)
    (hb : ∀ x y : H, y ∈ C x → M ≤ inner ℝ (x-u) (y-r)) :
    r ∈ closure (imOp C) := by
  apply Metric.mem_closure_iff.mpr
  intro δ hδ
  let K : ℝ := ‖u‖^2 + 2*|M| + 1
  have hK : 0 < K := by dsimp [K]; positivity
  let t : ℝ := min 1 (δ^2/(2*K))
  have ht : 0 < t := lt_min one_pos (div_pos (sq_pos_of_pos hδ) (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have hsmall : t*K ≤ δ^2/2 := by
    have h := min_le_right (1 : ℝ) (δ^2/(2*K))
    change t ≤ δ^2/(2*K) at h
    have := (le_div_iff₀ (show 0 < 2*K by positivity)).mp h
    linarith
  obtain ⟨x,y,hy,he⟩ := gdr_minty_core C hC t⁻¹ (inv_pos.mpr ht) (t⁻¹ • r)
  have hr : r = t • x + y := by
    have := congrArg (fun z : H => t • z) he
    simpa only [smul_add,smul_smul,mul_inv_cancel₀ ht.ne',one_smul] using this
  have hv : r-y = t • x := by rw [hr]; abel
  have hpair := hb x y hy
  have hh : ‖t • x‖^2 ≤ t * inner ℝ u (t • x) - t*M := by
    rw [show y-r = -(t • x) by rw [← hv]; abel] at hpair
    simp only [inner_neg_right,inner_smul_right,inner_sub_left,
      real_inner_self_eq_norm_sq] at hpair
    have hh := mul_le_mul_of_nonneg_left hpair ht.le
    rw [norm_smul,Real.norm_of_nonneg ht.le]
    simp only [inner_smul_right]
    nlinarith
  have hcs : inner ℝ u (t • x) ≤ ‖u‖*‖t • x‖ := real_inner_le_norm _ _
  have hM : -M ≤ |M| := neg_le_abs M
  have hq : ‖t • x‖^2 ≤ t^2*‖u‖^2 + 2*t*|M| := by
    nlinarith [sq_nonneg (‖t • x‖-t*‖u‖)]
  have hq2 : ‖t • x‖^2 < δ^2 := by
    have hpow : t^2 ≤ t := by nlinarith
    have hu := mul_le_mul_of_nonneg_right hpow (sq_nonneg ‖u‖)
    dsimp [K] at hsmall
    nlinarith
  refine ⟨y, ⟨x,hy⟩, ?_⟩
  rw [dist_eq_norm,hv]
  nlinarith [norm_nonneg (t • x)]

/-- The original L-property supplies the pairing bound for every sum of range points. -/
theorem sum_ranges_subset_closure (A B : H → Set H)
    (hA : IsMonotoneOp A) (ha : dom A ⊆ dom B)
    (hC : IsMaximalMonotone (opAdd A B))
    (hB : BregmanPPA.Existence.HasLProperty B) :
    imOp A + imOp B ⊆ closure (imOp (opAdd A B)) := by
  intro r hr
  obtain ⟨a,ha',b,hb',rfl⟩ := Set.mem_add.mp hr
  obtain ⟨u,hu⟩ := ha'
  have huB : u ∈ dom B := ha ⟨a,hu⟩
  obtain ⟨M,hM⟩ := hB.2 u huB b hb'
  apply range_closure_of_pairing_bound (opAdd A B) hC (a+b) u M
  intro x y hy
  obtain ⟨a',ha',b',hb',rfl⟩ := hy
  have hm := hA x u a' a ha' hu
  have hl := hM (show inner ℝ (x-u) (b'-b) ∈
      {t : ℝ | ∃ x y, y ∈ B x ∧ t = inner ℝ (x-u) (y-b)} from
        ⟨x,b',hb',rfl⟩)
  have he : inner ℝ (x-u) (a'+b'-(a+b)) =
      inner ℝ (x-u) (a'-a) + inner ℝ (x-u) (b'-b) := by
    rw [show a'+b'-(a+b) = (a'-a)+(b'-b) by abel,inner_add_right]
  rw [he]; linarith

/-- The full closure equality from the original range milestone. -/
theorem range_closure_equality (A B : H → Set H)
    (hA : IsMonotoneOp A) (ha : dom A ⊆ dom B)
    (hC : IsMaximalMonotone (opAdd A B))
    (hB : BregmanPPA.Existence.HasLProperty B) :
    closure (imOp (opAdd A B)) = closure (imOp A + imOp B) := by
  apply Set.Subset.antisymm
  · apply closure_mono
    intro y hy
    obtain ⟨x,a,ha',b,hb',rfl⟩ := hy
    exact Set.mem_add.mpr ⟨a,⟨x,ha'⟩,b,⟨x,hb'⟩,rfl⟩
  · exact closure_minimal (sum_ranges_subset_closure A B hA ha hC hB) isClosed_closure
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR Filter Topology Finset
open scoped Pointwise
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem norm_le_basis_pairings {I : Type*} [Fintype I]
    (e : OrthonormalBasis I ℝ H) (x : H) :
    ‖x‖ ≤ ∑ i, |inner ℝ x (e i)| := by
  classical
  calc
    ‖x‖ = ‖∑ i, inner ℝ (e i) x • e i‖ := congrArg norm (e.sum_repr' x).symm
    _ ≤ ∑ i, ‖inner ℝ (e i) x • e i‖ := norm_sum_le _ _
    _ = ∑ i, |inner ℝ x (e i)| := by
      apply sum_congr rfl; intro i _
      rw [norm_smul,Real.norm_eq_abs,e.norm_eq_one,mul_one,real_inner_comm]

theorem regularized_direction_bound (C : H → Set H) (r u x y e : H)
    (s t M : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (he : ‖e‖ = 1)
    (hy : y ∈ C x) (hr : r = t • x+y)
    (hb : ∀ z w : H, w ∈ C z → M ≤ inner ℝ (z-u) (w-(r+s • e))) :
    s*inner ℝ x e ≤ s*‖u‖ + t*‖u‖*‖x‖ + |M| := by
  have h := hb x y hy
  have hvec : y-(r+s • e) = -(t • x)-s • e := by rw [hr]; module
  rw [hvec,inner_sub_right,inner_neg_right,inner_smul_right,inner_smul_right,
    inner_sub_left,inner_sub_left,real_inner_self_eq_norm_sq] at h
  have hu := real_inner_le_norm u x
  have hue := real_inner_le_norm u e
  rw [he,mul_one] at hue
  have hn := mul_nonneg ht (sq_nonneg ‖x‖)
  have htU := mul_le_mul_of_nonneg_left hu ht
  have hsU := mul_le_mul_of_nonneg_left hue hs
  nlinarith [neg_le_abs M]

theorem regularized_basis_bound {I : Type*} [Fintype I]
    (e : OrthonormalBasis I ℝ H) (C : H → Set H) (r x y : H)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hy : y ∈ C x) (hr : r=t • x+y)
    (uP uN : I → H) (mP mN : I → ℝ)
    (hP : ∀ i z w, w ∈ C z → mP i ≤ inner ℝ (z-uP i) (w-(r+s • e i)))
    (hN : ∀ i z w, w ∈ C z → mN i ≤ inner ℝ (z-uN i) (w-(r-s • e i))) :
    s*‖x‖ ≤ (∑ i, (s*(‖uP i‖+‖uN i‖)+|mP i|+|mN i|)) +
      t*(∑ i, (‖uP i‖+‖uN i‖))*‖x‖ := by
  classical
  have hb (i : I) : s*|inner ℝ x (e i)| ≤
      s*(‖uP i‖+‖uN i‖)+|mP i|+|mN i|+t*(‖uP i‖+‖uN i‖)*‖x‖ := by
    have hp := regularized_direction_bound C r (uP i) x y (e i) s t (mP i)
      hs ht (e.norm_eq_one i) hy hr (hP i)
    have hn := regularized_direction_bound C r (uN i) x y (-e i) s t (mN i)
      hs ht (by rw [norm_neg,e.norm_eq_one]) hy hr (by simpa only [smul_neg,sub_eq_add_neg] using hN i)
    rw [inner_neg_right] at hn
    have hnP : 0 ≤ s*‖uP i‖+t*‖uP i‖*‖x‖+|mP i| := by positivity
    have hnN : 0 ≤ s*‖uN i‖+t*‖uN i‖*‖x‖+|mN i| := by positivity
    have habs : s*|inner ℝ x (e i)| = |s*inner ℝ x (e i)| := by
      rw [abs_mul,abs_of_nonneg hs]
    rw [habs]
    apply abs_le.mpr
    constructor <;> nlinarith
  calc
    s*‖x‖ ≤ s*(∑ i, |inner ℝ x (e i)|) :=
      mul_le_mul_of_nonneg_left (norm_le_basis_pairings e x) hs
    _ = ∑ i, s*|inner ℝ x (e i)| := mul_sum _ _ _
    _ ≤ ∑ i, (s*(‖uP i‖+‖uN i‖)+|mP i|+|mN i|+t*(‖uP i‖+‖uN i‖)*‖x‖) := sum_le_sum fun i _ => hb i
    _ = _ := by simp only [sum_add_distrib,sum_mul,mul_sum,mul_add,add_mul]
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR Filter Topology Finset
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem mem_range_of_ball_pairing_bounds (C : H → Set H) (hC : IsMaximalMonotone C)
    (r : H) (δ : ℝ) (hδ : 0 < δ)
    (hb : ∀ v ∈ Metric.ball r δ, ∃ u : H, ∃ M : ℝ,
      ∀ x y : H, y ∈ C x → M ≤ inner ℝ (x-u) (y-v)) : r ∈ imOp C := by
  classical
  let e := stdOrthonormalBasis ℝ H
  let s : ℝ := δ/2
  have hs : 0 < s := by dsimp [s]; positivity
  have hp (i : Fin (Module.finrank ℝ H)) : r+s • e i ∈ Metric.ball r δ := by
    rw [Metric.mem_ball,dist_eq_norm,show r+s • e i-r=s • e i by abel,
      norm_smul,Real.norm_of_nonneg hs.le,e.norm_eq_one,mul_one]
    dsimp [s]; linarith
  have hn (i : Fin (Module.finrank ℝ H)) : r-s • e i ∈ Metric.ball r δ := by
    rw [Metric.mem_ball,dist_eq_norm,show r-s • e i-r=-(s • e i) by abel,
      norm_neg,norm_smul,Real.norm_of_nonneg hs.le,e.norm_eq_one,mul_one]
    dsimp [s]; linarith
  choose uP mP hP using fun i => hb (r+s • e i) (hp i)
  choose uN mN hN using fun i => hb (r-s • e i) (hn i)
  let U : ℝ := ∑ i, (‖uP i‖+‖uN i‖)
  let K : ℝ := ∑ i, (s*(‖uP i‖+‖uN i‖)+|mP i|+|mN i|)
  have hU : 0 ≤ U := sum_nonneg fun i _ => by positivity
  have hK : 0 ≤ K := sum_nonneg fun i _ => by positivity
  let a : ℝ := s/(2*(U+1))
  have ha : 0 < a := div_pos hs (by positivity)
  have haU : a*U ≤ s/2 := by
    dsimp [a]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < 2*(U+1) by positivity)).mpr
    nlinarith
  let t : ℕ → ℝ := fun n => a/(n+1 : ℝ)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have hta (n : ℕ) : t n ≤ a := by
    dsimp [t]; apply (div_le_iff₀ (by positivity : 0 < (n+1 : ℝ))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have htu (n : ℕ) : t n*U ≤ s/2 :=
    (mul_le_mul_of_nonneg_right (hta n) hU).trans haU
  have htz : Tendsto t atTop (𝓝 0) := by
    simpa [t,div_eq_mul_inv] using
      (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => a*(1/(n+1 : ℝ))) atTop (𝓝 (a*0)))
  choose x y hym hem using fun n =>
    gdr_minty_core C hC (t n)⁻¹ (inv_pos.mpr (ht n)) ((t n)⁻¹ • r)
  have hr (n : ℕ) : r=t n • x n+y n := by
    have hh := congrArg (fun z : H => t n • z) (hem n)
    simpa only [smul_add,smul_smul,mul_inv_cancel₀ (ht n).ne',one_smul] using hh
  have hxb (n : ℕ) : ‖x n‖ ≤ 2*K/s := by
    have h := regularized_basis_bound e C r (x n) (y n) s (t n) hs.le (ht n).le
      (hym n) (hr n) uP uN mP mN hP hN
    change s*‖x n‖ ≤ K+t n*U*‖x n‖ at h
    have hu := mul_le_mul_of_nonneg_right (htu n) (norm_nonneg (x n))
    apply (le_div_iff₀ hs).mpr
    nlinarith
  have hbounded : Bornology.IsBounded (Set.range x) := by
    apply isBounded_iff_forall_norm_le.mpr
    exact ⟨2*K/s,fun z hz => by obtain ⟨n,rfl⟩ := hz; exact hxb n⟩
  obtain ⟨p,_,φ,hφ,hlim⟩ := tendsto_subseq_of_bounded hbounded (fun n => Set.mem_range_self n)
  have hprod : Tendsto (fun n => t (φ n) • x (φ n)) atTop (𝓝 (0 : H)) := by
    simpa using (htz.comp hφ.tendsto_atTop).smul hlim
  have hy : Tendsto (fun n => y (φ n)) atTop (𝓝 r) := by
    have hh : y = fun n => r-t n • x n := by funext n; rw [hr n]; abel
    rw [hh]
    simpa using tendsto_const_nhds.sub hprod
  exact ⟨p,BregmanPPACodex.maximal_graph_limit C hC (x ∘ φ) (y ∘ φ) p r
    hlim hy (fun n => hym (φ n))⟩
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open scoped Pointwise
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem sum_range_pairing_bound (A B : H → Set H)
    (hA : IsMonotoneOp A) (ha : dom A ⊆ dom B)
    (hB : BregmanPPA.Existence.HasLProperty B) (r : H) (hr : r ∈ imOp A+imOp B) :
    ∃ u : H, ∃ M : ℝ, ∀ x y : H, y ∈ opAdd A B x → M ≤ inner ℝ (x-u) (y-r) := by
  obtain ⟨a,ha',b,hb',rfl⟩ := Set.mem_add.mp hr
  obtain ⟨u,hu⟩ := ha'
  obtain ⟨M,hM⟩ := hB.2 u (ha ⟨a,hu⟩) b hb'
  refine ⟨u,M,?_⟩
  intro x y hy
  obtain ⟨a',ha',b',hb',rfl⟩ := hy
  have hm := hA x u a' a ha' hu
  have hl := hM (show inner ℝ (x-u) (b'-b) ∈
      {t : ℝ | ∃ x y, y ∈ B x ∧ t = inner ℝ (x-u) (y-b)} from ⟨x,b',hb',rfl⟩)
  rw [show a'+b'-(a+b) = (a'-a)+(b'-b) by abel,inner_add_right]
  linarith

theorem range_interior_equality (A B : H → Set H)
    (hA : IsMonotoneOp A) (ha : dom A ⊆ dom B)
    (hC : IsMaximalMonotone (opAdd A B))
    (hB : BregmanPPA.Existence.HasLProperty B) :
    interior (imOp (opAdd A B)) = interior (imOp A+imOp B) := by
  have hsum : imOp (opAdd A B) ⊆ imOp A+imOp B := by
    intro y hy
    obtain ⟨x,a,ha',b,hb',rfl⟩ := hy
    exact Set.mem_add.mpr ⟨a,⟨x,ha'⟩,b,⟨x,hb'⟩,rfl⟩
  have hi : interior (imOp A+imOp B) ⊆ imOp (opAdd A B) := by
    intro r hr
    obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hr)
    exact mem_range_of_ball_pairing_bounds (opAdd A B) hC r δ hδ
      (fun v hv => sum_range_pairing_bound A B hA ha hB v (hball hv))
  exact Set.Subset.antisymm (interior_mono hsum) (interior_maximal hi isOpen_interior)
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR InertialFB.IFB
namespace BregmanExistenceCodex
open BregmanPPA.Existence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem trimonotone_monotone (R : H → Set H) (hR : IsTrimonotone R) :
    IsMonotoneOp R := by
  intro x z y w hy hw
  have hc := hR x z x y w y hy hw hy
  simp only [sub_self, inner_zero_left, add_zero] at hc
  simp only [inner_sub_left] at hc
  simp only [inner_sub_left, inner_sub_right]
  linarith

theorem trimonotone_lproperty (R : H → Set H) (hR : IsTrimonotone R) :
    HasLProperty R := by
  refine ⟨trimonotone_monotone R hR, ?_⟩
  intro u hu v hv
  obtain ⟨a, ha⟩ := hu
  obtain ⟨q, hq⟩ := hv
  refine ⟨inner ℝ (q-u) a + inner ℝ (u-q) v, ?_⟩
  intro t ht
  obtain ⟨x,y,hy,rfl⟩ := ht
  have hc := hR x u q y a v hy ha hq
  simp only [inner_sub_left, inner_sub_right] at hc ⊢
  linarith

theorem subdiff_trimonotone (f : H → EReal) (hp : IsProperFn f) :
    IsTrimonotone (BregmanPPA.Convergence.subdiffOp f) := by
  intro x₀ x₁ x₂ y₀ y₁ y₂ h₀ h₁ h₂
  have h01 := BregmanPPACodex.subgradient_real_comparison f hp h₀ h₁.1
  have h12 := BregmanPPACodex.subgradient_real_comparison f hp h₁ h₂.1
  have h20 := BregmanPPACodex.subgradient_real_comparison f hp h₂ h₀.1
  rw [real_inner_comm] at h01 h12 h20
  linarith
end BregmanExistenceCodex

end

section
set_option autoImplicit false
namespace BregmanExistenceCodex
open BregmanPPA.Existence BregmanPPA.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem gradient_trimonotone (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h) :
    IsTrimonotone (gradOp S h) := by
  intro x₀ x₁ x₂ y₀ y₁ y₂ h₀ h₁ h₂
  obtain ⟨hx₀,rfl⟩ := h₀
  obtain ⟨hx₁,rfl⟩ := h₁
  obtain ⟨hx₂,rfl⟩ := h₂
  have h01 := BregmanPPACodex.gradient_support S h hh hx₀ (subset_closure hx₁)
  have h12 := BregmanPPACodex.gradient_support S h hh hx₁ (subset_closure hx₂)
  have h20 := BregmanPPACodex.gradient_support S h hh hx₂ (subset_closure hx₀)
  rw [real_inner_comm] at h01 h12 h20
  linarith

theorem gradient_lproperty (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h) :
    HasLProperty (gradOp S h) :=
  trimonotone_lproperty _ (gradient_trimonotone S h hh)
end BregmanExistenceCodex

end


end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

/-- The inverse of A+dI is a continuous monotone field, directly from the original Minty graph. -/
theorem inverse_field_exists (A : H → Set H) (hA : IsMaximalMonotone A)
    (d : ℝ) (hd : 0 < d) :
    ∃ J : H → H, Continuous J ∧ (∀ v, v-d • J v ∈ A (J v)) ∧
      (∀ v w, d*‖J v-J w‖^2 ≤ inner ℝ (J v-J w) (v-w)) := by
  classical
  choose J a ha he using fun v : H => gdr_minty_core A hA d⁻¹ (inv_pos.mpr hd) (d⁻¹ • v)
  have hmem (v : H) : v-d • J v ∈ A (J v) := by
    have hv := congrArg (fun z : H => d • z) (he v)
    simp only [smul_add,smul_smul,mul_inv_cancel₀ hd.ne',one_smul] at hv
    have heq : v-d • J v=a v := by
      calc
        v-d • J v=(d • J v+a v)-d • J v := congrArg (fun z => z-d • J v) hv
        _=a v := by abel
    rw [heq]; exact ha v
  have hstrong (v w : H) : d*‖J v-J w‖^2 ≤ inner ℝ (J v-J w) (v-w) := by
    have h := hA.1 (J v) (J w) (v-d • J v) (w-d • J w) (hmem v) (hmem w)
    have hv : (v-d • J v)-(w-d • J w)=(v-w)-d • (J v-J w) := by module
    rw [hv,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq] at h
    linarith
  have hlip : LipschitzWith (Real.toNNReal d⁻¹) J := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [dist_eq_norm,dist_eq_norm,Real.coe_toNNReal _ (inv_nonneg.mpr hd.le)]
    have h := hstrong v w
    have hc := real_inner_le_norm (J v-J w) (v-w)
    by_cases hn : ‖J v-J w‖=0
    · rw [hn]; positivity
    have hp : 0 < ‖J v-J w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    have hb : d*‖J v-J w‖ ≤ ‖v-w‖ := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hd.le)
    simpa only [← mul_assoc,inv_mul_cancel₀ hd.ne',one_mul] using hh
  exact ⟨J,hlip.continuous,hmem,hstrong⟩
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem inverse_pairing_lower (B : H → Set H) (hB : IsMonotoneOp B)
    (J : H → H) (d R δ K : ℝ) (hd : 0 ≤ d) (hR : 0 ≤ R) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hmem : ∀ v, v-d • J v ∈ B (J v)) (hbound : ∀ x y, y ∈ B x → ‖x‖ ≤ R)
    (hlocal : ∀ x ∈ Metric.ball (0 : H) δ, ∃ b ∈ B x, ‖b‖ ≤ K)
    (v : H) (hv : 0 < ‖v‖) :
    (δ/2)*‖v‖-d*(δ/2)*R-(R+δ/2)*K ≤ inner ℝ (J v) v := by
  let z : H := ((δ/2)/‖v‖) • v
  have hz : ‖z‖=δ/2 := by
    rw [norm_smul,Real.norm_of_nonneg (div_nonneg (by positivity) hv.le),div_mul_cancel₀ (δ / 2) hv.ne']
  have hzB : z ∈ Metric.ball (0 : H) δ := by
    rw [Metric.mem_ball,dist_zero_right,hz]; linarith
  obtain ⟨b,hb,hbK⟩ := hlocal z hzB
  have hJ := hbound (J v) (v-d • J v) (hmem v)
  have hp := hB (J v) z (v-d • J v) b (hmem v) hb
  have hzv : inner ℝ z v=(δ/2)*‖v‖ := by
    dsimp [z]; rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
    field_simp [hv.ne']
  have he : inner ℝ (J v-z) ((v-d • J v)-b) =
      inner ℝ (J v) v-inner ℝ z v-d*‖J v‖^2+d*inner ℝ z (J v)-
      inner ℝ (J v) b+inner ℝ z b := by
    simp only [inner_sub_left,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq]
    ring
  rw [he,hzv] at hp
  have h1 := real_inner_le_norm z (J v)
  have h2 := real_inner_le_norm (-J v) b
  have h3 := real_inner_le_norm z b
  rw [hz] at h1 h3
  rw [inner_neg_left,norm_neg] at h2
  have hd1 := mul_le_mul_of_nonneg_left h1 hd
  have hdR := mul_le_mul_of_nonneg_left hJ (show 0 ≤ d*(δ/2) by positivity)
  have hRK := mul_le_mul hJ hbK (norm_nonneg b) hR
  have hδK := mul_le_mul_of_nonneg_left hbK (show 0 ≤ δ/2 by positivity)
  nlinarith [mul_nonneg hd (sq_nonneg ‖J v‖)]
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open Filter Topology Finset
namespace MartinetVICodex

/-- A finite bilinear minimax criterion, applied below to original monotone operators.
The Sion interface follows the repository's Hart-Schmeidler minimax pattern. -/
theorem finite_minimax_criterion {I : Type*} [Fintype I] [Nonempty I]
    (A : I → I → ℝ)
    (hA : ∀ p ∈ stdSimplex ℝ I, 0 ≤ ∑ i, ∑ j, p i*p j*A i j) :
    ∃ q ∈ stdSimplex ℝ I, ∀ p ∈ stdSimplex ℝ I,
      0 ≤ ∑ i, ∑ j, p i*q j*A i j := by
  classical
  let f : (I → ℝ) → (I → ℝ) → ℝ := fun p q => ∑ i, ∑ j, p i*q j*A i j
  have hc1 (q : I → ℝ) : Continuous (fun p => f p q) := by dsimp [f]; fun_prop
  have hc2 (p : I → ℝ) : Continuous (fun q => f p q) := by dsimp [f]; fun_prop
  have hl1 (q p p' : I → ℝ) (a b : ℝ) :
      f (a • p+b • p') q = a*f p q+b*f p' q := by
    simp only [f,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_sum,← sum_add_distrib]
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring
  have hl2 (p q q' : I → ℝ) (a b : ℝ) :
      f p (a • q+b • q') = a*f p q+b*f p q' := by
    simp only [f,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_sum,← sum_add_distrib]
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring
  have hconv (q : I → ℝ) : ConvexOn ℝ (stdSimplex ℝ I) (fun p => f p q) := by
    refine ⟨convex_stdSimplex ℝ I, ?_⟩
    intro p _ p' _ a b _ _ _
    change f (a • p+b • p') q ≤ a*f p q+b*f p' q
    rw [hl1]
  have hconc (p : I → ℝ) : ConcaveOn ℝ (stdSimplex ℝ I) (fun q => f p q) := by
    refine ⟨convex_stdSimplex ℝ I, ?_⟩
    intro q _ q' _ a b _ _ _
    change a*f p q+b*f p q' ≤ f p (a • q+b • q')
    rw [hl2]
  have hne : (stdSimplex ℝ I).Nonempty :=
    ⟨Pi.single (Classical.arbitrary I) 1,single_mem_stdSimplex ℝ _⟩
  obtain ⟨p,hp,q,hq,hs⟩ := Sion.exists_isSaddlePointOn (X := stdSimplex ℝ I)
    (Y := stdSimplex ℝ I) (f := f) hne (convex_stdSimplex ℝ I)
    (isCompact_stdSimplex ℝ I)
    (fun q _ => (hc1 q).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun q _ => (hconv q).quasiconvexOn)
    (convex_stdSimplex ℝ I) hne (isCompact_stdSimplex ℝ I)
    (fun p _ => (hc2 p).upperSemicontinuous.upperSemicontinuousOn _)
    (fun p _ => (hconc p).quasiconcaveOn)
  exact ⟨q,hq,fun p' hp' => (hA p hp).trans (hs p' hp' p hp)⟩

/-- Pairwise nonnegative symmetric sums supply the finite minimax premise. -/
theorem matrix_simplex_nonneg {I : Type*} [Fintype I] (A : I → I → ℝ)
    (hA : ∀ i j, 0 ≤ A i j+A j i) (p : I → ℝ) (hp : p ∈ stdSimplex ℝ I) :
    0 ≤ ∑ i, ∑ j, p i*p j*A i j := by
  classical
  have ht : (∑ i, ∑ j, p i*p j*A j i) = ∑ i, ∑ j, p i*p j*A i j := by
    rw [sum_comm]; apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _; ring
  have hn : 0 ≤ ∑ i, ∑ j, p i*p j*(A i j+A j i) :=
    sum_nonneg fun i _ => sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hp.1 i) (hp.1 j)) (hA i j)
  have he : (∑ i, ∑ j, p i*p j*(A i j+A j i)) =
      (∑ i, ∑ j, p i*p j*A i j)+(∑ i, ∑ j, p i*p j*A j i) := by
    simp only [mul_add,sum_add_distrib]
  rw [he,ht] at hn; linarith
end MartinetVICodex

end

section
set_option autoImplicit false
open Set Filter Topology Finset
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem finite_primal_minty {I : Type*} [Fintype I] [Nonempty I]
    (F : H → H) (C : Set H) (hC : Convex ℝ C)
    (hm : ∀ x ∈ C, ∀ y ∈ C, 0 ≤ inner ℝ (x-y) (F x-F y))
    (y : I → H) (hy : ∀ i, y i ∈ C) :
    ∃ u ∈ C, ∀ i, 0 ≤ inner ℝ (F (y i)) (y i-u) := by
  classical
  let A : I → I → ℝ := fun i j => inner ℝ (F (y i)) (y i-y j)
  have hA (i j : I) : 0 ≤ A i j+A j i := by
    have h := hm (y i) (hy i) (y j) (hy j)
    have he : inner ℝ (F (y j)) (y j-y i) = -inner ℝ (F (y j)) (y i-y j) := by
      rw [← neg_sub (y i) (y j),inner_neg_right]
    dsimp [A]; rw [he]
    rw [real_inner_comm,inner_sub_left] at h
    simpa only [sub_eq_add_neg] using h
  obtain ⟨q,hq,hqs⟩ := MartinetVICodex.finite_minimax_criterion A
    (fun p hp => MartinetVICodex.matrix_simplex_nonneg A hA p hp)
  let u := ∑ j, q j • y j
  have hu : u ∈ C := hC.sum_mem (fun i _ => hq.1 i) hq.2 (fun i _ => hy i)
  refine ⟨u,hu,fun i => ?_⟩
  have hi : 0 ≤ ∑ j, q j*A i j := by
    simpa [Pi.single_apply] using hqs (Pi.single i 1) (single_mem_stdSimplex ℝ i)
  have he : inner ℝ (F (y i)) (y i-u) = ∑ j, q j*A i j := by
    simp only [u,A,inner_sub_right,inner_sum,inner_smul_right,mul_sub,sum_sub_distrib,
      ← sum_mul,hq.2,one_mul]
  rw [he]; exact hi

theorem compact_primal_vi (F : H → H) (C : Set H) (hc : IsCompact C)
    (hcv : Convex ℝ C) (hne : C.Nonempty) (hf : ContinuousOn F C)
    (hm : ∀ x ∈ C, ∀ y ∈ C, 0 ≤ inner ℝ (x-y) (F x-F y)) :
    ∃ u ∈ C, ∀ y ∈ C, 0 ≤ inner ℝ (F u) (y-u) := by
  classical
  let K : C → Set H := fun y => {w | 0 ≤ inner ℝ (F y.val) (y.val-w)}
  have hK (y : C) : IsClosed (K y) := by
    apply isClosed_le continuous_const
    fun_prop
  have hfinite (s : Finset C) : (C ∩ ⋂ y ∈ s, K y).Nonempty := by
    by_cases hs : s.Nonempty
    · let : Nonempty ↑s := ⟨⟨hs.choose,hs.choose_spec⟩⟩
      obtain ⟨u,hu,hus⟩ := finite_primal_minty F C hcv hm (fun i : s => i.val.val)
        (fun i => i.val.property)
      refine ⟨u,hu,?_⟩
      simp only [mem_iInter]
      intro y hy
      exact hus ⟨y,hy⟩
    · obtain ⟨u,hu⟩ := hne
      have hs0 : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      simp only [hs0,Finset.notMem_empty,iInter_of_empty,iInter_univ,inter_univ]
      exact ⟨u,hu⟩
  obtain ⟨u,hu,hKu⟩ := hc.inter_iInter_nonempty K hK hfinite
  have hminty (y : H) (hy : y ∈ C) : 0 ≤ inner ℝ (F y) (y-u) :=
    mem_iInter.mp hKu ⟨y,hy⟩
  refine ⟨u,hu,?_⟩
  intro y hy
  let a : ℕ → ℝ := fun n => 1/(n+1 : ℝ)
  have ha (n : ℕ) : 0 < a n ∧ a n ≤ 1 := by
    dsimp [a]; constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < (n+1 : ℝ))).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]
  let z : ℕ → H := fun n => (1-a n) • u+a n • y
  have hz (n : ℕ) : z n ∈ C := hcv hu hy (by linarith [(ha n).2]) (ha n).1.le (by ring)
  have hlim : Tendsto z atTop (𝓝 u) := by
    have haz : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [z] using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub haz).smul_const u |>.add (haz.smul_const y)
  have hzlim : Tendsto z atTop (𝓝[C] u) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim,Eventually.of_forall hz⟩
  have hFlim := (hf u hu).tendsto.comp hzlim
  have hp (n : ℕ) : 0 ≤ inner ℝ (F (z n)) (y-u) := by
    have h := hminty (z n) (hz n)
    have he : z n-u=a n • (y-u) := by dsimp [z]; module
    rw [he,inner_smul_right] at h
    exact nonneg_of_mul_nonneg_right h (ha n).1
  exact (isClosed_Ici : IsClosed (Ici (0 : ℝ))).mem_of_tendsto
    (hFlim.inner tendsto_const_nhds) (Eventually.of_forall hp)
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR Filter Topology
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

/-- Normal vectors to the closed ball, represented as a local helper operator. -/
def normal_ball (R : ℝ) : H → Set H := fun x =>
  {n | x ∈ Metric.closedBall (0 : H) R ∧ ∀ z ∈ Metric.closedBall (0 : H) R,
    inner ℝ (z-x) n ≤ 0}

theorem normal_ball_monotone (R : ℝ) : IsMonotoneOp (normal_ball (H := H) R) := by
  intro x y u v hu hv
  have h1 := hu.2 y hv.1
  have h2 := hv.2 x hu.1
  rw [← neg_sub x y,inner_neg_left] at h1
  rw [inner_sub_right]
  linarith

theorem normal_ball_zero_mem (R : ℝ) {x : H} (hx : x ∈ Metric.closedBall (0 : H) R) :
    (0 : H) ∈ normal_ball R x := ⟨hx,fun _ _ => by simp⟩

theorem normal_ball_interior_zero (R : ℝ) {x n : H}
    (hx : x ∈ Metric.ball (0 : H) R) (hn : n ∈ normal_ball R x) : n=0 := by
  have hmax : IsLocalMax (fun z : H => inner ℝ n (z-x)) x := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    have h := hn.2 z (Metric.ball_subset_closedBall hz)
    rw [real_inner_comm] at h
    simpa only [sub_self,inner_zero_right] using h
  have hl : HasFDerivAt (fun z : H => inner ℝ n (z-x)) ((InnerProductSpace.toDual ℝ H) n) x := by
    simpa only [inner_sub_right,InnerProductSpace.toDual_apply_apply] using
      (((InnerProductSpace.toDual ℝ H) n).hasFDerivAt.sub_const (inner ℝ n x))
  have he := hmax.hasFDerivAt_eq_zero hl
  apply (InnerProductSpace.toDual ℝ H).injective
  simpa using he

/-- Maximality of all sufficiently large normal-ball cutoffs implies original maximality. -/
theorem maximal_of_normal_ball_sums (A : H → Set H) (hA : IsMonotoneOp A)
    (R₀ : ℝ) (hmax : ∀ R : ℝ, R₀ < R → IsMaximalMonotone (opAdd A (normal_ball R))) :
    IsMaximalMonotone A := by
  refine ⟨hA,?_⟩
  intro A' hA' hsub
  funext x
  ext g
  constructor
  · intro hg
    let R : ℝ := |R₀|+‖x‖+1
    have hR : R₀ < R := by dsimp [R]; nlinarith [le_abs_self R₀,norm_nonneg x]
    have hx : x ∈ Metric.ball (0 : H) R := by
      rw [Metric.mem_ball,dist_zero_right]
      dsimp [R]; nlinarith [abs_nonneg R₀]
    have hsum : g ∈ opAdd A (normal_ball R) x := by
      apply BregmanPPACodex.maximal_related_point _ (hmax R hR) x g
      intro y w hw
      obtain ⟨a,ha,n,hn,rfl⟩ := hw
      have hp := hA' x y g a hg (hsub y ha)
      have hn' := normal_ball_monotone R x y 0 n
        (normal_ball_zero_mem R (Metric.ball_subset_closedBall hx)) hn
      simp only [zero_sub,inner_neg_right] at hn'
      rw [show g-(a+n)=(g-a)-n by abel,inner_sub_right]
      linarith
    obtain ⟨a,ha,n,hn,he⟩ := hsum
    have hn0 := normal_ball_interior_zero R hx hn
    rw [hn0,add_zero] at he
    exact he.symm ▸ ha
  · intro hg; exact hsub x hg
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

/-- A continuous monotone field pointing strictly outward on a sphere has a zero inside it. -/
theorem zero_of_outward_sphere (F : H → H) (hf : Continuous F)
    (hm : ∀ x y : H, 0 ≤ inner ℝ (x-y) (F x-F y)) (R : ℝ) (hR : 0 < R)
    (hout : ∀ x : H, ‖x‖=R → 0 < inner ℝ (F x) x) :
    ∃ x ∈ Metric.ball (0 : H) R, F x=0 := by
  have h0 : (0 : H) ∈ Metric.closedBall (0 : H) R := by
    simp only [Metric.mem_closedBall,dist_self]; exact hR.le
  obtain ⟨x,hx,hvi⟩ := compact_primal_vi F (Metric.closedBall (0 : H) R)
    (isCompact_closedBall 0 R) (convex_closedBall 0 R) ⟨0,h0⟩ hf.continuousOn
    (fun x _ y _ => hm x y)
  have hp : inner ℝ (F x) x ≤ 0 := by
    have h := hvi 0 h0
    simp only [zero_sub,inner_neg_right] at h
    linarith
  have hne : ‖x‖ ≠ R := fun he => (not_lt_of_ge hp) (hout x he)
  have hle : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
  have hxb : x ∈ Metric.ball (0 : H) R := by
    rw [Metric.mem_ball,dist_zero_right]
    exact lt_of_le_of_ne hle hne
  have hn : -F x ∈ normal_ball R x := by
    refine ⟨hx,?_⟩
    intro z hz
    have h := hvi z hz
    rw [inner_neg_right,real_inner_comm]
    linarith
  exact ⟨x,hxb,neg_eq_zero.mp (normal_ball_interior_zero R hxb hn)⟩
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

/-- The centered bounded-domain sum has a regularized zero. -/
theorem centered_sum_regularized_zero (A B : H → Set H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B) (hA0 : (0 : H) ∈ A 0)
    (R δ K : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hbound : ∀ x b, b ∈ B x → ‖x‖ ≤ R)
    (hlocal : ∀ x ∈ Metric.ball (0 : H) δ, ∃ b ∈ B x, ‖b‖ ≤ K) :
    ∃ x a b : H, a ∈ A x ∧ b ∈ B x ∧ x+a+b=0 := by
  let d : ℝ := 1/2
  have hd : 0 < d := by norm_num [d]
  obtain ⟨JA,hJA,hAm,hAs⟩ := inverse_field_exists A hA d hd
  obtain ⟨JB,hJB,hBm,hBs⟩ := inverse_field_exists B hB d hd
  let F : H → H := fun v => -JA (-v)+JB v
  have hF : Continuous F := (hJA.comp continuous_neg).neg.add hJB
  have hmono : ∀ v w : H, 0 ≤ inner ℝ (v-w) (F v-F w) := by
    intro v w
    have ha := hAs (-v) (-w)
    have hb := hBs v w
    have heA : inner ℝ (v-w) (-JA (-v)- -JA (-w)) =
        inner ℝ (JA (-v)-JA (-w)) (-v- -w) := by
      rw [show -JA (-v)- -JA (-w)=-(JA (-v)-JA (-w)) by abel,
        show -v- -w=-(v-w) by abel]
      simp only [inner_neg_right,inner_neg_left]
      rw [real_inner_comm]
    have heB : inner ℝ (v-w) (JB v-JB w) = inner ℝ (JB v-JB w) (v-w) := real_inner_comm _ _
    have hmA : 0 ≤ inner ℝ (v-w) (-JA (-v)- -JA (-w)) := by
      rw [heA]; nlinarith [mul_nonneg hd.le (sq_nonneg ‖JA (-v)-JA (-w)‖)]
    have hmB : 0 ≤ inner ℝ (v-w) (JB v-JB w) := by
      rw [heB]; nlinarith [mul_nonneg hd.le (sq_nonneg ‖JB v-JB w‖)]
    have heF : F v-F w=(-JA (-v)- -JA (-w))+(JB v-JB w) := by dsimp [F]; abel
    rw [heF,inner_add_right]; exact add_nonneg hmA hmB
  have hnonneg (v : H) : 0 ≤ inner ℝ (-JA (-v)) v := by
    have h := hA.1 (JA (-v)) 0 (-v-d • JA (-v)) 0 (hAm (-v)) hA0
    simp only [sub_zero,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,
      inner_neg_right] at h
    rw [inner_neg_left]
    nlinarith [mul_nonneg hd.le (sq_nonneg ‖JA (-v)‖)]
  let C : ℝ := d*(δ/2)*R+(R+δ/2)*K
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let L : ℝ := 2*(C+1)/δ
  have hL : 0 < L := div_pos (by positivity) hδ
  have hcalc : (δ/2)*L=C+1 := by dsimp [L]; field_simp
  have hout : ∀ v : H, ‖v‖=L → 0 < inner ℝ (F v) v := by
    intro v hv
    have hb := inverse_pairing_lower B hB.1 JB d R δ K hd.le hR hδ hK hBm hbound hlocal v
      (by rw [hv]; exact hL)
    have ha := hnonneg v
    rw [show (δ/2)*‖v‖-d*(δ/2)*R-(R+δ/2)*K=(δ/2)*‖v‖-C by dsimp [C]; ring] at hb
    rw [hv,hcalc] at hb
    dsimp [F]; rw [inner_add_left]
    linarith
  obtain ⟨v,_,hv⟩ := zero_of_outward_sphere F hF hmono L hL hout
  have heq : JA (-v)=JB v := by
    have hdiff : JB v-JA (-v)=0 := by simpa only [F,sub_eq_add_neg,add_comm] using hv
    exact (sub_eq_zero.mp hdiff).symm
  have ha := hAm (-v)
  rw [heq] at ha
  refine ⟨JB v,-v-d • JB v,v-d • JB v,ha,hBm v,?_⟩
  dsimp [d]; module
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

def shift_operator (A : H → Set H) (p q : H) : H → Set H :=
  fun x => {v | v+q ∈ A (x+p)}

theorem shift_monotone (A : H → Set H) (hA : IsMonotoneOp A) (p q : H) :
    IsMonotoneOp (shift_operator A p q) := by
  intro x y u v hu hv
  have h := hA (x+p) (y+p) (u+q) (v+q) hu hv
  rw [show x+p-(y+p)=x-y by abel,show u+q-(v+q)=u-v by abel] at h
  exact h

theorem shift_maximal (A : H → Set H) (hA : IsMaximalMonotone A) (p q : H) :
    IsMaximalMonotone (shift_operator A p q) := by
  refine ⟨shift_monotone A hA.1 p q,?_⟩
  intro A' hA' hsub
  funext x
  ext g
  constructor
  · intro hg
    apply BregmanPPACodex.maximal_related_point A hA (x+p) (g+q)
    intro y u hu
    have hm : u-q ∈ shift_operator A p q (y-p) := by
      simpa only [shift_operator,Set.mem_setOf_eq,sub_add_cancel] using hu
    have h := hA' x (y-p) g (u-q) hg (hsub _ hm)
    have h1 : x-(y-p)=(x+p)-y := by abel
    have h2 : g-(u-q)=(g+q)-u := by abel
    rwa [h1,h2] at h
  · intro hg; exact hsub x hg

theorem sum_monotone (A B : H → Set H) (hA : IsMonotoneOp A) (hB : IsMonotoneOp B) :
    IsMonotoneOp (opAdd A B) := by
  rintro x y u v ⟨a,ha,b,hb,rfl⟩ ⟨a',ha',b',hb',rfl⟩
  have h1 := hA x y a a' ha ha'
  have h2 := hB x y b b' hb hb'
  rw [show a+b-(a'+b')=(a-a')+(b-b') by abel,inner_add_right]
  exact add_nonneg h1 h2

theorem operator_sum_comm (A B : H → Set H) : opAdd A B=opAdd B A := by
  funext x
  ext w
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩; exact ⟨b,hb,a,ha,add_comm _ _⟩
  · rintro ⟨b,hb,a,ha,rfl⟩; exact ⟨a,ha,b,hb,add_comm _ _⟩
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem bounded_domain_sum_maximal (A B : H → Set H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x b, b ∈ B x → ‖x‖ ≤ R)
    (x₀ a₀ : H) (ha₀ : a₀ ∈ A x₀) (δ K : ℝ) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hlocal : ∀ x ∈ Metric.ball x₀ δ, ∃ b ∈ B x, ‖b‖ ≤ K) :
    IsMaximalMonotone (opAdd A B) := by
  have hm := sum_monotone A B hA.1 hB.1
  apply (gdr_max_iff (opAdd A B) hm 1 one_pos).mpr
  intro w
  let q := w-x₀-a₀
  let A' := shift_operator A x₀ a₀
  let B' := shift_operator B x₀ q
  have hA' : IsMaximalMonotone A' := shift_maximal A hA x₀ a₀
  have hB' : IsMaximalMonotone B' := shift_maximal B hB x₀ q
  have ha' : (0 : H) ∈ A' 0 := by simpa only [A',shift_operator,Set.mem_setOf_eq,zero_add] using ha₀
  have hbound' : ∀ x b, b ∈ B' x → ‖x‖ ≤ R+‖x₀‖ := by
    intro x b hb
    have h := hbound (x+x₀) (b+q) hb
    calc
      ‖x‖ = ‖(x+x₀)-x₀‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖x+x₀‖+‖x₀‖ := norm_sub_le _ _
      _ ≤ R+‖x₀‖ := by linarith
  have hlocal' : ∀ x ∈ Metric.ball (0 : H) δ, ∃ b ∈ B' x, ‖b‖ ≤ K+‖q‖ := by
    intro x hx
    have hx' : x+x₀ ∈ Metric.ball x₀ δ := by
      simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_right,sub_zero] using hx
    obtain ⟨b,hb,hbK⟩ := hlocal (x+x₀) hx'
    refine ⟨b-q,?_,(norm_sub_le b q).trans (by linarith)⟩
    simpa only [B',shift_operator,Set.mem_setOf_eq,sub_add_cancel] using hb
  obtain ⟨x,a,b,ha,hb,he⟩ := centered_sum_regularized_zero A' B' hA' hB' ha'
    (R+‖x₀‖) δ (K+‖q‖) (by positivity) hδ (by positivity) hbound' hlocal'
  refine ⟨x+x₀,(a+a₀)+(b+q),⟨a+a₀,ha,b+q,hb,rfl⟩,?_⟩
  rw [one_smul]
  symm
  calc
    (x+x₀)+((a+a₀)+(b+q))=(x+a+b)+w := by dsimp [q]; abel
    _=w := by rw [he,zero_add]
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open InertialFB.IFB ThreeOpSplitting.Convergence
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

noncomputable def restricted_real (C : Set H) (h : H → ℝ) : H → EReal := by
  classical
  exact fun x => if x ∈ C then (h x : EReal) else ⊤

theorem restricted_real_ne_bot (C : Set H) (h : H → ℝ) (x : H) :
    restricted_real C h x ≠ ⊥ := by
  classical
  by_cases hx : x ∈ C <;> simp [restricted_real,hx]

theorem restricted_real_mem_of_finite (C : Set H) (h : H → ℝ) {x : H}
    (hx : restricted_real C h x ≠ ⊤) : x ∈ C := by
  classical
  by_contra hn
  exact hx (by simp [restricted_real,hn])

theorem restricted_real_proper (C : Set H) (h : H → ℝ) (hne : C.Nonempty) :
    IsProperFn (restricted_real C h) := by
  classical
  obtain ⟨x,hx⟩ := hne
  exact ⟨restricted_real_ne_bot C h,⟨x,by simp [restricted_real,hx]⟩⟩

theorem restricted_real_convex (C : Set H) (h : H → ℝ) (hc : ConvexOn ℝ C h) :
    IsConvexFn (restricted_real C h) := by
  classical
  intro p hp q hq a b ha hb hab
  have hpC : p.1 ∈ C := by
    by_contra hn
    simp [restricted_real,hn] at hp
  have hqC : q.1 ∈ C := by
    by_contra hn
    simp [restricted_real,hn] at hq
  have hp' : h p.1 ≤ p.2 := by
    simpa only [Set.mem_setOf_eq,restricted_real,if_pos hpC,EReal.coe_le_coe_iff] using hp
  have hq' : h q.1 ≤ q.2 := by
    simpa only [Set.mem_setOf_eq,restricted_real,if_pos hqC,EReal.coe_le_coe_iff] using hq
  have hC := hc.1 hpC hqC ha hb hab
  have hf := hc.2 hpC hqC ha hb hab
  change restricted_real C h (a • p.1+b • q.1) ≤ ((a*p.2+b*q.2 : ℝ) : EReal)
  rw [restricted_real,if_pos hC,EReal.coe_le_coe_iff]
  calc
    h (a • p.1+b • q.1) ≤ a*h p.1+b*h q.1 := by simpa only [smul_eq_mul] using hf
    _ ≤ a*p.2+b*q.2 := add_le_add (mul_le_mul_of_nonneg_left hp' ha) (mul_le_mul_of_nonneg_left hq' hb)

theorem restricted_real_lsc (C : Set H) (h : H → ℝ) (hc : IsClosed C)
    (hh : ContinuousOn h C) : LowerSemicontinuous (restricted_real C h) := by
  classical
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  by_cases ha : a=⊤
  · subst a; simp
  by_cases hb : a=⊥
  · subst a
    have he : (restricted_real C h) ⁻¹' Set.Iic (⊥ : EReal) = ∅ := by
      ext x
      simp only [Set.mem_preimage,Set.mem_Iic,le_bot_iff,Set.mem_empty_iff_false]
      exact iff_false_intro (restricted_real_ne_bot C h x)
    rw [he]; exact isClosed_empty
  have he : (restricted_real C h) ⁻¹' Set.Iic a = C ∩ h ⁻¹' Set.Iic a.toReal := by
    ext x
    by_cases hx : x ∈ C
    · simp only [Set.mem_preimage,Set.mem_Iic,Set.mem_inter_iff]
      rw [show restricted_real C h x=(h x : EReal) by simp [restricted_real,hx]]
      have hab : (h x : EReal) ≤ a ↔ h x ≤ a.toReal := by
        conv_lhs => rw [← EReal.coe_toReal ha hb,EReal.coe_le_coe_iff]
      simpa only [hx,true_and] using hab
    · have ha' : ¬(⊤ : EReal) ≤ a := fun hn => ha (top_le_iff.mp hn)
      simp [restricted_real,hx,ha']
  rw [he]
  exact hh.preimage_isClosed_of_isClosed hc isClosed_Iic

noncomputable def closed_ball_extension (S : Set H) (h : H → ℝ) (R : ℝ) : H → EReal :=
  restricted_real (closure S ∩ Metric.closedBall 0 R) h

theorem closed_ball_subdiff_maximal (S : Set H) (h : H → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction S h) (R : ℝ)
    (hne : (closure S ∩ Metric.closedBall 0 R).Nonempty) :
    IsMaximalMonotone (BregmanPPA.Convergence.subdiffOp (closed_ball_extension S h R)) := by
  let C := closure S ∩ Metric.closedBall (0 : H) R
  have hc : IsClosed C := isClosed_closure.inter Metric.isClosed_closedBall
  have hcv : ConvexOn ℝ C h := by
    refine ⟨hh.strictConvexOn.convexOn.1.inter (convex_closedBall 0 R),?_⟩
    intro x hx y hy a b ha hb hab
    exact hh.strictConvexOn.convexOn.2 hx.1 hy.1 ha hb hab
  exact original_subdiff_maximal _ (restricted_real_proper C h hne)
    (restricted_real_convex C h hcv)
    (restricted_real_lsc C h hc (hh.continuousOn.mono Set.inter_subset_left))

theorem closed_ball_subdiff_domain (S : Set H) (h : H → ℝ) (R : ℝ) :
    dom (BregmanPPA.Convergence.subdiffOp (closed_ball_extension S h R)) ⊆
      Metric.closedBall 0 R := by
  rintro x ⟨g,hg⟩
  exact (restricted_real_mem_of_finite (closure S ∩ Metric.closedBall 0 R) h hg.1).2
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open InertialFB.IFB ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR Filter Topology
namespace BregmanExistenceCodex
open BregmanPPA.Convergence BregmanPPA.Existence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem closed_ball_subgradient_iff (S : Set H) (h : H → ℝ)
    (hh : IsBregmanFunction S h) (R : ℝ) {x g : H} (hx : x ∈ S) :
    IsSubgradient (closed_ball_extension S h R) x g ↔ g-gradient h x ∈ normal_ball R x := by
  classical
  let C := closure S ∩ Metric.closedBall (0 : H) R
  constructor
  · intro hg
    have hxC : x ∈ C := restricted_real_mem_of_finite C h hg.1
    refine ⟨hxC.2,?_⟩
    have hS : ∀ᶠ z in 𝓝[Metric.closedBall (0 : H) R] x, z ∈ S :=
      nhdsWithin_le_nhds (hh.isOpen.mem_nhds hx)
    have hmin : IsLocalMinOn (fun z : H => h z-inner ℝ g (z-x))
        (Metric.closedBall (0 : H) R) x := by
      filter_upwards [hS,self_mem_nhdsWithin] with z hzS hzB
      have hzC : z ∈ C := ⟨subset_closure hzS,hzB⟩
      have hs := hg.2 z
      change restricted_real C h x+((inner ℝ g (z-x) : ℝ) : EReal) ≤ restricted_real C h z at hs
      simp only [restricted_real,if_pos hxC,if_pos hzC] at hs
      rw [← EReal.coe_add,EReal.coe_le_coe_iff] at hs
      simp only [sub_self,inner_zero_right,sub_zero]
      linarith
    have hd : DifferentiableAt ℝ h x :=
      ((hh.contDiffOn.differentiableOn (by simp)) x hx).differentiableAt (hh.isOpen.mem_nhds hx)
    have hl : HasFDerivAt (fun z : H => inner ℝ g (z-x)) ((InnerProductSpace.toDual ℝ H) g) x := by
      simpa only [inner_sub_right,InnerProductSpace.toDual_apply_apply] using
        (((InnerProductSpace.toDual ℝ H) g).hasFDerivAt.sub_const (inner ℝ g x))
    intro z hz
    have ht : z-x ∈ posTangentConeAt (Metric.closedBall (0 : H) R) x :=
      sub_mem_posTangentConeAt_of_segment_subset ((convex_closedBall 0 R).segment_subset hxC.2 hz)
    have hs := hmin.hasFDerivWithinAt_nonneg (hd.hasFDerivAt.sub hl).hasFDerivWithinAt ht
    simp only [ContinuousLinearMap.sub_apply,InnerProductSpace.toDual_apply_apply] at hs
    rw [← inner_gradient_left] at hs
    rw [real_inner_comm,inner_sub_left]
    linarith
  · intro hn
    have hxC : x ∈ C := ⟨subset_closure hx,hn.1⟩
    refine ⟨?_,?_⟩
    · change restricted_real C h x ≠ ⊤
      simp [restricted_real,hxC]
    intro z
    by_cases hz : z ∈ C
    · have hs := BregmanPPACodex.gradient_support S h hh hx hz.1
      have hnormal := hn.2 z hz.2
      rw [real_inner_comm,inner_sub_left] at hnormal
      change restricted_real C h x+((inner ℝ g (z-x) : ℝ) : EReal) ≤ restricted_real C h z
      simp only [restricted_real,if_pos hxC,if_pos hz]
      rw [← EReal.coe_add,EReal.coe_le_coe_iff]
      linarith
    · change restricted_real C h x+((inner ℝ g (z-x) : ℝ) : EReal) ≤ restricted_real C h z
      simp [restricted_real,hz]

theorem clipped_sum_eq_normal_sum (T : H → Set H) (S : Set H) (h : H → ℝ)
    (hh : IsBregmanFunction S h) (hdom : dom T ⊆ S) (R : ℝ) :
    opAdd (subdiffOp (closed_ball_extension S h R)) T =
      opAdd (opAdd (gradOp S h) T) (normal_ball R) := by
  funext x
  ext w
  constructor
  · rintro ⟨g,hg,v,hv,rfl⟩
    have hx := hdom (show x ∈ dom T from ⟨v,hv⟩)
    have hn := (closed_ball_subgradient_iff S h hh R hx).mp hg
    exact ⟨gradient h x+v,⟨gradient h x,⟨hx,rfl⟩,v,hv,rfl⟩,
      g-gradient h x,hn,by abel⟩
  · rintro ⟨a,⟨g,⟨hx,rfl⟩,v,hv,rfl⟩,n,hn,rfl⟩
    have hn' : gradient h x+n-gradient h x ∈ normal_ball R x := by
      simpa only [add_sub_cancel_left] using hn
    exact ⟨gradient h x+n,(closed_ball_subgradient_iff S h hh R hx).mpr hn',v,hv,by abel⟩

theorem clipped_subdiff_interior_fibre (S : Set H) (h : H → ℝ)
    (hh : IsBregmanFunction S h) (R : ℝ) {x g : H}
    (hx : x ∈ S) (hxB : x ∈ Metric.ball (0 : H) R) :
    IsSubgradient (closed_ball_extension S h R) x g ↔ g=gradient h x := by
  rw [closed_ball_subgradient_iff S h hh R hx]
  constructor
  · intro hg
    exact sub_eq_zero.mp (normal_ball_interior_zero R hxB hg)
  · intro hg
    rw [hg,sub_self]
    exact normal_ball_zero_mem R (Metric.ball_subset_closedBall hxB)
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanExistenceCodex
open BregmanPPA.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem original_gradient_continuous (S : Set H) (h : H → ℝ)
    (hh : IsBregmanFunction S h) {x : H} (hx : x ∈ S) :
    ContinuousAt (gradient h) x := by
  have hf := (hh.contDiffOn.contDiffAt (hh.isOpen.mem_nhds hx)).continuousAt_fderiv (by simp)
  change ContinuousAt (fun y => (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ h y)) x
  simpa only [Function.comp_def] using
    (InnerProductSpace.toDual ℝ H).symm.continuous.continuousAt.comp hf

/-- Around any zone point strictly within a cutoff ball, clipped subgradients are locally bounded. -/
theorem clipped_subdiff_local_bound (S : Set H) (h : H → ℝ)
    (hh : IsBregmanFunction S h) (R : ℝ) {x₀ : H} (hx : x₀ ∈ S)
    (hxB : x₀ ∈ Metric.ball (0 : H) R) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 ≤ K ∧ ∀ x ∈ Metric.ball x₀ δ,
      ∃ g ∈ subdiffOp (closed_ball_extension S h R) x, ‖g‖ ≤ K := by
  let K : ℝ := ‖gradient h x₀‖+1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have ht : Tendsto (fun x => ‖gradient h x‖) (𝓝 x₀) (𝓝 ‖gradient h x₀‖) :=
    (original_gradient_continuous S h hh hx).norm
  have hb : ∀ᶠ x in 𝓝 x₀, ‖gradient h x‖ < K :=
    ht.eventually (Iio_mem_nhds (by dsimp [K]; linarith))
  have hU : S ∩ Metric.ball (0 : H) R ∩ {x | ‖gradient h x‖ < K} ∈ 𝓝 x₀ :=
    inter_mem (inter_mem (hh.isOpen.mem_nhds hx) (Metric.isOpen_ball.mem_nhds hxB)) hb
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨δ,K,hδ,hK,?_⟩
  intro x hxδ
  have hp := hball hxδ
  refine ⟨gradient h x,?_,hp.2.le⟩
  exact (clipped_subdiff_interior_fibre S h hh R hp.1.1 hp.1.2).mpr rfl
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR BregmanPPA.Existence
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem gradient_operator_monotone (S : Set H) (h : H → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction S h) : IsMonotoneOp (gradOp S h) := by
  rintro x y u v ⟨hx,rfl⟩ ⟨hy,rfl⟩
  have hxy := BregmanPPACodex.gradient_support S h hh hx (subset_closure hy)
  have hyx := BregmanPPACodex.gradient_support S h hh hy (subset_closure hx)
  rw [← neg_sub x y,inner_neg_right] at hxy
  rw [real_inner_comm] at hxy hyx
  rw [inner_sub_right]
  linarith

/-- Ball localization proves maximality under the original domain inclusion. -/
theorem gradient_sum_maximal (T : H → Set H) (S : Set H) (h : H → ℝ)
    (hT : IsMaximalMonotone T) (hh : BregmanPPA.Convergence.IsBregmanFunction S h)
    (hdom : dom T ⊆ S) : IsMaximalMonotone (opAdd (gradOp S h) T) := by
  obtain ⟨x₀,a₀,ha₀,_⟩ := gdr_minty_core T hT 1 one_pos 0
  have hx₀ : x₀ ∈ S := hdom ⟨a₀,ha₀⟩
  apply maximal_of_normal_ball_sums _
    (sum_monotone _ _ (gradient_operator_monotone S h hh) hT.1) ‖x₀‖
  intro R hR
  have hR0 : 0 ≤ R := (norm_nonneg x₀).trans hR.le
  have hxB : x₀ ∈ Metric.ball (0 : H) R := by
    simpa only [Metric.mem_ball,dist_zero_right] using hR
  let B := BregmanPPA.Convergence.subdiffOp (closed_ball_extension S h R)
  have hB : IsMaximalMonotone B := closed_ball_subdiff_maximal S h hh R
    ⟨x₀,subset_closure hx₀,Metric.ball_subset_closedBall hxB⟩
  have hbound : ∀ x b, b ∈ B x → ‖x‖ ≤ R := by
    intro x b hb
    have hx := closed_ball_subdiff_domain S h R (show x ∈ dom B from ⟨b,hb⟩)
    simpa only [Metric.mem_closedBall,dist_zero_right] using hx
  obtain ⟨δ,K,hδ,hK,hlocal⟩ := clipped_subdiff_local_bound S h hh R hx₀ hxB
  have hmax := bounded_domain_sum_maximal T B hT hB R hR0 hbound x₀ a₀ ha₀ δ K hδ hK hlocal
  rw [operator_sum_comm T B] at hmax
  change IsMaximalMonotone (opAdd (BregmanPPA.Convergence.subdiffOp
    (closed_ball_extension S h R)) T) at hmax
  rw [clipped_sum_eq_normal_sum T S h hh hdom R] at hmax
  exact hmax
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem scaled_operator_monotone (T : H → Set H) (hT : IsMonotoneOp T)
    (c : ℝ) (hc : 0 ≤ c) : IsMonotoneOp (opSmul c T) := by
  rintro x y u v ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
  rw [← smul_sub,inner_smul_right]
  exact mul_nonneg hc (hT x y a b ha hb)

theorem scaled_operator_maximal (T : H → Set H) (hT : IsMaximalMonotone T)
    (c : ℝ) (hc : 0 < c) : IsMaximalMonotone (opSmul c T) := by
  apply (gdr_max_iff _ (scaled_operator_monotone T hT.1 c hc.le) 1 one_pos).mpr
  intro w
  obtain ⟨x,a,ha,he⟩ := gdr_minty_core T hT c hc w
  exact ⟨x,c • a,⟨a,ha,rfl⟩,by simpa only [one_smul] using he⟩

theorem scaled_operator_domain (T : H → Set H) (c : ℝ) : dom (opSmul c T)=dom T := by
  ext x
  constructor
  · rintro ⟨w,a,ha,_⟩; exact ⟨a,ha⟩
  · rintro ⟨a,ha⟩; exact ⟨c • a,a,ha,rfl⟩
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR BregmanPPA.Existence
open scoped Pointwise
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem gradient_operator_image (S : Set H) (h : H → ℝ) :
    imOp (gradOp S h)=gradient h '' S := by
  ext y
  constructor
  · rintro ⟨x,hx,he⟩; exact ⟨x,hx,he.symm⟩
  · rintro ⟨x,hx,he⟩; exact ⟨x,hx,he.symm⟩

theorem original_image_inclusion (T : H → Set H) (S : Set H) (h : H → ℝ)
    (hT : IsMaximalMonotone T) (hh : BregmanPPA.Convergence.IsBregmanFunction S h)
    (hdom : dom T ⊆ S)
    (hcase : gradient h '' S=Set.univ ∨ (IsOpen (gradient h '' S) ∧ (0 : H) ∈ imOp T))
    (c : ℝ) (hc : 0 < c) :
    gradient h '' S ⊆ imOp (opAdd (gradOp S h) (opSmul c T)) := by
  let A := opSmul c T
  let B := gradOp S h
  have hA : IsMaximalMonotone A := scaled_operator_maximal T hT c hc
  have hdA : dom A ⊆ S := by rw [scaled_operator_domain T c]; exact hdom
  have hd : dom A ⊆ dom B := by
    intro x hx
    exact ⟨gradient h x,hdA hx,rfl⟩
  have hC := gradient_sum_maximal A S h hA hh hdA
  rw [operator_sum_comm B A] at hC
  have hi := range_interior_equality A B hA.1 hd hC (gradient_lproperty S h hh)
  have hG : imOp B=gradient h '' S := gradient_operator_image S h
  have hin : gradient h '' S ⊆ interior (imOp A+imOp B) := by
    rcases hcase with hall | ⟨hopen,hzero⟩
    · obtain ⟨x,a,ha,_⟩ := gdr_minty_core A hA 1 one_pos 0
      have hsum : imOp A+imOp B=Set.univ := by
        apply Set.eq_univ_of_forall
        intro r
        apply Set.mem_add.mpr
        refine ⟨a,⟨x,ha⟩,r-a,?_,by abel⟩
        rw [hG,hall]; trivial
      rw [hsum,interior_univ]
      exact Set.subset_univ _
    · have hzeroA : (0 : H) ∈ imOp A := by
        obtain ⟨x,hx⟩ := hzero
        exact ⟨x,0,hx,by simp⟩
      apply interior_maximal _ hopen
      intro r hr
      apply Set.mem_add.mpr
      exact ⟨0,hzeroA,r,by rwa [hG],by simp⟩
  intro r hr
  have hri := hin hr
  rw [← hi] at hri
  have hm := interior_subset hri
  rwa [operator_sum_comm A B] at hm
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR BregmanPPA.Existence
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem original_successor (T : H → Set H) (S : Set H) (h : H → ℝ)
    (hT : IsMaximalMonotone T) (hh : BregmanPPA.Convergence.IsBregmanFunction S h)
    (hdom : dom T ⊆ S)
    (hcase : gradient h '' S=Set.univ ∨ (IsOpen (gradient h '' S) ∧ (0 : H) ∈ imOp T))
    (c : ℝ) (hc : 0 < c) (x : H) (hx : x ∈ S) :
    ∃ z ∈ S, c⁻¹ • (gradient h x-gradient h z) ∈ T z := by
  have hy := original_image_inclusion T S h hT hh hdom hcase c hc
    (show gradient h x ∈ gradient h '' S from ⟨x,hx,rfl⟩)
  obtain ⟨z,g,hg,w,hw,he⟩ := hy
  obtain ⟨hz,rfl⟩ := hg
  obtain ⟨a,ha,rfl⟩ := hw
  refine ⟨z,hz,?_⟩
  have he' : gradient h x-gradient h z=c • a := by rw [he]; abel
  rw [he',smul_smul,inv_mul_cancel₀ hc.ne',one_smul]
  exact ha

theorem original_run_exists (T : H → Set H) (S : Set H) (h : H → ℝ)
    (hT : IsMaximalMonotone T) (hh : BregmanPPA.Convergence.IsBregmanFunction S h)
    (hdom : dom T ⊆ S)
    (hcase : gradient h '' S=Set.univ ∨ (IsOpen (gradient h '' S) ∧ (0 : H) ∈ imOp T))
    (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (x₀ : H) (hx₀ : x₀ ∈ S) :
    ∃ x : ℕ → H, x 0=x₀ ∧ IsBregmanPPARun S h T c x := by
  classical
  have hstep (k : ℕ) (y : S) :
      ∃ z : S, (c k)⁻¹ • (gradient h y.val-gradient h z.val) ∈ T z.val := by
    obtain ⟨z,hz,he⟩ := original_successor T S h hT hh hdom hcase (c k) (hc k) y.val y.property
    exact ⟨⟨z,hz⟩,he⟩
  let next (k : ℕ) (y : S) : S := Classical.choose (hstep k y)
  have hnext (k : ℕ) (y : S) :
      (c k)⁻¹ • (gradient h y.val-gradient h (next k y).val) ∈ T (next k y).val :=
    Classical.choose_spec (hstep k y)
  let xs : ℕ → S := fun k => Nat.rec ⟨x₀,hx₀⟩ (fun n y => next n y) k
  refine ⟨fun k => (xs k).val,rfl,?_⟩
  intro k
  exact ⟨(xs k).property,hnext k (xs k)⟩
end BregmanExistenceCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.ProxMult BregmanPPA.Convergence
open ThreeOpSplitting.Convergence
namespace BregmanProxMultCodex

theorem product_gradient_image {n m : ℕ} (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp)
    (himx : gradient hx '' Sx=Set.univ) (him : gradient hp '' Sp=Set.univ) :
    gradient (sumFn hx hp) '' prodZone Sx Sp=Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  have hzx : z.ofLp.1 ∈ gradient hx '' Sx := by rw [himx]; trivial
  have hzp : z.ofLp.2 ∈ gradient hp '' Sp := by rw [him]; trivial
  obtain ⟨x,hxS,hxe⟩ := hzx
  obtain ⟨p,hpS,hpe⟩ := hzp
  have hxd : DifferentiableAt ℝ hx x :=
    ((hhx.contDiffOn.differentiableOn (by simp)) x hxS).differentiableAt (hhx.isOpen.mem_nhds hxS)
  have hpd : DifferentiableAt ℝ hp p :=
    ((hhp.contDiffOn.differentiableOn (by simp)) p hpS).differentiableAt (hhp.isOpen.mem_nhds hpS)
  refine ⟨pair x p,⟨hxS,hpS⟩,?_⟩
  rw [sum_gradient_pair hx hp x p hxd hpd,hxe,hpe]
end BregmanProxMultCodex
namespace BregmanProxMultCodex

/-- Theorem 8, p. 221 (third sentence): if moreover `im ∇h_x = ℝⁿ`, then for every sequence of
positive scalars `c k` bounded away from zero and every `(x⁰, p⁰) ∈ C × Ω̄⁺` an infinite sequence conforming to (12)
and starting at `(x⁰, p⁰)` exists. -/
theorem original_theorem8_existence {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal)
    (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (Sx : Set (BregmanPPA.IneqMult.E n)) (hx : BregmanPPA.IneqMult.E n → ℝ) (Sp : Set (BregmanPPA.IneqMult.E m)) (hp : BregmanPPA.IneqMult.E m → ℝ)
    (hP : BregmanPPA.IneqMult.IsConvexProgram C f g)
    (hhx : BregmanPPA.Convergence.IsBregmanFunction Sx hx) (hSx : C ⊆ Sx)
    (hhp : BregmanPPA.Convergence.IsBregmanFunction Sp hp) (hSp : BregmanPPA.IneqMult.nonnegOrthant m ⊆ Sp)
    (him : gradient hp '' Sp = Set.univ)
    (himx : gradient hx '' Sx = Set.univ) :
    ∀ c : ℕ → ℝ, (∀ k, 0 < c k) →
      (∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k) → ∀ x₀ ∈ C, ∀ p₀ ∈ BregmanPPA.IneqMult.nonnegOrthant m,
      ∃ (x : ℕ → BregmanPPA.IneqMult.E n) (p : ℕ → BregmanPPA.IneqMult.E m), x 0 = x₀ ∧ p 0 = p₀ ∧
        IsProxMultRun C f g Sx hx Sp hp c x p := by
  intro c hc _ x0 hx0 p0 hp0
  have hclose := opK_closure_subset C f g Sx Sp hP.closed hSx hSp
  have hdom : dom (opK C f g) ⊆ prodZone Sx Sp := fun z hz => hclose (subset_closure hz)
  obtain ⟨xs,hxs,hr⟩ := BregmanExistenceCodex.original_run_exists (opK C f g)
    (prodZone Sx Sp) (sumFn hx hp) (original_K_maximal C f g hP)
    (product_bregman Sx Sp hx hp hhx hhp) hdom
    (Or.inl (product_gradient_image Sx Sp hx hp hhx hhp himx him)) c hc
    (pair x0 p0) ⟨hSx hx0,hSp hp0⟩
  let x : ℕ → E n := fun k => (xs k).ofLp.1
  let p : ℕ → E m := fun k => (xs k).ofLp.2
  have hr' : IsBregmanPPARun (prodZone Sx Sp) (sumFn hx hp) (opK C f g) c
      (fun k => pair (x k) (p k)) := hr
  refine ⟨x,p,?_,?_,original_run_of_product C f g Sx hx Sp hp c x p hP hc hhx hSx hhp hSp him hr'⟩
  · exact congrArg (fun z => z.ofLp.1) hxs
  · exact congrArg (fun z => z.ofLp.2) hxs

end BregmanProxMultCodex


end

set_option autoImplicit false
open Filter Topology BregmanPPA.ProxMult ThreeOpSplitting.Convergence

/-- Theorem 8, p. 221 (third sentence): if moreover `im ∇h_x = ℝⁿ`, then for every sequence of
positive scalars `c k` bounded away from zero and every `(x⁰, p⁰) ∈ C × Ω̄⁺` an infinite sequence conforming to (12)
and starting at `(x⁰, p⁰)` exists. -/
theorem solution {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal)
    (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (Sx : Set (BregmanPPA.IneqMult.E n)) (hx : BregmanPPA.IneqMult.E n → ℝ) (Sp : Set (BregmanPPA.IneqMult.E m)) (hp : BregmanPPA.IneqMult.E m → ℝ)
    (hP : BregmanPPA.IneqMult.IsConvexProgram C f g)
    (hhx : BregmanPPA.Convergence.IsBregmanFunction Sx hx) (hSx : C ⊆ Sx)
    (hhp : BregmanPPA.Convergence.IsBregmanFunction Sp hp) (hSp : BregmanPPA.IneqMult.nonnegOrthant m ⊆ Sp)
    (him : gradient hp '' Sp = Set.univ)
    (himx : gradient hx '' Sx = Set.univ) :
    ∀ c : ℕ → ℝ, (∀ k, 0 < c k) →
      (∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k) → ∀ x₀ ∈ C, ∀ p₀ ∈ BregmanPPA.IneqMult.nonnegOrthant m,
      ∃ (x : ℕ → BregmanPPA.IneqMult.E n) (p : ℕ → BregmanPPA.IneqMult.E m), x 0 = x₀ ∧ p 0 = p₀ ∧
        IsProxMultRun C f g Sx hx Sp hp c x p := by
  exact BregmanProxMultCodex.original_theorem8_existence C f g Sx hx Sp hp hP hhx hSx hhp hSp him himx




#print axioms solution
