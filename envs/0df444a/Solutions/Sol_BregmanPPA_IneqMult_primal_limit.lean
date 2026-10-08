-- Prove2me | solution 1 for BregmanPPA.IneqMult.primal_limit
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T21:36:53.500208+00:00
-- url     : https://prove2.me/submissions/3ed9f309-69ed-48ce-b1c0-a19022874d9c

import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_IneqMult_Program
import Definitions.Def_BregmanPPA_IneqMult_Run
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
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

theorem run_lagrangian_min (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (S : Set (E m)) (h : E m → ℝ)
    (c : ℕ → ℝ) (x : ℕ → E n) (p : ℕ → E m)
    (hP : IsConvexProgram C f g) (hh : IsBregmanFunction S h)
    (hS : posOrthant m ⊆ S) (him : posOrthant m ⊆ gradient h '' S)
    (hc : ∀ k, 0 < c k) (hrun : IsIneqMultiplierRun C f g S h c x p) (k : ℕ) :
    ∀ y ∈ C, (f (x (k+1))).toReal+inner ℝ (p (k+1)) (gvec g (x (k+1))) ≤
      (f y).toReal+inner ℝ (p (k+1)) (gvec g y) := by
  have hf := finite_convex_toReal C f hP.f_proper hP.f_convex hP.convex hP.f_finite
  have hg : ∀ i, ConvexOn ℝ C (fun y => gvec g y i) := by
    intro i
    exact finite_convex_toReal C (g i) (hP.g_proper i) (hP.g_convex i) hP.convex (hP.g_finite i)
  have hM := monoConj_real_properties S h hh hS him
  let M : E m → ℝ := fun z => (monoConj h z).toReal
  have hmin : ∀ y ∈ C, (f (x (k+1))).toReal+(c k)⁻¹*M (gradient h (p k)+c k • gvec g (x (k+1))) ≤
      (f y).toReal+(c k)⁻¹*M (gradient h (p k)+c k • gvec g y) := by
    intro y hy
    have hi := (hrun k).2.2.1 y hy
    have ex := EReal.coe_toReal (hP.f_finite _ (hrun k).2.1) (hP.f_proper.1 _)
    have ey := EReal.coe_toReal (hP.f_finite y hy) (hP.f_proper.1 y)
    rw [← ex,← ey,← EReal.coe_add,← EReal.coe_add] at hi
    exact EReal.coe_le_coe_iff.mp hi
  have hd := (hM.2.1 (gradient h (p k)+c k • gvec g (x (k+1)))).hasGradientAt.hasFDerivAt
  have hi := monotone_penalty_lagrangian_min C (fun y => (f y).toReal) (gvec g) M
    (gradient h (p k)) (c k) (x (k+1)) hf hg hM.2.2 (hc k) (hrun k).2.1 hd hmin
  rw [← (hrun k).2.2.2] at hi
  exact hi
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.Convergence
namespace BregmanIneqMultCodex
variable {n m : ℕ}

theorem dual_attained_of_lagrangian_min (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (x : E n) (hx : x ∈ C) (p : E m) (hp : p ∈ nonnegOrthant m)
    (hmin : ∀ y ∈ C, (f x).toReal+inner ℝ p (gvec g x) ≤
      (f y).toReal+inner ℝ p (gvec g y)) :
    dualFn C f g p=(((f x).toReal+inner ℝ p (gvec g x) : ℝ) : EReal) := by
  classical
  simp only [dualFn,if_pos hp]
  apply le_antisymm
  · have hi : (⨅ y ∈ C, f y+((inner ℝ p (gvec g y) : ℝ) : EReal)) ≤ f x+((inner ℝ p (gvec g x) : ℝ) : EReal) :=
      iInf_le_of_le x (iInf_le_of_le hx le_rfl)
    rw [← EReal.coe_toReal (hP.f_finite x hx) (hP.f_proper.1 x),← EReal.coe_add] at hi
    exact hi
  · apply le_iInf; intro y
    apply le_iInf; intro hy
    rw [← EReal.coe_toReal (hP.f_finite y hy) (hP.f_proper.1 y),← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr (hmin y hy)

theorem negDual_subgradient_of_lagrangian_min (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (x : E n) (hx : x ∈ C) (p v : E m) (hp : p ∈ nonnegOrthant m)
    (hmin : ∀ y ∈ C, (f x).toReal+inner ℝ p (gvec g x) ≤
      (f y).toReal+inner ℝ p (gvec g y))
    (hinner : ∀ q ∈ nonnegOrthant m, inner ℝ v (q-p) ≤ -inner ℝ (gvec g x) (q-p)) :
    IsSubgradient (fun q => -(dualFn C f g q)) p v := by
  classical
  have he := dual_attained_of_lagrangian_min C f g hP x hx p hp hmin
  refine ⟨?_,?_⟩
  · change -(dualFn C f g p) ≠ ⊤
    rw [he,← EReal.coe_neg]; exact EReal.coe_ne_top _
  · intro q
    change -(dualFn C f g p)+((inner ℝ v (q-p) : ℝ) : EReal) ≤ -(dualFn C f g q)
    by_cases hq : q ∈ nonnegOrthant m
    · have hi : dualFn C f g q ≤ (((f x).toReal+inner ℝ q (gvec g x) : ℝ) : EReal) := by
        simp only [dualFn,if_pos hq]
        have ht : (⨅ y ∈ C, f y+((inner ℝ q (gvec g y) : ℝ) : EReal)) ≤ f x+((inner ℝ q (gvec g x) : ℝ) : EReal) :=
          iInf_le_of_le x (iInf_le_of_le hx le_rfl)
        rw [← EReal.coe_toReal (hP.f_finite x hx) (hP.f_proper.1 x),← EReal.coe_add] at ht
        exact ht
      have hn := EReal.neg_le_neg_iff.mpr hi
      rw [he,← EReal.coe_neg,← EReal.coe_add]
      apply le_trans _ hn
      rw [← EReal.coe_neg]
      apply EReal.coe_le_coe_iff.mpr
      have hb := hinner q hq
      simp only [inner_sub_right] at hb ⊢
      have hxp := real_inner_comm (gvec g x) p
      have hxq := real_inner_comm (gvec g x) q
      rw [← hxp,← hxq] at hb
      linarith
    · simp only [dualFn,if_neg hq,EReal.neg_bot]; exact le_top

theorem original_proximal_identity (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (S : Set (E m)) (h : E m → ℝ)
    (c : ℕ → ℝ) (x : ℕ → E n) (p : ℕ → E m)
    (hP : IsConvexProgram C f g) (hd : ∃ q, dualFn C f g q ≠ ⊥)
    (hh : IsBregmanFunction S h) (hS : posOrthant m ⊆ S)
    (him : posOrthant m ⊆ gradient h '' S) (hc : ∀ k, 0 < c k)
    (hrun : IsIneqMultiplierRun C f g S h c x p) :
    IsBregmanPPARun S h (subdiffOp (fun q => -(dualFn C f g q))) c p := by
  intro k
  refine ⟨(hrun k).1,?_⟩
  let z := gradient h (p k)+c k • gvec g (x (k+1))
  have he : gradient (fun z => (monoConj h z).toReal) z=p (k+1) := (hrun k).2.2.2.symm
  have hps : gradient (fun z => (monoConj h z).toReal) z ∈ S := by rw [he]; exact (hrun (k+1)).1
  have hn := monoConj_projected_stationarity S h hh hS him z hps
  rw [he] at hn
  have hmin := run_lagrangian_min C f g S h c x p hP hh hS him hc hrun k
  apply negDual_subgradient_of_lagrangian_min C f g hP (x (k+1)) (hrun k).2.1
    (p (k+1)) ((c k)⁻¹ • (gradient h (p k)-gradient h (p (k+1)))) hn.1 hmin
  intro q hq
  have hi := hn.2 q hq
  dsimp only [z] at hi
  simp only [inner_sub_left,inner_add_left,real_inner_smul_left] at hi
  simp only [real_inner_smul_left,inner_sub_left]
  have hcinv : 0 < (c k)⁻¹ := inv_pos.mpr (hc k)
  have hmul := mul_le_mul_of_nonneg_left hi hcinv.le
  have hec : (c k)⁻¹*(c k)=1 := inv_mul_cancel₀ (hc k).ne'
  simp only [mul_add,mul_sub,← mul_assoc,hec,one_mul,mul_zero] at hmul
  linarith
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem three_point_identity (h : H → ℝ) (v y p : H) :
    bregmanD h v y-bregmanD h v p-bregmanD h p y =
      inner ℝ (p-v) (gradient h y-gradient h p) := by
  have he : v-y = (v-p)+(p-y) := by abel
  have hi : inner ℝ (gradient h y) (v-y) =
      inner ℝ (gradient h y) (v-p)+inner ℝ (gradient h y) (p-y) := by
    rw [he,inner_add_right]
  have hc1 : inner ℝ (p-v) (gradient h y) = inner ℝ (gradient h y) (p-v) :=
    real_inner_comm _ _
  have hc2 : inner ℝ (p-v) (gradient h p) = inner ℝ (gradient h p) (p-v) :=
    real_inner_comm _ _
  rw [inner_sub_right,hc1,hc2,← neg_sub v p,inner_neg_right,inner_neg_right]
  dsimp [bregmanD]
  linarith

theorem weighted_graph_comparison (T : H → Set H) (h : H → ℝ) (hT : IsMonotoneOp T)
    (v w y p : H) (c : ℝ) (hc : 0 < c) (hw : w ∈ T v)
    (hp : c⁻¹ • (gradient h y-gradient h p) ∈ T p) :
    c*inner ℝ w (p-v) ≤ bregmanD h v y-bregmanD h v p-bregmanD h p y := by
  have hm := hT p v _ w hp hw
  rw [inner_sub_right,inner_smul_right] at hm
  change 0 ≤ c⁻¹*inner ℝ (p-v) (gradient h y-gradient h p)-inner ℝ (p-v) w at hm
  have hm' : inner ℝ (p-v) w ≤ c⁻¹*inner ℝ (p-v) (gradient h y-gradient h p) := by linarith
  have ht := mul_le_mul_of_nonneg_left hm' hc.le
  simp only [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul] at ht
  rw [three_point_identity]
  have he : inner ℝ (p-v) w = inner ℝ w (p-v) := real_inner_comm _ _
  rwa [he] at ht

theorem weighted_descent (T : H → Set H) (h : H → ℝ) (hT : IsMonotoneOp T)
    (z y p : H) (c : ℝ) (hc : 0 < c) (hz : z ∈ zer T)
    (hp : c⁻¹ • (gradient h y-gradient h p) ∈ T p) :
    bregmanD h z p ≤ bregmanD h z y-bregmanD h p y := by
  have ht := weighted_graph_comparison T h hT z 0 y p c hc hz hp
  simp only [inner_zero_left,mul_zero] at ht
  linarith
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem zero_mem_closure (T : H → Set H) (S : Set H) (hdom : dom T ⊆ closure S)
    {z : H} (hz : z ∈ zer T) : z ∈ closure S := hdom ⟨0,hz⟩

theorem run_descent (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMonotoneOp T) (hc : ∀ k, 0 < c k) (hx : IsBregmanPPARun S h T c x)
    (z : H) (hz : z ∈ zer T) (k : ℕ) :
    bregmanD h z (x (k+1)) ≤ bregmanD h z (x k)-bregmanD h (x (k+1)) (x k) :=
  weighted_descent T h hT z (x k) (x (k+1)) (c k) (hc k) hz (hx k).2

theorem distance_antitone (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMonotoneOp T) (hh : IsBregmanFunction S h)
    (hc : ∀ k, 0 < c k) (hx : IsBregmanPPARun S h T c x) (z : H) (hz : z ∈ zer T) :
    Antitone (fun k => bregmanD h z (x k)) := by
  apply antitone_nat_of_succ_le
  intro k
  have hd := run_descent T S h c x hT hc hx z hz k
  have hn := bregman_nonneg S h hh (subset_closure (hx (k+1)).1) (hx k).1
  linarith

theorem step1 (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hx : IsBregmanPPARun S h T c x) (z : H) (hz : z ∈ zer T) :
    (∀ k, bregmanD h z (x (k+1)) ≤ bregmanD h z (x k)-bregmanD h (x (k+1)) (x k)) ∧
    (∃ δ : ℝ, 0 ≤ δ ∧ Tendsto (fun k => bregmanD h z (x k)) atTop (𝓝 δ)) ∧
    Bornology.IsBounded (Set.range x) := by
  have hzc := zero_mem_closure T S hdom hz
  have hnonneg (k : ℕ) : 0 ≤ bregmanD h z (x k) := bregman_nonneg S h hh hzc (hx k).1
  have hanti := distance_antitone T S h c x hT.1 hh hc hx z hz
  have hbelow : BddBelow (Set.range (fun k => bregmanD h z (x k))) := by
    refine ⟨0, ?_⟩; rintro _ ⟨k,rfl⟩; exact hnonneg k
  have ht := tendsto_atTop_ciInf hanti hbelow
  have hδ : 0 ≤ ⨅ k, bregmanD h z (x k) :=
    (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).mem_of_tendsto ht
      (Eventually.of_forall hnonneg)
  refine ⟨run_descent T S h c x hT.1 hc hx z hz,⟨_,hδ,ht⟩, ?_⟩
  apply (hh.bounded_L₂ (bregmanD h z (x 0)) z hzc).subset
  rintro _ ⟨k,rfl⟩
  exact ⟨(hx k).1,hanti (Nat.zero_le k)⟩
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology Finset
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem step_distance_sum (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMonotoneOp T) (hc : ∀ k, 0 < c k) (hx : IsBregmanPPARun S h T c x)
    (z : H) (hz : z ∈ zer T) (N : ℕ) :
    (∑ k ∈ range N, bregmanD h (x (k+1)) (x k))+bregmanD h z (x N) ≤ bregmanD h z (x 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have hd := run_descent T S h c x hT hc hx z hz N
    linarith

theorem step_distance_zero (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMonotoneOp T) (hh : IsBregmanFunction S h) (hdom : dom T ⊆ closure S)
    (hc : ∀ k, 0 < c k) (hx : IsBregmanPPARun S h T c x) (z : H) (hz : z ∈ zer T) :
    Tendsto (fun k => bregmanD h (x (k+1)) (x k)) atTop (𝓝 0) := by
  have hzc := zero_mem_closure T S hdom hz
  have hs : Summable (fun k => bregmanD h (x (k+1)) (x k)) := by
    apply summable_of_sum_range_le
      (fun k => bregman_nonneg S h hh (subset_closure (hx (k+1)).1) (hx k).1)
      (c := bregmanD h z (x 0))
    intro N
    have hsum := step_distance_sum T S h c x hT hc hx z hz N
    have hn := bregman_nonneg S h hh hzc (hx N).1
    linarith
  exact hs.tendsto_atTop_zero

theorem successor_subsequence_limit (T : H → Set H) (S : Set H) (h : H → ℝ)
    (c : ℕ → ℝ) (x : ℕ → H) (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k) (hx : IsBregmanPPARun S h T c x)
    (hz : (zer T).Nonempty) (φ : ℕ → ℕ) (hφ : StrictMono φ) (p : H)
    (hlim : Tendsto (x ∘ φ) atTop (𝓝 p)) :
    Tendsto (fun k => x (φ k+1)) atTop (𝓝 p) := by
  obtain ⟨z,hz⟩ := hz
  have hb := (step1 T S h c x hT hh hdom hc hcinf hx z hz).2.2
  have hfirst : Bornology.IsBounded (Set.range (fun k => x (φ k+1))) := hb.subset (by
    rintro _ ⟨k,rfl⟩; exact ⟨φ k+1,rfl⟩)
  have hpc : p ∈ closure S := isClosed_closure.mem_of_tendsto hlim
    (Eventually.of_forall (fun k => subset_closure (hx (φ k)).1))
  have hD : Tendsto (fun k => bregmanD h (x (φ k+1)) ((x ∘ φ) k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (step_distance_zero T S h c x hT.1 hh hdom hc hx z hz).comp hφ.tendsto_atTop
  exact hh.tendsto_of_zero (fun k => x (φ k+1)) (x ∘ φ) p
    (fun k => subset_closure (hx (φ k+1)).1) (fun k => (hx (φ k)).1)
    hlim hpc hfirst hD
end BregmanPPACodex

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
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem gradient_continuous_in_zone (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h)
    {p : H} (hp : p ∈ S) : ContinuousAt (gradient h) p := by
  have hf := (hh.contDiffOn.contDiffAt (hh.isOpen.mem_nhds hp)).continuousAt_fderiv (by simp)
  change ContinuousAt (fun y => (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ h y)) p
  simpa only [Function.comp_def] using
    (InnerProductSpace.toDual ℝ H).symm.continuous.continuousAt.comp hf

theorem bounded_inverse_residual (a : ℕ → H) (c : ℕ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hc : ∀ k, 0 < c k) (hle : ∀ k, ε ≤ c k)
    (ha : Tendsto a atTop (𝓝 0)) : Tendsto (fun k => (c k)⁻¹ • a k) atTop (𝓝 0) := by
  have hbound (k : ℕ) : ‖(c k)⁻¹ • a k‖ ≤ ‖a k‖/ε := by
    rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr (hc k)).le]
    simpa only [div_eq_mul_inv,mul_comm] using
      div_le_div_of_nonneg_left (norm_nonneg (a k)) hε (hle k)
  have ht : Tendsto (fun k => ‖a k‖/ε) atTop (𝓝 0) := by simpa using ha.norm.div_const ε
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun k => norm_nonneg _) hbound ht)

theorem interior_cluster_zero (T : H → Set H) (S : Set H) (h : H → ℝ)
    (c : ℕ → ℝ) (x : ℕ → H) (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k) (hx : IsBregmanPPARun S h T c x)
    (hz : (zer T).Nonempty) (hC1 : closure (dom T) ⊆ S)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (p : H) (hlim : Tendsto (x ∘ φ) atTop (𝓝 p)) :
    p ∈ zer T := by
  have hnext := successor_subsequence_limit T S h c x hT hh hdom hc hcinf hx hz φ hφ p hlim
  have hpdom : p ∈ closure (dom T) := isClosed_closure.mem_of_tendsto hnext
    (Eventually.of_forall (fun k => subset_closure ⟨_,(hx (φ k)).2⟩))
  have hgrad := (gradient_continuous_in_zone S h hh (hC1 hpdom)).tendsto
  have hdiff : Tendsto (fun k => gradient h (x (φ k))-gradient h (x (φ k+1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,sub_self] using (hgrad.comp hlim).sub (hgrad.comp hnext)
  obtain ⟨ε,hε,hle⟩ := hcinf
  have hres := bounded_inverse_residual _ (c ∘ φ) ε hε (fun k => hc (φ k))
    (fun k => hle (φ k)) hdiff
  exact maximal_graph_limit T hT (fun k => x (φ k+1))
    (fun k => (c (φ k))⁻¹ • (gradient h (x (φ k))-gradient h (x (φ k+1)))) p 0
    hnext hres (fun k => (hx (φ k)).2)
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.Convergence
namespace BregmanIneqMultCodex
variable {n m : ℕ}

theorem orthant_normal_nonpos_pairing (p w : E m)
    (hn : w ∈ normalCone (nonnegOrthant m) p) :
    (∀ i, w i ≤ 0) ∧ inner ℝ w p=0 := by
  classical
  have h0 := hn.2 0 (show (0 : E m) ∈ nonnegOrthant m by intro i; simp)
  have h2 := hn.2 (p+p) (show p+p ∈ nonnegOrthant m by intro i; exact add_nonneg (hn.1 i) (hn.1 i))
  simp only [zero_sub,inner_neg_right] at h0
  simp only [add_sub_cancel_left] at h2
  refine ⟨?_,by linarith⟩
  intro i
  have hq : p+EuclideanSpace.single i (1 : ℝ) ∈ nonnegOrthant m := by
    intro j
    change 0 ≤ p j+EuclideanSpace.single i (1 : ℝ) j
    apply add_nonneg (hn.1 j)
    simp only [EuclideanSpace.single_apply]
    split_ifs <;> norm_num
  have hi := hn.2 _ hq
  simpa [EuclideanSpace.inner_single_right] using hi

theorem run_constraint_bounds (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (S : Set (E m)) (h : E m → ℝ)
    (c : ℕ → ℝ) (x : ℕ → E n) (p : ℕ → E m)
    (hh : IsBregmanFunction S h) (hS : posOrthant m ⊆ S)
    (him : posOrthant m ⊆ gradient h '' S) (hc : ∀ k, 0 < c k)
    (hrun : IsIneqMultiplierRun C f g S h c x p) (k : ℕ) :
    p (k+1) ∈ nonnegOrthant m ∧
    (∀ i, gvec g (x (k+1)) i ≤ ((c k)⁻¹ • (gradient h (p (k+1))-gradient h (p k))) i) ∧
    inner ℝ (p (k+1)) (gvec g (x (k+1)))=
      inner ℝ (p (k+1)) ((c k)⁻¹ • (gradient h (p (k+1))-gradient h (p k))) := by
  let z := gradient h (p k)+c k • gvec g (x (k+1))
  have he : gradient (fun z => (monoConj h z).toReal) z=p (k+1) := (hrun k).2.2.2.symm
  have hps : gradient (fun z => (monoConj h z).toReal) z ∈ S := by rw [he]; exact (hrun (k+1)).1
  have hn := monoConj_projected_stationarity S h hh hS him z hps
  rw [he] at hn
  have hb := orthant_normal_nonpos_pairing _ _ hn
  refine ⟨hn.1,?_,?_⟩
  · intro i
    have hi := hb.1 i
    change gradient h (p k) i+c k*gvec g (x (k+1)) i-gradient h (p (k+1)) i ≤ 0 at hi
    change gvec g (x (k+1)) i ≤ (c k)⁻¹*(gradient h (p (k+1)) i-gradient h (p k) i)
    have hi' : c k*gvec g (x (k+1)) i ≤ gradient h (p (k+1)) i-gradient h (p k) i := by linarith
    have hmul := mul_le_mul_of_nonneg_left hi' (inv_nonneg.mpr (hc k).le)
    simpa only [← mul_assoc,inv_mul_cancel₀ (hc k).ne',one_mul] using hmul
  · have hi : inner ℝ (p (k+1)) (z-gradient h (p (k+1)))=0 := by
      rw [real_inner_comm]; exact hb.2
    dsimp only [z] at hi
    simp only [inner_sub_right,inner_add_right,inner_smul_right] at hi
    have heq : c k*inner ℝ (p (k+1)) (gvec g (x (k+1)))=
        inner ℝ (p (k+1)) (gradient h (p (k+1))-gradient h (p k)) := by
      simp only [inner_sub_right]; linarith
    rw [inner_smul_right,← heq,← mul_assoc,inv_mul_cancel₀ (hc k).ne',one_mul]
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.Convergence
namespace BregmanIneqMultCodex
variable {n m : ℕ}

theorem run_gradient_residual_zero (S : Set (E m)) (h : E m → ℝ)
    (c : ℕ → ℝ) (p : ℕ → E m) (pstar : E m)
    (hh : IsBregmanFunction S h) (hps : pstar ∈ S)
    (hc : ∀ k, 0 < c k) (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hp : Tendsto p atTop (𝓝 pstar)) :
    Tendsto (fun k => (c k)⁻¹ • (gradient h (p (k+1))-gradient h (p k))) atTop (𝓝 0) := by
  have hg := (BregmanPPACodex.gradient_continuous_in_zone S h hh hps).tendsto.comp hp
  have hdiff : Tendsto (fun k => gradient h (p (k+1))-gradient h (p k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,sub_self] using (hg.comp (tendsto_add_atTop_nat 1)).sub hg
  obtain ⟨ε,hε,hle⟩ := hcinf
  exact BregmanPPACodex.bounded_inverse_residual _ c ε hε hc hle hdiff

theorem run_complementarity_zero (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (S : Set (E m)) (h : E m → ℝ)
    (c : ℕ → ℝ) (x : ℕ → E n) (p : ℕ → E m) (pstar : E m)
    (hh : IsBregmanFunction S h) (hS : posOrthant m ⊆ S)
    (him : posOrthant m ⊆ gradient h '' S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hrun : IsIneqMultiplierRun C f g S h c x p) (hps : pstar ∈ S)
    (hp : Tendsto p atTop (𝓝 pstar)) :
    Tendsto (fun k => inner ℝ (p k) (gvec g (x k))) atTop (𝓝 0) := by
  have hr := run_gradient_residual_zero S h c p pstar hh hps hc hcinf hp
  have ht : Tendsto (fun k => inner ℝ (p (k+1)) ((c k)⁻¹ • (gradient h (p (k+1))-gradient h (p k)))) atTop
      (𝓝 (inner ℝ pstar 0)) := (hp.comp (tendsto_add_atTop_nat 1)).inner hr
  have he (k : ℕ) := (run_constraint_bounds C f g S h c x p hh hS him hc hrun k).2.2
  simp only [inner_zero_right] at ht
  simp_rw [← he] at ht
  exact (tendsto_add_atTop_iff_nat 1).mp ht

theorem run_eventually_mem (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (S : Set (E m)) (h : E m → ℝ)
    (c : ℕ → ℝ) (x : ℕ → E n) (p : ℕ → E m)
    (hrun : IsIneqMultiplierRun C f g S h c x p) : ∀ᶠ k in atTop, x k ∈ C := by
  rw [eventually_atTop]
  refine ⟨1,?_⟩
  intro k hk
  cases k with
  | zero => omega
  | succ j => exact (hrun j).2.1
end BregmanIneqMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.Convergence
namespace BregmanIneqMultCodex
variable {n m : ℕ}

theorem gvec_limit_on_C (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (hcont : ∀ i, ContinuousOn (g i) C) (xs : ℕ → E n) (xstar : E n)
    (hxstar : xstar ∈ C) (hx : Tendsto xs atTop (𝓝 xstar))
    (hxC : ∀ᶠ k in atTop, xs k ∈ C) :
    Tendsto (fun k => gvec g (xs k)) atTop (𝓝 (gvec g xstar)) := by
  have hw : Tendsto xs atTop (𝓝[C] xstar) := tendsto_nhdsWithin_iff.mpr ⟨hx,hxC⟩
  have hi (i : Fin m) : Tendsto (fun k => (g i (xs k)).toReal) atTop (𝓝 ((g i xstar).toReal)) :=
    (EReal.tendsto_toReal (hP.g_finite i xstar hxstar) ((hP.g_proper i).1 xstar)).comp
      ((hcont i xstar hxstar).tendsto.comp hw)
  have ht := tendsto_pi_nhds.mpr hi
  exact ((PiLp.homeomorph 2 (fun _ : Fin m => ℝ)).symm.continuous.tendsto _).comp ht

theorem original_primal_limit (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (S : Set (E m)) (h : E m → ℝ)
    (c : ℕ → ℝ) (x : ℕ → E n) (p : ℕ → E m) (pstar : E m)
    (hP : IsConvexProgram C f g) (hd : ∃ q, dualFn C f g q ≠ ⊥)
    (hh : IsBregmanFunction S h) (hS : posOrthant m ⊆ S)
    (him : posOrthant m ⊆ gradient h '' S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hrun : IsIneqMultiplierRun C f g S h c x p)
    (hcont : ∀ i, ContinuousOn (g i) C) (hSbar : nonnegOrthant m ⊆ S)
    (hoptimal : IsOptimalMultiplier C f g pstar) (hp : Tendsto p atTop (𝓝 pstar)) :
    ∀ (φ : ℕ → ℕ) (xstar : E n), StrictMono φ → Tendsto (x ∘ φ) atTop (𝓝 xstar) →
      xstar ∈ C ∧ (∀ i, g i xstar ≤ 0) ∧ inner ℝ pstar (gvec g xstar)=0 ∧
      (∀ y ∈ C, f xstar+((inner ℝ pstar (gvec g xstar) : ℝ) : EReal) ≤
        f y+((inner ℝ pstar (gvec g y) : ℝ) : EReal)) := by
  intro φ xstar hφ hx
  have hxe := hφ.tendsto_atTop.eventually (run_eventually_mem C f g S h c x p hrun)
  have hxC := hP.closed.mem_of_tendsto hx hxe
  have hgv := gvec_limit_on_C C f g hP hcont (x ∘ φ) xstar hxC hx hxe
  have hps : pstar ∈ S := hSbar hoptimal.1
  let R : ℕ → E m := fun k => (c k)⁻¹ • (gradient h (p (k+1))-gradient h (p k))
  have hr : Tendsto R atTop (𝓝 0) := run_gradient_residual_zero S h c p pstar hh hps hc hcinf hp
  have hrshift : Tendsto (fun k => R (k-1)) atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [Nat.add_sub_cancel] using hr
  have hbounds : ∀ᶠ k in atTop, ∀ i, gvec g (x k) i ≤ R (k-1) i := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    cases k with
    | zero => omega
    | succ j => simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel] using
        (run_constraint_bounds C f g S h c x p hh hS him hc hrun j).2.1
  have hfeasible : ∀ i, g i xstar ≤ 0 := by
    intro i
    have ha := (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).tendsto (gvec g xstar) |>.comp hgv
    have hb := (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).tendsto (0 : E m) |>.comp (hrshift.comp hφ.tendsto_atTop)
    have hi : gvec g xstar i ≤ 0 := le_of_tendsto_of_tendsto ha hb
      ((hφ.tendsto_atTop.eventually hbounds).mono (fun k hk => hk i))
    rw [← EReal.coe_toReal (hP.g_finite i xstar hxC) ((hP.g_proper i).1 xstar)]
    exact EReal.coe_le_coe_iff.mpr hi
  have hpair : inner ℝ pstar (gvec g xstar)=0 := by
    have hl : Tendsto (fun k => inner ℝ (p (φ k)) (gvec g (x (φ k)))) atTop
        (𝓝 (inner ℝ pstar (gvec g xstar))) := (hp.comp hφ.tendsto_atTop).inner hgv
    have hz := (run_complementarity_zero C f g S h c x p pstar hh hS him hc hcinf hrun hps hp).comp hφ.tendsto_atTop
    exact tendsto_nhds_unique hl hz
  refine ⟨hxC,hfeasible,hpair,?_⟩
  intro y hy
  have hmin : ∀ᶠ k in atTop, (f (x k)).toReal+inner ℝ (p k) (gvec g (x k)) ≤
      (f y).toReal+inner ℝ (p k) (gvec g y) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    cases k with
    | zero => omega
    | succ j => exact run_lagrangian_min C f g S h c x p hP hh hS him hc hrun j y hy
  have ht : Tendsto (fun k => (f y).toReal+inner ℝ (p (φ k)) (gvec g y)-inner ℝ (p (φ k)) (gvec g (x (φ k)))) atTop
      (𝓝 ((f y).toReal+inner ℝ pstar (gvec g y)-inner ℝ pstar (gvec g xstar))) :=
    (tendsto_const_nhds.add ((hp.comp hφ.tendsto_atTop).inner tendsto_const_nhds)).sub
      ((hp.comp hφ.tendsto_atTop).inner hgv)
  have he := (continuous_coe_real_ereal.tendsto _).comp ht
  have hbound : f xstar ≤ (((f y).toReal+inner ℝ pstar (gvec g y)-inner ℝ pstar (gvec g xstar) : ℝ) : EReal) := by
    change (xstar,(((f y).toReal+inner ℝ pstar (gvec g y)-inner ℝ pstar (gvec g xstar) : ℝ) : EReal)) ∈
      {a : E n × EReal | f a.1 ≤ a.2}
    apply hP.f_lsc.isClosed_epigraph.mem_of_tendsto (hx.prodMk_nhds he)
    filter_upwards [hφ.tendsto_atTop.eventually hmin,hxe] with k hk hkC
    change f (x (φ k)) ≤ (((f y).toReal+inner ℝ (p (φ k)) (gvec g y)-inner ℝ (p (φ k)) (gvec g (x (φ k))) : ℝ) : EReal)
    rw [← EReal.coe_toReal (hP.f_finite _ hkC) (hP.f_proper.1 _)]
    apply EReal.coe_le_coe_iff.mpr
    linarith
  have ex := EReal.coe_toReal (hP.f_finite xstar hxC) (hP.f_proper.1 xstar)
  have ey := EReal.coe_toReal (hP.f_finite y hy) (hP.f_proper.1 y)
  rw [← ex] at hbound
  have hir := EReal.coe_le_coe_iff.mp hbound
  rw [← ex,← ey,← EReal.coe_add,← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  linarith
end BregmanIneqMultCodex

end

set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult

/-- The limit point claim in the proof of Theorem 7, pp. 218–219. -/
theorem solution {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (S : Set (E m)) (h : E m → ℝ)
    (c : ℕ → ℝ) (x : ℕ → E n) (p : ℕ → E m) (pstar : E m)
    (hP : IsConvexProgram C f g)
    (hd : ∃ q : E m, dualFn C f g q ≠ ⊥)
    (hh : BregmanPPA.Convergence.IsBregmanFunction S h)
    (hS : posOrthant m ⊆ S)
    (him : posOrthant m ⊆ gradient h '' S)
    (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hrun : IsIneqMultiplierRun C f g S h c x p)
    (hcont : ∀ i, ContinuousOn (g i) C)
    (hSbar : nonnegOrthant m ⊆ S)
    (hoptimal : IsOptimalMultiplier C f g pstar)
    (hp : Tendsto p atTop (𝓝 pstar)) :
    ∀ (φ : ℕ → ℕ) (xstar : E n), StrictMono φ →
      Tendsto (x ∘ φ) atTop (𝓝 xstar) →
      xstar ∈ C ∧ (∀ i, g i xstar ≤ 0) ∧
      inner ℝ pstar (gvec g xstar) = 0 ∧
      (∀ y ∈ C,
        f xstar + ((inner ℝ pstar (gvec g xstar) : ℝ) : EReal) ≤
        f y + ((inner ℝ pstar (gvec g y) : ℝ) : EReal)) := by
  exact BregmanIneqMultCodex.original_primal_limit C f g S h c x p pstar hP hd hh hS him hc hcinf hrun hcont hSbar hoptimal hp




#print axioms solution
