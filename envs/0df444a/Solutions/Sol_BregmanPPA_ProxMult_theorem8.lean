-- Prove2me | solution 1 for BregmanPPA.ProxMult.theorem8
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T01:11:20.708077+00:00
-- url     : https://prove2.me/submissions/4d2c4647-a5d0-4c8f-a57b-22839b2fb74b

import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_IneqMult_Program
import Definitions.Def_BregmanPPA_ProxMult_Saddle
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Mathlib
set_option autoImplicit false
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
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.ProxMult
namespace BregmanProxMultCodex
theorem original_eq14 {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (Sx : Set (BregmanPPA.IneqMult.E n)) (hx : BregmanPPA.IneqMult.E n → ℝ) (Sp : Set (BregmanPPA.IneqMult.E m)) (hp : BregmanPPA.IneqMult.E m → ℝ)
    (c : ℕ → ℝ) (x : ℕ → BregmanPPA.IneqMult.E n) (p : ℕ → BregmanPPA.IneqMult.E m)
    (hP : BregmanPPA.IneqMult.IsConvexProgram C f g) (hc : ∀ k, 0 < c k)
    (hhx : BregmanPPA.Convergence.IsBregmanFunction Sx hx) (hSx : C ⊆ Sx)
    (hhp : BregmanPPA.Convergence.IsBregmanFunction Sp hp) (hSp : BregmanPPA.IneqMult.nonnegOrthant m ⊆ Sp)
    (him : gradient hp '' Sp = Set.univ)
    (hrun : IsProxMultRun C f g Sx hx Sp hp c x p) :
    ∀ k, p (k + 1) ∈ BregmanPPA.IneqMult.nonnegOrthant m ∧
      (c k)⁻¹ • (gradient hx (x k) - gradient hx (x (k + 1)))
        ∈ subdiffX C f g (x (k + 1)) (p (k + 1)) := by
  intro k
  exact primal_step C f g Sx hx Sp hp (c k) (x k) (x (k+1)) (p k) (p (k+1))
    hP (hc k) hhx hSx hhp hSp him (hrun.2 k).2.1 (hrun.2 k).2.2.1 (hrun.2 k).2.2.2
end BregmanProxMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.ProxMult
namespace BregmanProxMultCodex
theorem original_eq13 {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (Sx : Set (BregmanPPA.IneqMult.E n)) (hx : BregmanPPA.IneqMult.E n → ℝ) (Sp : Set (BregmanPPA.IneqMult.E m)) (hp : BregmanPPA.IneqMult.E m → ℝ)
    (c : ℕ → ℝ) (x : ℕ → BregmanPPA.IneqMult.E n) (p : ℕ → BregmanPPA.IneqMult.E m)
    (hP : BregmanPPA.IneqMult.IsConvexProgram C f g) (hc : ∀ k, 0 < c k)
    (hhx : BregmanPPA.Convergence.IsBregmanFunction Sx hx) (hSx : C ⊆ Sx)
    (hhp : BregmanPPA.Convergence.IsBregmanFunction Sp hp) (hSp : BregmanPPA.IneqMult.nonnegOrthant m ⊆ Sp)
    (him : gradient hp '' Sp = Set.univ)
    (hrun : IsProxMultRun C f g Sx hx Sp hp c x p) :
    BregmanPPA.Convergence.IsBregmanPPARun (prodZone Sx Sp) (sumFn hx hp) (opK C f g) c
      (fun k => pair (x k) (p k)) := by
  have hxS : ∀ k, x k ∈ Sx := by
    intro k
    cases k with
    | zero => exact hrun.1
    | succ j => exact hSx (hrun.2 j).2.1
  have hxD (k : ℕ) : DifferentiableAt ℝ hx (x k) :=
    ((hhx.contDiffOn.differentiableOn (by simp)) (x k) (hxS k)).differentiableAt
      (hhx.isOpen.mem_nhds (hxS k))
  have hpD (k : ℕ) : DifferentiableAt ℝ hp (p k) :=
    ((hhp.contDiffOn.differentiableOn (by simp)) (p k) (hrun.2 k).1).differentiableAt
      (hhp.isOpen.mem_nhds (hrun.2 k).1)
  have hpos : posOrthant m ⊆ Sp := fun p h => hSp (fun i => (h i).le)
  have himpos : posOrthant m ⊆ gradient hp '' Sp := by rw [him]; exact Set.subset_univ _
  intro k
  refine ⟨⟨hxS k,(hrun.2 k).1⟩,?_⟩
  rw [sum_gradient_pair hx hp (x k) (p k) (hxD k) (hpD k),
    sum_gradient_pair hx hp (x (k+1)) (p (k+1)) (hxD (k+1)) (hpD (k+1))]
  change (c k)⁻¹ • (gradient hx (x k)-gradient hx (x (k+1))) ∈
      subdiffX C f g (x (k+1)) (p (k+1)) ∧
    -((c k)⁻¹ • (gradient hp (p k)-gradient hp (p (k+1)))) ∈
      supdiffP C f g (x (k+1)) (p (k+1))
  have hprimal := original_eq14 C f g Sx hx Sp hp c x p hP hc hhx hSx hhp hSp him hrun k
  refine ⟨hprimal.2,?_⟩
  let z := gradient hp (p k)+c k • gvec g (x (k+1))
  have hq := (hrun.2 k).2.2.2
  have hqS : gradient (fun w => (monoConj hp w).toReal) z ∈ Sp := by
    rw [← hq]
    exact (hrun.2 (k+1)).1
  have hstation := BregmanIneqMultCodex.monoConj_projected_stationarity Sp hp hhp hpos himpos z hqS
  rw [← hq] at hstation
  let u := (c k)⁻¹ • (z-gradient hp (p (k+1)))
  have hu : IsSubgradient (indicatorPos m) (p (k+1)) u := by
    apply (indicator_support (p (k+1)) u hprimal.1).mpr
    intro q hqN
    have hi := hstation.2 q hqN
    dsimp only [u]
    rw [inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (hc k).le) hi
  rw [original_supdiff_formula C f g hP (x (k+1)) (hrun.2 k).2.1 (p (k+1)) hprimal.1]
  refine ⟨u,hu,?_⟩
  dsimp only [u,z]
  simp only [smul_sub,smul_add,smul_smul,inv_mul_cancel₀ (hc k).ne',one_smul]
  module
end BregmanProxMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB ThreeOpSplitting.Convergence BregmanPPA.IneqMult BregmanPPA.ProxMult
namespace BregmanProxMultCodex

theorem saddle_value_finite {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (x : E n) (p : E m) (hs : IsSaddlePair C f g x p) :
    lagr C f g x p ≠ ⊤ ∧ lagr C f g x p ≠ ⊥ := by
  classical
  obtain ⟨y,hy⟩ := hP.nonempty
  have hz : (0 : E m) ∈ nonnegOrthant m := by simp [nonnegOrthant]
  have hyt : lagr C f g y p ≠ ⊤ := by
    by_cases hp : p ∈ nonnegOrthant m
    · simp only [lagr,if_pos hy,if_pos hp]
      exact EReal.add_ne_top (hP.f_finite y hy) (EReal.coe_ne_top _)
    · simp [lagr,hy,hp]
  have ht : lagr C f g x p ≠ ⊤ := by
    intro he
    have hi := (hs y p).2
    rw [he] at hi
    exact hyt (top_le_iff.mp hi)
  have hx : x ∈ C := by
    by_contra hn
    exact ht (by simp [lagr,hn])
  have hxb : lagr C f g x (0 : E m) ≠ ⊥ := by
    simpa [lagr,hx,hz] using hP.f_proper.1 x
  have hb : lagr C f g x p ≠ ⊥ := by
    intro he
    have hi := (hs x 0).1
    rw [he] at hi
    exact hxb (le_bot_iff.mp hi)
  exact ⟨ht,hb⟩

theorem original_saddle_iff_zero {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (hP : IsConvexProgram C f g)
    (x : E n) (p : E m) :
    IsSaddlePair C f g x p ↔ pair x p ∈ zer (opK C f g) := by
  change IsSaddlePair C f g x p ↔
    IsSubgradient (fun y => lagr C f g y p) x 0 ∧
    IsSubgradient (fun q => -lagr C f g x q) p (-(-0))
  simp only [neg_zero]
  constructor
  · intro hs
    obtain ⟨ht,hb⟩ := saddle_value_finite C f g hP x p hs
    refine ⟨⟨ht,?_⟩,⟨?_,?_⟩⟩
    · intro y
      simpa using (hs y p).2
    · exact fun he => hb (EReal.neg_eq_top_iff.mp he)
    · intro q
      simpa using EReal.neg_le_neg_iff.mpr ((hs x q).1)
  · rintro ⟨⟨ht,hmin⟩,⟨hb,hmax⟩⟩ y q
    refine ⟨?_,?_⟩
    · have hi := hmax q
      simpa using hi
    · simpa using hmin y
end BregmanProxMultCodex

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
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence InertialFB.IFB
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem bregman_self (h : H → ℝ) (y : H) : bregmanD h y y = 0 := by simp [bregmanD]

theorem symmetrized_bregman (h : H → ℝ) (y p : H) :
    inner ℝ (gradient h y-gradient h p) (y-p) = bregmanD h y p+bregmanD h p y := by
  have hid := three_point_identity h y y p
  simp only [bregman_self] at hid
  have he : inner ℝ (p-y) (gradient h y-gradient h p) =
      -inner ℝ (gradient h y-gradient h p) (y-p) := by
    rw [← neg_sub y p,inner_neg_left]
    have hc : inner ℝ (y-p) (gradient h y-gradient h p) =
        inner ℝ (gradient h y-gradient h p) (y-p) := real_inner_comm _ _
    rw [hc]
  rw [he] at hid
  linarith

theorem subgradient_step_decrease (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h)
    (f : H → EReal) (hproper : IsProperFn f) (y p : H) (c : ℝ) (hc : 0 < c)
    (hy : y ∈ S) (hp : p ∈ S) (hfy : f y ≠ ⊤)
    (hsub : IsSubgradient f p (c⁻¹ • (gradient h y-gradient h p))) :
    (f p).toReal ≤ (f y).toReal := by
  have hg := subgradient_real_comparison f hproper hsub hfy
  rw [real_inner_smul_left,symmetrized_bregman] at hg
  have hD1 := bregman_nonneg S h hh (subset_closure hy) hp
  have hD2 := bregman_nonneg S h hh (subset_closure hp) hy
  have hn := mul_nonneg (inv_pos.mpr hc).le (add_nonneg hD1 hD2)
  linarith

theorem subgradient_step_gap (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h)
    (f : H → EReal) (hproper : IsProperFn f) (z y p : H) (c : ℝ) (hc : 0 < c)
    (hy : y ∈ S) (hp : p ∈ S) (hfz : f z ≠ ⊤)
    (hsub : IsSubgradient f p (c⁻¹ • (gradient h y-gradient h p))) :
    c*((f p).toReal-(f z).toReal) ≤ bregmanD h z y-bregmanD h z p := by
  have hg := subgradient_real_comparison f hproper hsub hfz
  rw [real_inner_smul_left] at hg
  have he : inner ℝ (gradient h y-gradient h p) (z-p) =
      -inner ℝ (p-z) (gradient h y-gradient h p) := by
    rw [← neg_sub p z,inner_neg_right]
    have he' : inner ℝ (gradient h y-gradient h p) (p-z) =
        inner ℝ (p-z) (gradient h y-gradient h p) := real_inner_comm _ _
    rw [he']
  rw [he] at hg
  have hg' : (f p).toReal-(f z).toReal ≤ c⁻¹*inner ℝ (p-z) (gradient h y-gradient h p) := by
    linarith
  have ht := mul_le_mul_of_nonneg_left hg' hc.le
  simp only [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul] at ht
  rw [← three_point_identity h z y p] at ht
  have hn := bregman_nonneg S h hh (subset_closure hp) hy
  linarith
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology Finset
namespace BregmanPPACodex

/-- Real gap telescoping follows the checked objective-rate pattern from the preceding Martinet lane. -/
theorem real_gap_sum_bound (v d : ℕ → ℝ) (m ε : ℝ)
    (hstep : ∀ k, ε*(v (k+1)-m) ≤ d k-d (k+1)) (N : ℕ) :
    (∑ k ∈ range N, ε*(v (k+1)-m))+d N ≤ d 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have hs := hstep N
    linarith

theorem real_gap_rate (v d : ℕ → ℝ) (m ε : ℝ) (hε : 0 < ε)
    (hanti : Antitone v) (hd : ∀ k, 0 ≤ d k)
    (hstep : ∀ k, ε*(v (k+1)-m) ≤ d k-d (k+1)) (N : ℕ) (hN : 0 < N) :
    v N-m ≤ (d 0/ε)/(N : ℝ) := by
  have hsum := real_gap_sum_bound v d m ε hstep N
  have hlower : (N : ℝ)*ε*(v N-m) ≤ ∑ k ∈ range N, ε*(v (k+1)-m) := by
    calc
      _ = ∑ k ∈ range N, ε*(v N-m) := by simp <;> ring
      _ ≤ _ := sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left
        (sub_le_sub_right (hanti (by have := mem_range.mp hk; omega)) m) hε.le)
  apply (le_div_iff₀ (by exact_mod_cast hN : 0 < (N : ℝ))).mpr
  apply (le_div_iff₀ hε).mpr
  nlinarith [hd N]

theorem real_gap_tendsto (v d : ℕ → ℝ) (m ε : ℝ) (hε : 0 < ε)
    (hanti : Antitone v) (hlower : ∀ k, m ≤ v k) (hd : ∀ k, 0 ≤ d k)
    (hstep : ∀ k, ε*(v (k+1)-m) ≤ d k-d (k+1)) : Tendsto v atTop (𝓝 m) := by
  have ht : Tendsto (fun N : ℕ => m+(d 0/ε)/(N : ℝ)) atTop (𝓝 m) := by
    have hm : Tendsto (fun _ : ℕ => m) atTop (𝓝 m) := tendsto_const_nhds
    simpa using hm.add (tendsto_const_div_atTop_nhds_zero_nat (d 0/ε))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Eventually.of_forall hlower
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hrate := real_gap_rate v d m ε hε hanti hd hstep N (by omega)
    linarith
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence InertialFB.IFB
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Objective convergence begins at x1, allowing the original x0 objective to be infinite. -/
theorem subgradient_objective_limit (T : H → Set H) (S : Set H) (h : H → ℝ)
    (c : ℕ → ℝ) (x : ℕ → H) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k) (hx : IsBregmanPPARun S h T c x)
    (f : H → EReal) (hproper : IsProperFn f) (hTeq : T = subdiffOp f)
    (z : H) (hz : z ∈ zer T) : Tendsto (fun k => f (x k)) atTop (𝓝 (f z)) := by
  have hsub (k : ℕ) : IsSubgradient f (x (k+1))
      ((c k)⁻¹ • (gradient h (x k)-gradient h (x (k+1)))) := by
    have hu := (hx k).2
    rw [hTeq] at hu
    exact hu
  have hzero : IsSubgradient f z 0 := by
    simpa only [hTeq,zer,subdiffOp,Set.mem_ofPred_eq] using hz
  let v : ℕ → ℝ := fun k => (f (x (k+1))).toReal
  let d : ℕ → ℝ := fun k => bregmanD h z (x (k+1))
  let m : ℝ := (f z).toReal
  obtain ⟨ε,hε,hle⟩ := hcinf
  have hlower (k : ℕ) : m ≤ v k :=
    zero_subgradient_real_min f hproper hzero (hsub k).1
  have hanti : Antitone v := by
    apply antitone_nat_of_succ_le
    intro k
    exact subgradient_step_decrease S h hh f hproper (x (k+1)) (x ((k+1)+1))
      (c (k+1)) (hc (k+1)) (hx (k+1)).1 (hx ((k+1)+1)).1 (hsub k).1 (hsub (k+1))
  have hd (k : ℕ) : 0 ≤ d k :=
    bregman_nonneg S h hh (zero_mem_closure T S hdom hz) (hx (k+1)).1
  have hstep (k : ℕ) : ε*(v (k+1)-m) ≤ d k-d (k+1) := by
    have hgap := subgradient_step_gap S h hh f hproper z (x (k+1)) (x ((k+1)+1))
      (c (k+1)) (hc (k+1)) (hx (k+1)).1 (hx ((k+1)+1)).1 hzero.1 (hsub (k+1))
    have hmul := mul_le_mul_of_nonneg_right (hle (k+1)) (sub_nonneg.mpr (hlower (k+1)))
    exact hmul.trans hgap
  have hreal := real_gap_tendsto v d m ε hε hanti hlower hd hstep
  have hE := (continuous_coe_real_ereal.tendsto m).comp hreal
  have hF (k : ℕ) : (v k : EReal) = f (x (k+1)) :=
    EReal.coe_toReal (hsub k).1 (hproper.1 _)
  have hM : (m : EReal) = f z := EReal.coe_toReal hzero.1 (hproper.1 z)
  change Tendsto (fun k => (v k : EReal)) atTop (𝓝 (m : EReal)) at hE
  simp_rw [hF,hM] at hE
  exact (tendsto_add_atTop_iff_nat 1).mp hE

/-- The original C2 cluster case permits a limit on the boundary of the open zone. -/
theorem subgradient_cluster_zero (T : H → Set H) (S : Set H) (h : H → ℝ)
    (c : ℕ → ℝ) (x : ℕ → H) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k) (hx : IsBregmanPPARun S h T c x)
    (f : H → EReal) (hproper : IsProperFn f) (hf : LowerSemicontinuous f)
    (hTeq : T = subdiffOp f) (hz : (zer T).Nonempty)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (p : H) (hlim : Tendsto (x ∘ φ) atTop (𝓝 p)) :
    p ∈ zer T := by
  obtain ⟨z,hz⟩ := hz
  have hm := subgradient_objective_limit T S h c x hh hdom hc hcinf hx f hproper hTeq z hz
  have hbound : f p ≤ f z := lsc_objective_limit f hf (x ∘ φ) p (f z) hlim
    (by simpa only [Function.comp_def] using hm.comp hφ.tendsto_atTop)
  have hzero : IsSubgradient f z 0 := by
    simpa only [hTeq,zer,subdiffOp,Set.mem_ofPred_eq] using hz
  have hmin (v : H) : f z ≤ f v := by simpa using hzero.2 v
  have hp := zero_subgradient_of_min f (ne_top_of_le_ne_top hzero.1 hbound)
    (fun v => hbound.trans (hmin v))
  change (0 : H) ∈ T p
  rw [hTeq]
  exact hp
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence InertialFB.IFB
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem step2 (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hx : IsBregmanPPARun S h T c x)
    (hC : closure (dom T) ⊆ S ∨ ∃ f : H → EReal,
      IsProperFn f ∧ IsConvexFn f ∧ LowerSemicontinuous f ∧ T = subdiffOp f)
    (hz : (zer T).Nonempty) :
    ∀ (p : H) (φ : ℕ → ℕ), StrictMono φ → Tendsto (x ∘ φ) atTop (𝓝 p) → p ∈ zer T := by
  intro p φ hφ hlim
  rcases hC with hC1 | ⟨f,hproper,hconv,hf,hTeq⟩
  · exact interior_cluster_zero T S h c x hT hh hdom hc hcinf hx hz hC1 φ hφ p hlim
  · exact subgradient_cluster_zero T S h c x hh hdom hc hcinf hx f hproper hf hTeq hz φ hφ p hlim
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence InertialFB.IFB
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem step3 (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hx : IsBregmanPPARun S h T c x)
    (hC : closure (dom T) ⊆ S ∨ ∃ f : H → EReal,
      IsProperFn f ∧ IsConvexFn f ∧ LowerSemicontinuous f ∧ T = subdiffOp f)
    (x' : H) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (x ∘ φ) atTop (𝓝 x')) (hzero : x' ∈ zer T) :
    Tendsto x atTop (𝓝 x') := by
  have hzc := zero_mem_closure T S hdom hzero
  have hanti := distance_antitone T S h c x hT.1 hh hc hx x' hzero
  have hDφ := hh.tendsto_zero (x ∘ φ) x' (fun k => (hx (φ k)).1) hlim
  have hD : Tendsto (fun k => bregmanD h x' (x k)) atTop (𝓝 0) := by
    apply (tendsto_iff_tendsto_subseq_of_antitone hanti hφ.tendsto_atTop).mpr
    simpa only [Function.comp_def] using hDφ
  have hb := (step1 T S h c x hT hh hdom hc hcinf hx x' hzero).2.2
  apply hb.isCompact_closure.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall (fun k => subset_closure (Set.mem_range_self k)))
  intro u _ hu
  obtain ⟨ψ,hψ,hψlim⟩ := hu.tendsto_subseq
  have huc : u ∈ closure S := isClosed_closure.mem_of_tendsto hψlim
    (Eventually.of_forall (fun k => subset_closure (hx (ψ k)).1))
  have hDψ : Tendsto (fun k => bregmanD h x' ((x ∘ ψ) k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using hD.comp hψ.tendsto_atTop
  have hconst : Tendsto (fun _ : ℕ => x') atTop (𝓝 u) :=
    hh.tendsto_of_zero (fun _ => x') (x ∘ ψ) u (fun _ => hzc)
      (fun k => (hx (ψ k)).1) hψlim huc (by simp) hDψ
  exact tendsto_nhds_unique hconst tendsto_const_nhds
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence InertialFB.IFB
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The exact first conclusion of the original root, with both original hC alternatives. -/
theorem convergence_when_zero (T : H → Set H) (S : Set H) (h : H → ℝ)
    (c : ℕ → ℝ) (x : ℕ → H) (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k) (hx : IsBregmanPPARun S h T c x)
    (hC : closure (dom T) ⊆ S ∨ ∃ f : H → EReal,
      IsProperFn f ∧ IsConvexFn f ∧ LowerSemicontinuous f ∧ T = subdiffOp f) :
    (zer T).Nonempty → ∃ z : H, z ∈ zer T ∧ Tendsto x atTop (𝓝 z) := by
  intro hz
  obtain ⟨z,hz0⟩ := hz
  have hb := (step1 T S h c x hT hh hdom hc hcinf hx z hz0).2.2
  obtain ⟨p,_,φ,hφ,hlim⟩ := tendsto_subseq_of_bounded hb (fun k => Set.mem_range_self k)
  have hp := step2 T S h c x hT hh hdom hc hcinf hx hC ⟨z,hz0⟩ p φ hφ hlim
  exact ⟨p,hp,step3 T S h c x hT hh hdom hc hcinf hx hC p φ hφ hlim hp⟩
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology Finset
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
noncomputable def prefix_weight (c : ℕ → ℝ) (N : ℕ) : ℝ := ∑ k ∈ range N, c k
noncomputable def weighted_mean (c : ℕ → ℝ) (x : ℕ → H) (N : ℕ) : H :=
  (prefix_weight c N)⁻¹ • ∑ k ∈ range N, c k • x (k+1)

theorem prefix_weight_lower (c : ℕ → ℝ) (ε : ℝ) (hle : ∀ k, ε ≤ c k) (N : ℕ) :
    ε*(N : ℝ) ≤ prefix_weight c N := by
  calc
    _ = ∑ k ∈ range N, ε := by simp <;> ring
    _ ≤ _ := sum_le_sum (fun k _ => hle k)

theorem prefix_weight_pos (c : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hle : ∀ k, ε ≤ c k) (N : ℕ) (hN : 0 < N) : 0 < prefix_weight c N :=
  lt_of_lt_of_le (mul_pos hε (by exact_mod_cast hN)) (prefix_weight_lower c ε hle N)

theorem weighted_mean_norm_bound (c : ℕ → ℝ) (x : ℕ → H) (ε R : ℝ)
    (hc : ∀ k, 0 < c k) (hε : 0 < ε) (hle : ∀ k, ε ≤ c k) (hR : 0 ≤ R)
    (hx : ∀ k, ‖x (k+1)‖ ≤ R) (N : ℕ) : ‖weighted_mean c x N‖ ≤ R := by
  by_cases hN : N=0
  · subst N; simpa [weighted_mean,prefix_weight] using hR
  have hW := prefix_weight_pos c ε hε hle N (by omega)
  have hs : ‖∑ k ∈ range N, c k • x (k+1)‖ ≤ prefix_weight c N*R := by
    calc
      _ ≤ ∑ k ∈ range N, ‖c k • x (k+1)‖ := norm_sum_le _ _
      _ = ∑ k ∈ range N, c k*‖x (k+1)‖ := sum_congr rfl (fun k _ => by
        rw [norm_smul,Real.norm_of_nonneg (hc k).le])
      _ ≤ ∑ k ∈ range N, c k*R := sum_le_sum (fun k _ =>
        mul_le_mul_of_nonneg_left (hx k) (hc k).le)
      _ = prefix_weight c N*R := by simp only [prefix_weight,sum_mul]
  rw [weighted_mean,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hW).le]
  calc
    _ ≤ (prefix_weight c N)⁻¹*(prefix_weight c N*R) :=
      mul_le_mul_of_nonneg_left hs (inv_pos.mpr hW).le
    _ = R := by rw [← mul_assoc,inv_mul_cancel₀ hW.ne',one_mul]

theorem graph_prefix_energy (T : H → Set H) (S : Set H) (h : H → ℝ)
    (c : ℕ → ℝ) (x : ℕ → H) (hT : IsMonotoneOp T) (hh : IsBregmanFunction S h)
    (hc : ∀ k, 0 < c k) (hx : IsBregmanPPARun S h T c x)
    (v w : H) (hw : w ∈ T v) (N : ℕ) :
    (∑ k ∈ range N, c k*inner ℝ w (x (k+1)-v))+bregmanD h v (x N) ≤ bregmanD h v (x 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have ht := weighted_graph_comparison T h hT v w (x N) (x (N+1)) (c N) (hc N) hw (hx N).2
    have hn := bregman_nonneg S h hh (subset_closure (hx (N+1)).1) (hx N).1
    linarith

theorem weighted_mean_pairing (c : ℕ → ℝ) (x : ℕ → H) (v w : H) (N : ℕ)
    (hW : 0 < prefix_weight c N) :
    prefix_weight c N*inner ℝ w (weighted_mean c x N-v) =
      ∑ k ∈ range N, c k*inner ℝ w (x (k+1)-v) := by
  simp only [weighted_mean,inner_sub_right,inner_smul_right,inner_sum,mul_sub,
    sum_sub_distrib,← sum_mul]
  rw [← mul_assoc,mul_inv_cancel₀ hW.ne',one_mul]
  rfl

theorem weighted_mean_graph_bound (T : H → Set H) (S : Set H) (h : H → ℝ)
    (c : ℕ → ℝ) (x : ℕ → H) (hT : IsMonotoneOp T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k) (hx : IsBregmanPPARun S h T c x)
    (ε : ℝ) (hε : 0 < ε) (hle : ∀ k, ε ≤ c k) (v w : H) (hw : w ∈ T v)
    (N : ℕ) (hN : 0 < N) :
    inner ℝ w (weighted_mean c x N-v) ≤ (bregmanD h v (x 0)/ε)/(N : ℝ) := by
  have hW := prefix_weight_pos c ε hε hle N hN
  have hvc : v ∈ closure S := hdom ⟨w,hw⟩
  have hB := bregman_nonneg S h hh hvc (hx 0).1
  have hBN := bregman_nonneg S h hh hvc (hx N).1
  have hsum := graph_prefix_energy T S h c x hT hh hc hx v w hw N
  have hpair := weighted_mean_pairing c x v w N hW
  have hfirst : inner ℝ w (weighted_mean c x N-v) ≤ bregmanD h v (x 0)/prefix_weight c N := by
    apply (le_div_iff₀ hW).mpr
    nlinarith
  have hden := div_le_div_of_nonneg_left hB (mul_pos hε (by exact_mod_cast hN))
    (prefix_weight_lower c ε hle N)
  exact hfirst.trans (by simpa only [div_div] using hden)

theorem zero_of_bounded_run (T : H → Set H) (S : Set H) (h : H → ℝ)
    (c : ℕ → ℝ) (x : ℕ → H) (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k) (hx : IsBregmanPPARun S h T c x)
    (hb : Bornology.IsBounded (Set.range x)) : (zer T).Nonempty := by
  obtain ⟨ε,hε,hle⟩ := hcinf
  obtain ⟨R,hR,hRx⟩ := hb.exists_pos_norm_le
  have hbmean : Bornology.IsBounded (Set.range (weighted_mean c x)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨R, ?_⟩
    rintro _ ⟨N,rfl⟩
    exact weighted_mean_norm_bound c x ε R hc hε hle hR.le
      (fun k => hRx _ (Set.mem_range_self (k+1))) N
  obtain ⟨u,_,φ,hφ,hlim⟩ := tendsto_subseq_of_bounded hbmean (fun k => Set.mem_range_self k)
  refine ⟨u, ?_⟩
  apply maximal_related_point T hT u 0
  intro v w hw
  have hev : ∀ᶠ N in atTop, inner ℝ w (weighted_mean c x N-v) ≤
      (bregmanD h v (x 0)/ε)/(N : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact weighted_mean_graph_bound T S h c x hT.1 hh hdom hc hx ε hε hle v w hw N (by omega)
  have hi : Tendsto (fun k => inner ℝ w (weighted_mean c x (φ k)-v)) atTop
      (𝓝 (inner ℝ w (u-v))) := tendsto_const_nhds.inner (hlim.sub_const v)
  have hz : Tendsto (fun k => (bregmanD h v (x 0)/ε)/(φ k : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat _).comp hφ.tendsto_atTop
  have hu : inner ℝ w (u-v) ≤ 0 := le_of_tendsto_of_tendsto hi hz
    (hφ.tendsto_atTop.eventually hev)
  rw [zero_sub,inner_neg_right]
  have he : inner ℝ (u-v) w = inner ℝ w (u-v) := real_inner_comm _ _
  rw [he]
  linarith
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence InertialFB.IFB
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem theorem1 (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hx : IsBregmanPPARun S h T c x)
    (hC : closure (dom T) ⊆ S ∨ ∃ f : H → EReal,
      IsProperFn f ∧ IsConvexFn f ∧ LowerSemicontinuous f ∧ T = subdiffOp f) :
    ((zer T).Nonempty → ∃ z : H, z ∈ zer T ∧ Tendsto x atTop (𝓝 z)) ∧
    (zer T = ∅ → closure (dom T) ⊆ S → ¬ Bornology.IsBounded (Set.range x)) := by
  constructor
  · exact convergence_when_zero T S h c x hT hh hdom hc hcinf hx hC
  · intro hnone hC1 hb
    obtain ⟨u,hu⟩ := zero_of_bounded_run T S h c x hT hh hdom hc hcinf hx hb
    simpa [hnone] using hu
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.ProxMult
open ThreeOpSplitting.Convergence
namespace BregmanProxMultCodex

/-- Theorem 8, pp. 220–221 (first two sentences): along a run of the nonquadratic proximal
method of multipliers (12), if (10) has a saddle pair (an optimal solution–Lagrange multiplier
pair), then `(x^k, p^k)` converges to one; if it has none, `{x^k}` or `{p^k}` is unbounded. -/
theorem original_theorem8 {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (Sx : Set (BregmanPPA.IneqMult.E n)) (hx : BregmanPPA.IneqMult.E n → ℝ) (Sp : Set (BregmanPPA.IneqMult.E m)) (hp : BregmanPPA.IneqMult.E m → ℝ)
    (c : ℕ → ℝ) (x : ℕ → BregmanPPA.IneqMult.E n) (p : ℕ → BregmanPPA.IneqMult.E m)
    (hP : BregmanPPA.IneqMult.IsConvexProgram C f g)
    (hc : ∀ k, 0 < c k) (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hhx : BregmanPPA.Convergence.IsBregmanFunction Sx hx) (hSx : C ⊆ Sx)
    (hhp : BregmanPPA.Convergence.IsBregmanFunction Sp hp) (hSp : BregmanPPA.IneqMult.nonnegOrthant m ⊆ Sp)
    (him : gradient hp '' Sp = Set.univ)
    (hrun : IsProxMultRun C f g Sx hx Sp hp c x p) :
    ((∃ x' p', IsSaddlePair C f g x' p') →
      ∃ x' p', IsSaddlePair C f g x' p' ∧
        Tendsto x atTop (𝓝 x') ∧ Tendsto p atTop (𝓝 p')) ∧
    ((¬ ∃ x' p', IsSaddlePair C f g x' p') →
      ¬ Bornology.IsBounded (Set.range x) ∨ ¬ Bornology.IsBounded (Set.range p)) := by
  have hclose := opK_closure_subset C f g Sx Sp hP.closed hSx hSp
  have hdom : dom (opK C f g) ⊆ closure (prodZone Sx Sp) :=
    fun z hz => subset_closure (hclose (subset_closure hz))
  have ht := BregmanPPACodex.theorem1 (opK C f g) (prodZone Sx Sp) (sumFn hx hp)
    c (fun k => pair (x k) (p k)) (original_K_maximal C f g hP)
    (product_bregman Sx Sp hx hp hhx hhp) hdom hc hcinf
    (original_eq13 C f g Sx hx Sp hp c x p hP hc hhx hSx hhp hSp him hrun) (Or.inl hclose)
  constructor
  · rintro ⟨a,b,hs⟩
    have hzero : (zer (opK C f g)).Nonempty :=
      ⟨pair a b,(original_saddle_iff_zero C f g hP a b).mp hs⟩
    obtain ⟨z,hz,hconv⟩ := ht.1 hzero
    refine ⟨z.ofLp.1,z.ofLp.2,(original_saddle_iff_zero C f g hP _ _).mpr hz,?_,?_⟩
    · exact ((WithLp.fstL 2 ℝ (BregmanPPA.IneqMult.E n) (BregmanPPA.IneqMult.E m)).continuous.tendsto z).comp hconv
    · exact ((WithLp.sndL 2 ℝ (BregmanPPA.IneqMult.E n) (BregmanPPA.IneqMult.E m)).continuous.tendsto z).comp hconv
  · intro hnone
    have he : zer (opK C f g)=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hnone ⟨z.ofLp.1,z.ofLp.2,(original_saddle_iff_zero C f g hP _ _).mpr hz⟩
    by_cases hxB : Bornology.IsBounded (Set.range x)
    · right
      intro hpB
      apply ht.2 he hclose
      apply (packed_bounded_iff _).mpr
      constructor
      · apply hxB.subset
        rintro _ ⟨z,⟨k,rfl⟩,rfl⟩
        exact ⟨k,rfl⟩
      · apply hpB.subset
        rintro _ ⟨z,⟨k,rfl⟩,rfl⟩
        exact ⟨k,rfl⟩
    · exact Or.inl hxB

end BregmanProxMultCodex


end

set_option autoImplicit false
open Filter Topology BregmanPPA.ProxMult ThreeOpSplitting.Convergence

/-- Theorem 8, pp. 220–221 (first two sentences): along a run of the nonquadratic proximal
method of multipliers (12), if (10) has a saddle pair (an optimal solution–Lagrange multiplier
pair), then `(x^k, p^k)` converges to one; if it has none, `{x^k}` or `{p^k}` is unbounded. -/
theorem solution {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (Sx : Set (BregmanPPA.IneqMult.E n)) (hx : BregmanPPA.IneqMult.E n → ℝ) (Sp : Set (BregmanPPA.IneqMult.E m)) (hp : BregmanPPA.IneqMult.E m → ℝ)
    (c : ℕ → ℝ) (x : ℕ → BregmanPPA.IneqMult.E n) (p : ℕ → BregmanPPA.IneqMult.E m)
    (hP : BregmanPPA.IneqMult.IsConvexProgram C f g)
    (hc : ∀ k, 0 < c k) (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hhx : BregmanPPA.Convergence.IsBregmanFunction Sx hx) (hSx : C ⊆ Sx)
    (hhp : BregmanPPA.Convergence.IsBregmanFunction Sp hp) (hSp : BregmanPPA.IneqMult.nonnegOrthant m ⊆ Sp)
    (him : gradient hp '' Sp = Set.univ)
    (hrun : IsProxMultRun C f g Sx hx Sp hp c x p) :
    ((∃ x' p', IsSaddlePair C f g x' p') →
      ∃ x' p', IsSaddlePair C f g x' p' ∧
        Tendsto x atTop (𝓝 x') ∧ Tendsto p atTop (𝓝 p')) ∧
    ((¬ ∃ x' p', IsSaddlePair C f g x' p') →
      ¬ Bornology.IsBounded (Set.range x) ∨ ¬ Bornology.IsBounded (Set.range p)) := by
  exact BregmanProxMultCodex.original_theorem8 C f g Sx hx Sp hp c x p hP hc hcinf hhx hSx hhp hSp him hrun




#print axioms solution
