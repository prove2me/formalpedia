-- Prove2me | solution 1 for CrossedProductGroups.Classification.corollary_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T03:05:48.04249+00:00
-- url     : https://prove2.me/submissions/fe8857c9-664b-4cde-9adf-514013dd4e52

import Definitions.Def_CrossedProductGroups_Classification_E2
import Theorems.Thm_CrossedProductGroups_Classification_lemma_1_2
import Theorems.Thm_CrossedProductGroups_Classification_theorem_1_3
import Theorems.Thm_CrossedProductGroups_Classification_theorem_2_1
import Theorems.Thm_CrossedProductGroups_Classification_corollary_2_2
import Mathlib.Algebra.Group.MinimalAxioms
set_option autoImplicit false

open CrossedProductGroups.Classification


theorem solution {H G : Type*} [Group H] [Group G]
    (α : G → MulAut H) (f : G → G → H) (hc : IsCrossedSystem α f) (hn : f 1 1 = 1)
    (α' : G → MulAut H) (f' : G → G → H) (hc' : IsCrossedSystem α' f') (hn' : f' 1 1 = 1) :
    ∃ e : {ψ : H × G → H × G // IsCrossedHom α f α' f' ψ} ≃
        {q : (H → H) × (G → H) × (G → G) × (H →* G) //
          IsMorphismQuadruple α f α' f' q.1 q.2.1 q.2.2.1 q.2.2.2},
      (∀ (u : H → H) (r : G → H) (v : G → G) (s : H →* G)
          (hq : IsMorphismQuadruple α f α' f' u r v s),
        (e.symm ⟨(u, r, v, s), hq⟩).1 =
          fun x : H × G => (u x.1 * α' (s x.1) (r x.2) * f' (s x.1) (v x.2), s x.1 * v x.2)) ∧
      ∀ (u : H → H) (r : G → H) (v : G → G) (s : H →* G),
        IsMorphismQuadruple α f α' f' u r v s → u 1 = 1 ∧ v 1 = 1 ∧ r 1 = 1 := by
  classical
  obtain ⟨hL,hA⟩ := (lemma_1_2 α f hc).2.2.2 hn
  obtain ⟨hL',hA'⟩ := (lemma_1_2 α' f' hc').2.2.2 hn'
  have hg := theorem_2_1 α f hc hn (H × G)
  have hfact (h : H) (g : G) : crossedMul α f (h,1) (1,g) = (h,g) := by
    simp [crossedMul,hA,(hL g).1]
  have unitlaws (u : H → H) (r : G → H) (v : G → G) (s : H →* G)
      (hq : IsMorphismQuadruple α f α' f' u r v s) : u 1 = 1 ∧ v 1 = 1 ∧ r 1 = 1 := by
    have hv : v 1 = 1 := by
      have hh := hq.cond1 1 1
      simp only [hn,map_one,one_mul] at hh
      exact mul_eq_right.mp hh
    have hu : u 1 = 1 := by
      have hh := hq.cond3 1 1
      simp only [one_mul,map_one,hA',hn',mul_one] at hh
      exact mul_eq_right.mp hh.symm
    have hr : r 1 = 1 := by
      have hh := hq.cond5 1 1
      simp only [hv,hn,map_one,hu,one_mul,hA',hn',mul_one] at hh
      exact mul_eq_right.mp hh
    exact ⟨hu,hv,hr⟩
  have hsrcunit : crossedMul α f (1,1) (1,1) = ((1,1) : H × G) := by simp [crossedMul,hn]
  have hstr := theorem_1_3 α' f'
  let e0 : H × G := ((f' 1 1)⁻¹,1)
  let iv : H × G → H × G := fun x => Classical.choose ((hstr.2 hc').2 x)
  letI : Mul (H × G) := ⟨crossedMul α' f'⟩
  letI : One (H × G) := ⟨e0⟩
  letI : Inv (H × G) := ⟨iv⟩
  let groupT : Group (H × G) := Group.ofLeftAxioms ((hstr.1).mpr hc')
    (fun x => ((hstr.2 hc').1 x).1) (fun x => (Classical.choose_spec ((hstr.2 hc').2 x)).1)
  letI : Group (H × G) := groupT
  letI : Monoid (H × G) := groupT.toMonoid
  letI : MulOneClass (H × G) := groupT.toMulOneClass
  letI : MulOne (H × G) := groupT.toMulOneClass.toMulOne
  letI : IsRightCancelMul (H × G) :=
    { mul_right_cancel := by
        intro right a b hh
        have hi := congrArg (fun z => crossedMul α' f' z (iv right)) hh
        have hz := (Classical.choose_spec ((hstr.2 hc').2 right)).2
        change crossedMul α' f' (crossedMul α' f' a right) (iv right) =
          crossedMul α' f' (crossedMul α' f' b right) (iv right) at hi
        rw [(hstr.1.mpr hc') a right (iv right),(hstr.1.mpr hc') b right (iv right),hz] at hi
        exact ((hstr.2 hc').1 a).2.symm.trans (hi.trans ((hstr.2 hc').1 b).2) }
  have hone : (1 : H × G) = ((1,1) : H × G) := by change ((f' 1 1)⁻¹,1) = (1,1); rw [hn',inv_one]
  have hchar := (corollary_2_2 α f hc hn (H × G)).1
  let Q := {q : (H → H) × (G → H) × (G → G) × (H →* G) //
    IsMorphismQuadruple α f α' f' q.1 q.2.1 q.2.2.1 q.2.2.2}
  let P := {ψ : H × G → H × G // IsCrossedHom α f α' f' ψ}
  have hψone (ψ : P) : ψ.val (1,1) = ((1,1) : H × G) := by
    have hh := ψ.property (1,1) (1,1)
    rw [hsrcunit] at hh
    change ψ.val (1,1) = ψ.val (1,1) * ψ.val (1,1) at hh
    exact (mul_eq_right.mp hh.symm).trans hone
  let sh (ψ : P) : H →* G :=
    { toFun := fun h => (ψ.val (h,1)).2
      map_one' := congrArg Prod.snd (hψone ψ)
      map_mul' := by
        intro h k
        have hh := congrArg Prod.snd (ψ.property (h,1) (k,1))
        rw [hg.1.1] at hh
        exact hh }
  have hfac (ψ : P) (h : H) (g : G) : ψ.val (h,g) =
      crossedMul α' f' (ψ.val (h,1)) (ψ.val (1,g)) := by
    rw [← ψ.property,hfact]
  have hmix (ψ : P) (g : G) (h : H) :
      crossedMul α' f' (ψ.val (1,g)) (ψ.val (h,1)) =
        crossedMul α' f' (ψ.val (α g h,1)) (ψ.val (1,g)) := by
    rw [← ψ.property,hg.1.2.2,ψ.property]
  have hgg (ψ : P) (g k : G) :
      crossedMul α' f' (ψ.val (1,g)) (ψ.val (1,k)) =
        crossedMul α' f' (ψ.val (f g k,1)) (ψ.val (1,g*k)) := by
    rw [← ψ.property,hg.1.2.1,ψ.property]
  let F : P → Q := fun ψ =>
    ⟨(fun h => (ψ.val (h,1)).1,fun g => (ψ.val (1,g)).1,
      fun g => (ψ.val (1,g)).2,sh ψ),
      { cond1 := fun g k => congrArg Prod.snd (hgg ψ g k)
        cond2 := fun g h => congrArg Prod.snd (hmix ψ g h)
        cond3 := fun h k => by
          have hh := congrArg Prod.fst (ψ.property (h,1) (k,1))
          rw [hg.1.1] at hh
          exact hh
        cond4 := fun g h => congrArg Prod.fst (hmix ψ g h).symm
        cond5 := fun g k => congrArg Prod.fst (hgg ψ g k) }⟩
  let Gq : Q → P := fun q => by
    let u := q.val.1
    let r := q.val.2.1
    let v := q.val.2.2.1
    let s := q.val.2.2.2
    have hu := (unitlaws u r v s q.property).1
    have hv := (unitlaws u r v s q.property).2.1
    have hr := (unitlaws u r v s q.property).2.2
    let U : H →* (H × G) :=
      { toFun := fun h => (u h,s h)
        map_one' := by rw [hone]; exact Prod.ext hu s.map_one
        map_mul' := fun h k => Prod.ext (q.property.cond3 h k) (s.map_mul h k) }
    let V : G → H × G := fun g => (r g,v g)
    let ψ : H × G → H × G := fun x =>
      (u x.1 * α' (s x.1) (r x.2) * f' (s x.1) (v x.2),s x.1*v x.2)
    refine ⟨ψ,?_⟩
    apply (hchar ψ).mpr
    refine ⟨U,V,?_,?_,fun _ _ => rfl⟩
    · intro g k
      exact Prod.ext (q.property.cond5 g k) (q.property.cond1 g k)
    · intro g h
      exact Prod.ext (q.property.cond4 g h).symm (q.property.cond2 g h)
  have hG (q : Q) (x : H × G) : (Gq q).val x =
      (q.val.1 x.1 * α' (q.val.2.2.2 x.1) (q.val.2.1 x.2) *
        f' (q.val.2.2.2 x.1) (q.val.2.2.1 x.2),q.val.2.2.2 x.1*q.val.2.2.1 x.2) := by rfl
  let e : P ≃ Q :=
    { toFun := F
      invFun := Gq
      left_inv := by
        intro ψ
        apply Subtype.ext
        funext x
        exact (hfac ψ x.1 x.2).symm
      right_inv := by
        intro q
        obtain ⟨hu,hv,hr⟩ := unitlaws q.val.1 q.val.2.1 q.val.2.2.1 q.val.2.2.2 q.property
        apply Subtype.ext
        apply Prod.ext
        · funext h
          change ((Gq q).val (h,1)).1 = q.val.1 h
          rw [hG]
          simp only [hr,hv,map_one,(hL' _).2,mul_one]
        · apply Prod.ext
          · funext g
            change ((Gq q).val (1,g)).1 = q.val.2.1 g
            rw [hG]
            simp only [hu,map_one,hA',(hL' _).1,one_mul,mul_one]
          · apply Prod.ext
            · funext g
              change ((Gq q).val (1,g)).2 = q.val.2.2.1 g
              rw [hG]
              simp only [map_one,one_mul]
            · apply MonoidHom.ext
              intro h
              change ((Gq q).val (h,1)).2 = q.val.2.2.2 h
              rw [hG]
              simp only [hv,mul_one] }
  exact ⟨e,fun _ _ _ _ _ => rfl,unitlaws⟩
