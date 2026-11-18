-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.path_law_sampling
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T18:06:46.417197+00:00
-- url     : https://prove2.me/submissions/3ec5eef5-f826-4e3d-84ba-0ae2f6052a48

import Mathlib
import Definitions.Def_EdgeSublinearMWIS_Main_Paths

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.FiniteLaw

structure Law (Ω : Type) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω,0 ≤ mass ω
  total : (∑ ω,mass ω)=1

variable {Ω A : Type} [Fintype Ω] [Fintype A]

 def expect (μ : Law Ω) (f : Ω → ℝ) : ℝ := ∑ ω,μ.mass ω*f ω
 def prob (μ : Law Ω) (E : Ω → Prop) : ℝ := expect μ (fun ω => if E ω then 1 else 0)

 theorem expect_one (μ : Law Ω) : expect μ (fun _ => 1)=1 := by simpa only [expect,mul_one] using μ.total
 theorem expect_add (μ : Law Ω) (f g : Ω → ℝ) : expect μ (fun ω => f ω+g ω)=expect μ f+expect μ g := by
  simp only [expect,mul_add,Finset.sum_add_distrib]
 theorem expect_nonneg (μ : Law Ω) (f : Ω → ℝ) (hf : ∀ ω,0 ≤ f ω) : 0 ≤ expect μ f :=
  Finset.sum_nonneg (fun ω _ => mul_nonneg (μ.nonneg ω) (hf ω))
 theorem expect_mono (μ : Law Ω) (f g : Ω → ℝ) (h : ∀ ω,f ω ≤ g ω) : expect μ f ≤ expect μ g :=
  Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω))

 theorem prob_nonneg (μ : Law Ω) (E : Ω → Prop) : 0 ≤ prob μ E := by
  apply expect_nonneg
  intro ω
  split_ifs <;> norm_num

 theorem prob_union (μ : Law Ω) (E F : Ω → Prop) : prob μ (fun ω => E ω ∨ F ω) ≤ prob μ E+prob μ F := by
  rw [prob,prob,prob,←expect_add]
  apply expect_mono
  intro ω
  by_cases he : E ω <;> by_cases hf : F ω <;> simp [he,hf]

 theorem markov (μ : Law Ω) (f : Ω → ℝ) (hf : ∀ ω,0 ≤ f ω) (a : ℝ) (ha : 0 < a) :
    prob μ (fun ω => a ≤ f ω) ≤ expect μ f/a := by
  apply (le_div_iff₀ ha).mpr
  unfold prob expect
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hh : a ≤ f ω
  · simpa only [hh,↓reduceIte,mul_one] using mul_le_mul_of_nonneg_left hh (μ.nonneg ω)
  · simp only [hh,↓reduceIte,mul_zero,zero_mul]
    exact mul_nonneg (μ.nonneg ω) (hf ω)

 theorem good_outcome (μ : Law Ω) (E F : Ω → Prop) (h : prob μ E+prob μ F < 1) :
    ∃ ω,0 < μ.mass ω ∧ ¬E ω ∧ ¬F ω := by
  by_contra hn
  have hbad : ∀ ω,0 < μ.mass ω → E ω ∨ F ω := by
    intro ω hpos
    by_contra hh
    exact hn ⟨ω,hpos,not_or.mp hh⟩
  have heq : prob μ (fun ω => E ω ∨ F ω)=1 := by
    unfold prob expect
    calc
      _ = ∑ ω,μ.mass ω := by
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases hp : μ.mass ω=0
        · simp only [hp,zero_mul]
        · dsimp only
          rw [if_pos (hbad ω (lt_of_le_of_ne (μ.nonneg ω) (Ne.symm hp))),mul_one]
      _ = 1 := μ.total
  have hu := prob_union μ E F
  linarith

 def uniform (Ω : Type) [Fintype Ω] [Nonempty Ω] : Law Ω where
  mass _ := 1/(Fintype.card Ω:ℝ)
  nonneg _ := by positivity
  total := by
    have hc : (Fintype.card Ω:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
    simp [hc]

 def bind (μ : Law Ω) (κ : Ω → Law A) : Law (Ω×A) where
  mass x := μ.mass x.1*(κ x.1).mass x.2
  nonneg x := mul_nonneg (μ.nonneg x.1) ((κ x.1).nonneg x.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [←Finset.mul_sum,Law.total,mul_one,μ.total]

 theorem expect_bind (μ : Law Ω) (κ : Ω → Law A) (f : Ω×A → ℝ) :
    expect (bind μ κ) f = expect μ (fun ω => expect (κ ω) (fun a => f (ω,a))) := by
  simp only [expect,bind,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

 def independent (μ : Law Ω) (ν : Law A) : Law (Ω×A) := bind μ (fun _ => ν)

 def pi {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i,Fintype (α i)] (μ : ∀ i,Law (α i)) : Law (∀ i,α i) where
  mass x := ∏ i,(μ i).mass (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (μ i).nonneg (x i))
  total := by
    have hh := Finset.prod_univ_sum (fun i => (Finset.univ : Finset (α i))) (fun i a => (μ i).mass a)
    simpa only [Fintype.piFinset_univ,Law.total,Finset.prod_const_one] using hh.symm

end EdgeSublinearMWIS.Main.FiniteLaw
end

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.FiniteLaw
variable {Ω : Type} [Fintype Ω]

 theorem expect_sum {ι : Type} [Fintype ι] (μ : Law Ω) (f : ι → Ω → ℝ) :
    expect μ (fun ω => ∑ i,f i ω) = ∑ i,expect μ (f i) := by
  simp only [expect,Finset.mul_sum]
  exact Finset.sum_comm

 theorem expect_mul (μ : Law Ω) (f : Ω → ℝ) (c : ℝ) :
    expect μ (fun ω => c*f ω)=c*expect μ f := by
  simp only [expect,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  ring

 theorem expect_pi_factor {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i,Fintype (α i)]
    (μ : ∀ i,Law (α i)) (f : ∀ i,α i → ℝ) :
    expect (pi μ) (fun x => ∏ i,f i (x i)) = ∏ i,expect (μ i) (f i) := by
  unfold expect
  simp only [pi]
  calc
    _ = ∑ x : ∀ i,α i,∏ i,(μ i).mass (x i)*f i (x i) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.prod_mul_distrib]
    _ = _ := by
      have hh := Finset.prod_univ_sum (fun i => (Finset.univ : Finset (α i))) (fun i a => (μ i).mass a*f i a)
      simpa only [Fintype.piFinset_univ] using hh.symm

 theorem expect_pi_coordinate {ι A : Type} [Fintype ι] [DecidableEq ι] [Fintype A]
    (μ : ι → Law A) (e : ι) (f : A → ℝ) :
    expect (pi μ) (fun x => f (x e))=expect (μ e) f := by
  let g : ι → A → ℝ := fun i a => if i=e then f a else 1
  have hg (x : ι → A) : (∏ i,g i (x i))=f (x e) := by simp [g]
  have hm (i : ι) : expect (μ i) (g i)=if i=e then expect (μ e) f else 1 := by
    by_cases hi : i=e
    · subst i; simp only [g,↓reduceIte]
    · simp only [g,hi,↓reduceIte,expect_one]
  calc
    _ = expect (pi μ) (fun x => ∏ i,g i (x i)) := congrArg (expect (pi μ)) (funext (fun x => (hg x).symm))
    _ = ∏ i,expect (μ i) (g i) := expect_pi_factor μ g
    _ = _ := by simp only [hm]; simp

end EdgeSublinearMWIS.Main.FiniteLaw
end

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.FiniteLaw

 theorem expect_pi_split {ι A : Type} [Fintype ι] [DecidableEq ι] [Fintype A]
    (μ : ι → Law A) (p : ι → Prop) [DecidablePred p] (f : ({i // p i} → A) → ({i // ¬p i} → A) → ℝ) :
    expect (pi μ) (fun x => f (fun i => x i) (fun i => x i)) =
      expect (pi (fun i : {i // p i} => μ i)) (fun x =>
        expect (pi (fun i : {i // ¬p i} => μ i)) (fun y => f x y)) := by
  let e := Equiv.piEquivPiSubtypeProd p (fun _ : ι => A)
  unfold expect
  simp only [pi]
  calc
    _ = ∑ z : ({i // p i} → A) × ({i // ¬p i} → A),
        ((∏ i : {i // p i},(μ i).mass (z.1 i)) *
        (∏ i : {i // ¬p i},(μ i).mass (z.2 i))) * f z.1 z.2 := by
      apply Fintype.sum_equiv e
      intro x
      change (∏ i,(μ i).mass (x i))*f (fun i => x i) (fun i => x i) =
        ((∏ i : {i // p i},(μ i).mass (x i)) * (∏ i : {i // ¬p i},(μ i).mass (x i))) *
          f (fun i => x i) (fun i => x i)
      rw [Fintype.prod_subtype_mul_prod_subtype p (fun i => (μ i).mass (x i))]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      ring

 theorem expect_pi_two {ι A : Type} [Fintype ι] [DecidableEq ι] [Fintype A]
    (μ : ι → Law A) (u v : ι) (huv : u≠v) (f : A → A → ℝ) :
    expect (pi μ) (fun x => f (x u) (x v)) =
      expect (μ u) (fun a => expect (μ v) (fun b => f a b)) := by
  letI : Fintype {i : ι // i=u} := Subtype.fintype (fun i : ι => i=u)
  letI : Fintype {i : ι // ¬i=u} := Subtype.fintype (fun i : ι => ¬i=u)
  let U : {i : ι // i=u} := ⟨u,rfl⟩
  let V : {i : ι // ¬i=u} := ⟨v,huv.symm⟩
  have hh := expect_pi_split μ (fun i => i=u) (fun x y => f (x U) (y V))
  change expect (pi μ) (fun x => f (x u) (x v)) = _ at hh
  rw [hh]
  calc
    _ = expect (pi (fun i : {i : ι // i=u} => μ i)) (fun x => expect (μ v) (fun b => f (x U) b)) := by
      apply congrArg (expect (pi (fun i : {i : ι // i=u} => μ i)))
      funext x
      exact expect_pi_coordinate _ V _
    _ = _ := by
      simpa only [U] using expect_pi_coordinate (fun i : {i : ι // i=u} => μ i) U
        (fun a => expect (μ v) (fun b => f a b))

end EdgeSublinearMWIS.Main.FiniteLaw
end

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.FiniteLaw

 theorem expect_pi_blocks {ι A : Type} [Fintype ι] [DecidableEq ι] [Fintype A]
    (μ : ι → Law A) (p : ι → Prop) [DecidablePred p]
    (f : ({i // p i} → A) → ℝ) (g : ({i // ¬p i} → A) → ℝ) :
    expect (pi μ) (fun x => f (fun i => x i)*g (fun i => x i)) =
      expect (pi (fun i : {i // p i} => μ i)) f * expect (pi (fun i : {i // ¬p i} => μ i)) g := by
  rw [expect_pi_split μ p (fun x y => f x*g y)]
  simp only [expect_mul]
  unfold expect
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  ring

 theorem expect_pi_four {ι A : Type} [Fintype ι] [DecidableEq ι] [Fintype A]
    (μ : ι → Law A) (u v w z : ι) (huv : u≠v) (hwz : w≠z)
    (huw : u≠w) (huz : u≠z) (hvw : v≠w) (hvz : v≠z) (f g : A → A → ℝ) :
    expect (pi μ) (fun x => f (x u) (x v)*g (x w) (x z)) =
      expect (μ u) (fun a => expect (μ v) (fun b => f a b)) *
      expect (μ w) (fun a => expect (μ z) (fun b => g a b)) := by
  let p : ι → Prop := fun i => i=u ∨ i=v
  let U : {i // p i} := ⟨u,Or.inl rfl⟩
  let V : {i // p i} := ⟨v,Or.inr rfl⟩
  let W : {i // ¬p i} := ⟨w,not_or.mpr ⟨huw.symm,hvw.symm⟩⟩
  let Z : {i // ¬p i} := ⟨z,not_or.mpr ⟨huz.symm,hvz.symm⟩⟩
  have hUV : U≠V := fun h => huv (congrArg Subtype.val h)
  have hWZ : W≠Z := fun h => hwz (congrArg Subtype.val h)
  have hh := expect_pi_blocks μ p (fun x => f (x U) (x V)) (fun y => g (y W) (y Z))
  change expect (pi μ) (fun x => f (x u) (x v)*g (x w) (x z)) = _ at hh
  rw [hh]
  have hF := expect_pi_two (fun i : {i // p i} => μ i) U V hUV f
  have hG := expect_pi_two (fun i : {i // ¬p i} => μ i) W Z hWZ g
  simpa only [U,V,W,Z] using congrArg₂ (fun a b : ℝ => a*b) hF hG

 theorem expect_pi_two_mul {ι A : Type} [Fintype ι] [DecidableEq ι] [Fintype A]
    (μ : ι → Law A) (u v : ι) (huv : u≠v) (f g : A → ℝ) :
    expect (pi μ) (fun x => f (x u)*g (x v))=expect (μ u) f*expect (μ v) g := by
  rw [expect_pi_two μ u v huv (fun a b => f a*g b)]
  simp only [expect_mul]
  unfold expect
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring

end EdgeSublinearMWIS.Main.FiniteLaw
end

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.FiniteLaw

 theorem prob_exists {Ω ι : Type} [Fintype Ω] [Fintype ι] (μ : Law Ω) (E : ι → Ω → Prop) :
    prob μ (fun ω => ∃ i,E i ω) ≤ ∑ i,prob μ (E i) := by
  unfold prob
  rw [←expect_sum]
  apply expect_mono
  intro ω
  dsimp only
  by_cases he : ∃ i,E i ω
  · rw [if_pos he]
    obtain ⟨i,hi⟩ := he
    have hh := Finset.single_le_sum (f := fun i => if E i ω then (1:ℝ) else 0)
      (fun i _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
    simpa only [if_pos hi] using hh
  · rw [if_neg he]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> norm_num

 theorem prob_conj_le {Ω : Type} [Fintype Ω] (μ : Law Ω) (P : Prop) (E : Ω → Prop) :
    prob μ (fun ω => P ∧ E ω) ≤ prob μ E := by
  apply expect_mono
  intro ω
  by_cases hp : P <;> by_cases he : E ω <;> simp [hp,he]

end EdgeSublinearMWIS.Main.FiniteLaw
end

noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PathMass

 theorem vertexMass_cons {n : ℕ} (e : List (Fin n) × ℝ) (f : List (List (Fin n) × ℝ)) (v : Fin n) :
    vertexMass (e::f) v = (if v∈e.1 then e.2 else 0)+vertexMass f v := by
  by_cases hv : v∈e.1 <;> simp [vertexMass,hv]

 theorem endpointMass_cons {n : ℕ} (e : List (Fin n) × ℝ) (f : List (List (Fin n) × ℝ)) (u v : Fin n) :
    endpointMass (e::f) u v = (if HasEndpoints e.1 u v then e.2 else 0)+endpointMass f u v := by
  by_cases hv : HasEndpoints e.1 u v <;> simp [endpointMass,hv]

 theorem sum_indicator {n : ℕ} (W : Finset (Fin n)) (p : List (Fin n)) (hp : p.Nodup)
    (hW : ∀ v∈p,v∈W) (w : ℝ) :
    (∑ v∈W,if v∈p then w else 0) = (p.length:ℝ)*w := by
  have heq : W.filter (fun v => v∈p)=p.toFinset := by
    ext v
    simp only [Finset.mem_filter,List.mem_toFinset]
    exact ⟨fun h => h.2,fun h => ⟨hW v h,h⟩⟩
  rw [←Finset.sum_filter,heq]
  simp only [Finset.sum_const,List.toFinset_card_of_nodup hp, nsmul_eq_mul]

 theorem length_identity {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (f : List (List (Fin n) × ℝ)) (hf : SparseValid G W f) :
    (f.map (fun e => e.2*(e.1.length:ℝ))).sum = ∑ v∈W,vertexMass f v := by
  induction f with
  | nil => simp [vertexMass]
  | cons e f ih =>
    have he := hf e (by simp)
    have hrest : SparseValid G W f := by intro x hx; exact hf x (by simp [hx])
    simp only [List.map_cons,List.sum_cons,vertexMass_cons,Finset.sum_add_distrib]
    rw [←ih hrest,sum_indicator W e.1 he.2.2.1 he.2.2.2.1 e.2]
    ring

 theorem expected_length_bound {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ)
    (ell : ℝ) (W : Finset (Fin n)) (f : List (List (Fin n) × ℝ))
    (hell : 0 ≤ ell) (hx : ∀ v,0 ≤ x v) (hk : 0 < vertexSum x Finset.univ)
    (hf : PathOutcome G x ell W f) :
    (f.map (fun e => e.2*(e.1.length:ℝ))).sum ≤ ell := by
  rw [length_identity G W f hf.2.1]
  have hsub : (∑ v∈W,x v) ≤ vertexSum x Finset.univ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => hx v)
  calc
    _ ≤ ∑ v∈W,ell*x v/vertexSum x Finset.univ := Finset.sum_le_sum (fun v hv => hf.2.2.2.2 v hv)
    _ = (ell/vertexSum x Finset.univ)*(∑ v∈W,x v) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ ≤ (ell/vertexSum x Finset.univ)*vertexSum x Finset.univ :=
      mul_le_mul_of_nonneg_left hsub (div_nonneg hell hk.le)
    _ = ell := div_mul_cancel₀ _ hk.ne'

end EdgeSublinearMWIS.Main.PathMass
end

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PathMass
open FiniteLaw

 theorem list_sum_index {A : Type} (f : List A) (g : A → ℝ) :
    (f.map g).sum=∑ i : Fin f.length,g f[i] := by
  induction f with
  | nil => simp
  | cons e f ih =>
    simpa only [List.length_cons,List.map_cons,List.sum_cons,Fin.sum_univ_succ,Fin.getElem_fin,Fin.val_zero,Fin.val_succ,List.getElem_cons_zero,List.getElem_cons_succ] using congrArg (fun z => g e+z) ih

 theorem endpointMass_sum {n : ℕ} (f : List (List (Fin n) × ℝ)) (u v : Fin n) :
    endpointMass f u v=∑ i : Fin f.length,if HasEndpoints f[i].1 u v then f[i].2 else 0 := by
  have hh : endpointMass f u v=(f.map (fun e => if HasEndpoints e.1 u v then e.2 else 0)).sum := by
    induction f with
    | nil => simp [endpointMass]
    | cons e f ih => simp only [endpointMass_cons,List.map_cons,List.sum_cons,ih]
  rw [hh,list_sum_index]

 theorem vertexMass_sum {n : ℕ} (f : List (List (Fin n) × ℝ)) (v : Fin n) :
    vertexMass f v=∑ i : Fin f.length,if v∈f[i].1 then f[i].2 else 0 := by
  have hh : vertexMass f v=(f.map (fun e => if v∈e.1 then e.2 else 0)).sum := by
    induction f with
    | nil => simp [vertexMass]
    | cons e f ih => simp only [vertexMass_cons,List.map_cons,List.sum_cons,ih]
  rw [hh,list_sum_index]

 def pathLaw {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) (ell : ℝ)
    (W : Finset (Fin n)) (f : List (List (Fin n) × ℝ)) (hf : PathOutcome G x ell W f) : Law (Fin f.length) where
  mass i := f[i].2
  nonneg i := (hf.2.1 _ (List.getElem_mem i.isLt)).1
  total := by
    rw [←list_sum_index f Prod.snd]
    exact hf.2.2.1

 theorem order_pos {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) (ell : ℝ)
    (W : Finset (Fin n)) (f : List (List (Fin n) × ℝ)) (hf : PathOutcome G x ell W f) : 0 < W.card := by
  have hh := hf.1
  omega

 def endpointLaw {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) (ell : ℝ)
    (W : Finset (Fin n)) (f : List (List (Fin n) × ℝ)) (hf : PathOutcome G x ell W f)
    (u v : W) : Law (Fin f.length) where
  mass i := if HasEndpoints f[i].1 u.val v.val then (W.card:ℝ)^2*f[i].2 else 0
  nonneg i := by
    split_ifs
    · exact mul_nonneg (sq_nonneg _) ((hf.2.1 _ (List.getElem_mem i.isLt)).1)
    · exact le_rfl
  total := by
    have hw : (W.card:ℝ)≠0 := by exact_mod_cast (order_pos G x ell W f hf).ne'
    calc
      _ = (W.card:ℝ)^2*(∑ i : Fin f.length,if HasEndpoints f[i].1 u.val v.val then f[i].2 else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        split_ifs <;> ring
      _ = (W.card:ℝ)^2*endpointMass f u.val v.val := by rw [endpointMass_sum]
      _ = 1 := by rw [hf.2.2.2.1 u.val u.property v.val v.property]; field_simp

 theorem endpointLaw_support {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) (ell : ℝ)
    (W : Finset (Fin n)) (f : List (List (Fin n) × ℝ)) (hf : PathOutcome G x ell W f)
    (u v : W) (i : Fin f.length) (h : 0 < (endpointLaw G x ell W f hf u v).mass i) :
    HasEndpoints f[i].1 u.val v.val := by
  by_contra hn
  simp only [endpointLaw,hn,↓reduceIte,lt_self_iff_false] at h

end EdgeSublinearMWIS.Main.PathMass
end

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PathMass
open FiniteLaw

 theorem endpoints_exist {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (p : List (Fin n)) (hp : SimplePath G W p) :
    ∃ u v : W,HasEndpoints p u.val v.val := by
  let u : W := ⟨p.head hp.1,hp.2.2.1 _ (List.head_mem hp.1)⟩
  let v : W := ⟨p.getLast hp.1,hp.2.2.1 _ (List.getLast_mem hp.1)⟩
  exact ⟨u,v,List.head?_eq_some_head hp.1,List.getLast?_eq_some_getLast hp.1⟩

 theorem endpoints_iff {n : ℕ} (W : Finset (Fin n)) (p : List (Fin n)) (u v a b : W)
    (hp : HasEndpoints p u.val v.val) : HasEndpoints p a.val b.val ↔ a=u ∧ b=v := by
  constructor
  · intro h
    exact ⟨Subtype.ext (Option.some.inj (h.1.symm.trans hp.1)),Subtype.ext (Option.some.inj (h.2.symm.trans hp.2))⟩
  · rintro ⟨rfl,rfl⟩
    exact hp

 theorem kernel_average {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) (ell : ℝ)
    (W : Finset (Fin n)) [Nonempty W] (f : List (List (Fin n) × ℝ))
    (hf : PathOutcome G x ell W f) (i : Fin f.length) :
    expect (uniform W) (fun u => expect (uniform W) (fun v => (endpointLaw G x ell W f hf u v).mass i)) =
      (pathLaw G x ell W f hf).mass i := by
  obtain ⟨u,v,he⟩ := endpoints_exist G W f[i].1 (hf.2.1 _ (List.getElem_mem i.isLt)).2
  have hiff (a b : W) := endpoints_iff W f[i].1 u v a b he
  have hw : (W.card:ℝ)≠0 := by exact_mod_cast (order_pos G x ell W f hf).ne'
  simp only [expect,uniform,endpointLaw,pathLaw,hiff,Fintype.card_coe,mul_ite,mul_zero]
  have hinner (a : W) :
      (∑ b : W, if a=u ∧ b=v then (1/(W.card:ℝ))*((W.card:ℝ)^2*f[i].2) else 0) =
      if a=u then (1/(W.card:ℝ))*((W.card:ℝ)^2*f[i].2) else 0 := by
    by_cases ha : a=u <;> simp [ha]
  simp only [hinner,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
  field_simp

end EdgeSublinearMWIS.Main.PathMass
end

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PathMass
open FiniteLaw

 theorem kernel_expectation {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) (ell : ℝ)
    (W : Finset (Fin n)) [Nonempty W] (f : List (List (Fin n) × ℝ))
    (hf : PathOutcome G x ell W f) (g : Fin f.length → ℝ) :
    expect (uniform W) (fun u => expect (uniform W) (fun v => expect (endpointLaw G x ell W f hf u v) g)) =
      expect (pathLaw G x ell W f hf) g := by
  have he (u v : W) : expect (endpointLaw G x ell W f hf u v) g =
      ∑ i : Fin f.length,g i*(endpointLaw G x ell W f hf u v).mass i := by
    unfold expect
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp only [he,expect_sum,expect_mul,kernel_average G x ell W f hf]
  unfold expect
  apply Finset.sum_congr rfl
  intro i hi
  ring

end EdgeSublinearMWIS.Main.PathMass
end

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PathMass
open FiniteLaw

abbrev Outcomes {h n : ℕ} (H : SimpleGraph (Fin h)) (W : Finset (Fin n))
    (f : List (List (Fin n) × ℝ)) := (Fin h → W) × (EdgeIndex H → Fin f.length)

 def sampler {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n)) (x : Fin n → ℝ)
    (ell : ℝ) (W : Finset (Fin n)) [Nonempty W] (f : List (List (Fin n) × ℝ))
    (hf : PathOutcome G x ell W f) : Law (Outcomes H W f) :=
  bind (pi (fun _ : Fin h => uniform W)) (fun φ =>
    pi (fun e : EdgeIndex H => endpointLaw G x ell W f hf (φ e.val.1) (φ e.val.2)))

 theorem sample_edge_expect {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n)) (x : Fin n → ℝ)
    (ell : ℝ) (W : Finset (Fin n)) [Nonempty W] (f : List (List (Fin n) × ℝ))
    (hf : PathOutcome G x ell W f) (e : EdgeIndex H) (g : Fin f.length → ℝ) :
    expect (sampler H G x ell W f hf) (fun ω => g (ω.2 e))=expect (pathLaw G x ell W f hf) g := by
  unfold sampler
  rw [expect_bind]
  have hi (φ : Fin h → W) := expect_pi_coordinate
    (fun d : EdgeIndex H => endpointLaw G x ell W f hf (φ d.val.1) (φ d.val.2)) e g
  simp only [hi]
  rw [expect_pi_two (fun _ : Fin h => uniform W) e.val.1 e.val.2 (Fin.ne_of_lt e.property.1)
    (fun u v => expect (endpointLaw G x ell W f hf u v) g)]
  exact kernel_expectation G x ell W f hf g

 theorem sample_pair_expect {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n)) (x : Fin n → ℝ)
    (ell : ℝ) (W : Finset (Fin n)) [Nonempty W] (f : List (List (Fin n) × ℝ))
    (hf : PathOutcome G x ell W f) (e d : EdgeIndex H)
    (h11 : e.val.1≠d.val.1) (h12 : e.val.1≠d.val.2) (h21 : e.val.2≠d.val.1) (h22 : e.val.2≠d.val.2)
    (g j : Fin f.length → ℝ) :
    expect (sampler H G x ell W f hf) (fun ω => g (ω.2 e)*j (ω.2 d)) =
      expect (pathLaw G x ell W f hf) g * expect (pathLaw G x ell W f hf) j := by
  have hed : e≠d := fun hh => h11 (congrArg (fun z : EdgeIndex H => z.val.1) hh)
  unfold sampler
  rw [expect_bind]
  have hi (φ : Fin h → W) := expect_pi_two_mul
    (fun c : EdgeIndex H => endpointLaw G x ell W f hf (φ c.val.1) (φ c.val.2)) e d hed g j
  simp only [hi]
  rw [expect_pi_four (fun _ : Fin h => uniform W) e.val.1 e.val.2 d.val.1 d.val.2
    (Fin.ne_of_lt e.property.1) (Fin.ne_of_lt d.property.1) h11 h12 h21 h22
    (fun u v => expect (endpointLaw G x ell W f hf u v) g)
    (fun u v => expect (endpointLaw G x ell W f hf u v) j)]
  rw [kernel_expectation,kernel_expectation]

 theorem positive_endpoints {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n)) (x : Fin n → ℝ)
    (ell : ℝ) (W : Finset (Fin n)) [Nonempty W] (f : List (List (Fin n) × ℝ))
    (hf : PathOutcome G x ell W f) (ω : Outcomes H W f)
    (hω : 0 < (sampler H G x ell W f hf).mass ω) (e : EdgeIndex H) :
    HasEndpoints f[ω.2 e].1 (ω.1 e.val.1).val (ω.1 e.val.2).val := by
  apply endpointLaw_support G x ell W f hf (ω.1 e.val.1) (ω.1 e.val.2) (ω.2 e)
  by_contra hn
  have hzero : (endpointLaw G x ell W f hf (ω.1 e.val.1) (ω.1 e.val.2)).mass (ω.2 e)=0 := by
    have hnonneg := (endpointLaw G x ell W f hf (ω.1 e.val.1) (ω.1 e.val.2)).nonneg (ω.2 e)
    linarith
  have hprod : (∏ d : EdgeIndex H,(endpointLaw G x ell W f hf (ω.1 d.val.1) (ω.1 d.val.2)).mass (ω.2 d))=0 :=
    Finset.prod_eq_zero (Finset.mem_univ e) hzero
  change 0 < (pi (fun _ : Fin h => uniform W)).mass ω.1 *
    (∏ d : EdgeIndex H,(endpointLaw G x ell W f hf (ω.1 d.val.1) (ω.1 d.val.2)).mass (ω.2 d)) at hω
  rw [hprod,mul_zero] at hω
  exact (lt_irrefl 0) hω

end EdgeSublinearMWIS.Main.PathMass
end

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PathMass
open FiniteLaw

 theorem vertex_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (f : List (List (Fin n) × ℝ)) (hf : SparseValid G W f) (v : Fin n) : 0 ≤ vertexMass f v := by
  rw [vertexMass_sum]
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact (hf _ (List.getElem_mem i.isLt)).1
  · exact le_rfl

 theorem vertex_outside {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (f : List (List (Fin n) × ℝ)) (hf : SparseValid G W f) (v : Fin n) (hv : v∉W) : vertexMass f v=0 := by
  rw [vertexMass_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hnot : v∉f[i].1 := fun hmem => hv ((hf _ (List.getElem_mem i.isLt)).2.2.2.1 v hmem)
  simp only [hnot,↓reduceIte]

 theorem global_vertex_bound {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ)
    (ell : ℝ) (W : Finset (Fin n)) (f : List (List (Fin n) × ℝ))
    (hf : PathOutcome G x ell W f) (hell : 0 ≤ ell) (hx : ∀ v,0 ≤ x v)
    (hk : 0 < vertexSum x Finset.univ) (v : Fin n) :
    0 ≤ vertexMass f v ∧ vertexMass f v ≤ ell*x v/vertexSum x Finset.univ := by
  refine ⟨vertex_nonneg G W f hf.2.1 v,?_⟩
  by_cases hv : v∈W
  · exact hf.2.2.2.2 v hv
  · rw [vertex_outside G W f hf.2.1 v hv]
    exact div_nonneg (mul_nonneg hell (hx v)) hk.le

 theorem indicator_expect {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) (ell : ℝ)
    (W : Finset (Fin n)) (f : List (List (Fin n) × ℝ)) (hf : PathOutcome G x ell W f) (v : Fin n) :
    expect (pathLaw G x ell W f hf) (fun i => if v∈f[i].1 then 1 else 0)=vertexMass f v := by
  rw [vertexMass_sum]
  unfold expect
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [pathLaw]
  by_cases hv : v∈f[i].1 <;> simp only [hv,↓reduceIte,mul_one,mul_zero]

 theorem square_mass_sum {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) (ell : ℝ)
    (W : Finset (Fin n)) (f : List (List (Fin n) × ℝ)) (hf : PathOutcome G x ell W f)
    (hell : 0 ≤ ell) (hx : ∀ v,0 ≤ x v ∧ x v ≤ 1) (hk : 0 < vertexSum x Finset.univ) :
    (∑ v,vertexMass f v^2) ≤ ell^2/vertexSum x Finset.univ := by
  let k := vertexSum x Finset.univ
  have hpoint (v : Fin n) : vertexMass f v^2 ≤ (ell^2/k^2)*x v := by
    have hm := global_vertex_bound G x ell W f hf hell (fun v => (hx v).1) hk v
    calc
      _ ≤ (ell*x v/k)^2 := pow_le_pow_left₀ hm.1 hm.2 2
      _ = (ell^2/k^2)*(x v)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [(hx v).1,(hx v).2] : (x v)^2 ≤ x v) (div_nonneg (sq_nonneg ell) (sq_nonneg k))
  calc
    _ ≤ ∑ v,(ell^2/k^2)*x v := Finset.sum_le_sum (fun v _ => hpoint v)
    _ = (ell^2/k^2)*k := by rw [←Finset.mul_sum]; rfl
    _ = _ := by dsimp only [k]; field_simp <;> ring

 def collision {h n : ℕ} (H : SimpleGraph (Fin h)) (W : Finset (Fin n))
    (f : List (List (Fin n) × ℝ)) (e d : EdgeIndex H) (ω : Outcomes H W f) : Prop :=
  ∃ v : Fin n,v∈f[ω.2 e].1 ∧ v∈f[ω.2 d].1

 theorem collision_bound {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n)) (x : Fin n → ℝ)
    (ell : ℝ) (W : Finset (Fin n)) [Nonempty W] (f : List (List (Fin n) × ℝ))
    (hf : PathOutcome G x ell W f) (hell : 0 ≤ ell) (hx : ∀ v,0 ≤ x v ∧ x v ≤ 1)
    (hk : 0 < vertexSum x Finset.univ) (e d : EdgeIndex H)
    (h11 : e.val.1≠d.val.1) (h12 : e.val.1≠d.val.2) (h21 : e.val.2≠d.val.1) (h22 : e.val.2≠d.val.2) :
    prob (sampler H G x ell W f hf) (collision H W f e d) ≤ ell^2/vertexSum x Finset.univ := by
  let μ := sampler H G x ell W f hf
  let Z : Fin n → Outcomes H W f → ℝ := fun v ω =>
    (if v∈f[ω.2 e].1 then 1 else 0)*(if v∈f[ω.2 d].1 then 1 else 0)
  have hZ (v : Fin n) (ω : Outcomes H W f) : 0 ≤ Z v ω := by dsimp only [Z]; split_ifs <;> norm_num
  have hpoint (ω : Outcomes H W f) : (if collision H W f e d ω then (1:ℝ) else 0) ≤ ∑ v,Z v ω := by
    by_cases hc : collision H W f e d ω
    · obtain ⟨v,hve,hvd⟩ := hc
      have hh := Finset.single_le_sum (fun v _ => hZ v ω) (Finset.mem_univ v)
      have hc0 : collision H W f e d ω := ⟨v,hve,hvd⟩
      simpa only [Z,hve,hvd,↓reduceIte,mul_one,if_pos hc0] using hh
    · simpa only [hc,↓reduceIte] using Finset.sum_nonneg (fun v _ => hZ v ω)
  unfold prob
  calc
    _ ≤ expect μ (fun ω => ∑ v,Z v ω) := expect_mono μ _ _ hpoint
    _ = ∑ v,expect μ (Z v) := expect_sum μ Z
    _ = ∑ v,vertexMass f v^2 := by
      apply Finset.sum_congr rfl
      intro v hv
      dsimp only [μ,Z]
      rw [sample_pair_expect H G x ell W f hf e d h11 h12 h21 h22
        (fun i => if v∈f[i].1 then (1:ℝ) else 0) (fun i => if v∈f[i].1 then (1:ℝ) else 0),
        indicator_expect]
      ring
    _ ≤ _ := square_mass_sum G x ell W f hf hell hx hk

end EdgeSublinearMWIS.Main.PathMass
end

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PathMass
open FiniteLaw

 theorem edgeEnergy_sum {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) :
    edgeEnergy G x = ∑ e : EdgeIndex G,x e.val.1*x e.val.2 := by
  unfold edgeEnergy
  apply Finset.sum_subtype
  intro e
  simp

 theorem mass_energy_bound {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) (ell : ℝ)
    (W : Finset (Fin n)) (f : List (List (Fin n) × ℝ)) (hf : PathOutcome G x ell W f)
    (hell : 0 ≤ ell) (hx : ∀ v,0 ≤ x v) (hk : 0 < vertexSum x Finset.univ) :
    edgeEnergy G (vertexMass f) ≤ (ell^2/(vertexSum x Finset.univ)^2)*edgeEnergy G x := by
  rw [edgeEnergy_sum,edgeEnergy_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  have hu := global_vertex_bound G x ell W f hf hell hx hk e.val.1
  have hv := global_vertex_bound G x ell W f hf hell hx hk e.val.2
  calc
    _ ≤ (ell*x e.val.1/vertexSum x Finset.univ)*(ell*x e.val.2/vertexSum x Finset.univ) :=
      mul_le_mul hu.2 hv.2 hv.1 (div_nonneg (mul_nonneg hell (hx e.val.1)) hk.le)
    _ = _ := by ring

 def adjoining {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (f : List (List (Fin n) × ℝ)) (e d : EdgeIndex H) (ω : Outcomes H W f) : Prop :=
  ∃ u∈f[ω.2 e].1,∃ v∈f[ω.2 d].1,G.Adj u v

 theorem adjacency_energy_bound {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n)) (x : Fin n → ℝ)
    (ell : ℝ) (W : Finset (Fin n)) [Nonempty W] (f : List (List (Fin n) × ℝ))
    (hf : PathOutcome G x ell W f) (e d : EdgeIndex H)
    (h11 : e.val.1≠d.val.1) (h12 : e.val.1≠d.val.2) (h21 : e.val.2≠d.val.1) (h22 : e.val.2≠d.val.2) :
    prob (sampler H G x ell W f hf) (adjoining H G W f e d) ≤ 2*edgeEnergy G (vertexMass f) := by
  let μ := sampler H G x ell W f hf
  let Z : EdgeIndex G → Outcomes H W f → ℝ := fun a ω =>
    (if a.val.1∈f[ω.2 e].1 then 1 else 0)*(if a.val.2∈f[ω.2 d].1 then 1 else 0) +
    (if a.val.2∈f[ω.2 e].1 then 1 else 0)*(if a.val.1∈f[ω.2 d].1 then 1 else 0)
  have hZ (a : EdgeIndex G) (ω : Outcomes H W f) : 0 ≤ Z a ω := by
    dsimp only [Z]; split_ifs <;> norm_num
  have hp (ω : Outcomes H W f) : (if adjoining H G W f e d ω then (1:ℝ) else 0) ≤ ∑ a,Z a ω := by
    by_cases hc : adjoining H G W f e d ω
    · rw [if_pos hc]
      obtain ⟨u,hu,v,hv,huv⟩ := hc
      rcases lt_or_gt_of_ne (G.ne_of_adj huv) with hlt | hlt
      · let a : EdgeIndex G := ⟨(u,v),hlt,huv⟩
        have hsingle := Finset.single_le_sum (fun a _ => hZ a ω) (Finset.mem_univ a)
        have hone : (1:ℝ) ≤ Z a ω := by dsimp only [Z,a]; simp only [hu,hv,↓reduceIte,mul_one]; split_ifs <;> norm_num
        exact hone.trans hsingle
      · let a : EdgeIndex G := ⟨(v,u),hlt,huv.symm⟩
        have hsingle := Finset.single_le_sum (fun a _ => hZ a ω) (Finset.mem_univ a)
        have hone : (1:ℝ) ≤ Z a ω := by dsimp only [Z,a]; simp only [hu,hv,↓reduceIte,mul_one]; split_ifs <;> norm_num
        exact hone.trans hsingle
    · rw [if_neg hc]
      exact Finset.sum_nonneg (fun a _ => hZ a ω)
  unfold prob
  calc
    _ ≤ expect μ (fun ω => ∑ a,Z a ω) := expect_mono μ _ _ hp
    _ = ∑ a,expect μ (Z a) := expect_sum μ Z
    _ = 2*edgeEnergy G (vertexMass f) := by
      rw [edgeEnergy_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      dsimp only [μ,Z]
      rw [expect_add,
        sample_pair_expect H G x ell W f hf e d h11 h12 h21 h22
          (fun i => if a.val.1∈f[i].1 then (1:ℝ) else 0) (fun i => if a.val.2∈f[i].1 then (1:ℝ) else 0),
        sample_pair_expect H G x ell W f hf e d h11 h12 h21 h22
          (fun i => if a.val.2∈f[i].1 then (1:ℝ) else 0) (fun i => if a.val.1∈f[i].1 then (1:ℝ) else 0)]
      simp only [indicator_expect]
      ring

 theorem adjacency_bound {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n)) (x : Fin n → ℝ)
    (ell : ℝ) (W : Finset (Fin n)) [Nonempty W] (f : List (List (Fin n) × ℝ))
    (hf : PathOutcome G x ell W f) (hell : 0 ≤ ell) (hx : ∀ v,0 ≤ x v)
    (hk : 0 < vertexSum x Finset.univ) (p : ℝ) (hp : 0 < p)
    (henergy : edgeEnergy G x ≤ (vertexSum x Finset.univ)^2/p) (e d : EdgeIndex H)
    (h11 : e.val.1≠d.val.1) (h12 : e.val.1≠d.val.2) (h21 : e.val.2≠d.val.1) (h22 : e.val.2≠d.val.2) :
    prob (sampler H G x ell W f hf) (adjoining H G W f e d) ≤ 2*ell^2/p := by
  calc
    _ ≤ 2*edgeEnergy G (vertexMass f) := adjacency_energy_bound H G x ell W f hf e d h11 h12 h21 h22
    _ ≤ 2*((ell^2/(vertexSum x Finset.univ)^2)*edgeEnergy G x) :=
      mul_le_mul_of_nonneg_left (mass_energy_bound G x ell W f hf hell hx hk) (by norm_num)
    _ ≤ 2*((ell^2/(vertexSum x Finset.univ)^2)*((vertexSum x Finset.univ)^2/p)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left henergy (div_nonneg (sq_nonneg ell) (sq_nonneg _))) (by norm_num)
    _ = _ := by field_simp <;> ring

end EdgeSublinearMWIS.Main.PathMass
end

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PathMass
open FiniteLaw

 def totalLength {h n : ℕ} (H : SimpleGraph (Fin h)) (W : Finset (Fin n))
    (f : List (List (Fin n) × ℝ)) (ω : Outcomes H W f) : ℝ :=
  ∑ e : EdgeIndex H,(f[ω.2 e].1.length:ℝ)

 theorem totalLength_nonneg {h n : ℕ} (H : SimpleGraph (Fin h)) (W : Finset (Fin n))
    (f : List (List (Fin n) × ℝ)) (ω : Outcomes H W f) : 0 ≤ totalLength H W f ω := by
  apply Finset.sum_nonneg
  intro e he
  positivity

 theorem expected_totalLength {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n)) (x : Fin n → ℝ)
    (ell : ℝ) (W : Finset (Fin n)) [Nonempty W] (f : List (List (Fin n) × ℝ))
    (hf : PathOutcome G x ell W f) (hell : 0 ≤ ell) (hx : ∀ v,0 ≤ x v)
    (hk : 0 < vertexSum x Finset.univ) :
    expect (sampler H G x ell W f hf) (totalLength H W f) ≤ ell*Fintype.card (EdgeIndex H) := by
  unfold totalLength
  rw [expect_sum]
  calc
    _ ≤ ∑ _e : EdgeIndex H,ell := by
      apply Finset.sum_le_sum
      intro e he
      rw [sample_edge_expect H G x ell W f hf e (fun i => (f[i].1.length:ℝ))]
      change (∑ i : Fin f.length,f[i].2*(f[i].1.length:ℝ)) ≤ ell
      rw [←list_sum_index f (fun q => q.2*(q.1.length:ℝ))]
      exact expected_length_bound G x ell W f hell hx hk hf
    _ = _ := by simp [mul_comm]

 theorem long_total_bound {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n)) (x : Fin n → ℝ)
    (ell : ℝ) (W : Finset (Fin n)) [Nonempty W] (f : List (List (Fin n) × ℝ))
    (hf : PathOutcome G x ell W f) (hell : 0 < ell) (hx : ∀ v,0 ≤ x v)
    (hk : 0 < vertexSum x Finset.univ) (hE : 0 < Fintype.card (EdgeIndex H)) :
    prob (sampler H G x ell W f hf)
      (fun ω => 4*ell*Fintype.card (EdgeIndex H) ≤ totalLength H W f ω) ≤ 1/4 := by
  have hER : 0 < (Fintype.card (EdgeIndex H):ℝ) := by exact_mod_cast hE
  have hA : 0 < 4*ell*(Fintype.card (EdgeIndex H):ℝ) := by positivity
  calc
    _ ≤ expect (sampler H G x ell W f hf) (totalLength H W f)/(4*ell*Fintype.card (EdgeIndex H)) :=
      markov _ _ (totalLength_nonneg H W f) _ hA
    _ ≤ (ell*Fintype.card (EdgeIndex H))/(4*ell*Fintype.card (EdgeIndex H)) :=
      div_le_div_of_nonneg_right (expected_totalLength H G x ell W f hf hell.le hx hk) hA.le
    _ = _ := by field_simp

end EdgeSublinearMWIS.Main.PathMass
end

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PathMass
open FiniteLaw

 def Nonincident {h : ℕ} {H : SimpleGraph (Fin h)} (e d : EdgeIndex H) : Prop :=
  e.val.1≠d.val.1 ∧ e.val.1≠d.val.2 ∧ e.val.2≠d.val.1 ∧ e.val.2≠d.val.2

 def badPair {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (f : List (List (Fin n) × ℝ)) (ed : EdgeIndex H × EdgeIndex H) (ω : Outcomes H W f) : Prop :=
  Nonincident ed.1 ed.2 ∧ (collision H W f ed.1 ed.2 ω ∨ adjoining H G W f ed.1 ed.2 ω)

 def bad {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (f : List (List (Fin n) × ℝ)) (ω : Outcomes H W f) : Prop := ∃ ed,badPair H G W f ed ω

 theorem badPair_bound {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n)) (x : Fin n → ℝ)
    (ell : ℝ) (W : Finset (Fin n)) [Nonempty W] (f : List (List (Fin n) × ℝ))
    (hf : PathOutcome G x ell W f) (hell : 0 ≤ ell) (hx : ∀ v,0 ≤ x v ∧ x v ≤ 1)
    (p : ℝ) (hp : 0 < p) (hk : p ≤ vertexSum x Finset.univ)
    (henergy : edgeEnergy G x ≤ (vertexSum x Finset.univ)^2/p) (ed : EdgeIndex H × EdgeIndex H) :
    prob (sampler H G x ell W f hf) (badPair H G W f ed) ≤ 3*ell^2/p := by
  let μ := sampler H G x ell W f hf
  by_cases he : Nonincident ed.1 ed.2
  · obtain ⟨h11,h12,h21,h22⟩ := he
    calc
      _ ≤ prob μ (fun ω => collision H W f ed.1 ed.2 ω ∨ adjoining H G W f ed.1 ed.2 ω) := prob_conj_le μ _ _
      _ ≤ prob μ (collision H W f ed.1 ed.2)+prob μ (adjoining H G W f ed.1 ed.2) := prob_union μ _ _
      _ ≤ ell^2/vertexSum x Finset.univ+2*ell^2/p := add_le_add
        (collision_bound H G x ell W f hf hell hx (hp.trans_le hk) ed.1 ed.2 h11 h12 h21 h22)
        (adjacency_bound H G x ell W f hf hell (fun v => (hx v).1) (hp.trans_le hk) p hp henergy ed.1 ed.2 h11 h12 h21 h22)
      _ ≤ _ := by
        have hh := div_le_div_of_nonneg_left (sq_nonneg ell) hp hk
        calc
          _ ≤ ell^2/p+2*ell^2/p := add_le_add hh le_rfl
          _ = _ := by ring
  · have hz : prob μ (badPair H G W f ed)=0 := by simp only [prob,expect,badPair,he,false_and,↓reduceIte,mul_zero,Finset.sum_const_zero]
    rw [hz]
    positivity

 theorem bad_probability {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n)) (x : Fin n → ℝ)
    (ell : ℝ) (W : Finset (Fin n)) [Nonempty W] (f : List (List (Fin n) × ℝ))
    (hf : PathOutcome G x ell W f) (hell : 0 ≤ ell) (hx : ∀ v,0 ≤ x v ∧ x v ≤ 1)
    (p : ℝ) (hp : 0 < p) (hk : p ≤ vertexSum x Finset.univ)
    (henergy : edgeEnergy G x ≤ (vertexSum x Finset.univ)^2/p)
    (hbudget : 12*(Fintype.card (EdgeIndex H):ℝ)^2*ell^2 ≤ p) :
    prob (sampler H G x ell W f hf) (bad H G W f) ≤ 1/4 := by
  calc
    _ ≤ ∑ ed : EdgeIndex H × EdgeIndex H,prob (sampler H G x ell W f hf) (badPair H G W f ed) := prob_exists _ _
    _ ≤ ∑ _ed : EdgeIndex H × EdgeIndex H,3*ell^2/p :=
      Finset.sum_le_sum (fun ed _ => badPair_bound H G x ell W f hf hell hx p hp hk henergy ed)
    _ = (Fintype.card (EdgeIndex H):ℝ)^2*(3*ell^2/p) := by simp [Fintype.card_prod,pow_two,nsmul_eq_mul,mul_assoc]
    _ ≤ _ := by
      apply (mul_le_mul_iff_right₀ hp).mp
      calc
        _ = 3*(Fintype.card (EdgeIndex H):ℝ)^2*ell^2 := by field_simp <;> ring
        _ ≤ (1/4)*p := by linarith
        _ = p*(1/4) := by ring

end EdgeSublinearMWIS.Main.PathMass
end

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PathMass
open FiniteLaw

 theorem good_sample {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n)) (x : Fin n → ℝ)
    (ell : ℝ) (W : Finset (Fin n)) [Nonempty W] (f : List (List (Fin n) × ℝ))
    (hf : PathOutcome G x ell W f) (hell : 0 < ell) (hx : ∀ v,0 ≤ x v ∧ x v ≤ 1)
    (p : ℝ) (hp : 0 < p) (hk : p ≤ vertexSum x Finset.univ)
    (henergy : edgeEnergy G x ≤ (vertexSum x Finset.univ)^2/p)
    (hbudget : 12*(Fintype.card (EdgeIndex H):ℝ)^2*ell^2 ≤ p)
    (hE : 0 < Fintype.card (EdgeIndex H)) :
    ∃ E : AlmostEmbedding H G,E.Induced ∧
      (∀ v,E.vertex v∈W) ∧
      (∀ (e : EdgeIndex H) (v : Fin n), v∈E.path e → v∈W) ∧
      (∑ e : EdgeIndex H,((E.path e).length:ℝ)) ≤ 4*ell*Fintype.card (EdgeIndex H) := by
  let μ := sampler H G x ell W f hf
  have hbad := bad_probability H G x ell W f hf hell.le hx p hp hk henergy hbudget
  have hlong := long_total_bound H G x ell W f hf hell (fun v => (hx v).1) (hp.trans_le hk) hE
  obtain ⟨ω,hω,hgood,hlength⟩ := good_outcome μ (bad H G W f)
    (fun ω => 4*ell*Fintype.card (EdgeIndex H) ≤ totalLength H W f ω) (by linarith)
  let E : AlmostEmbedding H G := {
    vertex v := (ω.1 v).val
    path e := f[ω.2 e].1
    valid e := by
      have hv := (hf.2.1 _ (List.getElem_mem (ω.2 e).isLt)).2
      exact ⟨⟨hv.1,hv.2.1,fun v hv => Finset.mem_univ v,hv.2.2.2⟩,
        positive_endpoints H G x ell W f hf ω hω e⟩
    disjoint e d h11 h12 h21 h22 v hv hd := by
      exact hgood ⟨(e,d),⟨h11,h12,h21,h22⟩,Or.inl ⟨v,hv,hd⟩⟩ }
  refine ⟨E,?_,?_,?_,?_⟩
  · intro e d h11 h12 h21 h22 u hu v hv huv
    exact hgood ⟨(e,d),⟨h11,h12,h21,h22⟩,Or.inr ⟨u,hu,v,hv,huv⟩⟩
  · intro v
    exact (ω.1 v).property
  · intro e v hv
    exact (hf.2.1 _ (List.getElem_mem (ω.2 e).isLt)).2.2.2.1 v hv
  · exact le_of_lt (lt_of_not_ge hlength)

end EdgeSublinearMWIS.Main.PathMass
end

noncomputable section

open scoped BigOperators Classical
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.PathMass
set_option autoImplicit false

theorem solution {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n))
    (x : Fin n → ℝ) (ell : ℝ) (W : Finset (Fin n)) (f : List (List (Fin n) × ℝ))
    (hf : PathOutcome G x ell W f) (hell : 1 ≤ ell) (hx : ∀ v,0 ≤ x v ∧ x v ≤ 1)
    (p : ℝ) (hp : 0 < p) (hk : p ≤ vertexSum x Finset.univ)
    (henergy : edgeEnergy G x ≤ (vertexSum x Finset.univ)^2/p)
    (hbudget : 12*(Fintype.card (EdgeIndex H):ℝ)^2*ell^2 ≤ p)
    (hE : 0 < Fintype.card (EdgeIndex H)) :
    ∃ E : AlmostEmbedding H G,E.Induced ∧ (∀ v,E.vertex v∈W) ∧
      (∀ (e : EdgeIndex H) (v : Fin n),v∈E.path e → v∈W) ∧
      (∑ e : EdgeIndex H,((E.path e).length:ℝ)) ≤ 4*ell*Fintype.card (EdgeIndex H) := by
  classical
  letI : Nonempty W := by
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (order_pos G x ell W f hf)
    exact ⟨⟨v,hv⟩⟩
  exact good_sample H G x ell W f hf (by linarith) hx p hp hk henergy hbudget hE
end
