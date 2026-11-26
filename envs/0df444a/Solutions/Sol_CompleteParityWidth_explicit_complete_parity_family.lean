-- Prove2me | solution 1 for CompleteParityWidth.explicit_complete_parity_family
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T21:29:09.953221+00:00
-- url     : https://prove2.me/submissions/49a9d3e8-bcee-415d-b18a-86c5ce7e1ee8

import Definitions.Def_CompleteParityWidth

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace CompleteParityWidth

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def row (v : V) (x : Assignment V) : Bit :=
  ∑ e ∈ Finset.univ.filter (incident v), x e

def Entails (charge : V → Bit) (S : Finset V) (C : Clause V) : Prop :=
  ∀ x : Assignment V, (∀ v ∈ S, row v x = charge v) → Holds x C

def varSet (C : Clause V) : Finset (Arc V) :=
  C.image Prod.fst

def width (C : Clause V) : ℕ := (varSet C).card

theorem proper_rows_satisfiable (charge : V → Bit) (S : Finset V) (r : V)
    (absent : r ∉ S) :
    ∃ x : Assignment V, ∀ v ∈ S, row v x = charge v := by
  let x : Assignment V := fun e => if e.1 ∈ S ∧ e.2 = r then charge e.1 else 0
  refine ⟨x, ?_⟩
  intro v hv
  have vr : v ≠ r := fun equal => absent (equal ▸ hv)
  unfold row
  rw [Finset.sum_eq_single (v,r)]
  · simp [x,hv]
  · rintro ⟨a,b⟩ held other
    by_cases written : a ∈ S ∧ b = r
    · have inc := (Finset.mem_filter.mp held).2
      rcases inc.2 with equal | equal
      · exact (other (Prod.ext equal written.2)).elim
      · exact (vr (equal.symm.trans written.2)).elim
    · simp [x,written]
  · intro missing
    exact (missing (Finset.mem_filter.mpr ⟨Finset.mem_univ _, vr, Or.inl rfl⟩)).elim

private theorem two_mul_zero (x : Bit) : 2 * x = 0 := by
  have h : (2 : Bit) = 0 := by decide
  rw [h,zero_mul]

theorem row_total_zero (x : Assignment V) : ∑ v, row v x = 0 := by
  classical
  simp only [row, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  rintro ⟨a,b⟩ -
  by_cases equal : a = b
  · simp [incident,equal]
  · calc
      _ = ∑ v : V, ((if a = v then x (a,b) else 0) + (if b = v then x (a,b) else 0)) := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases a_at : a = v <;> by_cases b_at : b = v
        · exact (equal (a_at.trans b_at.symm)).elim
        · have inc : incident v (a,b) := ⟨equal,Or.inl a_at⟩
          rw [if_pos inc, if_pos a_at, if_neg b_at, add_zero]
        · have inc : incident v (a,b) := ⟨equal,Or.inr b_at⟩
          rw [if_pos inc, if_neg a_at, if_pos b_at, zero_add]
        · have inc : ¬ incident v (a,b) := fun h => h.2.elim a_at b_at
          rw [if_neg inc,if_neg a_at,if_neg b_at,zero_add]
      _ = 0 := by
        simp only [Finset.sum_add_distrib]
        rw [show (∑ v : V, if a = v then x (a,b) else 0) = x (a,b) by
          simp, show (∑ v : V, if b = v then x (a,b) else 0) = x (a,b) by
          simp, ← two_mul, two_mul_zero]

theorem contradiction (charge : V → Bit) (odd : ∑ v, charge v = 1) :
    ¬ ∃ x : Assignment V, ∀ v, row v x = charge v := by
  rintro ⟨x,hx⟩
  have eq : (∑ v, row v x) = ∑ v, charge v := Finset.sum_congr rfl (fun v _ => hx v)
  rw [row_total_zero,odd] at eq
  exact (zero_ne_one : (0 : Bit) ≠ 1) eq

inductive RefutationTree (charge : V → Bit) : Clause V → Type _
  | input (C : Clause V) (v : V)
      (valid : ∀ x, row v x = charge v → Holds x C) : RefutationTree charge C
  | infer {A B C : Clause V} (left : RefutationTree charge A) (right : RefutationTree charge B)
      (valid : ∀ x, Holds x A → Holds x B → Holds x C) : RefutationTree charge C

variable {charge : V → Bit}

theorem support_exists (odd : ∑ v, charge v = 1) (C : Clause V) :
    ∃ n : ℕ, ∃ S : Finset V, S.card = n ∧ Entails charge S C := by
  refine ⟨Fintype.card V, Finset.univ, Finset.card_univ, ?_⟩
  intro x good
  exact (contradiction charge odd ⟨x, fun v => good v (Finset.mem_univ v)⟩).elim

noncomputable def need (odd : ∑ v, charge v = 1) (C : Clause V) : ℕ := by
  classical
  exact Nat.find (support_exists odd C)

theorem choose (odd : ∑ v, charge v = 1) (C : Clause V) :
    ∃ S : Finset V, S.card = need odd C ∧ Entails charge S C := by
  classical
  exact Nat.find_spec (support_exists odd C)

theorem need_le (odd : ∑ v, charge v = 1) {S : Finset V} {C : Clause V}
    (entails : Entails charge S C) : need odd C ≤ S.card := by
  classical
  exact Nat.find_min' (support_exists odd C) ⟨S,rfl,entails⟩

theorem need_empty (odd : ∑ v, charge v = 1) :
    need odd (∅ : Clause V) = Fintype.card V := by
  obtain ⟨S,number,entails⟩ := choose odd (∅ : Clause V)
  have full : S = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    by_contra absent
    obtain ⟨x,hx⟩ := proper_rows_satisfiable charge S v absent
    obtain ⟨p,hp,_⟩ := entails x hx
    exact Finset.notMem_empty _ hp
  rw [← number,full,Finset.card_univ]

theorem need_axiom (odd : ∑ v, charge v = 1) {C : Clause V} (v : V)
    (valid : ∀ x, row v x = charge v → Holds x C) :
    need odd C ≤ 1 := by
  have singletonSupport : Entails charge {v} C := fun x h => valid x (h v (by simp))
  simpa using need_le odd singletonSupport

theorem need_infer (odd : ∑ v, charge v = 1) {A B C : Clause V}
    (valid : ∀ x, Holds x A → Holds x B → Holds x C) :
    need odd C ≤ need odd A + need odd B := by
  obtain ⟨S,sSize,sValid⟩ := choose odd A
  obtain ⟨T,tSize,tValid⟩ := choose odd B
  have both : Entails charge (S ∪ T) C := by
    intro x h
    exact valid x (sValid x fun v hv => h v (Finset.mem_union_left _ hv))
      (tValid x fun v hv => h v (Finset.mem_union_right _ hv))
  calc
    _ ≤ (S ∪ T).card := need_le odd both
    _ ≤ S.card + T.card := Finset.card_union_le _ _
    _ = _ := by rw [sSize,tSize]

inductive Contains {charge : V → Bit} (target : Clause V) :
    {C : Clause V} → RefutationTree charge C → Prop
  | self {T : RefutationTree charge target} : Contains target T
  | left {A B C : Clause V} {l : RefutationTree charge A} {r : RefutationTree charge B}
      {valid : ∀ x, Holds x A → Holds x B → Holds x C} :
      Contains target l → Contains target (RefutationTree.infer l r valid)
  | right {A B C : Clause V} {l : RefutationTree charge A} {r : RefutationTree charge B}
      {valid : ∀ x, Holds x A → Holds x B → Holds x C} :
      Contains target r → Contains target (RefutationTree.infer l r valid)

theorem balanced_node (odd : ∑ v, charge v = 1) (k : ℕ) (positive : 1 ≤ k)
    {C : Clause V} (T : RefutationTree charge C) (large : k < need odd C) :
    ∃ D : Clause V, Contains D T ∧ k < need odd D ∧ need odd D ≤ 2*k := by
  induction T with
  | input C v valid =>
      exact (Nat.not_lt_of_ge ((need_axiom odd v valid).trans positive) large).elim
  | @infer A B C l r valid ihL ihR =>
    by_cases aLarge : k < need odd A
    · obtain ⟨D,inside,h1,h2⟩ := ihL aLarge
      exact ⟨D,.left inside,h1,h2⟩
    by_cases bLarge : k < need odd B
    · obtain ⟨D,inside,h1,h2⟩ := ihR bLarge
      exact ⟨D,.right inside,h1,h2⟩
    have sum := need_infer odd valid
    exact ⟨C,.self,large,by omega⟩



theorem row_update (v : V) (x : Assignment V) (e : Arc V) (delta : Bit) :
    row v (Function.update x e (x e + delta)) =
      row v x + if incident v e then delta else 0 := by
  have rewrite (f : Arc V) :
      Function.update x e (x e + delta) f = x f + (if f = e then delta else 0) := by
    by_cases same : f = e
    · subst f
      simp
    · simp [same]
  simp only [row,rewrite,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_filter,
    Finset.mem_univ,true_and]

/-- A single crossing variable can repair the inside equation while leaving the clause and all
other supporting equations unchanged. Consequently each crossing variable occurs in the clause. -/
theorem cut_arc_occurs (odd : ∑ v, charge v = 1) {S : Finset V} {C : Clause V}
    (size : S.card = need odd C) (entails : Entails charge S C)
    {u r : V} (inside : u ∈ S) (outside : r ∉ S) : (u,r) ∈ varSet C := by
  classical
  by_contra missing
  have smaller : ¬ Entails charge (S.erase u) C := by
    intro another
    have shorter := need_le odd another
    have drop := Finset.card_erase_lt_of_mem inside
    omega
  unfold Entails at smaller
  obtain ⟨x,hx⟩ := not_forall.mp smaller
  obtain ⟨others,notClause⟩ := Classical.not_imp.mp hx
  let delta := charge u - row u x
  let y := Function.update x (u,r) (x (u,r) + delta)
  have different : u ≠ r := fun h => outside (h ▸ inside)
  have works : ∀ v ∈ S, row v y = charge v := by
    intro v hv
    by_cases equal : v = u
    · subst v
      have inc : incident u (u,r) := ⟨different,Or.inl rfl⟩
      dsimp only [y]
      rw [row_update,if_pos inc]
      dsimp only [delta]
      abel
    · have inc : ¬ incident v (u,r) := by
        rintro ⟨_, left | right⟩
        · exact equal left.symm
        · change r = v at right
          exact outside (right.symm ▸ hv)
      dsimp only [y]
      rw [row_update,if_neg inc,add_zero]
      exact others v (Finset.mem_erase.mpr ⟨equal,hv⟩)
  obtain ⟨p,listed,lit⟩ := entails y works
  have unaffected : p.1 ≠ (u,r) := fun eq =>
    missing (Finset.mem_image.mpr ⟨p,listed,eq⟩)
  apply notClause
  exact ⟨p,listed,by simpa only [y, Function.update_of_ne unaffected] using lit⟩

theorem support_width_bound (odd : ∑ v, charge v = 1) {S : Finset V} {C : Clause V}
    (size : S.card = need odd C) (entails : Entails charge S C) :
    S.card * (Fintype.card V - S.card) ≤ width C := by
  have covered : S ×ˢ Sᶜ ⊆ varSet C := by
    rintro ⟨u,r⟩ member
    obtain ⟨inside,outside⟩ := Finset.mem_product.mp member
    exact cut_arc_occurs odd size entails inside (Finset.mem_compl.mp outside)
  have lower := Finset.card_le_card covered
  simpa [width,Finset.card_compl] using lower

/-- A complete-graph parity contradiction forces a quadratically wide clause even when
binary inference may use arbitrary semantic entailment, rather than just resolution. -/
theorem complete_parity_width (odd : ∑ v, charge v = 1) (k : ℕ)
    (positive : 1 ≤ k) (fit : 3*k ≤ Fintype.card V)
    (proof : RefutationTree charge (∅ : Clause V)) :
    ∃ C, Contains C proof ∧ k*k ≤ width C := by
  have enough : k < need odd (∅ : Clause V) := by rw [need_empty odd]; omega
  obtain ⟨C,used,lo,hi⟩ := balanced_node odd k positive proof enough
  obtain ⟨S,size,entails⟩ := choose odd C
  refine ⟨C,used,?_⟩
  have large : k ≤ S.card := by omega
  have outside : k ≤ Fintype.card V-S.card := by omega
  exact (Nat.mul_le_mul large outside).trans (support_width_bound odd size entails)

omit [Fintype V] in
/-- Ordinary resolution is a binary semantic inference in the finite-clause model. -/
theorem resolution_entailment (e : Arc V) (A B : Clause V) (x : Assignment V)
    (left : Holds x A) (right : Holds x B) :
    Holds x ((A.erase (e,0)) ∪ (B.erase (e,1))) := by
  obtain ⟨a,aMem,holdsA⟩ := left
  obtain ⟨b,bMem,holdsB⟩ := right
  by_cases fromLeft : a = (e,0)
  · by_cases fromRight : b = (e,1)
    · subst a
      subst b
      exact ((zero_ne_one : (0 : Bit) ≠ 1) (holdsA.symm.trans holdsB)).elim
    · exact ⟨b, Finset.mem_union_right _
        (Finset.mem_erase.mpr ⟨fromRight,bMem⟩), holdsB⟩
  · exact ⟨a, Finset.mem_union_left _
      (Finset.mem_erase.mpr ⟨fromLeft,aMem⟩), holdsA⟩


theorem incidentArcs_card (v : V) : (incidentArcs v).card ≤ 2*Fintype.card V := by
  let out : Finset (Arc V) := Finset.univ.image (fun u => (v,u))
  let incoming : Finset (Arc V) := Finset.univ.image (fun u => (u,v))
  have outSmall : out.card ≤ Fintype.card V := Finset.card_image_le.trans_eq Finset.card_univ
  have inSmall : incoming.card ≤ Fintype.card V := Finset.card_image_le.trans_eq Finset.card_univ
  have inside : incidentArcs v ⊆ out ∪ incoming := by
    rintro ⟨a,b⟩ held
    obtain ⟨_,hit | hit⟩ := (Finset.mem_filter.mp held).2
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b,Finset.mem_univ b,Prod.ext hit.symm rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ a,Prod.ext rfl hit.symm⟩)
  have small := (Finset.card_le_card inside).trans (Finset.card_union_le out incoming)
  omega

private theorem row_as_subtype (v : V) (x : Assignment V) :
    (∑ e : ↥(incidentArcs v), x e.val) = row v x := by
  change (∑ e ∈ (incidentArcs v).attach, x e.val) =
    (∑ e ∈ incidentArcs v, x e)
  rw [Finset.sum_attach]

private theorem bit_values (x : Bit) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem bit_eq_of_not_other (a b : Bit) (different : a ≠ b+1) : a = b := by
  rcases bit_values a with rfl | rfl <;> rcases bit_values b with rfl | rfl
  · rfl
  · exact (different (by decide)).elim
  · exact (different (by decide)).elim
  · rfl

theorem rowCNF_exact (v : V) (target : Bit) (x : Assignment V) :
    (∀ C ∈ rowCNF v target, Holds x C) ↔ row v x = target := by
  constructor
  · intro sat
    by_contra wrong
    let bad : ↥(incidentArcs v) → Bit := fun e => x e.val
    have sumWrong : (∑ e, bad e) ≠ target := by
      have sum := row_as_subtype v x
      exact fun h => wrong (sum.symm.trans h)
    have appears : patternClause v bad ∈ rowCNF v target := Finset.mem_image.mpr
      ⟨bad,Finset.mem_filter.mpr ⟨Finset.mem_univ bad,sumWrong⟩,rfl⟩
    obtain ⟨lit,present,matched⟩ := sat _ appears
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp present
    have relation : x e.val + 0 = x e.val + 1 := by
      simpa only [bad, Prod.fst, Prod.snd, add_zero] using matched
    have impossible : (0 : Bit) = 1 := add_left_cancel relation
    exact (zero_ne_one : (0 : Bit) ≠ 1) impossible
  · intro sound C contains
    obtain ⟨bad,badMem,rfl⟩ := Finset.mem_image.mp contains
    have parityWrong := (Finset.mem_filter.mp badMem).2
    by_contra missing
    have same (e : ↥(incidentArcs v)) : x e.val = bad e := by
      apply bit_eq_of_not_other
      intro hit
      exact missing ⟨(e.val,bad e+1),Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩,hit⟩
    apply parityWrong
    rw [← sound, ← row_as_subtype]
    exact Finset.sum_congr rfl (fun e _ => (same e).symm)

private theorem patternClause_width (v : V) (bad : ↥(incidentArcs v) → Bit) :
    width (patternClause v bad) ≤ (incidentArcs v).card := by
  apply Finset.card_le_card
  intro e appears
  obtain ⟨p,here,rfl⟩ := Finset.mem_image.mp appears
  obtain ⟨edge,_,rfl⟩ := Finset.mem_image.mp here
  exact edge.property

theorem rowCNF_width (v : V) (target : Bit) {C : Clause V} (present : C ∈ rowCNF v target) :
    width C ≤ 2*Fintype.card V := by
  obtain ⟨bad,_,rfl⟩ := Finset.mem_image.mp present
  exact (patternClause_width v bad).trans (incidentArcs_card v)

theorem rowCNF_card (v : V) (target : Bit) :
    (rowCNF v target).card ≤ 2^(2*Fintype.card V) := by
  calc
    _ ≤ (Finset.univ : Finset (↥(incidentArcs v) → Bit)).card :=
      Finset.card_image_le.trans (Finset.card_filter_le _ _)
    _ = 2^((incidentArcs v).card) := by simp [ZMod.card]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (incidentArcs_card v)

theorem parityCNF_width (charge : V → Bit) {C : Clause V} (present : C ∈ parityCNF charge) :
    width C ≤ 2*Fintype.card V := by
  obtain ⟨v,_,p⟩ := Finset.mem_biUnion.mp present
  exact rowCNF_width v _ p

theorem parityCNF_card (charge : V → Bit) :
    (parityCNF charge).card ≤ Fintype.card V * 2^(2*Fintype.card V) := by
  calc
    _ ≤ ∑ v, (rowCNF v (charge v)).card := Finset.card_biUnion_le
    _ ≤ ∑ _ : V, 2^(2*Fintype.card V) :=
      Finset.sum_le_sum (fun v _ => rowCNF_card v _)
    _ = _ := by simp

theorem parityCNF_unsatisfiable (odd : ∑ v, charge v = 1) :
    ¬ ∃ x, ∀ C ∈ parityCNF charge, Holds x C := by
  rintro ⟨x,sat⟩
  apply contradiction charge odd
  refine ⟨x,fun v => (rowCNF_exact v _ x).mp ?_⟩
  intro C present
  exact sat C (Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ _,present⟩)

def rowCNF_is_input {C : Clause V} {v : V} (present : C ∈ rowCNF v (charge v)) :
    RefutationTree charge C :=
  .input C v fun x solution => (rowCNF_exact v _ x).mpr solution C present


theorem parityCNF_literal_width (charge : V → Bit) {C : Clause V}
    (present : C ∈ parityCNF charge) : C.card ≤ 2*Fintype.card V := by
  obtain ⟨v,_,p⟩ := Finset.mem_biUnion.mp present
  obtain ⟨bad,_,rfl⟩ := Finset.mem_image.mp p
  exact Finset.card_image_le.trans ((Fintype.card_coe (incidentArcs v)).le.trans (incidentArcs_card v))

private theorem merge_bounds {A B C : Clause V}
    (l : RefutationTree charge A) (r : RefutationTree charge B)
    (valid : ∀ x, Holds x A → Holds x B → Holds x C) {limit : ℕ}
    (atMostLeft : ∀ D, Contains D l → width D ≤ limit)
    (atMostRight : ∀ D, Contains D r → width D ≤ limit) (atMostHere : C.card ≤ limit) :
    ∀ D, Contains D (RefutationTree.infer l r valid) → width D ≤ limit := by
  intro D supported
  cases supported with
  | self => exact Finset.card_image_le.trans atMostHere
  | left inside => exact atMostLeft _ inside
  | right inside => exact atMostRight _ inside

theorem resolution_model {limit : ℕ} {C : Clause V}
    (derivation : BoundedResolution (parityCNF charge) limit C) :
    ∃ T : RefutationTree charge C, ∀ D, Contains D T → width D ≤ limit := by
  induction derivation with
  | premise presented room =>
    obtain ⟨v,_,source⟩ := Finset.mem_biUnion.mp presented
    refine ⟨rowCNF_is_input source,?_⟩
    intro D appears
    cases appears
    exact Finset.card_image_le.trans room
  | resolve e _ _ room ihLeft ihRight =>
    obtain ⟨l,lSmall⟩ := ihLeft
    obtain ⟨r,rSmall⟩ := ihRight
    refine ⟨.infer l r (fun x => resolution_entailment e _ _ x), ?_⟩
    exact merge_bounds l r _ lSmall rSmall room
  | @weaken A C subset _ room ih =>
    obtain ⟨l,lSmall⟩ := ih
    have valid : ∀ x, Holds x A → Holds x A → Holds x C := fun x one _ => by
      obtain ⟨p,present,hit⟩ := one
      exact ⟨p,subset present,hit⟩
    exact ⟨.infer l l valid, merge_bounds l l valid lSmall lSmall room⟩

/-- This rules out every ordinary resolution derivation with literal width less than k squared.
Sharing subderivations cannot remove a width requirement, since the judgment has no size bound. -/
theorem resolution_width_lower (odd : ∑ v, charge v = 1) (k : ℕ)
    (positive : 1 ≤ k) (fit : 3*k ≤ Fintype.card V) (limit : ℕ)
    (derivation : BoundedResolution (parityCNF charge) limit (∅ : Clause V)) :
    k*k ≤ limit := by
  obtain ⟨T,bounded⟩ := resolution_model derivation
  obtain ⟨C,appears,wide⟩ := complete_parity_width odd k positive fit T
  exact wide.trans (bounded C appears)

theorem sum_oneCharge (root : V) : ∑ v, oneCharge root v = 1 := by
  simp [oneCharge]

end CompleteParityWidth

open CompleteParityWidth

theorem solution (n : ℕ) (enough : 3 ≤ n) :
    let charge : Fin n → Bit := oneCharge ⟨0,by omega⟩
    let F := parityCNF charge
    (¬ ∃ x, ∀ C ∈ F, Holds x C) ∧ F.card ≤ n * 2^(2*n) ∧
      (∀ C ∈ F, C.card ≤ 2*n) ∧
      ∀ w, BoundedResolution F w ∅ → (n/3)*(n/3) ≤ w := by
  dsimp only
  have odd := sum_oneCharge (⟨0,by omega⟩ : Fin n)
  refine ⟨parityCNF_unsatisfiable odd,?_,?_,?_⟩
  · simpa using parityCNF_card (oneCharge (⟨0,by omega⟩ : Fin n))
  · intro C present
    simpa using parityCNF_literal_width _ present
  · intro w derives
    apply resolution_width_lower odd (n/3) (by omega) _ w derives
    simpa using (show 3*(n/3) ≤ n by omega)

#print axioms solution
