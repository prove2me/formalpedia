-- Prove2me | solution 1 for CountOrderings.NFree.display_p17_count
-- status  : ACCEPTED   (prove)
-- author  : @bersubs
-- created : 2026-11-15T17:26:56.158768+00:00
-- url     : https://prove2.me/submissions/972189dc-caeb-4410-8832-469f23bd34ab

import Definitions.Def_CountOrderings_NFree_Poset
import Definitions.Def_CountOrderings_NFree_Reduction
import Theorems.Thm_CountOrderings_NFree_lemma_2_2
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Real.Basic

namespace CountOrderings.NFree

/-! A chain indexed by its positions has `q` leaves attached at each indexed
attachment place. Positions for hooks and attachments are one-based. -/

private def Spine (m : ℕ) {J : Type} (q : ℕ) (_attach : J → ℕ) : Type :=
  Fin m ⊕ (J × Fin q)

private instance {m q : ℕ} {J : Type} [Fintype J] (attach : J → ℕ) :
    Fintype (Spine m q attach) :=
  inferInstanceAs (Fintype (Fin m ⊕ (J × Fin q)))

private def node {m q : ℕ} {J : Type} (attach : J → ℕ) (p : Fin m) : Spine m q attach :=
  Sum.inl p

private def leaf {m q : ℕ} {J : Type} (attach : J → ℕ) (z : J × Fin q) : Spine m q attach :=
  Sum.inr z

private def spinePosition {m q : ℕ} {J : Type} {attach : J → ℕ} : Spine m q attach → ℕ
  | Sum.inl p => p.val + 1
  | Sum.inr z => attach z.1

private def spineLE {m q : ℕ} {J : Type} {attach : J → ℕ}
    (x y : Spine m q attach) : Prop :=
  match x with
  | Sum.inl p => p.val + 1 ≤ spinePosition y
  | Sum.inr _ => x = y

private instance {m q : ℕ} {J : Type} (attach : J → ℕ) :
    PartialOrder (Spine m q attach) where
  le := spineLE
  le_refl x := by
    rcases x with p | l
    · exact Nat.le_refl _
    · rfl
  le_trans x y z hxy hyz := by
    rcases x with p | x
    · rcases y with r | y
      · exact Nat.le_trans hxy hyz
      · exact (show Sum.inr y = z from hyz) ▸ hxy
    · exact (show Sum.inr x = y from hxy).symm ▸ hyz
  le_antisymm x y hxy hyx := by
    rcases x with p | x
    · rcases y with r | y
      · congr
        exact Fin.ext (Nat.add_right_cancel (Nat.le_antisymm hxy hyx))
      · exact (show Sum.inr y = Sum.inl p from hyx).symm
    · exact hxy

private theorem spine_rooted {m q : ℕ} {J : Type} (attach : J → ℕ) (hm : 0 < m)
    (hattach : ∀ j, 1 ≤ attach j ∧ attach j ≤ m) :
    IsRootedTreePoset (Spine m q attach) := by
  let root : Spine m q attach := Sum.inl ⟨0, hm⟩
  refine ⟨root, ?_, ?_⟩
  · intro x
    rcases x with p | j
    · change 1 ≤ p.val + 1
      omega
    · exact (hattach j.1).1
  · intro y hy
    suffices ∃ p : Spine m q attach, p < y ∧ ∀ x : Spine m q attach, x < y → x ≤ p from by
      obtain ⟨p, hp, hmax⟩ := this
      refine ⟨p, ⟨hp, fun x hpx hxy => (not_lt_of_ge (hmax x hxy)) hpx⟩, ?_⟩
      intro x hx
      have hxp := hmax x hx.lt
      by_contra hne
      exact hx.2 (lt_of_le_of_ne hxp hne) hp
    rcases y with p | j
    · have hp : 0 < p.val := by
        by_contra hn
        apply hy
        apply congrArg Sum.inl
        apply Fin.ext
        change p.val = 0
        omega
      let pred : Fin m := ⟨p.val - 1, by omega⟩
      refine ⟨Sum.inl pred, lt_of_le_of_ne ?_ ?_, ?_⟩
      · change p.val - 1 + 1 ≤ p.val + 1
        omega
      · intro heq
        have hval := congrArg Fin.val (Sum.inl.inj heq)
        change p.val - 1 = p.val at hval
        omega
      · intro x hx
        rcases x with r | l
        · have hle : r.val + 1 ≤ p.val + 1 := hx.le
          have hne : r.val ≠ p.val := fun h => hx.ne (congrArg Sum.inl (Fin.ext h))
          change r.val + 1 ≤ p.val - 1 + 1
          omega
        · exact False.elim (hx.ne hx.le)
    · have hj := hattach j.1
      let pred : Fin m := ⟨attach j.1 - 1, by omega⟩
      refine ⟨Sum.inl pred, lt_of_le_of_ne ?_ (fun h => ?_), ?_⟩
      · change attach j.1 - 1 + 1 ≤ attach j.1
        omega
      · cases h
      · intro x hx
        rcases x with p | l
        · have hle : p.val + 1 ≤ attach j.1 := hx.le
          change p.val + 1 ≤ attach j.1 - 1 + 1
          omega
        · exact False.elim (hx.ne hx.le)

private theorem spine_leaf_hook {m q : ℕ} {J : Type} [Fintype J] (attach : J → ℕ)
    (z : J × Fin q) : upSetCard (leaf (m := m) attach z) = 1 := by
  classical
  let v := leaf (m := m) attach z
  have hset : (Finset.univ.filter (fun x : Spine m q attach => v ≤ x)) = {v} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact Eq.comm
  change upSetCard v = 1
  rw [upSetCard, hset, Finset.card_singleton]

private theorem spine_chain_hook {m q : ℕ} {J : Type} [Fintype J] (attach : J → ℕ)
    (p : Fin m) : upSetCard (node (q := q) attach p) =
      (m - p.val) + q * (Finset.univ.filter (fun j => p.val + 1 ≤ attach j)).card := by
  classical
  let positions : Finset (Fin m) := Finset.univ.filter (fun r => p ≤ r)
  let attachments : Finset J := Finset.univ.filter (fun j => p.val + 1 ≤ attach j)
  let above : Finset (Fin m ⊕ (J × Fin q)) := Finset.univ.filter
    (fun x => spineLE (node (q := q) attach p) x)
  have hset : above = positions.disjSum (attachments ×ˢ (Finset.univ : Finset (Fin q))) := by
    ext x
    rcases x with r | ⟨j, k⟩
    · simp only [above, positions, Finset.mem_filter, Finset.mem_univ,
        Finset.inl_mem_disjSum, true_and]
      change p.val + 1 ≤ r.val + 1 ↔ p.val ≤ r.val
      omega
    · simp only [above, attachments, Finset.mem_filter, Finset.mem_univ, Finset.inr_mem_disjSum,
        Finset.mem_product, true_and, and_true]
      rfl
  have hpos : positions.card = m - p.val := by
    let e : Fin (m - p.val) ≃ ↥positions := {
      toFun := fun t => ⟨⟨p.val + t.val, by have := p.isLt; have := t.isLt; omega⟩, by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, Nat.le_add_right _ _⟩⟩
      invFun := fun r => ⟨r.val.val - p.val, by have := r.val.isLt; omega⟩
      left_inv := fun t => Fin.ext (by simp)
      right_inv := fun r => Subtype.ext (Fin.ext (by
        have hr : p.val ≤ r.val.val := (Finset.mem_filter.mp r.2).2
        exact Nat.add_sub_of_le hr))
    }
    simpa using (Fintype.card_congr e).symm
  change above.card = _
  rw [hset, Finset.card_disjSum, Finset.card_product, Finset.card_univ,
    Fintype.card_fin, hpos, Nat.mul_comm q]

private abbrev AttachmentIndex (I : X3CInstance) := Fin (3 * I.h) ⊕ Fin I.n

private def rootSetEdge {I : X3CInstance} (i : Fin I.n) : OrigEdge I :=
  ⟨.rootSet i, trivial⟩

private noncomputable def attachment {I : X3CInstance} (σ : Fin (4 * I.n) ≃ OrigEdge I) :
    AttachmentIndex I → ℕ
  | .inl j => rho σ j
  | .inr i => (σ.symm (rootSetEdge i)).val + 1

private def copyLayout {n m q : ℕ} : CopyEdge n m q ≃ (Fin m ⊕ Fin n) × Fin q where
  toFun
    | .elemCopy j k => (.inl j, k)
    | .setCopy i k => (.inr i, k)
  invFun
    | (.inl j, k) => .elemCopy j k
    | (.inr i, k) => .setCopy i k
  left_inv := by intro e; cases e <;> rfl
  right_inv := by rintro ⟨j | i, k⟩ <;> rfl

private def layout (I : X3CInstance) (q : ℕ) (σ : Fin (4 * I.n) ≃ OrigEdge I) :
    posetP I q ≃ Spine (4 * I.n) q (attachment σ) :=
  σ.symm.sumCongr copyLayout

private theorem rho_ge_position {I : X3CInstance} (σ : Fin (4 * I.n) ≃ OrigEdge I)
    (j : Fin (3 * I.h)) (p : Fin (4 * I.n)) (hp : ∃ i : Fin I.n, (σ p).1 = .setElem i j) :
    p.val + 1 ≤ rho σ j := by
  classical
  unfold rho
  apply Finset.le_sup (f := fun p : Fin (4 * I.n) => p.val + 1)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩

private theorem rho_has_position {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) :
    ∃ p : Fin (4 * I.n), p.val + 1 = rho σ j ∧ ∃ i : Fin I.n, (σ p).1 = .setElem i j := by
  classical
  let positions : Finset (Fin (4 * I.n)) := Finset.univ.filter
    (fun p => ∃ i : Fin I.n, (σ p).1 = .setElem i j)
  have hn : positions.Nonempty := by
    obtain ⟨i, hi⟩ := hI.1 j
    let e : OrigEdge I := ⟨.setElem i j, hi⟩
    refine ⟨σ.symm e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, ?_⟩⟩
    rw [σ.apply_symm_apply]
  obtain ⟨p, hp, hmax⟩ := positions.exists_max_image (fun p => p.val + 1) hn
  refine ⟨p, ?_, (Finset.mem_filter.mp hp).2⟩
  change p.val + 1 = positions.sup (fun p => p.val + 1)
  exact le_antisymm (Finset.le_sup (f := fun p : Fin (4 * I.n) => p.val + 1) hp)
    (Finset.sup_le hmax)

private theorem attachment_bounds {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : AttachmentIndex I) :
    1 ≤ attachment σ j ∧ attachment σ j ≤ 4 * I.n := by
  rcases j with j | i
  · obtain ⟨p, hp, _⟩ := rho_has_position hI σ j
    change 1 ≤ rho σ j ∧ rho σ j ≤ 4 * I.n
    rw [← hp]
    have := p.isLt
    omega
  · change 1 ≤ (σ.symm (rootSetEdge i)).val + 1 ∧
      (σ.symm (rootSetEdge i)).val + 1 ≤ 4 * I.n
    have := (σ.symm (rootSetEdge i)).isLt
    omega

private theorem copy_attachment_witness {I : X3CInstance} (hI : I.Standing) (q : ℕ)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (c : CopyEdge I.n (3 * I.h) q) :
    ∃ p : Fin (4 * I.n), p.val + 1 = attachment σ (copyLayout c).1 ∧
      (dagA I q).Follows (Sum.inl (σ p)) (Sum.inr c) := by
  cases c with
  | elemCopy j k =>
    obtain ⟨p, hp, i, hi⟩ := rho_has_position hI σ j
    refine ⟨p, hp, ?_⟩
    change Sum.inl ((σ p).tgt) = Sum.inl (BaseVertex.elem j)
    simp [OrigEdge.tgt, hi]
  | setCopy i k =>
    refine ⟨σ.symm (rootSetEdge i), rfl, ?_⟩
    change Sum.inl ((σ (σ.symm (rootSetEdge i))).tgt) = Sum.inl (BaseVertex.set i)
    rw [σ.apply_symm_apply]
    rfl

private theorem follows_le_layout {I : X3CInstance} {q : ℕ}
    {σ : Fin (4 * I.n) ≃ OrigEdge I} (hσ : σ ∈ omegaLE I)
    (e f : posetP I q) (hef : (dagA I q).Follows e f) : layout I q σ e ≤ layout I q σ f := by
  classical
  have hσorder : ∀ x y : OrigEdge I, (baseDAG I).EdgeLE x y → σ.symm x ≤ σ.symm y :=
    (Finset.mem_filter.mp hσ).2
  rcases e with e | e <;> rcases f with f | f
  · have hbase : (baseDAG I).Follows e f := Sum.inl.inj hef
    exact Nat.succ_le_succ (hσorder e f (Relation.ReflTransGen.single hbase))
  · rcases e with ⟨e, he⟩
    cases e <;> cases f <;>
      simp_all only [FinDigraph.Follows, dagA, OrigEdge.tgt, Sum.inl.injEq,
        BaseVertex.elem.injEq, BaseVertex.set.injEq, reduceCtorEq]
    · subst_vars
      exact Nat.le_refl _
    · subst_vars
      rename_i i j k
      change _ ≤ rho σ _
      apply rho_ge_position
      refine ⟨i, ?_⟩
      let v : OrigEdge I := ⟨.setElem i j, he⟩
      exact congrArg (fun e : OrigEdge I => e.1) (σ.apply_symm_apply v)
  · cases e <;> simp [FinDigraph.Follows, dagA] at hef
  · cases e <;> cases f <;> simp [FinDigraph.Follows, dagA] at hef

private abbrev GadgetRank (I : X3CInstance) (q : ℕ) :=
  posetP I q ≃ Fin (Fintype.card (posetP I q))

private def respectsProjection (I : X3CInstance) (q : ℕ) (σ : Fin (4 * I.n) ≃ OrigEdge I)
    (L : GadgetRank I q) : Prop :=
  L ∈ FCP.Order.LinearExtensions (posetP I q) ∧
    ∀ a b : Fin (4 * I.n), a < b → L (Sum.inl (σ a)) < L (Sum.inl (σ b))

private theorem respectsProjection_iff {I : X3CInstance} (hI : I.Standing) (q : ℕ)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (hσ : σ ∈ omegaLE I) (L : GadgetRank I q) :
    respectsProjection I q σ L ↔
      ∀ e f : posetP I q, layout I q σ e ≤ layout I q σ f → L e ≤ L f := by
  constructor
  · intro h e f hef
    have hmono : Monotone (fun p => L (Sum.inl (σ p))) := (show StrictMono _ from h.2).monotone
    rcases e with e | e
    · rcases f with f | f
      · have hle : (σ.symm e).val + 1 ≤ (σ.symm f).val + 1 := hef
        have hp : σ.symm e ≤ σ.symm f := Nat.le_of_succ_le_succ hle
        simpa only [Equiv.apply_symm_apply] using hmono hp
      · obtain ⟨p, hp, hstep⟩ := copy_attachment_witness hI q σ f
        have hle : (σ.symm e).val + 1 ≤ attachment σ (copyLayout f).1 := hef
        rw [← hp] at hle
        have hp' : σ.symm e ≤ p := Nat.le_of_succ_le_succ hle
        have he : L (Sum.inl e) ≤ L (Sum.inl (σ p)) := by
          simpa only [Equiv.apply_symm_apply] using hmono hp'
        exact he.trans (h.1 _ _ (Relation.ReflTransGen.single hstep))
    · have heq : layout I q σ (Sum.inr e) = layout I q σ f := hef
      have heq' := (layout I q σ).injective heq
      rw [heq']
  · intro hmono
    constructor
    · intro e f hef
      change Relation.ReflTransGen (dagA I q).Follows e f at hef
      induction hef with
      | refl => exact le_rfl
      | tail _ hstep ih => exact ih.trans (hmono _ _ (follows_le_layout hσ _ _ hstep))
    · intro a b hab
      have hle : layout I q σ (Sum.inl (σ a)) ≤ layout I q σ (Sum.inl (σ b)) := by
        change (σ.symm (σ a)).val + 1 ≤ (σ.symm (σ b)).val + 1
        simp only [Equiv.symm_apply_apply]
        exact Nat.succ_le_succ hab.le
      apply lt_of_le_of_ne (hmono _ _ hle)
      intro heq
      exact hab.ne (σ.injective (Sum.inl.inj (L.injective heq)))

private theorem count_eq_spine {I : X3CInstance} (hI : I.Standing) (q : ℕ)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (hσ : σ ∈ omegaLE I) :
    linExtCountGiven I q σ = numLinExt (Spine (4 * I.n) q (attachment σ)) := by
  let T := Spine (4 * I.n) q (attachment σ)
  let e := layout I q σ
  let hcard : Fintype.card (posetP I q) = Fintype.card T := Fintype.card_congr e
  let ranks : GadgetRank I q ≃ (T ≃ Fin (Fintype.card T)) := Equiv.equivCongr e (finCongr hcard)
  have hpoint (L : GadgetRank I q) (a b : posetP I q) :
      ranks L (e a) ≤ ranks L (e b) ↔ L a ≤ L b := by
    simp [ranks, finCongr]
  have hpred (L : GadgetRank I q) :
      respectsProjection I q σ L ↔ ranks L ∈ FCP.Order.LinearExtensions T := by
    rw [respectsProjection_iff hI q σ hσ L]
    constructor
    · intro h a b hab
      obtain ⟨a', rfl⟩ := e.surjective a
      obtain ⟨b', rfl⟩ := e.surjective b
      exact (hpoint L a' b').mpr (h _ _ hab)
    · intro h a b hab
      exact (hpoint L a b).mp (h (e a) (e b) hab)
  change {L | respectsProjection I q σ L}.ncard = (FCP.Order.LinearExtensions T).ncard
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (ranks.subtypeEquiv hpred)

private theorem count_attachments {I : X3CInstance} (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) :
    (Finset.univ.filter (fun j : AttachmentIndex I => 4 * I.n + 1 - i ≤ attachment σ j)).card =
      Ccount σ i := by
  classical
  let cut := 4 * I.n + 1 - i
  let elems := (Finset.univ : Finset (Fin (3 * I.h))).filter (fun j => cut ≤ rho σ j)
  let sets := (Finset.univ : Finset (Fin I.n)).filter (fun l => ∃ p : Fin (4 * I.n),
    cut ≤ p.val + 1 ∧ (σ p).1 = .rootSet l)
  have hfilter : (Finset.univ.filter (fun j : AttachmentIndex I => cut ≤ attachment σ j)) =
      elems.disjSum sets := by
    ext j
    cases j with
    | inl j =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.inl_mem_disjSum, elems]
      rfl
    | inr l =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.inr_mem_disjSum,
        sets]
      change cut ≤ (σ.symm (rootSetEdge l)).val + 1 ↔ _
      constructor
      · intro h
        refine ⟨σ.symm (rootSetEdge l), h, ?_⟩
        rw [σ.apply_symm_apply]
        rfl
      · rintro ⟨p, hp, he⟩
        have heq : σ p = rootSetEdge l := Subtype.ext he
        have hp' : σ.symm (rootSetEdge l) = p := (congrArg σ.symm heq).symm.trans (σ.symm_apply_apply p)
        rw [hp']
        exact hp
  change (Finset.univ.filter (fun j : AttachmentIndex I => cut ≤ attachment σ j)).card = _
  rw [hfilter, Finset.card_disjSum]
  rfl

private theorem spine_size (I : X3CInstance) (q : ℕ) (σ : Fin (4 * I.n) ≃ OrigEdge I) :
    Fintype.card (Spine (4 * I.n) q (attachment σ)) = 4 * I.n + 3 * I.h * q + I.n * q := by
  change Fintype.card (Fin (4 * I.n) ⊕ (AttachmentIndex I × Fin q)) = _
  simp [Fintype.card_sum, Fintype.card_prod, Nat.add_mul, Nat.add_assoc]

private theorem spine_hooks {I : X3CInstance} (q : ℕ) (σ : Fin (4 * I.n) ≃ OrigEdge I) :
    (∏ x : Spine (4 * I.n) q (attachment σ), (upSetCard x : ℝ)) =
      ∏ i ∈ Finset.Icc 1 (4 * I.n), ((i : ℝ) + (q : ℝ) * (Ccount σ i : ℝ)) := by
  classical
  let hook : Fin (4 * I.n) ⊕ (AttachmentIndex I × Fin q) → ℝ :=
    fun x => (upSetCard (show Spine (4 * I.n) q (attachment σ) from x) : ℝ)
  change (∏ x, hook x) = _
  rw [Fintype.prod_sum_type]
  have hleaf : (∏ z : AttachmentIndex I × Fin q, hook (Sum.inr z)) = 1 := by
    apply Finset.prod_eq_one
    intro z _
    change (upSetCard (leaf (m := 4 * I.n) (attachment σ) z) : ℝ) = 1
    rw [spine_leaf_hook, Nat.cast_one]
  rw [hleaf, mul_one]
  refine Finset.prod_bij (fun p _ => 4 * I.n - p.val) ?_ ?_ ?_ ?_
  · intro p _
    have hp := p.isLt
    exact Finset.mem_Icc.mpr ⟨by omega, Nat.sub_le _ _⟩
  · intro p _ r _ h
    have hp := p.isLt
    have hr := r.isLt
    exact Fin.ext (by omega)
  · intro i hi
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
    let p : Fin (4 * I.n) := ⟨4 * I.n - i, by omega⟩
    exact ⟨p, Finset.mem_univ _, by change 4 * I.n - (4 * I.n - i) = i; omega⟩
  · intro p _
    change (upSetCard (node (q := q) (attachment σ) p) : ℝ) = _
    rw [spine_chain_hook]
    have hcut : 4 * I.n + 1 - (4 * I.n - p.val) = p.val + 1 := by have := p.isLt; omega
    rw [← hcut, count_attachments, Nat.cast_add, Nat.cast_mul]

end CountOrderings.NFree

open CountOrderings.NFree in
theorem solution (I : X3CInstance) (hI : I.Standing) (q : ℕ) (_hq : 1 ≤ q)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (hσ : σ ∈ omegaLE I) :
    (linExtCountGiven I q σ : ℝ) =
      ((4 * I.n + 3 * I.h * q + I.n * q).factorial : ℝ) *
        ∏ i ∈ Finset.Icc 1 (4 * I.n), 1 / ((i : ℝ) + (q : ℝ) * (Ccount σ i : ℝ)) := by
  let T := Spine (4 * I.n) q (attachment σ)
  have hn : 0 < 4 * I.n := by have := hI.2; omega
  have htree : IsRootedTreePoset T := spine_rooted _ hn (attachment_bounds hI σ)
  have hHook := lemma_2_2 T htree
  have hReal := congrArg (fun x : ℚ => (x : ℝ)) hHook
  simp only [Rat.cast_natCast, Rat.cast_div, Rat.cast_prod] at hReal
  dsimp only [T] at hReal
  rw [spine_size, spine_hooks] at hReal
  rw [count_eq_spine hI q σ hσ]
  rw [Finset.prod_div_distrib, Finset.prod_const_one, ← div_eq_mul_one_div]
  exact hReal
