-- Prove2me | solution 1 for BKAbsorption.cyclic_simple_core
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T20:45:11.694828+00:00
-- url     : https://prove2.me/submissions/98450f80-95aa-4f5a-93e3-876f86b11e52

import Mathlib
import Definitions.Def_BKAbsorption_defs
import Theorems.Thm_BKAbsorption_cyclic_iff_subpower
import Theorems.Thm_BKAbsorption_loop_lemma

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open scoped Fin.NatCast

universe u v w w'


namespace BKAux
open BKAbsorption

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]

theorem realize_mem {S : Set M} (hS : IsSubuniverse L S) {α : Type*} (t : L.Term α) (a : α → M)
    (ha : ∀ i, a i ∈ S) : t.realize a ∈ S := by
  induction t with
  | var i => exact ha i
  | func f ts ih => exact hS _ f _ ih

def compTerm {m n : ℕ} (s : L.Term (Fin m)) (t : L.Term (Fin n)) : L.Term (Fin m × Fin n) :=
  s.subst (fun i => t.relabel (fun j => (i, j)))

theorem compTerm_realize {m n : ℕ} (s : L.Term (Fin m)) (t : L.Term (Fin n)) (a : Fin m × Fin n → M) :
    (compTerm s t).realize a = s.realize (fun i => t.realize (fun j => a (i, j))) := by
  unfold compTerm
  rw [Term.realize_subst]
  congr 1; ext i
  rw [Term.realize_relabel]; rfl

end BKAux

open BKAbsorption BKAux in
theorem absorbing_trans {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M] (B C : Set M)
    (hB : IsAbsorbing L B) (hC : IsSubuniverse L C) (hCB : C ⊆ B)
    (hs : ∃ (m : ℕ) (s : L.Term (Fin m)), 0 < m ∧
      ∀ (k : Fin m) (a : Fin m → M), (∀ i, a i ∈ B) → (∀ i, i ≠ k → a i ∈ C) → s.realize a ∈ C) :
    IsAbsorbing L C := by
  obtain ⟨-, n, t, hn, ht⟩ := hB
  obtain ⟨m, s, hm, hs⟩ := hs
  refine ⟨hC, m * n, (compTerm s t).relabel finProdFinEquiv, Nat.mul_pos hm hn, fun k a hk => ?_⟩
  rw [Term.realize_relabel, compTerm_realize]
  set a' : Fin m × Fin n → M := a ∘ finProdFinEquiv with ha'
  set k' : Fin m × Fin n := finProdFinEquiv.symm k with hk'
  have hk'' : ∀ p : Fin m × Fin n, p ≠ k' → a' p ∈ C := by
    intro p hp
    refine hk _ ?_
    intro h
    apply hp
    rw [hk']; rw [← h]; simp
  -- rows: all entries of rows other than k'.1 are in C ⊆ B
  have hrow : ∀ i : Fin m, (fun j => a' (i, j)) = fun j => a' (i, j) := fun _ => rfl
  refine hs k'.1 _ (fun i => ?_) (fun i hi => ?_)
  · -- t(row i) ∈ B : at most one coordinate (k') outside C, hence absorbed
    by_cases hik : i = k'.1
    · refine ht k'.2 _ (fun j hj => hCB (hk'' (i, j) ?_))
      intro h
      apply hj
      have := congrArg Prod.snd h
      simpa using this
    · exact hCB (realize_mem hC t _ (fun j => hk'' (i, j) (fun h => hik (by rw [← h]))))
  · exact realize_mem hC t _ (fun j => hk'' (i, j) (fun h => hi (by rw [← h])))

open BKAbsorption BKAux in
theorem absorbing_inter {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M] (B C : Set M)
    (hB : IsAbsorbing L B) (hC : IsAbsorbing L C) : IsAbsorbing L (B ∩ C) := by
  have hBC : IsSubuniverse L (B ∩ C) := fun n f x hx =>
    ⟨hB.1 n f x (fun i => (hx i).1), hC.1 n f x (fun i => (hx i).2)⟩
  obtain ⟨-, n, t, hn, ht⟩ := hB
  refine absorbing_trans C (B ∩ C) hC hBC Set.inter_subset_right ⟨n, t, hn, fun k a haC hak => ?_⟩
  exact ⟨ht k a (fun i hi => (hak i hi).1), realize_mem hC.1 t a haC⟩

open BKAbsorption BKAux in
theorem realize_prod {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]
    {α : Type*} (t : L.Term α) (a : α → A) (b : α → B) :
    t.realize (fun i => (a i, b i)) = (t.realize a, t.realize b) := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    simp only [Term.realize]
    show (funMap f (fun i => ((ts i).realize (fun j => (a j, b j))).1),
      funMap f (fun i => ((ts i).realize (fun j => (a j, b j))).2)) = _
    simp only [ih]

open BKAbsorption BKAux in
theorem nbhd_subuniverse {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'}
    [L.Structure A] [L.Structure B] (R : Set (A × B)) (hR : IsSubuniverse L R)
    (X : Set A) (hX : IsSubuniverse L X) :
    IsSubuniverse L {b : B | ∃ a ∈ X, (a, b) ∈ R} := by
  intro n f y hy
  choose a haX haR using hy
  refine ⟨funMap f a, hX n f a haX, ?_⟩
  have := hR n f (fun i => (a i, y i)) haR
  exact this

open BKAbsorption BKAux in
theorem nbhd_absorbing {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'}
    [L.Structure A] [L.Structure B] (R : Set (A × B)) (hR : IsSubuniverse L R) (hsub : Subdirect R)
    (X : Set A) (hX : IsAbsorbing L X) :
    IsAbsorbing L {b : B | ∃ a ∈ X, (a, b) ∈ R} := by
  refine ⟨nbhd_subuniverse R hR X hX.1, ?_⟩
  obtain ⟨-, n, t, hn, ht⟩ := hX
  refine ⟨n, t, hn, fun k b hb => ?_⟩
  have hex : ∀ i, ∃ a : A, (i ≠ k → a ∈ X) ∧ (a, b i) ∈ R := by
    intro i
    by_cases hik : i = k
    · have : b i ∈ Prod.snd '' R := by rw [hsub.2]; trivial
      obtain ⟨⟨a, b'⟩, hab, rfl⟩ := this
      exact ⟨a, fun h => absurd hik h, hab⟩
    · obtain ⟨a, haX, haR⟩ := hb i hik
      exact ⟨a, fun _ => haX, haR⟩
  choose a haX haR using hex
  refine ⟨t.realize a, ht k a haX, ?_⟩
  have := realize_mem hR t (fun i => (a i, b i)) haR
  rwa [realize_prod] at this

namespace BKAux
open BKAbsorption

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]

def IsIdem (L : FirstOrder.Language.{u, v}) (M : Type w) [L.Structure M] : Prop :=
  ∀ (n : ℕ) (f : L.Functions n) (a : M), funMap f (fun _ => a) = a

theorem term_idem (h : IsIdem L M) {α : Type*} (t : L.Term α) (a : M) :
    t.realize (fun _ => a) = a := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    simp only [Term.realize]
    simp only [ih]
    exact h _ f a

def compTerm' {m n : ℕ} (s : L.Term (Fin m)) (t : L.Term (Fin n)) : L.Term (Fin (m * n)) :=
  (compTerm s t).relabel finProdFinEquiv

theorem compTerm'_realize {m n : ℕ} (s : L.Term (Fin m)) (t : L.Term (Fin n)) (a : Fin (m * n) → M) :
    (compTerm' s t).realize a = s.realize (fun i => t.realize (fun j => a (finProdFinEquiv (i, j)))) := by
  unfold compTerm'
  rw [Term.realize_relabel, compTerm_realize]; rfl

end BKAux

open BKAbsorption BKAux in
theorem exists_universal_term {L : FirstOrder.Language.{u, v}} {A : Type w} [L.Structure A] [Finite A]
    (hid : IsIdem L A) :
    ∃ (n : ℕ) (s : L.Term (Fin n)), 0 < n ∧ ∀ (B : Set A) (b : A), B.Nonempty →
      (∃ (m : ℕ) (u : L.Term (Fin m)) (c : Fin m → A), (∀ j, c j ∈ B) ∧ u.realize c = b) →
        ∃ a : Fin n → A, (∀ i, a i ∈ B) ∧ s.realize a = b := by
  classical
  haveI := Fintype.ofFinite A
  let P : (Set A × A) → Prop := fun p => p.1.Nonempty ∧ ∃ (m : ℕ) (u : L.Term (Fin m)) (c : Fin m → A),
    (∀ j, c j ∈ p.1) ∧ u.realize c = p.2
  have key : ∀ F : Finset (Set A × A), ∃ (n : ℕ) (s : L.Term (Fin n)), 0 < n ∧
      ∀ p ∈ F, P p → ∃ a : Fin n → A, (∀ i, a i ∈ p.1) ∧ s.realize a = p.2 := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨1, Term.var 0, one_pos, by simp⟩
    | insert p0 F hp0 ih =>
      obtain ⟨n, s, hn, hs⟩ := ih
      by_cases hP : P p0
      · obtain ⟨⟨e, he⟩, m, u, c, hc, hu⟩ := hP
        -- extend c by a dummy value e to get positive arity
        let c' : Fin (m + 1) → A := fun j => if h : (j : ℕ) < m then c ⟨j, h⟩ else e
        let u' : L.Term (Fin (m + 1)) := u.relabel Fin.castSucc
        have hc'cs : c' ∘ Fin.castSucc = c := by
          ext j; simp [c', j.2]
        have hu' : u'.realize c' = p0.2 := by
          simp only [u', Term.realize_relabel, hc'cs, hu]
        have hc'mem : ∀ j, c' j ∈ p0.1 := by
          intro j
          by_cases h : (j : ℕ) < m
          · simp only [c', h, dif_pos]; exact hc _
          · simp only [c', h, dif_neg, not_false_eq_true]; exact he
        refine ⟨n * (m + 1), compTerm' s u', Nat.mul_pos hn (Nat.succ_pos m), fun p hp hPp => ?_⟩
        rcases Finset.mem_insert.1 hp with rfl | hp'
        · refine ⟨fun k => c' (finProdFinEquiv.symm k).2, fun k => hc'mem _, ?_⟩
          rw [compTerm'_realize]
          simp only [Equiv.symm_apply_apply]
          rw [hu']
          exact term_idem hid s _
        · obtain ⟨a, ha, hsa⟩ := hs p hp' hPp
          refine ⟨fun k => a (finProdFinEquiv.symm k).1, fun k => ha _, ?_⟩
          rw [compTerm'_realize]
          simp only [Equiv.symm_apply_apply]
          have : (fun i => u'.realize (fun _ => a i)) = a := by
            ext i; exact term_idem hid u' (a i)
          rw [this, hsa]
      · exact ⟨n, s, hn, fun p hp hPp => by
          rcases Finset.mem_insert.1 hp with rfl | hp'
          · exact absurd hPp hP
          · exact hs p hp' hPp⟩
  obtain ⟨n, s, hn, hs⟩ := key Finset.univ
  exact ⟨n, s, hn, fun B b hB hb => hs (B, b) (Finset.mem_univ _) ⟨hB, hb⟩⟩


namespace BKAux
open BKAbsorption

variable {L : FirstOrder.Language.{u, v}} {A : Type w} [L.Structure A]

def Wset {n : ℕ} (t : L.Term (Fin n)) (b : A) (i : Fin n) : Set A :=
  {c | ∃ a : Fin n → A, a i = b ∧ t.realize a = c}

theorem comp_mem (hid : IsIdem L A) {n N : ℕ} (s : L.Term (Fin n)) (v : L.Term (Fin N))
    (f : Fin n → A) (j : Fin n) (l : Fin N) (b : A) (hfj : f j ∈ Wset v b l) :
    s.realize f ∈ Wset (compTerm' s v) b (finProdFinEquiv (j, l)) := by
  obtain ⟨ac, hacl, hac⟩ := hfj
  refine ⟨fun k => if (finProdFinEquiv.symm k).1 = j then ac (finProdFinEquiv.symm k).2
    else f (finProdFinEquiv.symm k).1, ?_, ?_⟩
  · simp [hacl]
  · rw [compTerm'_realize]
    congr 1
    ext i
    simp only [Equiv.symm_apply_apply]
    by_cases hij : i = j
    · subst hij; simp [hac]
    · simp only [hij, if_false]
      exact term_idem hid v (f i)

end BKAux

open BKAbsorption BKAux in
theorem claim28 {L : FirstOrder.Language.{u, v}} {A : Type w} [L.Structure A] [Finite A]
    (T : TaylorDatum L) (hA : IsTaylorAlg T A)
    (hno : ∀ B : Set A, IsAbsorbing L B → B.Nonempty → B = Set.univ)
    {N : ℕ} (v : L.Term (Fin N)) (r : ℕ) (hr1 : 1 ≤ r) (hr : r < Nat.card A)
    (hv : ∀ (b : A) (l : Fin N), ∃ B : Set A, IsSubuniverse L B ∧ r ≤ B.ncard ∧ B ⊆ Wset v b l) :
    ∀ (b : A) (i : Fin (T.k * N)), r + 1 ≤ (Wset (compTerm' T.t v) b i).ncard := by
  intro b i
  obtain ⟨⟨j, l⟩, rfl⟩ : ∃ p : Fin T.k × Fin N, finProdFinEquiv p = i := ⟨finProdFinEquiv.symm i, finProdFinEquiv.apply_symm_apply i⟩
  obtain ⟨B, hBsub, hBr, hBW⟩ := hv b l
  have hfinW : (Wset (compTerm' T.t v) b (finProdFinEquiv (j, l))).Finite := Set.toFinite _
  have hBne : B.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have hBW' : B ⊆ Wset (compTerm' T.t v) b (finProdFinEquiv (j, l)) := by
    intro c hc
    have := comp_mem hA.1 T.t v (fun _ => c) j l b (hBW hc)
    rwa [term_idem hA.1] at this
  by_cases hBu : B = Set.univ
  · subst hBu
    have h1 : (Set.univ : Set A).ncard ≤ (Wset (compTerm' T.t v) b (finProdFinEquiv (j, l))).ncard :=
      Set.ncard_le_ncard hBW' hfinW
    rw [Set.ncard_univ] at h1
    omega
  · -- B is not absorbing for the Taylor binary term
    set r2 : L.Term (Fin 2) := T.t.relabel (fun l' => cond (T.σ j l') (1 : Fin 2) 0) with hr2
    have hnabs : ¬ (∀ (k : Fin 2) (a : Fin 2 → A), (∀ i, i ≠ k → a i ∈ B) → r2.realize a ∈ B) := by
      intro h
      exact hBu (hno B ⟨hBsub, 2, r2, two_pos, h⟩ hBne)
    push_neg at hnabs
    obtain ⟨k, a, hak, hr2a⟩ := hnabs
    have hrel : r2.realize a = T.t.realize (fun l' => cond (T.σ j l') (a 1) (a 0)) := by
      rw [hr2, Term.realize_relabel]
      congr 1; ext l'
      cases h : T.σ j l' <;> simp [h]
    rw [hrel] at hr2a
    have he1 : T.t.realize (fun l' => cond (T.σ j l') (a 1) (a 0)) ∈
        Wset (compTerm' T.t v) b (finProdFinEquiv (j, l)) := by
      fin_cases k
      · -- k = 0 : a 1 ∈ B, use the Taylor identity
        have h1 : a 1 ∈ B := hak 1 (by simp)
        rw [hA.2 j (a 0) (a 1)]
        refine comp_mem hA.1 T.t v (fun l' => cond (T.τ j l') (a 1) (a 0)) j l b ?_
        simp only [T.τ_self, cond_true]
        exact hBW h1
      · have h1 : a 0 ∈ B := hak 0 (by simp)
        refine comp_mem hA.1 T.t v (fun l' => cond (T.σ j l') (a 1) (a 0)) j l b ?_
        simp only [T.σ_self, cond_false]
        exact hBW h1
    have hins : insert (T.t.realize (fun l' => cond (T.σ j l') (a 1) (a 0))) B ⊆
        Wset (compTerm' T.t v) b (finProdFinEquiv (j, l)) := Set.insert_subset he1 hBW'
    have h2 := Set.ncard_le_ncard hins hfinW
    rw [Set.ncard_insert_of_notMem hr2a (Set.toFinite B)] at h2
    omega

open BKAbsorption BKAux in
theorem claim29 {L : FirstOrder.Language.{u, v}} {A : Type w} [L.Structure A] [Finite A]
    (hid : IsIdem L A) {n : ℕ} (s : L.Term (Fin n))
    (hs : ∀ (B : Set A) (b : A), B.Nonempty →
      (∃ (m : ℕ) (u : L.Term (Fin m)) (c : Fin m → A), (∀ j, c j ∈ B) ∧ u.realize c = b) →
        ∃ a : Fin n → A, (∀ i, a i ∈ B) ∧ s.realize a = b)
    {N : ℕ} (w : L.Term (Fin N)) (r : ℕ) (hr : 1 ≤ r)
    (hw : ∀ (b : A) (l : Fin N), r ≤ (Wset w b l).ncard) :
    ∀ (b : A) (i : Fin (n * N)), ∃ B : Set A, IsSubuniverse L B ∧ r ≤ B.ncard ∧
      B ⊆ Wset (compTerm' s w) b i := by
  intro b i
  obtain ⟨⟨j, l⟩, rfl⟩ : ∃ p : Fin n × Fin N, finProdFinEquiv p = i :=
    ⟨finProdFinEquiv.symm i, finProdFinEquiv.apply_symm_apply i⟩
  set B0 := Wset w b l with hB0
  have hB0ne : B0.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hB0]; have := hw b l; omega)
  refine ⟨(Substructure.closure L B0 : Set A), fun m f x hx => Substructure.fun_mem _ f x hx,
    ?_, ?_⟩
  · exact (hw b l).trans (Set.ncard_le_ncard (Substructure.subset_closure (L := L)) (Set.toFinite _))
  · intro c hc
    obtain ⟨t, rfl⟩ := (Substructure.mem_closure_iff_exists_term).1 hc
    haveI : Finite B0 := (Set.toFinite B0).to_subtype
    obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin B0
    obtain ⟨f, hfB, hf⟩ := hs B0 (t.realize (fun x : B0 => (x : A))) hB0ne
      ⟨m, t.relabel e, fun q => (e.symm q : A), fun q => (e.symm q).2, by
        rw [Term.realize_relabel]; congr 1; ext x; simp⟩
    rw [← hf]
    exact comp_mem hid s w f j l b (hfB j)

open BKAbsorption BKAux in
theorem taylor_k_pos {L : FirstOrder.Language.{u, v}} {A : Type w} [L.Structure A] [Finite A]
    (T : TaylorDatum L) (hA : IsTaylorAlg T A) (h2 : 1 < Nat.card A) : 0 < T.k := by
  by_contra h
  have hk : T.k = 0 := by omega
  obtain ⟨a, b, hab⟩ := (Finite.one_lt_card_iff_nontrivial (α := A)).1 h2 |>.exists_pair_ne
  apply hab
  have h1 := term_idem (show IsIdem L A from hA.1) T.t a
  have h3 := term_idem (show IsIdem L A from hA.1) T.t b
  have hfun : (fun _ : Fin T.k => a) = (fun _ : Fin T.k => b) := by
    ext i; exact absurd i.2 (by omega)
  rw [← h1, ← h3, hfun]

open BKAbsorption BKAux in
theorem prop27 {L : FirstOrder.Language.{u, v}} {A : Type w} [L.Structure A] [Finite A]
    (T : TaylorDatum L) (hA : IsTaylorAlg T A)
    (hno : ∀ B : Set A, IsAbsorbing L B → B.Nonempty → B = Set.univ) :
    ∃ (N : ℕ) (v : L.Term (Fin N)), 0 < N ∧ ∀ (b c : A) (i : Fin N),
      ∃ a : Fin N → A, a i = b ∧ v.realize a = c := by
  classical
  by_cases hne : Nonempty A
  · have hid : IsIdem L A := hA.1
    obtain ⟨ns, s, hns, hs⟩ := exists_universal_term hid
    have hcard : 1 ≤ Nat.card A := Nat.card_pos_iff.2 ⟨hne, inferInstance⟩
    have key : ∀ r : ℕ, 1 ≤ r → r ≤ Nat.card A → ∃ (N : ℕ) (v : L.Term (Fin N)), 0 < N ∧
        ∀ (b : A) (l : Fin N), ∃ B : Set A, IsSubuniverse L B ∧ r ≤ B.ncard ∧ B ⊆ Wset v b l := by
      intro r hr1 hrc
      induction r, hr1 using Nat.le_induction with
      | base =>
        refine ⟨1, Term.var 0, one_pos, fun b l => ⟨{b}, ?_, by simp, ?_⟩⟩
        · intro n f x hx
          have : x = fun _ => b := by ext i; exact hx i
          rw [this]; simp only [Set.mem_singleton_iff]; exact hid n f b
        · intro c hc
          rw [Set.mem_singleton_iff] at hc
          subst hc
          exact ⟨fun _ => c, by simp [Subsingleton.elim l 0], rfl⟩
      | succ r hr1 ih =>
        obtain ⟨N, v, hN, hv⟩ := ih (by omega)
        have hkpos := taylor_k_pos T hA (by omega)
        have h28 := claim28 T hA hno v r hr1 (by omega) hv
        have h29 := claim29 hid s hs (compTerm' T.t v) (r + 1) (by omega) h28
        exact ⟨ns * (T.k * N), compTerm' s (compTerm' T.t v),
          Nat.mul_pos hns (Nat.mul_pos hkpos hN), h29⟩
    obtain ⟨N, v, hN, hv⟩ := key (Nat.card A) hcard le_rfl
    refine ⟨N, v, hN, fun b c i => ?_⟩
    obtain ⟨B, -, hBc, hBW⟩ := hv b i
    have hBu : B = Set.univ :=
      Set.eq_of_subset_of_ncard_le (Set.subset_univ B) (by rw [Set.ncard_univ]; exact hBc) (Set.toFinite _)
    have : c ∈ Wset v b i := hBW (hBu ▸ Set.mem_univ c)
    exact this
  · exact ⟨1, Term.var 0, one_pos, fun b => (hne ⟨b⟩).elim⟩

open BKAbsorption BKAux in
theorem cor210 {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]
    [Finite A] [Finite B] (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    (hnoA : ∀ X : Set A, IsAbsorbing L X → X.Nonempty → X = Set.univ)
    (hnoB : ∀ X : Set B, IsAbsorbing L X → X.Nonempty → X = Set.univ) :
    ∃ (N : ℕ) (v : L.Term (Fin N)), 0 < N ∧
      (∀ (b c : A) (i : Fin N), ∃ a : Fin N → A, a i = b ∧ v.realize a = c) ∧
      (∀ (b c : B) (i : Fin N), ∃ a : Fin N → B, a i = b ∧ v.realize a = c) := by
  obtain ⟨N1, v1, h1, hv1⟩ := prop27 T hA hnoA
  obtain ⟨N2, v2, h2, hv2⟩ := prop27 T hB hnoB
  refine ⟨N1 * N2, compTerm' v1 v2, Nat.mul_pos h1 h2, ?_, ?_⟩
  · intro b c i
    obtain ⟨⟨j, l⟩, rfl⟩ : ∃ p : Fin N1 × Fin N2, finProdFinEquiv p = i :=
      ⟨finProdFinEquiv.symm i, finProdFinEquiv.apply_symm_apply i⟩
    obtain ⟨f, hfj, hf⟩ := hv1 b c j
    have hmem : f j ∈ Wset v2 b l :=
      ⟨fun _ => b, rfl, by rw [term_idem (show IsIdem L A from hA.1) v2 b, hfj]⟩
    have := comp_mem (show IsIdem L A from hA.1) v1 v2 f j l b hmem
    rw [hf] at this
    exact this
  · intro b c i
    obtain ⟨⟨j, l⟩, rfl⟩ : ∃ p : Fin N1 × Fin N2, finProdFinEquiv p = i :=
      ⟨finProdFinEquiv.symm i, finProdFinEquiv.apply_symm_apply i⟩
    have hmem : (fun _ : Fin N1 => c) j ∈ Wset v2 b l := hv2 b c l
    have := comp_mem (show IsIdem L B from hB.1) v1 v2 (fun _ => c) j l b hmem
    rw [term_idem (show IsIdem L B from hB.1) v1 c] at this
    exact this

open BKAbsorption BKAux in
theorem thm211_core {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]
    [Finite A] [Finite B] (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    (hnoA : ∀ X : Set A, IsAbsorbing L X → X.Nonempty → X = Set.univ)
    (hnoB : ∀ X : Set B, IsAbsorbing L X → X.Nonempty → X = Set.univ)
    (R : Set (A × B)) (hR : IsSubuniverse L R) (hsub : Subdirect R)
    (hRR : ∀ a c : A, ∃ b : B, (a, b) ∈ R ∧ (c, b) ∈ R) (hne : R ≠ Set.univ) : False := by
  classical
  have hidA : IsIdem L A := hA.1
  have hidB : IsIdem L B := hB.1
  obtain ⟨N0, v, hN0, hvA, hvB⟩ := cor210 T hA hB hnoA hnoB
  let NN : Set A → Set B := fun X => {b | ∀ a ∈ X, (a, b) ∈ R}
  have NN_sub : ∀ X : Set A, IsSubuniverse L (NN X) := by
    intro X n f y hy a ha
    have := hR n f (fun i => (a, y i)) (fun i => hy i a ha)
    have e : funMap f (fun i => (a, y i)) = (a, funMap f y) := by
      show (funMap f (fun _ => a), funMap f y) = _
      rw [hidA n f a]
    rwa [e] at this
  have NN_anti : ∀ X Y : Set A, X ⊆ Y → NN Y ⊆ NN X := fun X Y h b hb a ha => hb a (h ha)
  have NN_closure : ∀ X : Set A, NN X ⊆ NN (Substructure.closure L X : Set A) := by
    intro X b hb c hc
    obtain ⟨t, rfl⟩ := (Substructure.mem_closure_iff_exists_term).1 hc
    have := realize_mem hR t (fun x : X => ((x : A), b)) (fun x => hb x x.2)
    rw [realize_prod, term_idem hidB t b] at this
    exact this
  let good : Set A → Prop := fun X => ∀ c : A, ∃ b ∈ NN X, (c, b) ∈ R
  have hsingle : ∀ a : A, good {a} := by
    intro a c
    obtain ⟨b, h1, h2⟩ := hRR a c
    exact ⟨b, fun x hx => by rw [Set.mem_singleton_iff] at hx; subst hx; exact h1, h2⟩
  -- A is nonempty
  have hAne : Nonempty A := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hne (Set.eq_univ_of_forall fun p => isEmptyElim p.1)
  obtain ⟨a0⟩ := hAne
  obtain ⟨X, hle, hXmax⟩ := (Set.toFinite {X : Set A | good X}).exists_le_maximal (a := ({a0} : Set A))
    (show ({a0} : Set A) ∈ {X : Set A | good X} from hsingle a0)
  have hXgood : good X := hXmax.prop
  have hcl_good : good (Substructure.closure L X : Set A) := fun c => by
    obtain ⟨b, hb, hcb⟩ := hXgood c
    exact ⟨b, NN_closure X hb, hcb⟩
  have hXsub : IsSubuniverse L X := by
    intro n f x hx
    have hmem : funMap f x ∈ (Substructure.closure L X : Set A) :=
      Substructure.fun_mem _ f x (fun i => Substructure.subset_closure (hx i))
    have : (Substructure.closure L X : Set A) ≤ X := hXmax.2 hcl_good Substructure.subset_closure
    exact this hmem
  have hXne : X.Nonempty := ⟨a0, hle rfl⟩
  have hXuniv : X = Set.univ := by
    by_contra hXu
    have hnabs : ¬ IsAbsorbing L X := fun h => hXu (hnoA X h hXne)
    have h1 : ¬ (∀ (k : Fin N0) (a : Fin N0 → A), (∀ i, i ≠ k → a i ∈ X) → v.realize a ∈ X) :=
      fun h => hnabs ⟨hXsub, N0, v, hN0, h⟩
    push_neg at h1
    obtain ⟨j, a, haX, hvX⟩ := h1
    have hgood2 : good (insert (v.realize a) X) := by
      intro c
      obtain ⟨d, hdj, hvd⟩ := hvA (a j) c j
      choose e heN heR using fun i => hXgood (d i)
      refine ⟨v.realize e, ?_, ?_⟩
      · intro x hx
        rcases hx with rfl | hx
        · have := realize_mem hR v (fun i => (a i, e i)) (fun i => by
            by_cases hij : i = j
            · subst hij; rw [← hdj]; exact heR i
            · exact heN i (a i) (haX i hij))
          rwa [realize_prod] at this
        · exact (realize_mem (NN_sub X) v e heN) x hx
      · have := realize_mem hR v (fun i => (d i, e i)) heR
        rwa [realize_prod, hvd] at this
    have hle2 : X ≤ insert (v.realize a) X := Set.subset_insert _ _
    have := hXmax.2 hgood2 hle2
    exact hvX (this (Set.mem_insert _ _))
  have hNne : (NN Set.univ).Nonempty := by
    obtain ⟨b, hb, -⟩ := hXgood a0
    exact ⟨b, by rwa [hXuniv] at hb⟩
  have hNnu : NN Set.univ ≠ Set.univ := by
    intro h
    apply hne
    ext ⟨a, b⟩
    simp only [Set.mem_univ, iff_true]
    have : b ∈ NN Set.univ := by rw [h]; trivial
    exact this a trivial
  have hnabsN : ¬ IsAbsorbing L (NN Set.univ) := fun h => hNnu (hnoB _ h hNne)
  have h2 : ¬ (∀ (k : Fin N0) (b : Fin N0 → B), (∀ i, i ≠ k → b i ∈ NN Set.univ) → v.realize b ∈ NN Set.univ) :=
    fun h => hnabsN ⟨NN_sub _, N0, v, hN0, h⟩
  push_neg at h2
  obtain ⟨j, bt, hbt, hvb⟩ := h2
  apply hvb
  intro d _
  have hj : bt j ∈ Prod.snd '' R := by rw [hsub.2]; trivial
  obtain ⟨⟨a, b'⟩, hab, hb'⟩ := hj
  obtain ⟨a', hja, hva⟩ := hvA a d j
  have := realize_mem hR v (fun i => (a' i, bt i)) (fun i => by
    by_cases hij : i = j
    · subst hij; rw [hja]; simp only at hb'; rw [← hb']; exact hab
    · exact hbt i hij (a' i) trivial)
  rwa [realize_prod, hva] at this

namespace BKAux
open BKAbsorption

variable {L : FirstOrder.Language.{u, v}} {A : Type w} [L.Structure A]

def relComp (P Q : Set (A × A)) : Set (A × A) := {p | ∃ c, (p.1, c) ∈ P ∧ (c, p.2) ∈ Q}

theorem relComp_sub {P Q : Set (A × A)} (hP : IsSubuniverse L P) (hQ : IsSubuniverse L Q) :
    IsSubuniverse L (relComp P Q) := by
  intro n f x hx
  choose c hc1 hc2 using hx
  refine ⟨funMap f c, ?_, ?_⟩
  · have := hP n f (fun i => ((x i).1, c i)) hc1
    exact this
  · have := hQ n f (fun i => (c i, (x i).2)) hc2
    exact this

def Spow (S : Set (A × A)) : ℕ → Set (A × A)
  | 0 => {p | p.1 = p.2}
  | m + 1 => relComp (Spow S m) S

theorem diag_sub : IsSubuniverse L {p : A × A | p.1 = p.2} := by
  intro n f x hx
  show funMap f (fun i => (x i).1) = funMap f (fun i => (x i).2)
  congr 1; ext i; exact hx i

theorem Spow_sub {S : Set (A × A)} (hS : IsSubuniverse L S) (m : ℕ) : IsSubuniverse L (Spow S m) := by
  induction m with
  | zero => exact diag_sub
  | succ m ih => exact relComp_sub ih hS

end BKAux

namespace BKAux
open BKAbsorption
variable {L : FirstOrder.Language.{u, v}} {A : Type w} [L.Structure A]

theorem Spow_refl {S : Set (A × A)} (hS : ∀ a, (a, a) ∈ S) (m : ℕ) (a : A) : (a, a) ∈ Spow S m := by
  induction m with
  | zero => rfl
  | succ m ih => exact ⟨a, ih, hS a⟩

theorem Spow_mono {S : Set (A × A)} (hS : ∀ a, (a, a) ∈ S) {m m' : ℕ} (h : m ≤ m') : Spow S m ⊆ Spow S m' := by
  induction h with
  | refl => exact fun _ h => h
  | step _ ih =>
    intro p hp
    exact ⟨p.2, ih hp, hS p.2⟩

theorem Spow_add (S : Set (A × A)) (m m' : ℕ) (a a' : A) :
    (a, a') ∈ Spow S (m + m') ↔ ∃ c, (a, c) ∈ Spow S m ∧ (c, a') ∈ Spow S m' := by
  induction m' generalizing a' with
  | zero =>
    constructor
    · intro h; exact ⟨a', h, rfl⟩
    · rintro ⟨c, h1, h2⟩
      have : c = a' := h2
      subst this; exact h1
  | succ m' ih =>
    constructor
    · rintro ⟨d, hd, hdS⟩
      obtain ⟨c, hc1, hc2⟩ := (ih d).1 hd
      exact ⟨c, hc1, d, hc2, hdS⟩
    · rintro ⟨c, hc1, d, hc2, hdS⟩
      exact ⟨d, (ih d).2 ⟨c, hc1, hc2⟩, hdS⟩

theorem Spow_symm {S : Set (A × A)} (hS : ∀ a b, (a, b) ∈ S → (b, a) ∈ S) (m : ℕ) (a a' : A) :
    (a, a') ∈ Spow S m → (a', a) ∈ Spow S m := by
  induction m generalizing a a' with
  | zero => intro h; exact h.symm
  | succ m ih =>
    intro h
    have h' : (a, a') ∈ Spow S (m + 1) := h
    rw [show m + 1 = 1 + m by omega, Spow_add] at h'
    obtain ⟨c, hc1, hc2⟩ := h'
    have h1 : (c, a) ∈ Spow S 1 := by
      obtain ⟨d, hd, hdS⟩ := hc1
      have : a = d := hd
      subst this
      exact ⟨c, rfl, hS _ _ hdS⟩
    have h2 := ih _ _ hc2
    show (a', a) ∈ Spow S (m + 1)
    rw [Spow_add]
    exact ⟨c, h2, h1⟩

end BKAux


open BKAbsorption BKAux in
theorem thm211 {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]
    [Finite A] [Finite B] (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    (hnoA : ∀ X : Set A, IsAbsorbing L X → X.Nonempty → X = Set.univ)
    (hnoB : ∀ X : Set B, IsAbsorbing L X → X.Nonempty → X = Set.univ)
    (R : Set (A × B)) (hR : IsSubuniverse L R) (hsub : Subdirect R) (hlin : Linked R)
    (hne : R ≠ Set.univ) : False := by
  classical
  haveI := Fintype.ofFinite A
  set S : Set (A × A) := {p | LinkStep R p.1 p.2} with hSdef
  have hfst : ∀ a : A, ∃ b, (a, b) ∈ R := by
    intro a
    have : a ∈ Prod.fst '' R := by rw [hsub.1]; trivial
    obtain ⟨⟨a', b⟩, hab, rfl⟩ := this
    exact ⟨b, hab⟩
  have hSrefl : ∀ a, (a, a) ∈ S := fun a => by
    obtain ⟨b, hb⟩ := hfst a; exact ⟨b, hb, hb⟩
  have hSsymm : ∀ a b, (a, b) ∈ S → (b, a) ∈ S := fun a b ⟨c, h1, h2⟩ => ⟨c, h2, h1⟩
  have hSsub : IsSubuniverse L S := by
    intro n f x hx
    choose b hb1 hb2 using hx
    refine ⟨funMap f b, ?_, ?_⟩
    · exact hR n f (fun i => ((x i).1, b i)) hb1
    · exact hR n f (fun i => ((x i).2, b i)) hb2
  have hpath : ∀ a a' : A, ∃ m, (a, a') ∈ Spow S m := by
    intro a a'
    have ha : a ∈ Prod.fst '' R := by rw [hsub.1]; trivial
    have ha' : a' ∈ Prod.fst '' R := by rw [hsub.1]; trivial
    have hrtg := hlin a a' ha ha'
    clear ha'
    induction hrtg with
    | refl => exact ⟨0, rfl⟩
    | tail _ hbc ih => obtain ⟨m, hm⟩ := ih; exact ⟨m + 1, _, hm, hbc⟩
  have hex : ∃ K, ∀ a a', (a, a') ∈ Spow S K := by
    choose m hm using hpath
    refine ⟨Finset.univ.sup (fun p : A × A => m p.1 p.2), fun a a' => ?_⟩
    exact Spow_mono hSrefl (Finset.le_sup (f := fun p : A × A => m p.1 p.2) (Finset.mem_univ (a, a'))) (hm a a')
  set K0 := Nat.find hex with hK0
  have hK0spec : ∀ a a', (a, a') ∈ Spow S K0 := Nat.find_spec hex
  by_cases hK : K0 ≤ 1
  · have hSall : ∀ a c : A, (a, c) ∈ S := by
      intro a c
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hK with h | h
      · have := hK0spec a c
        rw [h] at this
        have : a = c := this
        subst this; exact hSrefl a
      · have := hK0spec a c
        rw [h] at this
        obtain ⟨d, hd, hdS⟩ := this
        have : a = d := hd
        subst this; exact hdS
    exact thm211_core T hA hB hnoA hnoB R hR hsub (fun a c => hSall a c) hne
  · push_neg at hK
    have hmin : ¬ ∀ a a', (a, a') ∈ Spow S (K0 - 1) := Nat.find_min hex (by omega)
    set Q := Spow S (K0 - 1) with hQ
    have hQsub : IsSubuniverse L Q := Spow_sub hSsub _
    have hQsd : Subdirect Q := by
      constructor
      · apply Set.eq_univ_of_forall; intro a; exact ⟨(a, a), Spow_refl hSrefl _ a, rfl⟩
      · apply Set.eq_univ_of_forall; intro a; exact ⟨(a, a), Spow_refl hSrefl _ a, rfl⟩
    have hQne : Q ≠ Set.univ := by
      intro h
      apply hmin
      intro a a'
      have : (a, a') ∈ Q := by rw [h]; trivial
      exact this
    have hQRR : ∀ a c : A, ∃ b : A, (a, b) ∈ Q ∧ (c, b) ∈ Q := by
      intro a c
      have h1 : (a, c) ∈ Spow S K0 := hK0spec a c
      have h2 : (a, c) ∈ Spow S ((K0 - 1) + (K0 - 1)) := Spow_mono hSrefl (by omega) h1
      obtain ⟨b, hb1, hb2⟩ := (Spow_add S _ _ a c).1 h2
      exact ⟨b, hb1, Spow_symm hSsymm _ _ _ hb2⟩
    exact thm211_core T hA hA hnoA hnoA Q hQsub hQsd hQRR hQne

namespace BKAux
open BKAbsorption

section Transfer
variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]

def subS (S : Set M) (hS : IsSubuniverse L S) : L.Substructure M where
  carrier := S
  fun_mem := fun {n} f x hx => hS n f x hx

theorem subS_funMap' (S : Set M) (hS : IsSubuniverse L S) {n : ℕ} (f : L.Functions n)
    (x : Fin n → subS S hS) :
    ((funMap f x : subS S hS) : M) = funMap f (fun i => (x i : M)) := rfl

theorem subS_realize (S : Set M) (hS : IsSubuniverse L S) {α : Type*} (t : L.Term α)
    (a : α → subS S hS) :
    ((t.realize a : subS S hS) : M) = t.realize (fun i => (a i : M)) := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    simp only [Term.realize]
    rw [subS_funMap']
    simp only [ih]

theorem subS_funMap (S : Set M) (hS : IsSubuniverse L S) {n : ℕ} (f : L.Functions n)
    (x : Fin n → subS S hS) :
    ((funMap f x : subS S hS) : M) = funMap f (fun i => (x i : M)) := rfl

theorem subS_idem (S : Set M) (hS : IsSubuniverse L S) (h : IsIdempotent L M) :
    IsIdempotent L (subS S hS) := by
  intro n f a
  apply Subtype.ext
  rw [subS_funMap]
  exact h n f a

theorem subS_taylor (S : Set M) (hS : IsSubuniverse L S) (T : TaylorDatum L) (h : IsTaylorAlg T M) :
    IsTaylorAlg T (subS S hS) := by
  refine ⟨subS_idem S hS h.1, fun j x y => ?_⟩
  apply Subtype.ext
  rw [subS_realize, subS_realize]
  have := h.2 j (x : M) (y : M)
  convert this using 2 <;> (ext i; cases T.σ j i <;> cases T.τ j i <;> simp)

end Transfer
end BKAux

namespace BKAbsorption
variable (L : FirstOrder.Language.{u, v})

/-- `E` absorbs the subuniverse `Rr` (relative absorption). -/
def AbsorbsIn {M : Type w} [L.Structure M] (Rr E : Set M) : Prop :=
  IsSubuniverse L E ∧ E ⊆ Rr ∧ ∃ (n : ℕ) (t : L.Term (Fin n)), 0 < n ∧
    ∀ (k : Fin n) (a : Fin n → M), (∀ i, a i ∈ Rr) → (∀ i, i ≠ k → a i ∈ E) → t.realize a ∈ E
end BKAbsorption

namespace BKAux
open BKAbsorption
variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]

theorem absorbs_trans_rel {B C : Set M} (hB : IsAbsorbing L B) (h : AbsorbsIn L B C) : IsAbsorbing L C := by
  obtain ⟨hC, hCB, m, s, hm, hs⟩ := h
  exact absorbing_trans B C hB hC hCB ⟨m, s, hm, hs⟩

theorem hno_of_min {C : Set M} (hC : MinAbsorbing L C) :
    ∀ F : Set (subS C hC.2.1.1), IsAbsorbing L F → F.Nonempty → F = Set.univ := by
  intro F hF hFne
  have hCs : IsSubuniverse L C := hC.2.1.1
  set F' : Set M := Subtype.val '' F with hF'
  have hF'sub : IsSubuniverse L F' := by
    intro n f x hx
    choose y hyF hyx using hx
    refine ⟨funMap f y, hF.1 n f y hyF, ?_⟩
    rw [subS_funMap']
    congr 1; ext i; exact hyx i
  have hF'C : F' ⊆ C := by
    rintro _ ⟨y, -, rfl⟩; exact y.2
  obtain ⟨-, n, t, hn, ht⟩ := hF
  have habs : AbsorbsIn L C F' := by
    refine ⟨hF'sub, hF'C, n, t, hn, fun k a haC hak => ?_⟩
    let a' : Fin n → subS C hCs := fun i => ⟨a i, haC i⟩
    have hmem : ∀ i, i ≠ k → a' i ∈ F := by
      intro i hik
      obtain ⟨y, hyF, hy⟩ := hak i hik
      have : a' i = y := Subtype.ext hy.symm
      rw [this]; exact hyF
    have := ht k a' hmem
    refine ⟨_, this, ?_⟩
    rw [subS_realize]
  have hF'abs : IsAbsorbing L F' := absorbs_trans_rel hC.2.1 habs
  have hne : F'.Nonempty := hFne.image _
  have := hC.2.2 F' hne hF'C hF'abs
  apply Set.eq_univ_of_forall
  intro y
  have hy : (y : M) ∈ F' := by rw [this]; exact y.2
  obtain ⟨z, hz, hzy⟩ := hy
  have : z = y := Subtype.ext hzy
  rw [← this]; exact hz

theorem swap_sub {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B] {R : Set (A × B)}
    (hR : IsSubuniverse L R) : IsSubuniverse L {p : B × A | (p.2, p.1) ∈ R} := by
  intro n f x hx
  exact hR n f (fun i => ((x i).2, (x i).1)) hx

theorem swap_subdirect {A : Type w} {B : Type w'} {R : Set (A × B)} (h : Subdirect R) :
    Subdirect {p : B × A | (p.2, p.1) ∈ R} := by
  constructor
  · apply Set.eq_univ_of_forall; intro b
    have : b ∈ Prod.snd '' R := by rw [h.2]; trivial
    obtain ⟨⟨a, b'⟩, hab, rfl⟩ := this
    exact ⟨(b', a), hab, rfl⟩
  · apply Set.eq_univ_of_forall; intro a
    have : a ∈ Prod.fst '' R := by rw [h.1]; trivial
    obtain ⟨⟨a', b⟩, hab, rfl⟩ := this
    exact ⟨(b, a'), hab, rfl⟩

end BKAux

open BKAbsorption BKAux in
theorem prop215_ii {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]
    (R : Set (A × B)) (hR : IsSubuniverse L R) (hsd : Subdirect R)
    {C : Set A} {D : Set B} (hC : MinAbsorbing L C) (hD : MinAbsorbing L D)
    (hne : ∃ c ∈ C, ∃ d ∈ D, (c, d) ∈ R) :
    (∀ c ∈ C, ∃ d ∈ D, (c, d) ∈ R) ∧ (∀ d ∈ D, ∃ c ∈ C, (c, d) ∈ R) := by
  obtain ⟨c0, hc0, d0, hd0, hcd0⟩ := hne
  constructor
  · -- D⁻ is absorbing in A
    have h1 : IsAbsorbing L {a : A | ∃ b ∈ D, (b, a) ∈ {p : B × A | (p.2, p.1) ∈ R}} :=
      nbhd_absorbing _ (swap_sub hR) (swap_subdirect hsd) D hD.2.1
    have h2 := absorbing_inter C _ hC.2.1 h1
    have hne' : (C ∩ {a : A | ∃ b ∈ D, (b, a) ∈ {p : B × A | (p.2, p.1) ∈ R}}).Nonempty :=
      ⟨c0, hc0, d0, hd0, hcd0⟩
    have h3 := hC.2.2 _ hne' Set.inter_subset_left h2
    intro c hc
    have : c ∈ C ∩ {a : A | ∃ b ∈ D, (b, a) ∈ {p : B × A | (p.2, p.1) ∈ R}} := by rw [h3]; exact hc
    obtain ⟨-, d, hd, hdc⟩ := this
    exact ⟨d, hd, hdc⟩
  · have h1 : IsAbsorbing L {b : B | ∃ a ∈ C, (a, b) ∈ R} := nbhd_absorbing R hR hsd C hC.2.1
    have h2 := absorbing_inter D _ hD.2.1 h1
    have hne' : (D ∩ {b : B | ∃ a ∈ C, (a, b) ∈ R}).Nonempty := ⟨d0, hd0, c0, hc0, hcd0⟩
    have h3 := hD.2.2 _ hne' Set.inter_subset_left h2
    intro d hd
    have : d ∈ D ∩ {b : B | ∃ a ∈ C, (a, b) ∈ R} := by rw [h3]; exact hd
    obtain ⟨-, c, hc, hcd⟩ := this
    exact ⟨c, hc, hcd⟩

open BKAbsorption BKAux in
theorem prop215_i {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]
    (hidA : IsIdempotent L A) (R : Set (A × B)) (hlin : Linked R) (E : Set (A × B))
    (hE : AbsorbsIn L R E) : Linked E := by
  obtain ⟨hEsub, hER, n, t, hn, ht⟩ := hE
  intro a a' ha ha'
  obtain ⟨⟨a₁, b⟩, hab, rfl⟩ := ha
  obtain ⟨⟨a₁', b'⟩, hab', rfl⟩ := ha'
  simp only at *
  have hrt := hlin a₁ a₁' ⟨(a₁, b), hER hab, rfl⟩ ⟨(a₁', b'), hER hab', rfl⟩
  -- the chain of stages
  let x : ℕ → A := fun s => t.realize (fun i : Fin n => if i.val < s then a₁' else a₁)
  have hx0 : x 0 = a₁ := by
    simp only [x, Nat.not_lt_zero, if_false]
    exact term_idem (show IsIdem L A from hidA) t a₁
  have hxn : x n = a₁' := by
    simp only [x]
    have : (fun i : Fin n => if i.val < n then a₁' else a₁) = fun _ => a₁' := by
      ext i; simp [i.2]
    rw [this]; exact term_idem (show IsIdem L A from hidA) t a₁'
  have hstage : ∀ s : ℕ, s < n → Relation.ReflTransGen (LinkStep E) (x s) (x (s + 1)) := by
    intro s hs
    let Φ : A → A := fun c => t.realize (fun i : Fin n => if i.val < s then a₁' else if i.val = s then c else a₁)
    have hΦ : ∀ c c', LinkStep R c c' → LinkStep E (Φ c) (Φ c') := by
      rintro c c' ⟨d, hcd, hc'd⟩
      let Ψ : B → B := fun d => t.realize (fun i : Fin n => if i.val < s then b' else if i.val = s then d else b)
      refine ⟨Ψ d, ?_, ?_⟩
      · have key := ht ⟨s, hs⟩ (fun i : Fin n => if i.val < s then (a₁', b') else if i.val = s then (c, d) else (a₁, b))
          (fun i => by
            by_cases h1 : i.val < s
            · simp only [h1, if_true]; exact hER hab'
            · by_cases h2 : i.val = s
              · rw [if_neg h1, if_pos h2]; exact hcd
              · simp only [h1, h2, if_false]; exact hER hab)
          (fun i hik => by
            have h2 : i.val ≠ s := fun h => hik (Fin.ext h)
            by_cases h1 : i.val < s
            · simp only [h1, if_true]; exact hab'
            · simp only [h1, h2, if_false]; exact hab)
        have e : (fun i : Fin n => if i.val < s then (a₁', b') else if i.val = s then (c, d) else (a₁, b))
            = fun i => ((fun i : Fin n => if i.val < s then a₁' else if i.val = s then c else a₁) i,
                (fun i : Fin n => if i.val < s then b' else if i.val = s then d else b) i) := by
          ext i <;> (by_cases h1 : i.val < s <;> by_cases h2 : i.val = s <;> simp [h1, h2])
        rw [e, realize_prod] at key
        exact key
      · have key := ht ⟨s, hs⟩ (fun i : Fin n => if i.val < s then (a₁', b') else if i.val = s then (c', d) else (a₁, b))
          (fun i => by
            by_cases h1 : i.val < s
            · simp only [h1, if_true]; exact hER hab'
            · by_cases h2 : i.val = s
              · rw [if_neg h1, if_pos h2]; exact hc'd
              · simp only [h1, h2, if_false]; exact hER hab)
          (fun i hik => by
            have h2 : i.val ≠ s := fun h => hik (Fin.ext h)
            by_cases h1 : i.val < s
            · simp only [h1, if_true]; exact hab'
            · simp only [h1, h2, if_false]; exact hab)
        have e : (fun i : Fin n => if i.val < s then (a₁', b') else if i.val = s then (c', d) else (a₁, b))
            = fun i => ((fun i : Fin n => if i.val < s then a₁' else if i.val = s then c' else a₁) i,
                (fun i : Fin n => if i.val < s then b' else if i.val = s then d else b) i) := by
          ext i <;> (by_cases h1 : i.val < s <;> by_cases h2 : i.val = s <;> simp [h1, h2])
        rw [e, realize_prod] at key
        exact key
    have hlift := Relation.ReflTransGen.lift (p := LinkStep E) Φ (fun c c' h => hΦ c c' h) a₁ a₁' hrt
    have e1 : Φ a₁ = x s := by
      simp only [Φ, x]; congr 1; ext i
      by_cases h1 : i.val < s <;> by_cases h2 : i.val = s <;> simp [h1, h2]
    have e2 : Φ a₁' = x (s + 1) := by
      simp only [Φ, x]; congr 1; ext i
      by_cases h1 : i.val < s <;> by_cases h2 : i.val = s <;> simp [h1, h2] <;> omega
    have hlift' : Relation.ReflTransGen (LinkStep E) (Φ a₁) (Φ a₁') := hlift
    rw [e1, e2] at hlift'
    exact hlift'
  have hall : ∀ s : ℕ, s ≤ n → Relation.ReflTransGen (LinkStep E) a₁ (x s) := by
    intro s
    induction s with
    | zero => intro _; rw [hx0]
    | succ s ih => intro hs; exact (ih (by omega)).trans (hstage s (by omega))
  have := hall n le_rfl
  rwa [hxn] at this

open BKAbsorption BKAux in
theorem sub_thm211 {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]
    [Finite A] [Finite B] (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    {C : Set A} {D : Set B} (hC : MinAbsorbing L C) (hD : MinAbsorbing L D)
    (R'' : Set (A × B)) (hR : IsSubuniverse L R'') (hCD : R'' ⊆ C ×ˢ D)
    (hs1 : ∀ c ∈ C, ∃ d ∈ D, (c, d) ∈ R'') (hs2 : ∀ d ∈ D, ∃ c ∈ C, (c, d) ∈ R'')
    (hlin : Linked R'') : C ×ˢ D ⊆ R'' := by
  have hCs : IsSubuniverse L C := hC.2.1.1
  have hDs : IsSubuniverse L D := hD.2.1.1
  let R' : Set (subS C hCs × subS D hDs) := {p | ((p.1 : A), (p.2 : B)) ∈ R''}
  have hR'sub : IsSubuniverse L R' := by
    intro n f x hx
    show (((funMap f x).1 : A), ((funMap f x).2 : B)) ∈ R''
    exact hR n f (fun i => (((x i).1 : A), ((x i).2 : B))) hx
  have hR'sd : Subdirect R' := by
    constructor
    · apply Set.eq_univ_of_forall; intro c
      obtain ⟨d, hd, hcd⟩ := hs1 c c.2
      exact ⟨(c, ⟨d, hd⟩), hcd, rfl⟩
    · apply Set.eq_univ_of_forall; intro d
      obtain ⟨c, hc, hcd⟩ := hs2 d d.2
      exact ⟨(⟨c, hc⟩, d), hcd, rfl⟩
  have hR'lin : Linked R' := by
    intro x x' _ _
    obtain ⟨d, hd, hxd⟩ := hs1 x x.2
    obtain ⟨d', hd', hxd'⟩ := hs1 x' x'.2
    have hrt := hlin (x : A) (x' : A) ⟨((x : A), d), hxd, rfl⟩ ⟨((x' : A), d'), hxd', rfl⟩
    have key : ∀ y : A, Relation.ReflTransGen (LinkStep R'') (x : A) y →
        ∃ y' : subS C hCs, (y' : A) = y ∧ Relation.ReflTransGen (LinkStep R') x y' := by
      intro y hy
      induction hy with
      | refl => exact ⟨x, rfl, Relation.ReflTransGen.refl⟩
      | tail _ hlk ih =>
        obtain ⟨y', rfl, hy'⟩ := ih
        obtain ⟨b, hb1, hb2⟩ := hlk
        have hzC : _ ∈ C := (hCD hb2).1
        have hbD : b ∈ D := (hCD hb2).2
        exact ⟨⟨_, hzC⟩, rfl, hy'.tail ⟨⟨b, hbD⟩, hb1, hb2⟩⟩
    obtain ⟨y', hy', hrt'⟩ := key _ hrt
    have : y' = x' := Subtype.ext hy'
    rw [this] at hrt'
    exact hrt'
  by_contra hnot
  have hne : R' ≠ Set.univ := by
    intro h
    apply hnot
    rintro ⟨c, d⟩ ⟨hc, hd⟩
    have : ((⟨c, hc⟩ : subS C hCs), (⟨d, hd⟩ : subS D hDs)) ∈ R' := by rw [h]; trivial
    exact this
  exact thm211 T (subS_taylor C hCs T hA) (subS_taylor D hDs T hB) (hno_of_min hC) (hno_of_min hD)
    R' hR'sub hR'sd hR'lin hne

open BKAbsorption BKAux in
theorem common_absorb {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]
    {C : Set A} {D : Set B} (hC : IsAbsorbing L C) (hD : IsAbsorbing L D) :
    ∃ (n : ℕ) (u : L.Term (Fin n)), 0 < n ∧
      (∀ (k : Fin n) (a : Fin n → A), (∀ i, i ≠ k → a i ∈ C) → u.realize a ∈ C) ∧
      (∀ (k : Fin n) (b : Fin n → B), (∀ i, i ≠ k → b i ∈ D) → u.realize b ∈ D) := by
  obtain ⟨hCs, n1, t1, h1, ht1⟩ := hC
  obtain ⟨hDs, n2, t2, h2, ht2⟩ := hD
  refine ⟨n1 * n2, compTerm' t1 t2, Nat.mul_pos h1 h2, ?_, ?_⟩
  · intro k a hk
    obtain ⟨⟨k1, k2⟩, rfl⟩ : ∃ p : Fin n1 × Fin n2, finProdFinEquiv p = k :=
      ⟨finProdFinEquiv.symm k, finProdFinEquiv.apply_symm_apply k⟩
    rw [compTerm'_realize]
    refine ht1 k1 _ (fun i hi => ?_)
    refine realize_mem hCs t2 _ (fun j => hk _ ?_)
    intro h
    have := finProdFinEquiv.injective h
    exact hi (Prod.mk.inj this).1
  · intro k b hk
    obtain ⟨⟨k1, k2⟩, rfl⟩ : ∃ p : Fin n1 × Fin n2, finProdFinEquiv p = k :=
      ⟨finProdFinEquiv.symm k, finProdFinEquiv.apply_symm_apply k⟩
    rw [compTerm'_realize]
    refine realize_mem hDs t1 _ (fun i => ?_)
    by_cases hi : i = k1
    · subst hi
      refine ht2 k2 _ (fun j hj => hk _ ?_)
      intro h
      have := finProdFinEquiv.injective h
      exact hj (Prod.mk.inj this).2
    · refine realize_mem hDs t2 _ (fun j => hk _ ?_)
      intro h
      have := finProdFinEquiv.injective h
      exact hi (Prod.mk.inj this).1

open BKAbsorption BKAux in
theorem proj_absorbs {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]
    {C : Set A} {D : Set B} (R F : Set (A × B)) (hF : AbsorbsIn L R F) (hFCD : F ⊆ C ×ˢ D)
    (hFR : F ⊆ R) (hs : ∀ c ∈ C, ∃ d, (c, d) ∈ R) :
    AbsorbsIn L C (Prod.fst '' F) := by
  classical
  obtain ⟨hFs, -, n, t, hn, ht⟩ := hF
  refine ⟨?_, ?_, n, t, hn, ?_⟩
  · intro m f x hx
    choose p hpF hpx using hx
    refine ⟨funMap f p, hFs m f p hpF, ?_⟩
    show funMap f (fun i => (p i).1) = funMap f x
    congr 1; ext i; exact hpx i
  · rintro _ ⟨p, hp, rfl⟩; exact (hFCD hp).1
  · intro k a haC hak
    choose g hg using fun (i : Fin n) (h : i ≠ k) => hak i h
    obtain ⟨dk, hdk⟩ := hs (a k) (haC k)
    let p : Fin n → A × B := fun i => if h : i = k then (a k, dk) else g i h
    have hpR : ∀ i, p i ∈ R := by
      intro i
      by_cases h : i = k
      · simp only [p, h, dif_pos]; subst h; exact hdk
      · simp only [p, h, dif_neg, not_false_eq_true]
        exact hFR (hg i h).1
    have hpF : ∀ i, i ≠ k → p i ∈ F := by
      intro i h
      simp only [p, h, dif_neg, not_false_eq_true]
      exact (hg i h).1
    have := ht k p hpR hpF
    refine ⟨_, this, ?_⟩
    have e : p = fun i => (a i, (p i).2) := by
      ext i
      · by_cases h : i = k
        · simp [p, h]
        · simp only [p, h, dif_neg, not_false_eq_true]; exact (hg i h).2
      · rfl
    rw [e, realize_prod]

open BKAbsorption BKAux in
theorem swap_absorbsIn {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]
    {R F : Set (A × B)} (hF : AbsorbsIn L R F) :
    AbsorbsIn L {p : B × A | (p.2, p.1) ∈ R} {p : B × A | (p.2, p.1) ∈ F} := by
  obtain ⟨hFs, hFR, n, t, hn, ht⟩ := hF
  refine ⟨swap_sub hFs, fun p hp => hFR hp, n, t, hn, fun k a haR hak => ?_⟩
  have := ht k (fun i => ((a i).2, (a i).1)) haR hak
  have e : (fun i => ((a i).2, (a i).1)) = fun i => ((fun j => (a j).2) i, (fun j => (a j).1) i) := rfl
  rw [e, realize_prod] at this
  have e2 : t.realize a = (t.realize (fun j => (a j).1), t.realize (fun j => (a j).2)) :=
    realize_prod t (fun j => (a j).1) (fun j => (a j).2)
  show ((t.realize a).2, (t.realize a).1) ∈ F
  rw [e2]
  exact this

open BKAbsorption BKAux in
theorem prop215_iii {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]
    [Finite A] [Finite B] (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    (R : Set (A × B)) (hR : IsSubuniverse L R) (hsd : Subdirect R) (hlin : Linked R)
    {C : Set A} {D : Set B} (hC : MinAbsorbing L C) (hD : MinAbsorbing L D)
    (hne : ∃ c ∈ C, ∃ d ∈ D, (c, d) ∈ R) :
    C ×ˢ D ⊆ R ∧ AbsorbsIn L R (C ×ˢ D) ∧
      ∀ F : Set (A × B), F.Nonempty → F ⊆ C ×ˢ D → AbsorbsIn L R F → F = C ×ˢ D := by
  classical
  obtain ⟨hs1, hs2⟩ := prop215_ii R hR hsd hC hD hne
  obtain ⟨n, u, hn, huC, huD⟩ := common_absorb hC.2.1 hD.2.1
  have hCs : IsSubuniverse L C := hC.2.1.1
  have hDs : IsSubuniverse L D := hD.2.1.1
  set E : Set (A × B) := (C ×ˢ D) ∩ R with hE
  have hEabs : AbsorbsIn L R E := by
    refine ⟨?_, Set.inter_subset_right, n, u, hn, ?_⟩
    · intro m f x hx
      refine ⟨⟨hCs m f _ (fun i => (hx i).1.1), hDs m f _ (fun i => (hx i).1.2)⟩, hR m f x (fun i => (hx i).2)⟩
    · intro k a haR hak
      have h1 : u.realize (fun i => (a i).1) ∈ C := huC k _ (fun i hi => (hak i hi).1.1)
      have h2 : u.realize (fun i => (a i).2) ∈ D := huD k _ (fun i hi => (hak i hi).1.2)
      have h3 := realize_mem hR u a haR
      have e : u.realize a = (u.realize (fun i => (a i).1), u.realize (fun i => (a i).2)) :=
        realize_prod u (fun i => (a i).1) (fun i => (a i).2)
      exact ⟨⟨by rw [e]; exact h1, by rw [e]; exact h2⟩, h3⟩
  have hElin : Linked E := prop215_i hA.1 R hlin E hEabs
  have hCDE : C ×ˢ D ⊆ E := sub_thm211 T hA hB hC hD E hEabs.1 (Set.inter_subset_left)
    (fun c hc => by obtain ⟨d, hd, hcd⟩ := hs1 c hc; exact ⟨d, hd, ⟨hc, hd⟩, hcd⟩)
    (fun d hd => by obtain ⟨c, hc, hcd⟩ := hs2 d hd; exact ⟨c, hc, ⟨hc, hd⟩, hcd⟩) hElin
  have hEeq : E = C ×ˢ D := Set.Subset.antisymm Set.inter_subset_left hCDE
  have hCDR : C ×ˢ D ⊆ R := fun p hp => (hCDE hp).2
  refine ⟨hCDR, by rw [← hEeq]; exact hEabs, ?_⟩
  intro F hFne hFCD hF
  have hFlin : Linked F := prop215_i hA.1 R hlin F hF
  have hFR : F ⊆ R := fun p hp => hCDR (hFCD hp)
  -- projections of F
  have hp1 : AbsorbsIn L C (Prod.fst '' F) :=
    proj_absorbs R F hF hFCD hFR (fun c hc => by obtain ⟨d, -, hd⟩ := hs1 c hc; exact ⟨d, hd⟩)
  have hp2' : AbsorbsIn L D (Prod.fst '' {p : B × A | (p.2, p.1) ∈ F}) :=
    proj_absorbs {p : B × A | (p.2, p.1) ∈ R} {p : B × A | (p.2, p.1) ∈ F} (swap_absorbsIn hF)
      (fun p hp => ⟨(hFCD hp).2, (hFCD hp).1⟩) (fun p hp => hFR hp)
      (fun d hd => by obtain ⟨c, -, hc⟩ := hs2 d hd; exact ⟨c, hc⟩)
  have hπ1 : Prod.fst '' F = C := by
    have habs := absorbs_trans_rel hC.2.1 hp1
    have hne1 : (Prod.fst '' F).Nonempty := hFne.image _
    exact hC.2.2 _ hne1 (by rintro _ ⟨p, hp, rfl⟩; exact (hFCD hp).1) habs
  have hπ2 : Prod.fst '' {p : B × A | (p.2, p.1) ∈ F} = D := by
    have habs := absorbs_trans_rel hD.2.1 hp2'
    have hne1 : (Prod.fst '' {p : B × A | (p.2, p.1) ∈ F}).Nonempty := by
      obtain ⟨p, hp⟩ := hFne; exact ⟨p.2, (p.2, p.1), hp, rfl⟩
    exact hD.2.2 _ hne1 (by rintro _ ⟨p, hp, rfl⟩; exact (hFCD hp).2) habs
  have hsF1 : ∀ c ∈ C, ∃ d ∈ D, (c, d) ∈ F := by
    intro c hc
    rw [← hπ1] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    exact ⟨p.2, (hFCD hp).2, hp⟩
  have hsF2 : ∀ d ∈ D, ∃ c ∈ C, (c, d) ∈ F := by
    intro d hd
    rw [← hπ2] at hd
    obtain ⟨p, hp, rfl⟩ := hd
    exact ⟨p.2, (hFCD hp).1, hp⟩
  exact Set.Subset.antisymm hFCD (sub_thm211 T hA hB hC hD F hF.1 hFCD hsF1 hsF2 hFlin)

open BKAbsorption BKAux in
theorem exists_min_absorbing {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M] [Finite M]
    (X : Set M) (hX : IsAbsorbing L X) (hne : X.Nonempty) :
    ∃ D : Set M, D ⊆ X ∧ MinAbsorbing L D := by
  classical
  have hmem : X ∈ {Y : Set M | Y ⊆ X ∧ Y.Nonempty ∧ IsAbsorbing L Y} := ⟨subset_rfl, hne, hX⟩
  obtain ⟨D, hDX, hDmin⟩ := (Set.toFinite {Y : Set M | Y ⊆ X ∧ Y.Nonempty ∧ IsAbsorbing L Y}).exists_le_minimal hmem
  obtain ⟨hDsub, hDne, hDabs⟩ := hDmin.prop
  refine ⟨D, hDsub, hDne, hDabs, fun F hFne hFD hFabs => ?_⟩
  exact ((hDmin.2 ⟨hFD.trans hDsub, hFne, hFabs⟩ hFD).antisymm hFD).symm

open BKAbsorption BKAux in
theorem prop215_iv {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]
    [Finite A] [Finite B] (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    (R : Set (A × B)) (hR : IsSubuniverse L R) (hsd : Subdirect R) (hlin : Linked R)
    {C : Set A} (hC : MinAbsorbing L C) :
    ∃ D : Set B, MinAbsorbing L D ∧ C ×ˢ D ⊆ R := by
  have h1 : IsAbsorbing L {b : B | ∃ a ∈ C, (a, b) ∈ R} := nbhd_absorbing R hR hsd C hC.2.1
  have hne : {b : B | ∃ a ∈ C, (a, b) ∈ R}.Nonempty := by
    obtain ⟨a, ha⟩ := hC.1
    have : a ∈ Prod.fst '' R := by rw [hsd.1]; trivial
    obtain ⟨⟨a', b⟩, hab, rfl⟩ := this
    exact ⟨b, a', ha, hab⟩
  obtain ⟨D, hDX, hD⟩ := exists_min_absorbing _ h1 hne
  obtain ⟨d, hd⟩ := hD.1
  obtain ⟨c, hc, hcd⟩ := hDX hd
  exact ⟨D, hD, (prop215_iii T hA hB R hR hsd hlin hC hD ⟨c, hc, d, hd, hcd⟩).1⟩


namespace BKAux
open BKAbsorption
section sets
variable {A : Type w} {B : Type w'}

abbrev SS (A : Type w) (B : Type w') := Set A ⊕ Set B

def memS : A ⊕ B → SS A B → Prop
  | Sum.inl a, Sum.inl X => a ∈ X
  | Sum.inr b, Sum.inr Y => b ∈ Y
  | _, _ => False

def nbS (R : Set (A × B)) : SS A B → SS A B
  | Sum.inl X => Sum.inr {b | ∃ a ∈ X, (a, b) ∈ R}
  | Sum.inr Y => Sum.inl {a | ∃ b ∈ Y, (a, b) ∈ R}

theorem memS_nbS (R : Set (A × B)) (S : SS A B) (y : A ⊕ B) :
    memS y (nbS R S) ↔ ∃ x, memS x S ∧ LinkAdj R x y := by
  rcases S with X | Y <;> rcases y with a | b
  · simp [nbS, memS, LinkAdj]
  · simp only [nbS, memS, LinkAdj]
    constructor
    · rintro ⟨a, ha, h⟩; exact ⟨Sum.inl a, ha, h⟩
    · rintro ⟨x, hx, h⟩
      rcases x with a' | b'
      · exact ⟨a', hx, h⟩
      · exact absurd hx (by simp [memS])
  · simp only [nbS, memS, LinkAdj]
    constructor
    · rintro ⟨b, hb, h⟩; exact ⟨Sum.inr b, hb, h⟩
    · rintro ⟨x, hx, h⟩
      rcases x with a' | b'
      · exact absurd hx (by simp [memS])
      · exact ⟨b', hx, h⟩
  · simp [nbS, memS, LinkAdj]

end sets
end BKAux

namespace BKAux
open BKAbsorption
section sets2
variable {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]

def AbsS (L : FirstOrder.Language.{u, v}) [L.Structure A] [L.Structure B] : SS A B → Prop
  | Sum.inl X => IsAbsorbing L X
  | Sum.inr Y => IsAbsorbing L Y

def MinS (L : FirstOrder.Language.{u, v}) [L.Structure A] [L.Structure B] : SS A B → Prop
  | Sum.inl X => MinAbsorbing L X
  | Sum.inr Y => MinAbsorbing L Y

theorem nbS_abs (R : Set (A × B)) (hR : IsSubuniverse L R) (hsd : Subdirect R) (S : SS A B)
    (h : AbsS L S) : AbsS L (nbS R S) := by
  rcases S with X | Y
  · exact nbhd_absorbing R hR hsd X h
  · exact nbhd_absorbing _ (swap_sub hR) (swap_subdirect hsd) Y h

theorem inMin_iff (x : A ⊕ B) : InMinAbs L x ↔ ∃ S : SS A B, MinS L S ∧ memS x S := by
  rcases x with a | b
  · constructor
    · rintro ⟨C, hC, ha⟩; exact ⟨Sum.inl C, hC, ha⟩
    · rintro ⟨S, hS, hm⟩
      rcases S with X | Y
      · exact ⟨X, hS, hm⟩
      · exact absurd hm (by simp [memS])
  · constructor
    · rintro ⟨D, hD, hb⟩; exact ⟨Sum.inr D, hD, hb⟩
    · rintro ⟨S, hS, hm⟩
      rcases S with X | Y
      · exact absurd hm (by simp [memS])
      · exact ⟨Y, hS, hm⟩

theorem linked_swap {R : Set (A × B)} (hsd : Subdirect R) (hlin : Linked R) :
    Linked {p : B × A | (p.2, p.1) ∈ R} := by
  intro b b' _ _
  have hn : ∀ b : B, ∃ a, (a, b) ∈ R := by
    intro b
    have : b ∈ Prod.snd '' R := by rw [hsd.2]; trivial
    obtain ⟨⟨a, b₀⟩, hab, rfl⟩ := this
    exact ⟨a, hab⟩
  obtain ⟨a, hab⟩ := hn b
  obtain ⟨a', hab'⟩ := hn b'
  have ha : a ∈ Prod.fst '' R := ⟨(a, b), hab, rfl⟩
  have ha' : a' ∈ Prod.fst '' R := ⟨(a', b'), hab', rfl⟩
  have hrt := hlin a a' ha ha'
  -- chain of B-elements
  have key : ∀ y : A, Relation.ReflTransGen (LinkStep R) a y →
      ∃ c : B, (y, c) ∈ R ∧ Relation.ReflTransGen (LinkStep {p : B × A | (p.2, p.1) ∈ R}) b c := by
    intro y hy
    induction hy with
    | refl => exact ⟨b, hab, Relation.ReflTransGen.refl⟩
    | tail _ hlk ih =>
      obtain ⟨c, hc, hrtc⟩ := ih
      obtain ⟨d, hd1, hd2⟩ := hlk
      exact ⟨d, hd2, hrtc.tail ⟨_, hc, hd1⟩⟩
  obtain ⟨c, hc, hrtc⟩ := key a' hrt
  exact hrtc.tail ⟨a', hc, hab'⟩

end sets2
end BKAux

namespace BKAux
open BKAbsorption
section sets3
variable {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]

theorem LinkAdj_symm (R : Set (A × B)) {x y : A ⊕ B} (h : LinkAdj R x y) : LinkAdj R y x := by
  rcases x with a | b <;> rcases y with a' | b' <;> simpa [LinkAdj] using h

theorem rtg_symm (R : Set (A × B)) {x y : A ⊕ B} (h : Relation.ReflTransGen (LinkAdj R) x y) :
    Relation.ReflTransGen (LinkAdj R) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hyz ih => exact (Relation.ReflTransGen.single (LinkAdj_symm R hyz)).trans ih

theorem reach (R : Set (A × B)) (hsd : Subdirect R) (hlin : Linked R) (x y : A ⊕ B) :
    Relation.ReflTransGen (LinkAdj R) x y := by
  have hAA : ∀ a a' : A, Relation.ReflTransGen (LinkAdj R) (Sum.inl a) (Sum.inl a') := by
    intro a a'
    have ha : a ∈ Prod.fst '' R := by rw [hsd.1]; trivial
    have ha' : a' ∈ Prod.fst '' R := by rw [hsd.1]; trivial
    have hrt := hlin a a' ha ha'
    clear ha'
    induction hrt with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hlk ih =>
      obtain ⟨d, hd1, hd2⟩ := hlk
      exact (ih.tail (c := Sum.inr d) (by simpa [LinkAdj] using hd1)).tail (by simpa [LinkAdj] using hd2)
  have hnb : ∀ b : B, ∃ a : A, (a, b) ∈ R := by
    intro b
    have : b ∈ Prod.snd '' R := by rw [hsd.2]; trivial
    obtain ⟨⟨a, b₀⟩, hab, rfl⟩ := this
    exact ⟨a, hab⟩
  have hAB : ∀ (a : A) (b : B), Relation.ReflTransGen (LinkAdj R) (Sum.inl a) (Sum.inr b) := by
    intro a b
    obtain ⟨a', hab⟩ := hnb b
    exact (hAA a a').tail (by simpa [LinkAdj] using hab)
  rcases x with a | b <;> rcases y with a' | b'
  · exact hAA a a'
  · exact hAB a b'
  · exact rtg_symm R (hAB a' b)
  · obtain ⟨a, -⟩ := hnb b
    exact (rtg_symm R (hAB a b)).trans (hAB a b')
end sets3
end BKAux

open BKAbsorption BKAux in
theorem step_exists {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]
    [Finite A] [Finite B] (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    (R : Set (A × B)) (hR : IsSubuniverse L R) (hsd : Subdirect R) (hlin : Linked R)
    (N D : SS A B) (hN : AbsS L N) (hD : MinS L D) (y : A ⊕ B) (hy : memS y D)
    (hx : ∃ x, memS x N ∧ LinkAdj R x y) :
    ∃ E : SS A B, MinS L E ∧ (∀ e, memS e E → memS e N) ∧ (∀ e, memS e E → LinkAdj R e y) := by
  obtain ⟨x, hxN, hxy⟩ := hx
  rcases N with X | Y <;> rcases D with Dset | Dset' <;> rcases y with a | b <;> rcases x with a' | b' <;>
    simp only [memS, LinkAdj] at hy hxN hxy
  · -- N = inl X, D = inr Dset'  (y = inr b, x = inl a')
    have hdown : IsAbsorbing L {a : A | ∃ b ∈ Dset', (a, b) ∈ R} := nbS_abs R hR hsd (Sum.inr Dset') hD.2.1
    have hint := absorbing_inter X _ hN hdown
    have hne : (X ∩ {a : A | ∃ b ∈ Dset', (a, b) ∈ R}).Nonempty := ⟨a', hxN, b, hy, hxy⟩
    obtain ⟨Es, hEs, hEmin⟩ := exists_min_absorbing _ hint hne
    obtain ⟨e0, he0⟩ := hEmin.1
    obtain ⟨-, d0, hd0, hed0⟩ := hEs he0
    have hiii := (prop215_iii T hA hB R hR hsd hlin hEmin hD ⟨e0, he0, d0, hd0, hed0⟩).1
    refine ⟨Sum.inl Es, hEmin, fun e he => ?_, fun e he => ?_⟩
    · rcases e with e | e
      · exact (hEs he).1
      · exact absurd he (by simp [memS])
    · rcases e with e | e
      · exact hiii ⟨he, hy⟩
      · exact absurd he (by simp [memS])
  · -- N = inr Y, D = inl Dset  (y = inl a, x = inr b')
    have hup : IsAbsorbing L {b : B | ∃ a ∈ Dset, (a, b) ∈ R} := nbS_abs R hR hsd (Sum.inl Dset) hD.2.1
    have hint := absorbing_inter Y _ hN hup
    have hne : (Y ∩ {b : B | ∃ a ∈ Dset, (a, b) ∈ R}).Nonempty := ⟨b', hxN, a, hy, hxy⟩
    obtain ⟨Es, hEs, hEmin⟩ := exists_min_absorbing _ hint hne
    obtain ⟨e0, he0⟩ := hEmin.1
    obtain ⟨d0, hd0, hd0e⟩ := (hEs he0).2
    have hiii := (prop215_iii T hA hB R hR hsd hlin hD hEmin ⟨d0, hd0, e0, he0, hd0e⟩).1
    refine ⟨Sum.inr Es, hEmin, fun e he => ?_, fun e he => ?_⟩
    · rcases e with e | e
      · exact absurd he (by simp [memS])
      · exact (hEs he).1
    · rcases e with e | e
      · exact absurd he (by simp [memS])
      · exact hiii ⟨hy, he⟩

namespace BKAux
open BKAbsorption
section sets4
variable {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]

def MinStep (L : FirstOrder.Language.{u, v}) [L.Structure A] [L.Structure B] (R : Set (A × B)) (x y : A ⊕ B) : Prop :=
  LinkAdj R x y ∧ InMinAbs L x ∧ InMinAbs L y

theorem minS_exists (E : SS A B) (hE : MinS L E) : ∃ e, memS e E := by
  rcases E with X | Y
  · obtain ⟨a, ha⟩ := hE.1; exact ⟨Sum.inl a, ha⟩
  · obtain ⟨b, hb⟩ := hE.1; exact ⟨Sum.inr b, hb⟩

theorem inMin_of_minS {E : SS A B} (hE : MinS L E) {e : A ⊕ B} (he : memS e E) : InMinAbs L e :=
  (inMin_iff e).2 ⟨E, hE, he⟩

theorem iter_abs (R : Set (A × B)) (hR : IsSubuniverse L R) (hsd : Subdirect R) (S : SS A B) (h : AbsS L S)
    (n : ℕ) : AbsS L ((nbS R)^[n] S) := by
  induction n with
  | zero => exact h
  | succ n ih => rw [Function.iterate_succ_apply']; exact nbS_abs R hR hsd _ ih

theorem minS_abs {S : SS A B} (h : MinS L S) : AbsS L S := by
  rcases S with X | Y
  · exact h.2.1
  · exact h.2.1

theorem reach_iter (R : Set (A × B)) {x y : A ⊕ B} (S : SS A B) (hx : memS x S)
    (h : Relation.ReflTransGen (LinkAdj R) x y) : ∃ n, memS y ((nbS R)^[n] S) := by
  induction h with
  | refl => exact ⟨0, hx⟩
  | tail _ hyz ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    rw [Function.iterate_succ_apply', memS_nbS]
    exact ⟨_, hn, hyz⟩

end sets4
end BKAux

open BKAbsorption BKAux in
theorem chain_base {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]
    [Finite A] [Finite B] (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    (R : Set (A × B)) (hR : IsSubuniverse L R) (hsd : Subdirect R) (hlin : Linked R)
    (S : SS A B) (hS : MinS L S) (x y : A ⊕ B) (hx : memS x S) (hy : memS y S) :
    Relation.ReflTransGen (MinStep L R) x y := by
  rcases S with C | Dset
  · rcases x with c | b
    swap; · exact absurd hx (by simp [memS])
    rcases y with c' | b'
    swap; · exact absurd hy (by simp [memS])
    simp only [memS] at hx hy
    obtain ⟨D, hD, hCD⟩ := prop215_iv T hA hB R hR hsd hlin hS
    obtain ⟨d, hd⟩ := hD.1
    have h1 : MinStep L R (Sum.inl c) (Sum.inr d) :=
      ⟨hCD ⟨hx, hd⟩, ⟨C, hS, hx⟩, ⟨D, hD, hd⟩⟩
    have h2 : MinStep L R (Sum.inr d) (Sum.inl c') :=
      ⟨hCD ⟨hy, hd⟩, ⟨D, hD, hd⟩, ⟨C, hS, hy⟩⟩
    exact (Relation.ReflTransGen.single h1).tail h2
  · rcases x with c | b
    · exact absurd hx (by simp [memS])
    rcases y with c' | b'
    · exact absurd hy (by simp [memS])
    simp only [memS] at hx hy
    obtain ⟨D, hD, hCD⟩ := prop215_iv T hB hA {p : B × A | (p.2, p.1) ∈ R} (swap_sub hR) (swap_subdirect hsd)
      (linked_swap hsd hlin) hS
    obtain ⟨d, hd⟩ := hD.1
    have h1 : MinStep L R (Sum.inr b) (Sum.inl d) :=
      ⟨(hCD (show (b, d) ∈ Dset ×ˢ D from ⟨hx, hd⟩) : (d, b) ∈ R), ⟨Dset, hS, hx⟩, ⟨D, hD, hd⟩⟩
    have h2 : MinStep L R (Sum.inl d) (Sum.inr b') :=
      ⟨(hCD (show (b', d) ∈ Dset ×ˢ D from ⟨hy, hd⟩) : (d, b') ∈ R), ⟨D, hD, hd⟩, ⟨Dset, hS, hy⟩⟩
    exact (Relation.ReflTransGen.single h1).tail h2

open BKAbsorption BKAux in
theorem chain_n {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]
    [Finite A] [Finite B] (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    (R : Set (A × B)) (hR : IsSubuniverse L R) (hsd : Subdirect R) (hlin : Linked R) :
    ∀ n : ℕ, ∀ S : SS A B, MinS L S → ∀ x, memS x S → ∀ y, memS y ((nbS R)^[n] S) → InMinAbs L y →
      Relation.ReflTransGen (MinStep L R) x y := by
  intro n
  induction n with
  | zero => intro S hS x hx y hy _; exact chain_base T hA hB R hR hsd hlin S hS x y hx hy
  | succ n ih =>
    intro S hS x hx y hy hyM
    rw [Function.iterate_succ_apply', memS_nbS] at hy
    obtain ⟨x', hx'N, hx'y⟩ := hy
    obtain ⟨D, hD, hyD⟩ := (inMin_iff y).1 hyM
    have hN : AbsS L ((nbS R)^[n] S) := iter_abs R hR hsd S (minS_abs hS) n
    obtain ⟨E, hE, hEN, hEy⟩ := step_exists T hA hB R hR hsd hlin _ D hN hD y hyD ⟨x', hx'N, hx'y⟩
    obtain ⟨e, he⟩ := minS_exists E hE
    have hxe := ih S hS x hx e (hEN e he) (inMin_of_minS hE he)
    exact hxe.tail ⟨hEy e he, inMin_of_minS hE he, hyM⟩

open BKAbsorption BKAux in
theorem prop215_v {L : FirstOrder.Language.{u, v}} {A : Type w} {B : Type w'} [L.Structure A] [L.Structure B]
    [Finite A] [Finite B] (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hB : IsTaylorAlg T B)
    (R : Set (A × B)) (hR : IsSubuniverse L R) (hsd : Subdirect R) (hlin : Linked R)
    (x y : A ⊕ B) (hx : InMinAbs L x) (hy : InMinAbs L y) :
    Relation.ReflTransGen (MinStep L R) x y := by
  obtain ⟨S, hS, hxS⟩ := (inMin_iff x).1 hx
  obtain ⟨n, hn⟩ := reach_iter R S hxS (reach R hsd hlin x y)
  exact chain_n T hA hB R hR hsd hlin n S hS x hxS y hn hy

namespace BKAbsorption
theorem Walk.append {X : Type*} {E : Set (X × X)} {a b c : X} {z z' : ℤ} (h : Walk E a b z)
    (h' : Walk E b c z') : Walk E a c (z + z') := by
  induction h' with
  | refl => simpa using h
  | fwd _ he ih => have := Walk.fwd ih he; convert this using 1; ring
  | bwd _ he ih => have := Walk.bwd ih he; convert this using 1; ring

theorem Walk.symm {X : Type*} {E : Set (X × X)} {a b : X} {z : ℤ} (h : Walk E a b z) :
    Walk E b a (-z) := by
  induction h with
  | refl => simpa using Walk.refl _
  | fwd _ he ih =>
    have := (Walk.bwd (Walk.refl _) he).append ih
    convert this using 1; ring
  | bwd _ he ih =>
    have := (Walk.fwd (Walk.refl _) he).append ih
    convert this using 1; ring

end BKAbsorption

open BKAbsorption BKAux

namespace BKGlue
section alg
variable {L : FirstOrder.Language.{u, v}} {X : Type w} {Y : Type w'} [L.Structure X] [L.Structure Y]

/-- a bijective homomorphism (isomorphism) -/
structure AlgIso (L : FirstOrder.Language.{u, v}) (X : Type w) (Y : Type w') [L.Structure X] [L.Structure Y] where
  toEquiv : X ≃ Y
  map_fun : ∀ (n : ℕ) (f : L.Functions n) (x : Fin n → X),
    toEquiv (funMap f x) = funMap f (fun i => toEquiv (x i))

theorem AlgIso.map_realize (e : AlgIso L X Y) {α : Type*} (t : L.Term α) (a : α → X) :
    e.toEquiv (t.realize a) = t.realize (fun i => e.toEquiv (a i)) := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    simp only [Term.realize]
    rw [e.map_fun]
    simp only [ih]

def AlgIso.symm (e : AlgIso L X Y) : AlgIso L Y X where
  toEquiv := e.toEquiv.symm
  map_fun := by
    intro n f y
    apply e.toEquiv.injective
    rw [Equiv.apply_symm_apply, e.map_fun]
    congr 1; ext i; simp

theorem AlgIso.image_sub (e : AlgIso L X Y) {S : Set X} (hS : IsSubuniverse L S) :
    IsSubuniverse L (e.toEquiv '' S) := by
  intro n f y hy
  choose x hxS hxy using hy
  refine ⟨funMap f x, hS n f x hxS, ?_⟩
  rw [e.map_fun]
  congr 1; ext i; exact hxy i

theorem AlgIso.image_abs (e : AlgIso L X Y) {S : Set X} (hS : IsAbsorbing L S) :
    IsAbsorbing L (e.toEquiv '' S) := by
  obtain ⟨hs, n, t, hn, ht⟩ := hS
  refine ⟨e.image_sub hs, n, t, hn, fun k a ha => ?_⟩
  choose x hxS hxa using fun i : {i // i ≠ k} => ha i.1 i.2
  let a' : Fin n → X := fun i => e.toEquiv.symm (a i)
  have hmem : ∀ i, i ≠ k → a' i ∈ S := by
    intro i hi
    obtain ⟨x, hx, hxa⟩ := ha i hi
    simp only [a']
    rw [← hxa]; simpa using hx
  have := ht k a' hmem
  refine ⟨_, this, ?_⟩
  rw [e.map_realize]
  congr 1; ext i; simp [a']

theorem AlgIso.image_min (e : AlgIso L X Y) {S : Set X} (hS : MinAbsorbing L S) :
    MinAbsorbing L (e.toEquiv '' S) := by
  refine ⟨hS.1.image _, e.image_abs hS.2.1, fun F hFne hFS hFabs => ?_⟩
  have hF' : IsAbsorbing L (e.toEquiv.symm '' F) := e.symm.image_abs hFabs
  have hsub : e.toEquiv.symm '' F ⊆ S := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hFS hy
    have : e.toEquiv.symm y = x := by rw [← hxy]; simp
    rw [this]; exact hx
  have heq := hS.2.2 _ (hFne.image _) hsub hF'
  ext y
  constructor
  · intro hy
    exact hFS hy
  · rintro ⟨x, hx, rfl⟩
    have : x ∈ e.toEquiv.symm '' F := by rw [heq]; exact hx
    obtain ⟨y, hy, hyx⟩ := this
    have : e.toEquiv x = y := by rw [← hyx]; simp
    rw [this]; exact hy


end alg

variable {L : FirstOrder.Language.{u, v}} {A : Type w} [L.Structure A]

instance piStr {ι : Type*} : L.Structure (ι → A) where
  funMap f x := fun j => funMap f (fun i => x i j)
  RelMap r x := ∀ j, RelMap r (fun i => x i j)

theorem piStr_funMap {ι : Type*} {n : ℕ} (f : L.Functions n) (x : Fin n → ι → A) (j : ι) :
    (funMap f x : ι → A) j = funMap f (fun i => x i j) := rfl

theorem realize_pi {ι : Type*} {α : Type*} (t : L.Term α) (x : α → ι → A) (j : ι) :
    (t.realize x : ι → A) j = t.realize (fun i => x i j) := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    simp only [Term.realize]
    rw [piStr_funMap]
    simp only [ih]

section windows
variable {p : ℕ} (R : Set (Fin p → A))

/-- the projection of `R` on the first `n` coordinates -/
def Rn (n : ℕ) (hn : n ≤ p) : Set (Fin n → A) :=
  {w | ∃ r ∈ R, ∀ i : Fin n, r (Fin.castLE hn i) = w i}

theorem Rn_sub (hR : IsSubuniverse L R) (n : ℕ) (hn : n ≤ p) : IsSubuniverse L (Rn R n hn) := by
  intro m f x hx
  choose r hrR hrx using hx
  refine ⟨funMap f r, hR m f r hrR, fun i => ?_⟩
  rw [piStr_funMap]
  show funMap f (fun k => r k (Fin.castLE hn i)) = funMap f (fun k => x k i)
  congr 1; ext k; exact hrx k i

end windows

section rot
theorem rot_castLE {q n : ℕ} (hn : n + 1 ≤ q + 1) (i : Fin n) :
    finRotate (q + 1) (Fin.castLE (Nat.le_of_succ_le hn) i) = Fin.castLE hn i.succ := by
  apply Fin.ext
  have h1 : (Fin.castLE (Nat.le_of_succ_le hn) i : Fin (q + 1)) ≠ Fin.last q := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  rw [coe_finRotate_of_ne_last h1]
  simp

variable {q : ℕ} {R : Set (Fin (q + 1) → A)}

theorem Rn_tail (hcyc : IsCyclicRel R) {n : ℕ} (hn : n + 1 ≤ q + 1) {w : Fin (n + 1) → A}
    (hw : w ∈ Rn R (n + 1) hn) : Fin.tail w ∈ Rn R n (Nat.le_of_succ_le hn) := by
  obtain ⟨r, hr, hrw⟩ := hw
  refine ⟨r ∘ finRotate (q + 1), hcyc r hr, fun i => ?_⟩
  simp only [Function.comp_apply, rot_castLE hn]
  exact hrw i.succ

theorem Rn_init {n : ℕ} (hn : n + 1 ≤ q + 1) {w : Fin (n + 1) → A}
    (hw : w ∈ Rn R (n + 1) hn) : Fin.init w ∈ Rn R n (Nat.le_of_succ_le hn) := by
  obtain ⟨r, hr, hrw⟩ := hw
  refine ⟨r, hr, fun i => ?_⟩
  have := hrw (Fin.castSucc i)
  simp only [Fin.init]
  rw [← this]
  congr 1

theorem cyc_shift (hcyc : IsCyclicRel R) {x : Fin (q + 1) → A} (hx : x ∈ R) (j : ℕ) :
    (fun i => x (i + (j : Fin (q + 1)))) ∈ R := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    have := hcyc _ ih
    convert this using 1
    ext i
    simp only [Function.comp_apply, finRotate_apply]
    congr 1
    rw [Nat.cast_succ, add_assoc, add_comm (1 : Fin (q + 1)) _]

theorem Rn_ext_right {n : ℕ} (hn : n + 1 ≤ q + 1) {w : Fin n → A}
    (hw : w ∈ Rn R n (Nat.le_of_succ_le hn)) : ∃ a : A, Fin.snoc (α := fun _ => A) w a ∈ Rn R (n + 1) hn := by
  obtain ⟨r, hr, hrw⟩ := hw
  refine ⟨r (Fin.castLE hn (Fin.last n)), r, hr, fun i => ?_⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp [hrw j]

end rot

theorem rtg_of_Spow {A : Type w} (Tr : Set (A × A)) (m : ℕ) (a a' : A) :
    (a, a') ∈ Spow Tr m → Relation.ReflTransGen (fun x y => (x, y) ∈ Tr) a a' := by
  induction m generalizing a' with
  | zero => intro h; have : a = a' := h; subst this; exact Relation.ReflTransGen.refl
  | succ m ih =>
    rintro ⟨c, hc, hcT⟩
    exact (ih c hc).tail hcT

theorem fork_linked {L : FirstOrder.Language.{u, v}} {Y : Type w'} {A : Type w} [L.Structure Y] [L.Structure A]
    [Finite A]
    (hsimple : ∀ r : A → A → Prop, Equivalence r →
      (∀ (n : ℕ) (f : L.Functions n) (x y : Fin n → A), (∀ i, r (x i) (y i)) →
        r (Structure.funMap f x) (Structure.funMap f y)) →
      (∀ a b, r a b → a = b) ∨ ∀ a b, r a b)
    (S : Set (Y × A)) (hS : IsSubuniverse L S) (hsd : Subdirect S)
    (hfork : ∃ (y : Y) (b b' : A), b ≠ b' ∧ (y, b) ∈ S ∧ (y, b') ∈ S) : Linked S := by
  classical
  set Tr : Set (A × A) := {p | ∃ y : Y, (y, p.1) ∈ S ∧ (y, p.2) ∈ S} with hTr
  have hTrsub : IsSubuniverse L Tr := by
    intro n f z hz
    choose y hy1 hy2 using hz
    refine ⟨funMap f y, ?_, ?_⟩
    · exact hS n f (fun i => (y i, (z i).1)) hy1
    · exact hS n f (fun i => (y i, (z i).2)) hy2
  have hTrrefl : ∀ a, (a, a) ∈ Tr := by
    intro a
    have : a ∈ Prod.snd '' S := by rw [hsd.2]; trivial
    obtain ⟨⟨y, a'⟩, hy, rfl⟩ := this
    exact ⟨y, hy, hy⟩
  have hTrsymm : ∀ a b, (a, b) ∈ Tr → (b, a) ∈ Tr := fun a b ⟨y, h1, h2⟩ => ⟨y, h2, h1⟩
  -- stabilisation of the powers
  haveI : Finite (Set (A × A)) := inferInstance
  have hstab : ∃ K, ∀ m, K ≤ m → Spow Tr K = Spow Tr m := by
    obtain ⟨K, hK⟩ := WellFoundedGT.monotone_chain_condition
      (⟨fun m => Spow Tr m, fun a b h => Spow_mono hTrrefl h⟩ : ℕ →o Set (A × A))
    exact ⟨K, hK⟩
  obtain ⟨K0, hK0⟩ := hstab
  set K := K0 + 1 with hK
  have hKK : Spow Tr K = Spow Tr (K + K) := by
    rw [← hK0 K (by omega), ← hK0 (K + K) (by omega)]
  have hKsub : IsSubuniverse L (Spow Tr K) := Spow_sub hTrsub K
  have hEq : Equivalence (fun a b => (a, b) ∈ Spow Tr K) :=
    ⟨fun a => Spow_refl hTrrefl K a, fun {a b} h => Spow_symm hTrsymm K a b h,
      fun {a b c} h1 h2 => by
        rw [hKK]
        exact (Spow_add Tr K K a c).2 ⟨b, h1, h2⟩⟩
  have hcomp : ∀ (n : ℕ) (f : L.Functions n) (x y : Fin n → A),
      (∀ i, (x i, y i) ∈ Spow Tr K) → (funMap f x, funMap f y) ∈ Spow Tr K := by
    intro n f x y h
    exact hKsub n f (fun i => (x i, y i)) h
  obtain ⟨y, b, b', hbb, h1, h2⟩ := hfork
  have hbb' : (b, b') ∈ Spow Tr K := by
    have : (b, b') ∈ Spow Tr 1 := ⟨b, rfl, y, h1, h2⟩
    exact Spow_mono hTrrefl (by omega) this
  rcases hsimple _ hEq hcomp with htriv | hfull
  · exact absurd (htriv b b' hbb') hbb
  · -- the transposed relation is linked
    have hlinkT : Linked {p : A × Y | (p.2, p.1) ∈ S} := by
      intro a a' _ _
      have := rtg_of_Spow Tr K a a' (hfull a a')
      exact this
    have hsdT : Subdirect {p : A × Y | (p.2, p.1) ∈ S} := swap_subdirect hsd
    have := linked_swap hsdT hlinkT
    exact this


section glue
variable {L : FirstOrder.Language.{u, v}} {A : Type w} [L.Structure A] {q : ℕ}

theorem const_of_proper
    (hsub : ∀ S : L.Substructure A, (S : Set A) ≠ Set.univ → HasCyclicTermOp L S (q + 1))
    (I : Set A) (hI : IsSubuniverse L I) (hIne : I ≠ Set.univ)
    (S : Set (Fin (q + 1) → A)) (hSI : ∀ s ∈ S, ∀ i, s i ∈ I) (hSne : S.Nonempty)
    (hSsub : IsSubuniverse L S) (hScyc : IsCyclicRel S) : ∃ a : A, (fun _ => a) ∈ S := by
  obtain ⟨s, hs⟩ := hSne
  have hIs : (subS I hI : Set A) ≠ Set.univ := hIne
  obtain ⟨t, ht1, ht2⟩ := hsub (subS I hI) hIs
  have hrows : ∀ k : Fin (q + 1), (fun i => s (i + k)) ∈ S := by
    intro k
    have := cyc_shift hScyc hs k.val
    simpa using this
  have hu := realize_mem hSsub t (fun k : Fin (q + 1) => fun i => s (i + k)) hrows
  have key : ∀ i : Fin (q + 1), (t.realize (fun k : Fin (q + 1) => fun i => s (i + k)) : Fin (q + 1) → A) i
      = t.realize (fun k : Fin (q + 1) => s (i + k)) := by
    intro i; rw [realize_pi]
  have hcyc : ∀ i : Fin (q + 1), t.realize (fun k : Fin (q + 1) => s (i + k)) = t.realize (fun k : Fin (q + 1) => s (i + 1 + k)) := by
    intro i
    let x : Fin (q + 1) → subS I hI := fun k => ⟨s (i + k), hSI s hs _⟩
    have h2 := ht2 x
    have e1 : ((t.realize x : subS I hI) : A) = t.realize (fun k : Fin (q + 1) => s (i + k)) := by
      rw [subS_realize]
    have e2 : ((t.realize (x ∘ finRotate (q + 1)) : subS I hI) : A) = t.realize (fun k : Fin (q + 1) => s (i + 1 + k)) := by
      rw [subS_realize]
      congr 1; ext k
      simp only [x, Function.comp_apply, finRotate_apply]
      congr 1; abel
    rw [← e1, ← e2, h2]
  set g : Fin (q + 1) → A := fun i => t.realize (fun k : Fin (q + 1) => s (i + k)) with hg
  have hgnat : ∀ j : ℕ, g (j : Fin (q + 1)) = g 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.cast_succ]
      exact (show g ((j : Fin (q + 1)) + 1) = g (j : Fin (q + 1)) from (hcyc _).symm).trans ih
  have hfin : (fun _ => g 0) = t.realize (fun k : Fin (q + 1) => fun i => s (i + k)) := by
    ext i
    rw [key i]
    have := hgnat i.val
    rw [Fin.cast_val_eq_self] at this
    exact this.symm
  exact ⟨g 0, by rw [hfin]; exact hu⟩

theorem coord_surj {R : Set (Fin (q + 1) → A)} (hcyc : IsCyclicRel R)
    (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a) (i : Fin (q + 1)) (a : A) : ∃ r ∈ R, r i = a := by
  obtain ⟨r, hr, hr0⟩ := h0 a
  refine ⟨fun j => r (j + ((q + 1 - i.val : ℕ) : Fin (q + 1))), cyc_shift hcyc hr (q + 1 - i.val), ?_⟩
  have h2 : i.val + (q + 1 - i.val) = q + 1 := by have := i.2; omega
  have : i + ((q + 1 - i.val : ℕ) : Fin (q + 1)) = 0 := by
    calc i + ((q + 1 - i.val : ℕ) : Fin (q + 1))
        = ((i.val : ℕ) : Fin (q + 1)) + ((q + 1 - i.val : ℕ) : Fin (q + 1)) := by
          rw [Fin.cast_val_eq_self]
      _ = ((i.val + (q + 1 - i.val) : ℕ) : Fin (q + 1)) := by rw [Nat.cast_add]
      _ = 0 := by rw [h2]; exact Fin.natCast_self (q + 1)
  simp only [this]
  exact hr0

theorem R1_univ
    (hsub : ∀ S : L.Substructure A, (S : Set A) ≠ Set.univ → HasCyclicTermOp L S (q + 1))
    (R : Set (Fin (q + 1) → A)) (hR : IsSubuniverse L R) (hcyc : IsCyclicRel R) (hne : R.Nonempty)
    (hnc : ∀ a : A, (fun _ => a) ∉ R) : ∀ a : A, ∃ r ∈ R, r 0 = a := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨a0, ha0⟩ := hcon
  set B : Set A := {a | ∃ r ∈ R, r 0 = a} with hB
  have hBsub : IsSubuniverse L B := by
    intro n f x hx
    choose r hrR hrx using hx
    refine ⟨funMap f r, hR n f r hrR, ?_⟩
    show funMap f (fun k => r k 0) = funMap f x
    congr 1; ext k; exact hrx k
  have hBne : B ≠ Set.univ := by
    intro h
    have : a0 ∈ B := by rw [h]; trivial
    obtain ⟨r, hr, hr0⟩ := this
    exact ha0 r hr hr0
  have hall : ∀ r ∈ R, ∀ i, r i ∈ B := by
    intro r hr i
    refine ⟨fun j => r (j + ((i.val : ℕ) : Fin (q + 1))), cyc_shift hcyc hr i.val, ?_⟩
    simp [Fin.cast_val_eq_self]
  obtain ⟨a, ha⟩ := const_of_proper hsub B hBsub hBne R hall hne hR hcyc
  exact hnc a ha


/-- (P1) at level `n` -/
def P1 (L : FirstOrder.Language.{u, v}) {A : Type w} [L.Structure A] {q : ℕ} (R : Set (Fin (q + 1) → A))
    (hR : IsSubuniverse L R) (n : ℕ) (hn : n ≤ q + 1) : Prop :=
  ∃ I : Set A, MinAbsorbing L I ∧ (∀ x : Fin n → A, (∀ i, x i ∈ I) → x ∈ Rn R n hn) ∧
    MinAbsorbing L {x : subS (Rn R n hn) (Rn_sub R hR n hn) | ∀ i, x.1 i ∈ I}

/-- (P2) at level `n` -/
def P2 (L : FirstOrder.Language.{u, v}) {A : Type w} [L.Structure A] {q : ℕ} (R : Set (Fin (q + 1) → A))
    (hR : IsSubuniverse L R) (n : ℕ) (hn : n ≤ q + 1) : Prop :=
  ∀ I : Fin n → Set A, (∀ i, MinAbsorbing L (I i)) →
    (∃ x : Fin n → A, x ∈ Rn R n hn ∧ ∀ i, x i ∈ I i) →
    (∀ x : Fin n → A, (∀ i, x i ∈ I i) → x ∈ Rn R n hn) ∧
    MinAbsorbing L {x : subS (Rn R n hn) (Rn_sub R hR n hn) | ∀ i, x.1 i ∈ I i}

theorem base_case [Finite A]
    (hsub : ∀ S : L.Substructure A, (S : Set A) ≠ Set.univ → HasCyclicTermOp L S (q + 1))
    (R : Set (Fin (q + 1) → A)) (hR : IsSubuniverse L R) (hcyc : IsCyclicRel R) (hne : R.Nonempty)
    (hnc : ∀ a : A, (fun _ => a) ∉ R) :
    P1 L R hR 1 (by omega) ∧ P2 L R hR 1 (by omega) := by
  have h0 := R1_univ hsub R hR hcyc hne hnc
  have hmem : ∀ x : Fin 1 → A, x ∈ Rn R 1 (by omega) := by
    intro x
    obtain ⟨r, hr, hr0⟩ := h0 (x 0)
    refine ⟨r, hr, fun i => ?_⟩
    have : i = 0 := Subsingleton.elim _ _
    subst this
    simpa using hr0
  let e : AlgIso L (subS (Rn R 1 (by omega)) (Rn_sub R hR 1 (by omega))) A :=
    { toEquiv :=
        { toFun := fun x => x.1 0
          invFun := fun a => ⟨fun _ => a, hmem _⟩
          left_inv := fun x => by
            apply Subtype.ext; ext i
            have : i = 0 := Subsingleton.elim _ _
            subst this; rfl
          right_inv := fun a => rfl }
      map_fun := fun n f x => rfl }
  have hesymm : ∀ I : Set A, {x : subS (Rn R 1 (by omega)) (Rn_sub R hR 1 (by omega)) | ∀ i, x.1 i ∈ I}
      = e.symm.toEquiv '' I := by
    intro I
    ext x
    constructor
    · intro hx
      exact ⟨x.1 0, hx 0, by
        apply Subtype.ext; ext i
        have : i = 0 := Subsingleton.elim _ _
        subst this; rfl⟩
    · rintro ⟨a, ha, rfl⟩ i
      have : i = 0 := Subsingleton.elim _ _
      subst this; exact ha
  refine ⟨?_, ?_⟩
  · have hIabs : IsAbsorbing L (Set.univ : Set A) :=
      ⟨fun _ _ _ _ => trivial, 1, Term.var 0, one_pos, fun _ _ _ => trivial⟩
    obtain ⟨a⟩ : Nonempty A := by
      obtain ⟨r, -⟩ := hne
      exact ⟨r 0⟩
    obtain ⟨I, -, hI⟩ := exists_min_absorbing Set.univ hIabs ⟨a, trivial⟩
    refine ⟨I, hI, fun x _ => hmem x, ?_⟩
    rw [hesymm]
    exact e.symm.image_min hI
  · intro I hI _
    refine ⟨fun x _ => hmem x, ?_⟩
    have h1 : {x : subS (Rn R 1 (by omega)) (Rn_sub R hR 1 (by omega)) | ∀ i, x.1 i ∈ I i}
        = e.symm.toEquiv '' (I 0) := by
      ext x
      constructor
      · intro hx
        exact ⟨x.1 0, hx 0, by
          apply Subtype.ext; ext i
          have : i = 0 := Subsingleton.elim _ _
          subst this; rfl⟩
      · rintro ⟨a, ha, rfl⟩ i
        have : i = 0 := Subsingleton.elim _ _
        subst this; exact ha
    rw [h1]
    exact e.symm.image_min (hI 0)


section step
variable [Finite A] (R : Set (Fin (q + 1) → A)) (hR : IsSubuniverse L R) {n : ℕ} (hn : n + 1 ≤ q + 1)

theorem snoc_funMap {m : ℕ} (f : L.Functions m) (xs : Fin m → Fin n → A) (as : Fin m → A) :
    (Fin.snoc (α := fun _ => A) (funMap f xs : Fin n → A) (funMap f as))
      = funMap f (fun i => Fin.snoc (α := fun _ => A) (xs i) (as i)) := by
  ext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [piStr_funMap]
  · simp [piStr_funMap]

/-- the relation `S ⊆ R_n × A` coming from `R_{n+1}` -/
def Srel : Set (subS (Rn R n (Nat.le_of_succ_le hn)) (Rn_sub R hR n (Nat.le_of_succ_le hn)) × A) :=
  {z | Fin.snoc (α := fun _ => A) z.1.1 z.2 ∈ Rn R (n + 1) hn}

theorem Srel_sub : IsSubuniverse L (Srel R hR hn) := by
  intro m f z hz
  show Fin.snoc (α := fun _ => A) (funMap f (fun i => (z i).1.1)) (funMap f (fun i => (z i).2)) ∈ Rn R (n + 1) hn
  rw [snoc_funMap]
  exact Rn_sub R hR (n + 1) hn m f _ hz

theorem Srel_subdirect (hcyc : IsCyclicRel R) (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a) : Subdirect (Srel R hR hn) := by
  constructor
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, ha⟩ := Rn_ext_right hn x.2
    exact ⟨(x, a), ha, rfl⟩
  · apply Set.eq_univ_of_forall
    intro a
    obtain ⟨r, hr, hra⟩ := coord_surj hcyc h0 ⟨n, by omega⟩ a
    set w : Fin (n + 1) → A := fun i => r (Fin.castLE hn i) with hw
    have hwR : w ∈ Rn R (n + 1) hn := ⟨r, hr, fun i => rfl⟩
    have hlast : w (Fin.last n) = a := by
      simp only [hw]
      have : Fin.castLE hn (Fin.last n) = (⟨n, by omega⟩ : Fin (q + 1)) := Fin.ext (by simp)
      rw [this]; exact hra
    refine ⟨(⟨Fin.init w, Rn_init hn hwR⟩, a), ?_, rfl⟩
    show Fin.snoc (α := fun _ => A) (Fin.init w) a ∈ Rn R (n + 1) hn
    rw [← hlast, Fin.snoc_init_self]
    exact hwR


/-- `S ≅ R_{n+1}` -/
def SIso : AlgIso L (subS (Srel R hR hn) (Srel_sub R hR hn))
    (subS (Rn R (n + 1) hn) (Rn_sub R hR (n + 1) hn)) where
  toEquiv :=
    { toFun := fun z => ⟨Fin.snoc (α := fun _ => A) z.1.1.1 z.1.2, z.2⟩
      invFun := fun w => ⟨(⟨Fin.init w.1, Rn_init hn w.2⟩, w.1 (Fin.last n)), by
        show Fin.snoc (α := fun _ => A) (Fin.init w.1) (w.1 (Fin.last n)) ∈ Rn R (n + 1) hn
        rw [Fin.snoc_init_self]; exact w.2⟩
      left_inv := fun z => by
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          show Fin.init (Fin.snoc (α := fun _ => A) z.1.1.1 z.1.2) = z.1.1.1
          exact Fin.init_snoc _ _
        · show Fin.snoc (α := fun _ => A) z.1.1.1 z.1.2 (Fin.last n) = z.1.2
          exact Fin.snoc_last _ _
      right_inv := fun w => by
        apply Subtype.ext
        show Fin.snoc (α := fun _ => A) (Fin.init w.1) (w.1 (Fin.last n)) = w.1
        exact Fin.snoc_init_self _ }
  map_fun := fun m f z => by
    apply Subtype.ext
    show Fin.snoc (α := fun _ => A) (funMap f (fun i => (z i).1.1.1)) (funMap f (fun i => (z i).1.2))
      = funMap f (fun i => Fin.snoc (α := fun _ => A) (z i).1.1.1 (z i).1.2)
    exact snoc_funMap f _ _

end step

theorem absorbsIn_image {M : Type w} [L.Structure M] {S : Set M} (hS : IsSubuniverse L S)
    {F : Set (subS S hS)} (hF : IsAbsorbing L F) : AbsorbsIn L S (Subtype.val '' F) := by
  have hF'sub : IsSubuniverse L (Subtype.val '' F : Set M) := by
    intro n f x hx
    choose y hyF hyx using hx
    refine ⟨funMap f y, hF.1 n f y hyF, ?_⟩
    rw [subS_funMap']
    congr 1; ext i; exact hyx i
  obtain ⟨-, n, t, hn, ht⟩ := hF
  refine ⟨hF'sub, ?_, n, t, hn, fun k a haC hak => ?_⟩
  · rintro _ ⟨y, -, rfl⟩; exact y.2
  · let a' : Fin n → subS S hS := fun i => ⟨a i, haC i⟩
    have hmem : ∀ i, i ≠ k → a' i ∈ F := by
      intro i hik
      obtain ⟨y, hyF, hy⟩ := hak i hik
      have : a' i = y := Subtype.ext hy.symm
      rw [this]; exact hyF
    have := ht k a' hmem
    refine ⟨_, this, ?_⟩
    rw [subS_realize]

theorem minAbs_sub_of_rel {M : Type w} [L.Structure M] (S : Set M) (hS : IsSubuniverse L S)
    (E : Set M) (hES : E ⊆ S) (hne : E.Nonempty) (hE : AbsorbsIn L S E)
    (hmin : ∀ F : Set M, F.Nonempty → F ⊆ E → AbsorbsIn L S F → F = E) :
    MinAbsorbing L {z : subS S hS | z.1 ∈ E} := by
  obtain ⟨hEs, -, n, t, hn, ht⟩ := hE
  have habs : IsAbsorbing L {z : subS S hS | z.1 ∈ E} := by
    refine ⟨?_, n, t, hn, fun k a hak => ?_⟩
    · intro m f x hx
      show funMap f (fun i => (x i).1) ∈ E
      exact hEs m f _ hx
    · show (t.realize a).1 ∈ E
      rw [subS_realize]
      exact ht k (fun i => (a i).1) (fun i => (a i).2) (fun i hi => hak i hi)
  obtain ⟨z0, hz0⟩ := hne
  refine ⟨⟨⟨z0, hES hz0⟩, hz0⟩, habs, fun F hFne hFsub hFabs => ?_⟩
  have himg : AbsorbsIn L S (Subtype.val '' F) := absorbsIn_image hS hFabs
  have hsub : Subtype.val '' F ⊆ E := by
    rintro _ ⟨z, hz, rfl⟩; exact hFsub hz
  have heq := hmin _ (hFne.image _) hsub himg
  ext z
  constructor
  · intro hz; exact hFsub hz
  · intro hz
    have : z.1 ∈ Subtype.val '' F := by rw [heq]; exact hz
    obtain ⟨z', hz', hzz⟩ := this
    have : z' = z := Subtype.ext hzz
    rw [← this]; exact hz'


theorem taylor_pi {ι : Type*} (T : TaylorDatum L) (hA : IsTaylorAlg T A) : IsTaylorAlg T (ι → A) := by
  refine ⟨fun n f a => ?_, fun j x y => ?_⟩
  · ext i
    rw [piStr_funMap]
    exact hA.1 n f (a i)
  · ext i
    rw [realize_pi, realize_pi]
    have := hA.2 j (x i) (y i)
    convert this using 2 <;> (ext k; cases T.σ j k <;> cases T.τ j k <;> simp)

theorem taylor_Rn (T : TaylorDatum L) (hA : IsTaylorAlg T A) (R : Set (Fin (q + 1) → A))
    (hR : IsSubuniverse L R) (n : ℕ) (hn : n ≤ q + 1) :
    IsTaylorAlg T (subS (Rn R n hn) (Rn_sub R hR n hn)) :=
  subS_taylor _ _ T (taylor_pi T hA)


theorem P2_step [Finite A] (T : TaylorDatum L) (hA : IsTaylorAlg T A)
    (R : Set (Fin (q + 1) → A)) (hR : IsSubuniverse L R) (hcyc : IsCyclicRel R)
    (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a) {n : ℕ} (hn : n + 1 ≤ q + 1)
    (H2 : P2 L R hR n (Nat.le_of_succ_le hn))
    (hlin : Linked (Srel R hR hn)) : P2 L R hR (n + 1) hn := by
  intro I hI ⟨x, hxR, hxI⟩
  have hn' : n ≤ q + 1 := Nat.le_of_succ_le hn
  let C : Set (subS (Rn R n hn') (Rn_sub R hR n hn')) := {z | ∀ i : Fin n, z.1 i ∈ I (Fin.castSucc i)}
  have hxinit : Fin.init x ∈ Rn R n hn' := Rn_init hn hxR
  obtain ⟨hCsub, hCmin⟩ := H2 (fun i => I (Fin.castSucc i)) (fun i => hI _) ⟨Fin.init x, hxinit, fun i => hxI _⟩
  have hTX : IsTaylorAlg T (subS (Rn R n hn') (Rn_sub R hR n hn')) := taylor_Rn T hA R hR n hn'
  have hne : ∃ c ∈ C, ∃ d ∈ I (Fin.last n), (c, d) ∈ Srel R hR hn := by
    refine ⟨⟨Fin.init x, hxinit⟩, fun i => hxI _, x (Fin.last n), hxI _, ?_⟩
    show Fin.snoc (α := fun _ => A) (Fin.init x) (x (Fin.last n)) ∈ Rn R (n + 1) hn
    rw [Fin.snoc_init_self]; exact hxR
  obtain ⟨hCD, hEabs, hEmin⟩ := prop215_iii T hTX hA (Srel R hR hn) (Srel_sub R hR hn)
    (Srel_subdirect R hR hn hcyc h0) hlin hCmin (hI (Fin.last n)) hne
  refine ⟨fun y hy => ?_, ?_⟩
  · have hyinit : Fin.init y ∈ Rn R n hn' := hCsub _ (fun i => hy _)
    have := hCD (show (⟨Fin.init y, hyinit⟩, y (Fin.last n)) ∈ C ×ˢ I (Fin.last n) from ⟨fun i => hy _, hy _⟩)
    have h2 : Fin.snoc (α := fun _ => A) (Fin.init y) (y (Fin.last n)) ∈ Rn R (n + 1) hn := this
    rwa [Fin.snoc_init_self] at h2
  · have hmin := minAbs_sub_of_rel (Srel R hR hn) (Srel_sub R hR hn) (C ×ˢ I (Fin.last n)) hCD
      (by obtain ⟨c, hc, d, hd, -⟩ := hne; exact ⟨(c, d), hc, hd⟩) hEabs hEmin
    have himg := (SIso R hR hn).image_min hmin
    convert himg using 1
    ext w
    constructor
    · intro hw
      refine ⟨(SIso R hR hn).symm.toEquiv w, ?_, ?_⟩
      · show (_, _) ∈ C ×ˢ I (Fin.last n)
        exact ⟨fun i => hw _, hw _⟩
      · exact (SIso R hR hn).toEquiv.apply_symm_apply w
    · rintro ⟨z, hz, rfl⟩ i
      obtain ⟨hz1, hz2⟩ := hz
      refine Fin.lastCases ?_ (fun k => ?_) i
      · show Fin.snoc (α := fun _ => A) z.1.1.1 z.1.2 (Fin.last n) ∈ I (Fin.last n)
        rw [Fin.snoc_last]; exact hz2
      · show Fin.snoc (α := fun _ => A) z.1.1.1 z.1.2 (Fin.castSucc k) ∈ I (Fin.castSucc k)
        rw [Fin.snoc_castSucc]; exact hz1 k


section counting
variable [Finite A]

/-- the cyclic shift as an endomorphism of `↥R` -/
def shiftEnd (R : Set (Fin (q + 1) → A)) (hcyc : IsCyclicRel R) : Function.End R :=
  fun x => ⟨fun i => x.1 (i + 1), by
    have := hcyc x.1 x.2
    convert this using 1
    ext i; simp [finRotate_apply]⟩

theorem shiftEnd_pow (R : Set (Fin (q + 1) → A)) (hcyc : IsCyclicRel R) (k : ℕ) (x : R) (i : Fin (q + 1)) :
    ((shiftEnd R hcyc ^ k) x).1 i = x.1 (i + (k : Fin (q + 1))) := by
  induction k generalizing x with
  | zero => simp; rfl
  | succ k ih =>
    rw [pow_succ]
    show ((shiftEnd R hcyc ^ k) (shiftEnd R hcyc x)).1 i = _
    rw [ih]
    show x.1 (i + (k : Fin (q + 1)) + 1) = x.1 (i + ((k + 1 : ℕ) : Fin (q + 1)))
    rw [Nat.cast_succ, add_assoc]

theorem counting_contra (R : Set (Fin (q + 1) → A)) (hcyc : IsCyclicRel R) (hRne : R.Nonempty)
    (hnc : ∀ a : A, (fun _ => a) ∉ R) (hprime : (q + 1).Prime) (hpA : Nat.card A < q + 1)
    {n : ℕ} (hn : n ≤ q + 1)
    (hdet : ∀ r ∈ R, ∀ r' ∈ R, (∀ i : Fin (q + 1), i.val < n → r i = r' i) → r = r')
    (hsurj : ∀ w : Fin n → A, ∃ r ∈ R, ∀ i : Fin n, r (Fin.castLE hn i) = w i) : False := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype R := Fintype.ofFinite R
  haveI : Fact (q + 1).Prime := ⟨hprime⟩
  have hf : shiftEnd R hcyc ^ (q + 1) ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    funext i
    rw [pow_one, shiftEnd_pow, Fin.natCast_self]
    simp
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := shiftEnd R hcyc) (p := q + 1) (n := 1) hf
  haveI hfix : IsEmpty (shiftEnd R hcyc).fixedPoints := by
    refine ⟨fun ⟨x, hx⟩ => ?_⟩
    have hx' : shiftEnd R hcyc x = x := hx
    have hconst : ∀ i : Fin (q + 1), x.1 (i + 1) = x.1 i := fun i => by
      have := congrArg (fun y : R => y.1 i) hx'
      exact this
    have hnat : ∀ j : ℕ, x.1 (j : Fin (q + 1)) = x.1 0 := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [Nat.cast_succ, hconst, ih]
    apply hnc (x.1 0)
    have : (fun _ => x.1 0) = x.1 := by
      funext i
      have := hnat i.val
      rw [Fin.cast_val_eq_self] at this
      exact this.symm
    rw [this]; exact x.2
  have h0 : ∀ inst : Fintype (shiftEnd R hcyc).fixedPoints, Fintype.card (shiftEnd R hcyc).fixedPoints = 0 :=
    fun inst => Fintype.card_eq_zero
  rw [h0 _] at hmod
  have hdvd : (q + 1) ∣ Fintype.card R := (Nat.modEq_zero_iff_dvd).1 hmod
  -- cardinality of R equals |A|^n
  let φ : R → (Fin n → A) := fun x i => x.1 (Fin.castLE hn i)
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    apply hdet x.1 x.2 y.1 y.2
    intro i hi
    have := congrFun hxy ⟨i.val, hi⟩
    simpa [φ] using this
  have hφsurj : Function.Surjective φ := by
    intro w
    obtain ⟨r, hr, hrw⟩ := hsurj w
    exact ⟨⟨r, hr⟩, funext hrw⟩
  have hcard : Fintype.card R = Fintype.card A ^ n := by
    rw [Fintype.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)]
    simp
  rw [hcard] at hdvd
  have hAc : Fintype.card A = Nat.card A := Nat.card_eq_fintype_card.symm
  have hApos : 0 < Fintype.card A := by
    obtain ⟨r, hr⟩ := hRne
    exact Fintype.card_pos_iff.2 ⟨r 0⟩
  have hdA : (q + 1) ∣ Fintype.card A := hprime.dvd_of_dvd_pow hdvd
  have := Nat.le_of_dvd hApos hdA
  omega

end counting

section fork
variable [Finite A] (R : Set (Fin (q + 1) → A))

theorem fin_add_nat_val {a : Fin (q + 1)} {s : ℕ} (h : a.val + s < q + 1) :
    (a + (s : Fin (q + 1))).val = a.val + s := by
  rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : s < q + 1)]
  exact Nat.mod_eq_of_lt h

theorem fork_of_diff (hR : IsSubuniverse L R) {n : ℕ} (hcyc : IsCyclicRel R) (hn : n + 1 ≤ q + 1) (r r' : Fin (q + 1) → A) (hr : r ∈ R) (hr' : r' ∈ R)
    (j : Fin (q + 1)) (hj : n ≤ j.val) (hagree : ∀ l : Fin (q + 1), l.val < j.val → r l = r' l)
    (hdiff : r j ≠ r' j) :
    ∃ (y : subS (Rn R n (Nat.le_of_succ_le hn)) (Rn_sub R hR n (Nat.le_of_succ_le hn))) (b b' : A),
      b ≠ b' ∧ (y, b) ∈ Srel R hR hn ∧ (y, b') ∈ Srel R hR hn := by
  set s := j.val - n with hs
  have hρ := cyc_shift hcyc hr s
  have hρ' := cyc_shift hcyc hr' s
  have hn' : n ≤ q + 1 := Nat.le_of_succ_le hn
  -- the value of the shifted tuples
  have hidx : ∀ i : Fin (n + 1), (Fin.castLE hn i + (s : Fin (q + 1))).val = i.val + s := by
    intro i
    apply fin_add_nat_val
    have := i.2; have := j.2; simp; omega
  have hlt : ∀ i : Fin n, (Fin.castLE hn' i + (s : Fin (q + 1))).val < j.val := by
    intro i
    have h1 := hidx (Fin.castSucc i)
    simp only [Fin.val_castSucc] at h1
    have : Fin.castLE hn (Fin.castSucc i) = Fin.castLE hn' i := rfl
    rw [this] at h1
    rw [h1]; have := i.2; omega
  have hlast : Fin.castLE hn (Fin.last n) + (s : Fin (q + 1)) = j := by
    apply Fin.ext
    rw [hidx]; simp; omega
  let x : Fin n → A := fun i => r (Fin.castLE hn' i + (s : Fin (q + 1)))
  have hxx : x = fun i => r' (Fin.castLE hn' i + (s : Fin (q + 1))) := by
    funext i; exact hagree _ (hlt i)
  have hxR : x ∈ Rn R n hn' := ⟨_, hρ, fun i => rfl⟩
  refine ⟨⟨x, hxR⟩, r j, r' j, hdiff, ?_, ?_⟩
  · refine ⟨_, hρ, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp only [Fin.snoc_last]; rw [hlast]
    · simp only [Fin.snoc_castSucc, x]; rfl
  · refine ⟨_, hρ', fun i => ?_⟩
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp only [Fin.snoc_last]; rw [hlast]
    · simp only [Fin.snoc_castSucc]
      show r' (Fin.castLE hn (Fin.castSucc k) + (s : Fin (q + 1))) = x k
      rw [hxx]; rfl


theorem S_linked_univ (hR : IsSubuniverse L R)
    (hsimple : ∀ r : A → A → Prop, Equivalence r →
      (∀ (n : ℕ) (f : L.Functions n) (x y : Fin n → A), (∀ i, r (x i) (y i)) →
        r (Structure.funMap f x) (Structure.funMap f y)) →
      (∀ a b, r a b → a = b) ∨ ∀ a b, r a b)
    (hcyc : IsCyclicRel R) (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a) (hRne : R.Nonempty)
    (hnc : ∀ a : A, (fun _ => a) ∉ R) (hprime : (q + 1).Prime) (hpA : Nat.card A < q + 1)
    {n : ℕ} (hn : n + 1 ≤ q + 1)
    (hall : ∀ x : Fin n → A, x ∈ Rn R n (Nat.le_of_succ_le hn)) : Linked (Srel R hR hn) := by
  classical
  by_cases hf : ∃ r ∈ R, ∃ r' ∈ R, ∃ j : Fin (q + 1), n ≤ j.val ∧
      (∀ l : Fin (q + 1), l.val < j.val → r l = r' l) ∧ r j ≠ r' j
  · obtain ⟨r, hr, r', hr', j, hj, hag, hdiff⟩ := hf
    obtain ⟨y, b, b', hbb, h1, h2⟩ := fork_of_diff R hR hcyc hn r r' hr hr' j hj hag hdiff
    exact fork_linked hsimple (Srel R hR hn) (Srel_sub R hR hn) (Srel_subdirect R hR hn hcyc h0)
      ⟨y, b, b', hbb, h1, h2⟩
  · exfalso
    push_neg at hf
    refine counting_contra R hcyc hRne hnc hprime hpA (Nat.le_of_succ_le hn) ?_ ?_
    · intro r hr r' hr' hagree
      funext j
      -- strong induction on the index
      have key : ∀ m : ℕ, ∀ hm : m < q + 1, r ⟨m, hm⟩ = r' ⟨m, hm⟩ := by
        intro m
        induction m using Nat.strong_induction_on with
        | _ m ih =>
          intro hm
          by_cases hmn : m < n
          · exact hagree ⟨m, hm⟩ hmn
          · exact hf r hr r' hr' ⟨m, hm⟩ (by simpa using hmn) (fun l hl => ih l.val hl l.2)
      exact key j.val j.2
    · intro w
      exact hall w


theorem abs_coord_set (hR : IsSubuniverse L R) {I : Set A} (hIabs : IsAbsorbing L (I : Set A)) (hcyc : IsCyclicRel R)
    (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a) (c : Fin (q + 1)) (Lset : Set (Fin (q + 1))) :
    IsAbsorbing L {a : A | ∃ r ∈ R, (∀ l ∈ Lset, r l ∈ I) ∧ r c = a} := by
  obtain ⟨hIs, m, t, hm, ht⟩ := hIabs
  have hsub : IsSubuniverse L {a : A | ∃ r ∈ R, (∀ l ∈ Lset, r l ∈ I) ∧ r c = a} := by
    intro n f x hx
    choose r hrR hrI hrc using hx
    refine ⟨funMap f r, hR n f r hrR, fun l hl => ?_, ?_⟩
    · rw [piStr_funMap]
      exact hIs n f _ (fun i => hrI i l hl)
    · rw [piStr_funMap]
      congr 1; ext i; exact hrc i
  refine ⟨hsub, m, t, hm, fun j a haj => ?_⟩
  have hex : ∀ i, ∃ r ∈ R, (i ≠ j → ∀ l ∈ Lset, r l ∈ I) ∧ r c = a i := by
    intro i
    by_cases hij : i = j
    · obtain ⟨r, hr, hrc⟩ := coord_surj hcyc h0 c (a i)
      exact ⟨r, hr, fun h => absurd hij h, hrc⟩
    · obtain ⟨r, hr, hrI, hrc⟩ := haj i hij
      exact ⟨r, hr, fun _ => hrI, hrc⟩
  choose r hrR hrI hrc using hex
  refine ⟨t.realize r, realize_mem hR t r hrR, fun l hl => ?_, ?_⟩
  · rw [realize_pi]
    exact ht j (fun i => r i l) (fun i hi => hrI i hi l hl)
  · rw [realize_pi]
    congr 1; ext i; exact hrc i


theorem fin_add_q_val {l : Fin (q + 1)} (hl : 1 ≤ l.val) :
    (l + (q : Fin (q + 1))).val = l.val - 1 := by
  rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : q < q + 1)]
  have : l.val + q = (l.val - 1) + (q + 1) := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := l.2; omega)]

theorem no_prefix_in_I (hR : IsSubuniverse L R) (hcyc : IsCyclicRel R) (hnc : ∀ a : A, (fun _ => a) ∉ R)
    (hsub : ∀ S : L.Substructure A, (S : Set A) ≠ Set.univ → HasCyclicTermOp L S (q + 1))
    {I : Set A} (hIs : IsSubuniverse L I) (hIne : I ≠ Set.univ) :
    ∀ r ∈ R, ¬ ∀ i, r i ∈ I := by
  intro r hr hall
  have hSsub : IsSubuniverse L {r' : Fin (q + 1) → A | r' ∈ R ∧ ∀ i, r' i ∈ I} := by
    intro n f x hx
    refine ⟨hR n f x (fun k => (hx k).1), fun i => ?_⟩
    rw [piStr_funMap]
    exact hIs n f _ (fun k => (hx k).2 i)
  have hScyc : IsCyclicRel {r' : Fin (q + 1) → A | r' ∈ R ∧ ∀ i, r' i ∈ I} := by
    intro x hx
    exact ⟨hcyc x hx.1, fun i => hx.2 _⟩
  obtain ⟨a, ha⟩ := const_of_proper hsub I hIs hIne {r' : Fin (q + 1) → A | r' ∈ R ∧ ∀ i, r' i ∈ I}
    (fun s hs i => hs.2 i) ⟨r, hr, hall⟩ hSsub hScyc
  exact hnc a ha.1

theorem exists_greatest {I : Set A} (hIne' : I.Nonempty)
    (hnoP : ∀ r ∈ R, ¬ ∀ i, r i ∈ I) {n : ℕ} (hn : n ≤ q + 1)
    (hIpow : ∀ x : Fin n → A, (∀ i, x i ∈ I) → x ∈ Rn R n hn) :
    ∃ k, n ≤ k ∧ k ≤ q ∧ (∃ r ∈ R, ∀ l : Fin (q + 1), l.val < k → r l ∈ I) ∧
      ¬ ∃ r ∈ R, ∀ l : Fin (q + 1), l.val < k + 1 → r l ∈ I := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨a, ha⟩ := hIne'
  have hPn : ∃ r ∈ R, ∀ l : Fin (q + 1), l.val < n → r l ∈ I := by
    obtain ⟨r, hr, hrw⟩ := hIpow (fun _ => a) (fun _ => ha)
    refine ⟨r, hr, fun l hl => ?_⟩
    have := hrw ⟨l.val, hl⟩
    have e : Fin.castLE hn (⟨l.val, hl⟩ : Fin n) = l := Fin.ext rfl
    rw [e] at this
    rw [this]; exact ha
  have hall : ∀ m : ℕ, n ≤ m → m ≤ q + 1 → ∃ r ∈ R, ∀ l : Fin (q + 1), l.val < m → r l ∈ I := by
    intro m hnm
    induction m, hnm using Nat.le_induction with
    | base => intro _; exact hPn
    | succ m hnm ih =>
      intro hm
      exact hcon m hnm (by omega) (ih (by omega))
  obtain ⟨r, hr, hrI⟩ := hall (q + 1) (by omega) le_rfl
  exact hnoP r hr (fun i => hrI i (by have := i.2; omega))


theorem claim49 (hR : IsSubuniverse L R) (hcyc : IsCyclicRel R) (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a)
    (hnc : ∀ a : A, (fun _ => a) ∉ R)
    (hsub : ∀ S : L.Substructure A, (S : Set A) ≠ Set.univ → HasCyclicTermOp L S (q + 1))
    {I : Set A} (hI : MinAbsorbing L I) (hIne : I ≠ Set.univ)
    {n : ℕ} (hn : n + 1 ≤ q + 1)
    (hIpow : ∀ x : Fin n → A, (∀ i, x i ∈ I) → x ∈ Rn R n (Nat.le_of_succ_le hn)) :
    (∃ J : Set A, MinAbsorbing L J ∧ J ≠ I ∧ ∃ w ∈ Rn R (n + 1) hn,
        (∀ i : Fin n, w (Fin.castSucc i) ∈ I) ∧ w (Fin.last n) ∈ J) ∧
    (∃ J' : Set A, MinAbsorbing L J' ∧ J' ≠ I ∧ ∃ w ∈ Rn R (n + 1) hn,
        w 0 ∈ J' ∧ ∀ i : Fin n, w (Fin.succ i) ∈ I) := by
  have hn' : n ≤ q + 1 := Nat.le_of_succ_le hn
  have hnoP := no_prefix_in_I R hR hcyc hnc hsub hI.2.1.1 hIne
  obtain ⟨k, hnk, hkq, ⟨r0, hr0, hr0I⟩, hnotP⟩ := exists_greatest R hI.1 hnoP hn' hIpow
  have hkfin : k < q + 1 := by omega
  refine ⟨?_, ?_⟩
  · -- the right-hand side
    set X' : Set A := {a | ∃ r ∈ R, (∀ l ∈ {l : Fin (q + 1) | l.val < k}, r l ∈ I) ∧ r ⟨k, hkfin⟩ = a} with hX'
    have hX'abs : IsAbsorbing L X' := abs_coord_set R hR hI.2.1 hcyc h0 ⟨k, hkfin⟩ _
    have hX'ne : X'.Nonempty := ⟨r0 ⟨k, hkfin⟩, r0, hr0, fun l hl => hr0I l hl, rfl⟩
    obtain ⟨J, hJX, hJ⟩ := exists_min_absorbing X' hX'abs hX'ne
    have hdisj : ∀ a ∈ X', a ∉ I := by
      rintro a ⟨r, hr, hrI, hra⟩ haI
      apply hnotP
      refine ⟨r, hr, fun l hl => ?_⟩
      by_cases hlk : l.val < k
      · exact hrI l hlk
      · have : l = ⟨k, hkfin⟩ := Fin.ext (by simp only; omega)
        rw [this, hra]; exact haI
    refine ⟨J, hJ, ?_, ?_⟩
    · intro hJI
      obtain ⟨a, ha⟩ := hJ.1
      exact hdisj a (hJX ha) (hJI ▸ ha)
    · obtain ⟨a, ha⟩ := hJ.1
      obtain ⟨r, hr, hrI, hra⟩ := hJX ha
      have hρ := cyc_shift hcyc hr (k - n)
      have hidx : ∀ i : Fin (n + 1), (Fin.castLE hn i + ((k - n : ℕ) : Fin (q + 1))).val = i.val + (k - n) := by
        intro i
        apply fin_add_nat_val
        have := i.2; simp; omega
      refine ⟨fun i => r (Fin.castLE hn i + ((k - n : ℕ) : Fin (q + 1))), ⟨_, hρ, fun i => rfl⟩, fun i => ?_, ?_⟩
      · apply hrI
        show (Fin.castLE hn (Fin.castSucc i) + ((k - n : ℕ) : Fin (q + 1))).val < k
        rw [hidx]; simp; have := i.2; omega
      · have : Fin.castLE hn (Fin.last n) + ((k - n : ℕ) : Fin (q + 1)) = ⟨k, hkfin⟩ := by
          apply Fin.ext; rw [hidx]; simp; omega
        show r (Fin.castLE hn (Fin.last n) + ((k - n : ℕ) : Fin (q + 1))) ∈ J
        rw [this, hra]; exact ha
  · -- the left-hand side
    set X'' : Set A := {a | ∃ r ∈ R, (∀ l ∈ {l : Fin (q + 1) | 1 ≤ l.val ∧ l.val ≤ k}, r l ∈ I) ∧ r 0 = a} with hX''
    have hX''abs : IsAbsorbing L X'' := abs_coord_set R hR hI.2.1 hcyc h0 0 _
    have hX''ne : X''.Nonempty := by
      have hρ := cyc_shift hcyc hr0 q
      refine ⟨(fun i => r0 (i + (q : Fin (q + 1)))) 0, _, hρ, fun l hl => ?_, rfl⟩
      obtain ⟨hl1, hlk⟩ := hl
      apply hr0I
      show (l + (q : Fin (q + 1))).val < k
      rw [fin_add_q_val hl1]; omega
    obtain ⟨J, hJX, hJ⟩ := exists_min_absorbing X'' hX''abs hX''ne
    have hdisj : ∀ a ∈ X'', a ∉ I := by
      rintro a ⟨r, hr, hrI, hra⟩ haI
      apply hnotP
      refine ⟨r, hr, fun l hl => ?_⟩
      by_cases hl0 : l.val = 0
      · have : l = 0 := Fin.ext hl0
        rw [this, hra]; exact haI
      · exact hrI l ⟨by omega, by omega⟩
    refine ⟨J, hJ, ?_, ?_⟩
    · intro hJI
      obtain ⟨a, ha⟩ := hJ.1
      exact hdisj a (hJX ha) (hJI ▸ ha)
    · obtain ⟨a, ha⟩ := hJ.1
      obtain ⟨r, hr, hrI, hra⟩ := hJX ha
      refine ⟨fun i => r (Fin.castLE hn i), ⟨r, hr, fun i => rfl⟩, ?_, fun i => ?_⟩
      · show r (Fin.castLE hn 0) ∈ J
        have : Fin.castLE hn (0 : Fin (n + 1)) = 0 := rfl
        rw [this, hra]; exact ha
      · apply hrI
        show 1 ≤ (Fin.castLE hn (Fin.succ i)).val ∧ (Fin.castLE hn (Fin.succ i)).val ≤ k
        simp; have := i.2; omega


/-- the relation `F ⊆ A²` : first and last coordinate of `R_{n+1}`-tuples -/
def Frel {n : ℕ} (hn : n + 1 ≤ q + 1) : Set (A × A) :=
  {p | ∃ w ∈ Rn R (n + 1) hn, w 0 = p.1 ∧ w (Fin.last n) = p.2}

/-- the relation `E ⊆ F` : same with the inner coordinates in `I` -/
def Erel (I : Set A) {n : ℕ} (hn : n + 1 ≤ q + 1) : Set (A × A) :=
  {p | ∃ w ∈ Rn R (n + 1) hn, w 0 = p.1 ∧ w (Fin.last n) = p.2 ∧
    ∀ i : Fin n, 0 < i.val → w (Fin.castSucc i) ∈ I}

theorem Frel_sub (hR : IsSubuniverse L R) {n : ℕ} (hn : n + 1 ≤ q + 1) : IsSubuniverse L (Frel R hn) := by
  intro m f z hz
  choose w hwR hw0 hwl using hz
  refine ⟨funMap f w, Rn_sub R hR (n + 1) hn m f w hwR, ?_, ?_⟩
  · show (funMap f w : Fin (n + 1) → A) 0 = funMap f (fun i => (z i).1)
    rw [piStr_funMap]; congr 1; ext i; exact hw0 i
  · show (funMap f w : Fin (n + 1) → A) (Fin.last n) = funMap f (fun i => (z i).2)
    rw [piStr_funMap]; congr 1; ext i; exact hwl i

theorem Erel_sub (hR : IsSubuniverse L R) {I : Set A} (hI : IsSubuniverse L I) {n : ℕ} (hn : n + 1 ≤ q + 1) :
    IsSubuniverse L (Erel R I hn) := by
  intro m f z hz
  choose w hwR hw0 hwl hwI using hz
  refine ⟨funMap f w, Rn_sub R hR (n + 1) hn m f w hwR, ?_, ?_, fun i hi => ?_⟩
  · show (funMap f w : Fin (n + 1) → A) 0 = funMap f (fun i => (z i).1)
    rw [piStr_funMap]; congr 1; ext i; exact hw0 i
  · show (funMap f w : Fin (n + 1) → A) (Fin.last n) = funMap f (fun i => (z i).2)
    rw [piStr_funMap]; congr 1; ext i; exact hwl i
  · rw [piStr_funMap]
    exact hI m f _ (fun k => hwI k i hi)

theorem Erel_sub_Frel (I : Set A) {n : ℕ} (hn : n + 1 ≤ q + 1) : Erel R I hn ⊆ Frel R hn := by
  rintro p ⟨w, hw, h0, hl, -⟩; exact ⟨w, hw, h0, hl⟩

theorem Frel_subdirect (hcyc : IsCyclicRel R) (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a) {n : ℕ} (hn : n + 1 ≤ q + 1) :
    Subdirect (Frel R hn) := by
  constructor
  · apply Set.eq_univ_of_forall
    intro a
    obtain ⟨r, hr, hra⟩ := h0 a
    exact ⟨(a, r (Fin.castLE hn (Fin.last n))), ⟨fun i => r (Fin.castLE hn i), ⟨r, hr, fun i => rfl⟩, hra, rfl⟩, rfl⟩
  · apply Set.eq_univ_of_forall
    intro b
    obtain ⟨r, hr, hrb⟩ := coord_surj hcyc h0 ⟨n, by omega⟩ b
    refine ⟨(r 0, b), ⟨fun i => r (Fin.castLE hn i), ⟨r, hr, fun i => rfl⟩, rfl, ?_⟩, rfl⟩
    have : Fin.castLE hn (Fin.last n) = (⟨n, by omega⟩ : Fin (q + 1)) := Fin.ext (by simp)
    show r (Fin.castLE hn (Fin.last n)) = b
    rw [this]; exact hrb

theorem Erel_absorbs {I : Set A} (hI : IsAbsorbing L I) (hR : IsSubuniverse L R) {n : ℕ} (hn : n + 1 ≤ q + 1) :
    AbsorbsIn L (Frel R hn) (Erel R I hn) := by
  obtain ⟨hIs, m, t, hm, ht⟩ := hI
  refine ⟨Erel_sub R hR hIs hn, Erel_sub_Frel R I hn, m, t, hm, fun j z hzF hzE => ?_⟩
  have hex : ∀ i, ∃ w ∈ Rn R (n + 1) hn, w 0 = (z i).1 ∧ w (Fin.last n) = (z i).2 ∧
      (i ≠ j → ∀ l : Fin n, 0 < l.val → w (Fin.castSucc l) ∈ I) := by
    intro i
    by_cases hij : i = j
    · obtain ⟨w, hw, h0, hl⟩ := hzF i
      exact ⟨w, hw, h0, hl, fun h => absurd hij h⟩
    · obtain ⟨w, hw, h0, hl, hI⟩ := hzE i hij
      exact ⟨w, hw, h0, hl, fun _ => hI⟩
  choose w hwR hw0 hwl hwI using hex
  have hz : t.realize z = (t.realize (fun i => (z i).1), t.realize (fun i => (z i).2)) :=
    realize_prod t (fun i => (z i).1) (fun i => (z i).2)
  refine ⟨t.realize w, realize_mem (Rn_sub R hR (n + 1) hn) t w hwR, ?_, ?_, fun l hl => ?_⟩
  · rw [hz, realize_pi]
    show t.realize (fun i => w i 0) = t.realize (fun i => (z i).1)
    congr 1; ext i; exact hw0 i
  · rw [hz, realize_pi]
    show t.realize (fun i => w i (Fin.last n)) = t.realize (fun i => (z i).2)
    congr 1; ext i; exact hwl i
  · rw [realize_pi]
    exact ht j (fun i => w i (Fin.castSucc l)) (fun i hi => hwI i hi l hl)


theorem mem_Frel (hcyc : IsCyclicRel R) {n : ℕ} (hn : n + 1 ≤ q + 1) {r : Fin (q + 1) → A} (hr : r ∈ R)
    (ι : Fin (q + 1)) : (r ι, r (ι + (n : Fin (q + 1)))) ∈ Frel R hn := by
  have hρ := cyc_shift hcyc hr ι.val
  have e : ((ι.val : ℕ) : Fin (q + 1)) = ι := Fin.cast_val_eq_self ι
  rw [e] at hρ
  refine ⟨fun l => r (Fin.castLE hn l + ι), ⟨_, hρ, fun l => rfl⟩, ?_, ?_⟩
  · show r (Fin.castLE hn 0 + ι) = r ι
    congr 1
    apply Fin.ext
    simp
  · show r (Fin.castLE hn (Fin.last n) + ι) = r (ι + (n : Fin (q + 1)))
    congr 1
    have : Fin.castLE hn (Fin.last n) = (n : Fin (q + 1)) := by
      apply Fin.ext
      rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega : n < q + 1)]
      simp
    rw [this]; exact add_comm _ _

theorem exists_mul_cast (hp : (q + 1).Prime) {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ q) (y : Fin (q + 1)) :
    ∃ m : ℕ, ((m * a : ℕ) : Fin (q + 1)) = y := by
  have hcop : Nat.Coprime a (q + 1) := by
    have hnd : ¬ (q + 1) ∣ a := fun h => by have := Nat.le_of_dvd (by omega) h; omega
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_of_coprime y.val hcop (by omega : q + 1 ≠ 0)
  refine ⟨m, ?_⟩
  apply Fin.ext
  rw [Fin.val_natCast, Nat.mul_comm, hm, Nat.mod_eq_of_lt y.2]


theorem Frel_fork (hcyc : IsCyclicRel R) (hRne : R.Nonempty) (hnc : ∀ a : A, (fun _ => a) ∉ R)
    (hprime : (q + 1).Prime) (hpA : Nat.card A < q + 1) {n : ℕ} (h1 : 1 ≤ n) (hn : n + 1 ≤ q + 1) :
    ∃ a b b' : A, b ≠ b' ∧ (a, b) ∈ Frel R hn ∧ (a, b') ∈ Frel R hn := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  obtain ⟨r, hr⟩ := hRne
  obtain ⟨i, j, hij, hrij⟩ := Fintype.exists_ne_map_eq_of_card_lt r (by
    rw [Fintype.card_fin]; rw [← Nat.card_eq_fintype_card]; exact hpA)
  have hn2 : n ≤ q := by omega
  by_cases hm : ∃ m : ℕ, r (i + ((m * n : ℕ) : Fin (q + 1))) ≠ r (j + ((m * n : ℕ) : Fin (q + 1)))
  · set m0 := Nat.find hm with hm0
    have hspec : r (i + ((m0 * n : ℕ) : Fin (q + 1))) ≠ r (j + ((m0 * n : ℕ) : Fin (q + 1))) := Nat.find_spec hm
    have hm0pos : m0 ≠ 0 := by
      intro h
      rw [h] at hspec
      simp at hspec
      exact hspec hrij
    obtain ⟨m1, hm1⟩ : ∃ m1, m0 = m1 + 1 := ⟨m0 - 1, by omega⟩
    have hmin : r (i + ((m1 * n : ℕ) : Fin (q + 1))) = r (j + ((m1 * n : ℕ) : Fin (q + 1))) := by
      have := Nat.find_min hm (show m1 < m0 by omega)
      push_neg at this
      exact this
    have hcast : ((m0 * n : ℕ) : Fin (q + 1)) = ((m1 * n : ℕ) : Fin (q + 1)) + (n : Fin (q + 1)) := by
      rw [hm1, Nat.succ_mul, Nat.cast_add]
    rw [hcast, ← add_assoc, ← add_assoc] at hspec
    refine ⟨r (i + ((m1 * n : ℕ) : Fin (q + 1))), r (i + ((m1 * n : ℕ) : Fin (q + 1)) + (n : Fin (q + 1))),
      r (j + ((m1 * n : ℕ) : Fin (q + 1)) + (n : Fin (q + 1))), hspec, ?_, ?_⟩
    · exact mem_Frel R hcyc hn hr _
    · rw [hmin]; exact mem_Frel R hcyc hn hr _
  · exfalso
    push_neg at hm
    set d : Fin (q + 1) := j - i with hd
    have hjd : j = i + d := by rw [hd]; abel
    have hdne : d ≠ 0 := by
      intro h; apply hij; rw [hjd, h]; simp
    have hper : ∀ x : Fin (q + 1), r x = r (x + d) := by
      intro x
      obtain ⟨m, hmx⟩ := exists_mul_cast hprime h1 hn2 (x - i)
      have hx : x = i + ((m * n : ℕ) : Fin (q + 1)) := by rw [hmx]; abel
      have := hm m
      rw [hx]
      rw [hjd] at this
      rw [this]
      congr 1; abel
    have hda : 1 ≤ d.val ∧ d.val ≤ q := by
      refine ⟨Nat.pos_of_ne_zero (fun h => hdne (Fin.ext (by simpa using h))), by have := d.2; omega⟩
    have hconst : ∀ y : Fin (q + 1), r y = r 0 := by
      intro y
      obtain ⟨k, hk⟩ := exists_mul_cast hprime hda.1 hda.2 y
      have hmul : ∀ k : ℕ, r (((k * d.val : ℕ) : Fin (q + 1))) = r 0 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hd' : ((d.val : ℕ) : Fin (q + 1)) = d := Fin.cast_val_eq_self d
          have : (((k + 1) * d.val : ℕ) : Fin (q + 1)) = ((k * d.val : ℕ) : Fin (q + 1)) + d := by
            rw [Nat.succ_mul, Nat.cast_add, hd']
          rw [this, ← hper, ih]
      rw [← hk]; exact hmul k
    apply hnc (r 0)
    have : (fun _ => r 0) = r := by funext y; exact (hconst y).symm
    rw [this]; exact hr


theorem univ_abs : IsAbsorbing L (Set.univ : Set A) :=
  ⟨fun _ _ _ _ => trivial, 1, Term.var 0, one_pos, fun _ _ _ => trivial⟩

theorem Frel_linked (hR : IsSubuniverse L R)
    (hsimple : ∀ r : A → A → Prop, Equivalence r →
      (∀ (n : ℕ) (f : L.Functions n) (x y : Fin n → A), (∀ i, r (x i) (y i)) →
        r (Structure.funMap f x) (Structure.funMap f y)) →
      (∀ a b, r a b → a = b) ∨ ∀ a b, r a b)
    (hcyc : IsCyclicRel R) (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a) (hRne : R.Nonempty)
    (hnc : ∀ a : A, (fun _ => a) ∉ R) (hprime : (q + 1).Prime) (hpA : Nat.card A < q + 1)
    {n : ℕ} (h1 : 1 ≤ n) (hn : n + 1 ≤ q + 1) : Linked (Frel R hn) := by
  obtain ⟨a, b, b', hbb, h1, h2⟩ := Frel_fork R hcyc hRne hnc hprime hpA h1 hn
  exact fork_linked hsimple (Frel R hn) (Frel_sub R hR hn) (Frel_subdirect R hcyc h0 hn) ⟨a, b, b', hbb, h1, h2⟩

theorem Erel_linked (hR : IsSubuniverse L R) (hid : IsIdempotent L A)
    (hsimple : ∀ r : A → A → Prop, Equivalence r →
      (∀ (n : ℕ) (f : L.Functions n) (x y : Fin n → A), (∀ i, r (x i) (y i)) →
        r (Structure.funMap f x) (Structure.funMap f y)) →
      (∀ a b, r a b → a = b) ∨ ∀ a b, r a b)
    (hcyc : IsCyclicRel R) (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a) (hRne : R.Nonempty)
    (hnc : ∀ a : A, (fun _ => a) ∉ R) (hprime : (q + 1).Prime) (hpA : Nat.card A < q + 1)
    {I : Set A} (hI : IsAbsorbing L I) {n : ℕ} (h1 : 1 ≤ n) (hn : n + 1 ≤ q + 1) :
    Linked (Erel R I hn) :=
  prop215_i hid (Frel R hn) (Frel_linked R hR hsimple hcyc h0 hRne hnc hprime hpA h1 hn) (Erel R I hn)
    (Erel_absorbs R hI hR hn)

theorem Erel_fst_abs (hR : IsSubuniverse L R) (hcyc : IsCyclicRel R) (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a)
    {I : Set A} (hI : IsAbsorbing L I) {n : ℕ} (hn : n + 1 ≤ q + 1) :
    IsAbsorbing L (Prod.fst '' Erel R I hn) := by
  have h := proj_absorbs (C := (Set.univ : Set A)) (D := (Set.univ : Set A)) (Frel R hn) (Erel R I hn)
    (Erel_absorbs R hI hR hn) (fun _ _ => ⟨trivial, trivial⟩) (Erel_sub_Frel R I hn)
    (fun c _ => by
      obtain ⟨p, hp, hpc⟩ := (Frel_subdirect R hcyc h0 hn).1 ▸ (show c ∈ (Set.univ : Set A) from trivial)
      exact ⟨p.2, by rw [← hpc]; exact hp⟩)
  exact absorbs_trans_rel univ_abs h

theorem Erel_snd_abs (hR : IsSubuniverse L R) (hcyc : IsCyclicRel R) (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a)
    {I : Set A} (hI : IsAbsorbing L I) {n : ℕ} (hn : n + 1 ≤ q + 1) :
    IsAbsorbing L (Prod.snd '' Erel R I hn) := by
  have hsw := swap_absorbsIn (Erel_absorbs R hI hR hn)
  have h := proj_absorbs (C := (Set.univ : Set A)) (D := (Set.univ : Set A))
    {p : A × A | (p.2, p.1) ∈ Frel R hn} {p : A × A | (p.2, p.1) ∈ Erel R I hn} hsw
    (fun _ _ => ⟨trivial, trivial⟩) (fun p hp => Erel_sub_Frel R I hn hp)
    (fun c _ => by
      obtain ⟨p, hp, hpc⟩ := (Frel_subdirect R hcyc h0 hn).2 ▸ (show c ∈ (Set.univ : Set A) from trivial)
      exact ⟨p.1, by rw [← hpc]; exact hp⟩)
  have himg : Prod.fst '' {p : A × A | (p.2, p.1) ∈ Erel R I hn} = Prod.snd '' Erel R I hn := by
    ext b
    constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨(p.2, p.1), hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩; exact ⟨(p.2, p.1), hp, rfl⟩
  rw [himg] at h
  exact absorbs_trans_rel univ_abs h


theorem min_eq_or_disjoint {M : Type w} [L.Structure M] {C D : Set M} (hC : MinAbsorbing L C)
    (hD : MinAbsorbing L D) : C = D ∨ C ∩ D = ∅ := by
  by_cases h : (C ∩ D).Nonempty
  · left
    have h1 := hC.2.2 _ h Set.inter_subset_left (absorbing_inter C D hC.2.1 hD.2.1)
    have h2 := hD.2.2 _ h Set.inter_subset_right (absorbing_inter C D hC.2.1 hD.2.1)
    exact h1.symm.trans h2
  · right
    exact Set.not_nonempty_iff_eq_empty.1 h

theorem abs_preimage {M : Type w} [L.Structure M] {V : Set M} (hV : IsSubuniverse L V) {F : Set M}
    (hF : IsAbsorbing L F) (hFV : F ⊆ V) : IsAbsorbing L {z : subS V hV | z.1 ∈ F} := by
  obtain ⟨hFs, m, t, hm, ht⟩ := hF
  refine ⟨?_, m, t, hm, fun k a hak => ?_⟩
  · intro n f x hx
    show funMap f (fun i => (x i).1) ∈ F
    exact hFs n f _ hx
  · show (t.realize a).1 ∈ F
    rw [subS_realize]
    exact ht k (fun i => (a i).1) (fun i hi => hak i hi)

theorem minAbs_restrict {M : Type w} [L.Structure M] {V : Set M} (hV : IsSubuniverse L V)
    (hVabs : IsAbsorbing L V) {C : Set M} (hC : MinAbsorbing L C) (hCV : C ⊆ V) :
    MinAbsorbing L {z : subS V hV | z.1 ∈ C} := by
  obtain ⟨c, hc⟩ := hC.1
  refine ⟨⟨⟨c, hCV hc⟩, hc⟩, abs_preimage hV hC.2.1 hCV, fun F' hFne hFC hFabs => ?_⟩
  have himg := absorbsIn_image hV hFabs
  have habs : IsAbsorbing L (Subtype.val '' F') := absorbs_trans_rel hVabs himg
  have hsub : Subtype.val '' F' ⊆ C := by rintro _ ⟨z, hz, rfl⟩; exact hFC hz
  have heq := hC.2.2 _ (hFne.image _) hsub habs
  ext z
  constructor
  · intro hz; exact hFC hz
  · intro hz
    have : z.1 ∈ Subtype.val '' F' := by rw [heq]; exact hz
    obtain ⟨z', hz', hzz⟩ := this
    have : z' = z := Subtype.ext hzz
    rw [← this]; exact hz'

theorem minAbs_lift {M : Type w} [L.Structure M] {V : Set M} (hV : IsSubuniverse L V)
    (hVabs : IsAbsorbing L V) {C' : Set (subS V hV)} (hC' : MinAbsorbing L C') :
    MinAbsorbing L (Subtype.val '' C') := by
  refine ⟨hC'.1.image _, absorbs_trans_rel hVabs (absorbsIn_image hV hC'.2.1), fun F hFne hFC hFabs => ?_⟩
  have hFV : F ⊆ V := fun x hx => by
    obtain ⟨z, -, rfl⟩ := hFC hx; exact z.2
  have hpre := abs_preimage hV hFabs hFV
  have hsub : {z : subS V hV | z.1 ∈ F} ⊆ C' := by
    intro z hz
    obtain ⟨z', hz', hzz⟩ := hFC hz
    have : z' = z := Subtype.ext hzz
    rw [← this]; exact hz'
  obtain ⟨x, hx⟩ := hFne
  have hne : ({z : subS V hV | z.1 ∈ F}).Nonempty := ⟨⟨x, hFV hx⟩, hx⟩
  have heq := hC'.2.2 _ hne hsub hpre
  ext x
  constructor
  · intro hx; exact hFC hx
  · rintro ⟨z, hz, rfl⟩
    have : z ∈ {z : subS V hV | z.1 ∈ F} := by rw [heq]; exact hz
    exact this


/-- the relation `E` seen on `V1 × V2` -/
def Esub (E : Set (A × A)) (V1 V2 : Set A) (h1 : IsSubuniverse L V1) (h2 : IsSubuniverse L V2) :
    Set (subS V1 h1 × subS V2 h2) := {p | ((p.1 : A), (p.2 : A)) ∈ E}

theorem Esub_facts {E : Set (A × A)} (hE : IsSubuniverse L E) (hlin : Linked E)
    {V1 V2 : Set A} (h1 : IsSubuniverse L V1) (h2 : IsSubuniverse L V2)
    (hV1 : V1 = Prod.fst '' E) (hV2 : V2 = Prod.snd '' E) :
    IsSubuniverse L (Esub E V1 V2 h1 h2) ∧ Subdirect (Esub E V1 V2 h1 h2) ∧
      Linked (Esub E V1 V2 h1 h2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m f z hz
    show (((funMap f z).1 : A), ((funMap f z).2 : A)) ∈ E
    exact hE m f (fun i => (((z i).1 : A), ((z i).2 : A))) hz
  · constructor
    · apply Set.eq_univ_of_forall; intro x
      have : (x : A) ∈ Prod.fst '' E := hV1 ▸ x.2
      obtain ⟨p, hp, hpx⟩ := this
      have hp2 : p.2 ∈ V2 := hV2 ▸ ⟨p, hp, rfl⟩
      refine ⟨(x, ⟨p.2, hp2⟩), ?_, rfl⟩
      show ((x : A), p.2) ∈ E
      rw [← hpx]; exact hp
    · apply Set.eq_univ_of_forall; intro y
      have : (y : A) ∈ Prod.snd '' E := hV2 ▸ y.2
      obtain ⟨p, hp, hpy⟩ := this
      have hp1 : p.1 ∈ V1 := hV1 ▸ ⟨p, hp, rfl⟩
      refine ⟨(⟨p.1, hp1⟩, y), ?_, rfl⟩
      show (p.1, (y : A)) ∈ E
      rw [← hpy]; exact hp
  · intro x x' _ _
    have hx : (x : A) ∈ Prod.fst '' E := hV1 ▸ x.2
    have hx' : (x' : A) ∈ Prod.fst '' E := hV1 ▸ x'.2
    have hrt := hlin _ _ hx hx'
    have key : ∀ y : A, Relation.ReflTransGen (LinkStep E) (x : A) y →
        ∃ y' : subS V1 h1, (y' : A) = y ∧ Relation.ReflTransGen (LinkStep (Esub E V1 V2 h1 h2)) x y' := by
      intro y hy
      induction hy with
      | refl => exact ⟨x, rfl, Relation.ReflTransGen.refl⟩
      | @tail y₀ c _ hlk ih =>
        obtain ⟨y', rfl, hy'⟩ := ih
        obtain ⟨b, hb1, hb2⟩ := hlk
        have hzV : c ∈ V1 := by rw [hV1]; exact ⟨(c, b), hb2, rfl⟩
        have hbV : b ∈ V2 := by rw [hV2]; exact ⟨(c, b), hb2, rfl⟩
        exact ⟨⟨c, hzV⟩, rfl, hy'.tail ⟨⟨b, hbV⟩, hb1, hb2⟩⟩
    obtain ⟨y', hy', hrt'⟩ := key _ hrt
    have : y' = x' := Subtype.ext hy'
    rw [this] at hrt'
    exact hrt'


theorem E_fork [Finite A] (T : TaylorDatum L) (hA : IsTaylorAlg T A) {E : Set (A × A)}
    (hE : IsSubuniverse L E) (hlin : Linked E) {V1 V2 : Set A} (h1 : IsSubuniverse L V1)
    (h2 : IsSubuniverse L V2) (hV1 : V1 = Prod.fst '' E) (hV2 : V2 = Prod.snd '' E)
    (hV1abs : IsAbsorbing L V1) (hV2abs : IsAbsorbing L V2) {I J : Set A}
    (hI : MinAbsorbing L I) (hJ : MinAbsorbing L J) (hIJ : I ≠ J) {b b' : A} (hb : b ∈ I) (hb' : b' ∈ J)
    (hbV : b ∈ V2) (hb'V : b' ∈ V2) :
    ∃ (w u v : A) (U V W : Set A), MinAbsorbing L U ∧ MinAbsorbing L V ∧ MinAbsorbing L W ∧
      w ∈ W ∧ u ∈ U ∧ v ∈ V ∧ U ≠ V ∧ (w, u) ∈ E ∧ (w, v) ∈ E := by
  obtain ⟨hsubE, hsdE, hlinE⟩ := Esub_facts hE hlin h1 h2 hV1 hV2
  have hT1 := subS_taylor V1 h1 T hA
  have hT2 := subS_taylor V2 h2 T hA
  -- J ⊆ V2 and I ⊆ V2
  have hJV : J ⊆ V2 := by
    have := hJ.2.2 (J ∩ V2) ⟨b', hb', hb'V⟩ Set.inter_subset_left (absorbing_inter J V2 hJ.2.1 hV2abs)
    intro x hx; rw [← this] at hx; exact hx.2
  have hIV : I ⊆ V2 := by
    have := hI.2.2 (I ∩ V2) ⟨b, hb, hbV⟩ Set.inter_subset_left (absorbing_inter I V2 hI.2.1 hV2abs)
    intro x hx; rw [← this] at hx; exact hx.2
  have hJm := minAbs_restrict h2 hV2abs hJ hJV
  have hIm := minAbs_restrict h2 hV2abs hI hIV
  let x0 : subS V1 h1 ⊕ subS V2 h2 := Sum.inr ⟨b', hb'V⟩
  let y0 : subS V1 h1 ⊕ subS V2 h2 := Sum.inr ⟨b, hbV⟩
  have hrt := prop215_v T hT1 hT2 (Esub E V1 V2 h1 h2) hsubE hsdE hlinE x0 y0
    ⟨{z | z.1 ∈ J}, hJm, hb'⟩ ⟨{z | z.1 ∈ I}, hIm, hb⟩
  have hdisj : b ∉ J := by
    intro hbJ
    rcases min_eq_or_disjoint hI hJ with h | h
    · exact hIJ h
    · have : b ∈ I ∩ J := ⟨hb, hbJ⟩
      rw [h] at this; exact this
  let Fork : Prop := ∃ (w u v : A) (U V W : Set A), MinAbsorbing L U ∧ MinAbsorbing L V ∧ MinAbsorbing L W ∧
      w ∈ W ∧ u ∈ U ∧ v ∈ V ∧ U ≠ V ∧ (w, u) ∈ E ∧ (w, v) ∈ E
  have key : ∀ z, Relation.ReflTransGen (MinStep L (Esub E V1 V2 h1 h2)) x0 z →
      (match z with
        | Sum.inl w => Fork ∨ ∃ y : subS V2 h2, (w, y) ∈ Esub E V1 V2 h1 h2 ∧ (y : A) ∈ J
        | Sum.inr y => Fork ∨ (y : A) ∈ J) := by
    intro z hz
    induction hz with
    | refl => exact Or.inr hb'
    | @tail z₀ z₁ _ hstep ih =>
      obtain ⟨hadj, hm0, hm1⟩ := hstep
      rcases z₀ with w | y <;> rcases z₁ with w' | y'
      · exact absurd hadj (by simp [LinkAdj])
      · -- w → y'
        simp only [LinkAdj] at hadj
        rcases ih with hF | ⟨y, hy, hyJ⟩
        · exact Or.inl hF
        · by_cases hy'J : (y' : A) ∈ J
          · exact Or.inr hy'J
          · left
            obtain ⟨V', hV', hy'V'⟩ := hm1
            obtain ⟨W', hW', hwW'⟩ := hm0
            exact ⟨w, y, y', J, Subtype.val '' V', Subtype.val '' W', hJ, minAbs_lift h2 hV2abs hV',
              minAbs_lift h1 hV1abs hW', ⟨w, hwW', rfl⟩, hyJ, ⟨y', hy'V', rfl⟩,
              fun h => hy'J (h ▸ ⟨y', hy'V', rfl⟩), hy, hadj⟩
      · -- y → w'
        simp only [LinkAdj] at hadj
        rcases ih with hF | hyJ
        · exact Or.inl hF
        · exact Or.inr ⟨y, hadj, hyJ⟩
      · exact absurd hadj (by simp [LinkAdj])
  rcases key y0 hrt with hF | hbJ
  · exact hF
  · exact absurd hbJ hdisj


theorem S_linked_proper (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hR : IsSubuniverse L R)
    (hsimple : ∀ r : A → A → Prop, Equivalence r →
      (∀ (n : ℕ) (f : L.Functions n) (x y : Fin n → A), (∀ i, r (x i) (y i)) →
        r (Structure.funMap f x) (Structure.funMap f y)) →
      (∀ a b, r a b → a = b) ∨ ∀ a b, r a b)
    (hsub : ∀ S : L.Substructure A, (S : Set A) ≠ Set.univ → HasCyclicTermOp L S (q + 1))
    (hcyc : IsCyclicRel R) (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a) (hRne : R.Nonempty)
    (hnc : ∀ a : A, (fun _ => a) ∉ R) (hprime : (q + 1).Prime) (hpA : Nat.card A < q + 1)
    {I : Set A} (hI : MinAbsorbing L I) (hIne : I ≠ Set.univ) {n : ℕ} (h1 : 1 ≤ n) (hn : n + 1 ≤ q + 1)
    (hIpow : ∀ x : Fin n → A, (∀ i, x i ∈ I) → x ∈ Rn R n (Nat.le_of_succ_le hn))
    (H2 : P2 L R hR n (Nat.le_of_succ_le hn)) : Linked (Srel R hR hn) := by
  classical
  have hn' : n ≤ q + 1 := Nat.le_of_succ_le hn
  obtain ⟨⟨J, hJ, hJI, wR, hwR, hwRI, hwRJ⟩, ⟨J', hJ', hJ'I, wL, hwL, hwL0, hwLI⟩⟩ :=
    claim49 R hR hcyc h0 hnc hsub hI hIne hn hIpow
  have hEsub := Erel_sub R hR hI.2.1.1 (n := n) hn
  have hElin := Erel_linked R hR hA.1 hsimple hcyc h0 hRne hnc hprime hpA hI.2.1 h1 hn
  have hV1abs := Erel_fst_abs R hR hcyc h0 hI.2.1 hn
  have hV2abs := Erel_snd_abs R hR hcyc h0 hI.2.1 hn
  -- the two E-pairs
  have hn0 : 0 < n := h1
  have hpR : (wR 0, wR (Fin.last n)) ∈ Erel R I hn := by
    refine ⟨wR, hwR, rfl, rfl, fun i hi => hwRI i⟩
  have hpL : (wL 0, wL (Fin.last n)) ∈ Erel R I hn := by
    refine ⟨wL, hwL, rfl, rfl, fun i hi => ?_⟩
    have : Fin.castSucc i = Fin.succ ⟨i.val - 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [this]; exact hwLI _
  have hbI : wL (Fin.last n) ∈ I := by
    have : Fin.last n = Fin.succ ⟨n - 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [this]; exact hwLI _
  obtain ⟨w, u, v, U, V, W, hU, hV, hW, hwW, huU, hvV, hUV, hwu, hwv⟩ :=
    E_fork T hA hEsub hElin hV1abs.1 hV2abs.1 rfl rfl hV1abs hV2abs hI hJ (Ne.symm hJI) hbI hwRJ
      ⟨_, hpL, rfl⟩ ⟨_, hpR, rfl⟩
  -- the tuples
  let Iw : Fin n → Set A := fun i => if i.val = 0 then W else I
  have hIw : ∀ i, MinAbsorbing L (Iw i) := by
    intro i; by_cases h : i.val = 0 <;> simp [Iw, h] <;> assumption
  obtain ⟨w1, hw1, hw10, hw1l, hw1I⟩ := hwu
  obtain ⟨w2, hw2, hw20, hw2l, hw2I⟩ := hwv
  replace hw10 : w1 (0 : Fin (n + 1)) = w := hw10
  replace hw1l : w1 (Fin.last n) = u := hw1l
  replace hw20 : w2 (0 : Fin (n + 1)) = w := hw20
  replace hw2l : w2 (Fin.last n) = v := hw2l
  have hmem : ∀ (w' : Fin (n + 1) → A), w' 0 = w → (∀ i : Fin n, 0 < i.val → w' (Fin.castSucc i) ∈ I) →
      ∀ i : Fin n, Fin.init w' i ∈ Iw i := by
    intro w' h0' hI' i
    by_cases hi : i.val = 0
    · simp only [Iw, hi, if_true]
      have : Fin.castSucc i = 0 := Fin.ext (by simp [hi])
      show w' (Fin.castSucc i) ∈ W
      rw [this, h0']; exact hwW
    · simp only [Iw, hi, if_false]
      exact hI' i (by omega)
  have hC := H2 Iw hIw ⟨Fin.init w1, Rn_init hn hw1, hmem w1 hw10 hw1I⟩
  obtain ⟨hCsub, hCmin⟩ := hC
  have hTX : IsTaylorAlg T (subS (Rn R n hn') (Rn_sub R hR n hn')) := taylor_Rn T hA R hR n hn'
  have hVmin : MinAbsorbing L V := hV
  have hne : ∃ c ∈ {x : subS (Rn R n hn') (Rn_sub R hR n hn') | ∀ i, x.1 i ∈ Iw i}, ∃ d ∈ V, (c, d) ∈ Srel R hR hn := by
    refine ⟨⟨Fin.init w2, Rn_init hn hw2⟩, hmem w2 hw20 hw2I, v, hvV, ?_⟩
    show Fin.snoc (α := fun _ => A) (Fin.init w2) v ∈ Rn R (n + 1) hn
    rw [← hw2l, Fin.snoc_init_self]; exact hw2
  obtain ⟨hii, -⟩ := prop215_ii (Srel R hR hn) (Srel_sub R hR hn) (Srel_subdirect R hR hn hcyc h0) hCmin hVmin hne
  obtain ⟨v', hv'V, hcv'⟩ := hii ⟨Fin.init w1, Rn_init hn hw1⟩ (hmem w1 hw10 hw1I)
  have hcu : (⟨Fin.init w1, Rn_init hn hw1⟩, u) ∈ Srel R hR hn := by
    show Fin.snoc (α := fun _ => A) (Fin.init w1) u ∈ Rn R (n + 1) hn
    rw [← hw1l, Fin.snoc_init_self]; exact hw1
  have huv' : u ≠ v' := by
    intro h
    rcases min_eq_or_disjoint hU hV with h' | h'
    · exact hUV h'
    · have : u ∈ U ∩ V := ⟨huU, h ▸ hv'V⟩
      rw [h'] at this; exact this
  exact fork_linked hsimple (Srel R hR hn) (Srel_sub R hR hn) (Srel_subdirect R hR hn hcyc h0)
    ⟨⟨Fin.init w1, Rn_init hn hw1⟩, u, v', huv', hcu, hcv'⟩


end fork

section loop
variable {L : FirstOrder.Language.{u, v}} {A : Type w} [L.Structure A] {q : ℕ}



variable [Finite A] (R : Set (Fin (q + 1) → A))

theorem init_funMap {n m : ℕ} (f : L.Functions m) (ws : Fin m → Fin (n + 1) → A) :
    Fin.init (funMap f ws : Fin (n + 1) → A) = funMap f (fun i => Fin.init (ws i)) := by
  ext j; simp [Fin.init, piStr_funMap]

theorem tail_funMap {n m : ℕ} (f : L.Functions m) (ws : Fin m → Fin (n + 1) → A) :
    Fin.tail (funMap f ws : Fin (n + 1) → A) = funMap f (fun i => Fin.tail (ws i)) := by
  ext j; simp [Fin.tail, piStr_funMap]

theorem Rn_ext_left (hcyc : IsCyclicRel R) {n : ℕ} (hn : n + 1 ≤ q + 1) {w : Fin n → A}
    (hw : w ∈ Rn R n (Nat.le_of_succ_le hn)) : ∃ a : A, Fin.cons (α := fun _ => A) a w ∈ Rn R (n + 1) hn := by
  obtain ⟨r, hr, hrw⟩ := hw
  have hρ := cyc_shift hcyc hr q
  refine ⟨r (0 + (q : Fin (q + 1))), fun i => r (i + (q : Fin (q + 1))), hρ, fun i => ?_⟩
  refine Fin.cases ?_ (fun k => ?_) i
  · simp
  · simp only [Fin.cons_succ]
    show r (Fin.castLE hn (Fin.succ k) + (q : Fin (q + 1))) = w k
    have h1 : 1 ≤ (Fin.castLE hn (Fin.succ k)).val := by simp
    have h2 : Fin.castLE hn (Fin.succ k) + (q : Fin (q + 1)) = Fin.castLE (Nat.le_of_succ_le hn) k := by
      apply Fin.ext
      rw [fin_add_q_val h1]; simp
    rw [h2]; exact hrw k

/-- the digraph `H` on `R_n` -/
def Hrel (hR : IsSubuniverse L R) {n : ℕ} (hn : n + 1 ≤ q + 1) :
    Set (subS (Rn R n (Nat.le_of_succ_le hn)) (Rn_sub R hR n (Nat.le_of_succ_le hn)) ×
      subS (Rn R n (Nat.le_of_succ_le hn)) (Rn_sub R hR n (Nat.le_of_succ_le hn))) :=
  {z | ∃ w ∈ Rn R (n + 1) hn, z.1.1 = Fin.init w ∧ z.2.1 = Fin.tail w}

theorem Hrel_sub (hR : IsSubuniverse L R) {n : ℕ} (hn : n + 1 ≤ q + 1) : IsSubuniverse L (Hrel R hR hn) := by
  intro m f z hz
  choose w hwR hw1 hw2 using hz
  refine ⟨funMap f w, Rn_sub R hR (n + 1) hn m f w hwR, ?_, ?_⟩
  · show funMap f (fun i => (z i).1.1) = Fin.init (funMap f w)
    rw [init_funMap]; congr 1; funext i; exact hw1 i
  · show funMap f (fun i => (z i).2.1) = Fin.tail (funMap f w)
    rw [tail_funMap]; congr 1; funext i; exact hw2 i

theorem Hrel_smooth (hR : IsSubuniverse L R) (hcyc : IsCyclicRel R) {n : ℕ} (hn : n + 1 ≤ q + 1) :
    Smooth (Hrel R hR hn) := by
  intro x
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha⟩ := Rn_ext_right hn x.2
    refine ⟨⟨Fin.tail (Fin.snoc (α := fun _ => A) x.1 a), Rn_tail hcyc hn ha⟩, Fin.snoc (α := fun _ => A) x.1 a, ha, ?_, rfl⟩
    show x.1 = Fin.init (Fin.snoc (α := fun _ => A) x.1 a)
    rw [Fin.init_snoc]
  · obtain ⟨a, ha⟩ := Rn_ext_left R hcyc hn x.2
    refine ⟨⟨Fin.init (Fin.cons (α := fun _ => A) a x.1), Rn_init hn ha⟩, Fin.cons (α := fun _ => A) a x.1, ha, rfl, ?_⟩
    show x.1 = Fin.tail (Fin.cons (α := fun _ => A) a x.1)
    rw [Fin.tail_cons]


theorem comp_abs_outer {C : Set A} (hCs : IsSubuniverse L C) {m n : ℕ} {t : L.Term (Fin m)}
    (ht : ∀ (k : Fin m) (a : Fin m → A), (∀ i, i ≠ k → a i ∈ C) → t.realize a ∈ C) (u : L.Term (Fin n)) :
    ∀ (k : Fin (m * n)) (a : Fin (m * n) → A), (∀ i, i ≠ k → a i ∈ C) → (compTerm' t u).realize a ∈ C := by
  intro k a hk
  obtain ⟨⟨k1, k2⟩, rfl⟩ : ∃ p : Fin m × Fin n, finProdFinEquiv p = k :=
    ⟨finProdFinEquiv.symm k, finProdFinEquiv.apply_symm_apply k⟩
  rw [compTerm'_realize]
  refine ht k1 _ (fun i hi => ?_)
  refine realize_mem hCs u _ (fun j => hk _ ?_)
  intro h
  have := finProdFinEquiv.injective h
  exact hi (Prod.mk.inj this).1

theorem comp_abs_inner {D : Set A} (hDs : IsSubuniverse L D) {m n : ℕ} (t : L.Term (Fin m)) {u : L.Term (Fin n)}
    (hu : ∀ (k : Fin n) (a : Fin n → A), (∀ i, i ≠ k → a i ∈ D) → u.realize a ∈ D) :
    ∀ (k : Fin (m * n)) (a : Fin (m * n) → A), (∀ i, i ≠ k → a i ∈ D) → (compTerm' t u).realize a ∈ D := by
  intro k a hk
  obtain ⟨⟨k1, k2⟩, rfl⟩ : ∃ p : Fin m × Fin n, finProdFinEquiv p = k :=
    ⟨finProdFinEquiv.symm k, finProdFinEquiv.apply_symm_apply k⟩
  rw [compTerm'_realize]
  refine realize_mem hDs t _ (fun i => ?_)
  by_cases hi : i = k1
  · subst hi
    refine hu k2 _ (fun j hj => hk _ ?_)
    intro h
    have := finProdFinEquiv.injective h
    exact hj (Prod.mk.inj this).2
  · refine realize_mem hDs u _ (fun j => hk _ ?_)
    intro h
    have := finProdFinEquiv.injective h
    exact hi (Prod.mk.inj this).1

theorem common_term_family {ι : Type} [Fintype ι] (C : ι → Set A) (hC : ∀ l, IsAbsorbing L (C l)) :
    ∃ (m : ℕ) (t : L.Term (Fin m)), 0 < m ∧
      ∀ (l : ι) (k : Fin m) (a : Fin m → A), (∀ i, i ≠ k → a i ∈ C l) → t.realize a ∈ C l := by
  classical
  have key : ∀ s : Finset ι, ∃ (m : ℕ) (t : L.Term (Fin m)), 0 < m ∧
      ∀ l ∈ s, ∀ (k : Fin m) (a : Fin m → A), (∀ i, i ≠ k → a i ∈ C l) → t.realize a ∈ C l := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, Term.var 0, one_pos, by simp⟩
    | insert l0 s hl0 ih =>
      obtain ⟨m, t, hm, ht⟩ := ih
      obtain ⟨hs0, m0, t0, hm0, ht0⟩ := hC l0
      refine ⟨m * m0, compTerm' t t0, Nat.mul_pos hm hm0, fun l hl => ?_⟩
      rcases Finset.mem_insert.1 hl with rfl | hl'
      · exact comp_abs_inner hs0 t ht0
      · exact comp_abs_outer (hC l).1 (ht l hl') t0
  obtain ⟨m, t, hm, ht⟩ := key Finset.univ
  exact ⟨m, t, hm, fun l => ht l (Finset.mem_univ l)⟩


theorem abs_coord_pat (hR : IsSubuniverse L R) (hcyc : IsCyclicRel R) (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a)
    (C : Fin (q + 1) → Set A) (hC : ∀ l, IsAbsorbing L (C l)) (c : Fin (q + 1)) (Lset : Set (Fin (q + 1))) :
    IsAbsorbing L {a : A | ∃ r ∈ R, (∀ l ∈ Lset, r l ∈ C l) ∧ r c = a} := by
  obtain ⟨m, t, hm, ht⟩ := common_term_family C hC
  have hsub : IsSubuniverse L {a : A | ∃ r ∈ R, (∀ l ∈ Lset, r l ∈ C l) ∧ r c = a} := by
    intro n f x hx
    choose r hrR hrI hrc using hx
    refine ⟨funMap f r, hR n f r hrR, fun l hl => ?_, ?_⟩
    · rw [piStr_funMap]
      exact (hC l).1 n f _ (fun i => hrI i l hl)
    · rw [piStr_funMap]
      congr 1; ext i; exact hrc i
  refine ⟨hsub, m, t, hm, fun j a haj => ?_⟩
  have hex : ∀ i, ∃ r ∈ R, (i ≠ j → ∀ l ∈ Lset, r l ∈ C l) ∧ r c = a i := by
    intro i
    by_cases hij : i = j
    · obtain ⟨r, hr, hrc⟩ := coord_surj hcyc h0 c (a i)
      exact ⟨r, hr, fun h => absurd hij h, hrc⟩
    · obtain ⟨r, hr, hrI, hrc⟩ := haj i hij
      exact ⟨r, hr, fun _ => hrI, hrc⟩
  choose r hrR hrI hrc using hex
  refine ⟨t.realize r, realize_mem hR t r hrR, fun l hl => ?_, ?_⟩
  · rw [realize_pi]
    exact ht l j (fun i => r i l) (fun i hi => hrI i hi l hl)
  · rw [realize_pi]
    congr 1; ext i; exact hrc i

theorem ext_pattern (hR : IsSubuniverse L R) (hcyc : IsCyclicRel R) (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a)
    {m : ℕ} (hm : m + 1 ≤ q + 1) (Cm : Fin m → Set A) (hCm : ∀ i, MinAbsorbing L (Cm i))
    (hne : ∃ x ∈ Rn R m (Nat.le_of_succ_le hm), ∀ i, x i ∈ Cm i) :
    ∃ D : Set A, MinAbsorbing L D ∧ ∃ y ∈ Rn R (m + 1) hm,
      (∀ i : Fin m, y (Fin.castSucc i) ∈ Cm i) ∧ y (Fin.last m) ∈ D := by
  classical
  let Cs : Fin (q + 1) → Set A := fun l => if h : l.val < m then Cm ⟨l.val, h⟩ else Set.univ
  have hCs : ∀ l, IsAbsorbing L (Cs l) := by
    intro l
    by_cases h : l.val < m
    · simp only [Cs, h, dif_pos]; exact (hCm _).2.1
    · simp only [Cs, h, dif_neg, not_false_eq_true]; exact univ_abs
  have hmq : m < q + 1 := by omega
  set X : Set A := {a | ∃ r ∈ R, (∀ l ∈ {l : Fin (q + 1) | l.val < m}, r l ∈ Cs l) ∧ r ⟨m, hmq⟩ = a} with hX
  have hXabs : IsAbsorbing L X := abs_coord_pat R hR hcyc h0 Cs hCs ⟨m, hmq⟩ _
  obtain ⟨x, ⟨r, hr, hrx⟩, hxC⟩ := hne
  have hXne : X.Nonempty := by
    refine ⟨r ⟨m, hmq⟩, r, hr, fun l hl => ?_, rfl⟩
    have hlm : l.val < m := hl
    simp only [Cs, hlm, dif_pos]
    have := hrx ⟨l.val, hlm⟩
    have e : Fin.castLE (Nat.le_of_succ_le hm) (⟨l.val, hlm⟩ : Fin m) = l := Fin.ext rfl
    rw [e] at this
    rw [this]; exact hxC _
  obtain ⟨D, hDX, hD⟩ := exists_min_absorbing X hXabs hXne
  obtain ⟨a, ha⟩ := hD.1
  obtain ⟨r', hr', hr'C, hr'a⟩ := hDX ha
  refine ⟨D, hD, fun i => r' (Fin.castLE hm i), ⟨r', hr', fun i => rfl⟩, fun i => ?_, ?_⟩
  · have := hr'C (Fin.castLE hm (Fin.castSucc i)) (by simp)
    simpa [Cs] using this
  · have e : Fin.castLE hm (Fin.last m) = (⟨m, hmq⟩ : Fin (q + 1)) := Fin.ext (by simp)
    show r' (Fin.castLE hm (Fin.last m)) ∈ D
    rw [e, hr'a]; exact ha


/-- pattern sets of the `i`-th stage -/
def patSet (I : Set A) (Xs : ℕ → Set A) (n i : ℕ) (p : ℕ) : Set A :=
  if p < n - i then I else Xs (p - (n - i))

theorem exists_Xs (hR : IsSubuniverse L R) (hcyc : IsCyclicRel R) (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a)
    {I : Set A} (hI : MinAbsorbing L I) {n : ℕ} (h1 : 1 ≤ n) (hn : n + 1 ≤ q + 1)
    (hIpow : ∀ x : Fin n → A, (∀ i, x i ∈ I) → x ∈ Rn R n (Nat.le_of_succ_le hn)) :
    ∀ i : ℕ, i < n → ∃ Xs : ℕ → Set A, (∀ j ≤ i, MinAbsorbing L (Xs j)) ∧
      ∀ i' ≤ i, ∃ y ∈ Rn R (n + 1) hn, ∀ p : Fin (n + 1), y p ∈ patSet I Xs n i' p.val := by
  intro i
  induction i with
  | zero =>
    intro _
    obtain ⟨a, ha⟩ := hI.1
    obtain ⟨D, hD, y, hy, hyC, hyl⟩ := ext_pattern R hR hcyc h0 hn (fun _ => I) (fun _ => hI)
      ⟨fun _ => a, hIpow _ (fun _ => ha), fun _ => ha⟩
    refine ⟨fun _ => D, fun j _ => hD, fun i' hi' => ?_⟩
    have : i' = 0 := by omega
    subst this
    refine ⟨y, hy, fun p => ?_⟩
    simp only [patSet, Nat.sub_zero]
    by_cases hp : p.val < n
    · rw [if_pos hp]
      have : p = Fin.castSucc ⟨p.val, hp⟩ := Fin.ext rfl
      rw [this]; exact hyC _
    · rw [if_neg hp]
      have : p = Fin.last n := Fin.ext (by simp only [Fin.val_last]; have := p.2; omega)
      rw [this]; exact hyl
  | succ i ih =>
    intro hi
    obtain ⟨Xs, hXs, hy⟩ := ih (by omega)
    obtain ⟨y, hyR, hyp⟩ := hy i le_rfl
    -- the tail of the stage-i witness
    have hty : Fin.tail y ∈ Rn R n (Nat.le_of_succ_le hn) := Rn_tail hcyc hn hyR
    let Cm : Fin n → Set A := fun p => patSet I Xs n (i + 1) p.val
    have hCm : ∀ p, MinAbsorbing L (Cm p) := by
      intro p
      simp only [Cm, patSet]
      by_cases hp : p.val < n - (i + 1)
      · rw [if_pos hp]; exact hI
      · rw [if_neg hp]; exact hXs _ (by omega)
    obtain ⟨D, hD, y', hy'R, hy'C, hy'l⟩ := ext_pattern R hR hcyc h0 hn Cm hCm ⟨Fin.tail y, hty, fun p => by
      have := hyp (Fin.succ p)
      simp only [Cm, Fin.tail]
      simp only [patSet, Fin.val_succ, Fin.val_castSucc, Fin.val_last] at this ⊢
      by_cases hp : p.val < n - (i + 1)
      · have hp' : p.val + 1 < n - i := by omega
        rw [if_pos hp]; rw [if_pos hp'] at this; exact this
      · have hp' : ¬ p.val + 1 < n - i := by omega
        rw [if_neg hp]; rw [if_neg hp'] at this
        have e : p.val + 1 - (n - i) = p.val - (n - (i + 1)) := by omega
        rw [e] at this; exact this⟩
    refine ⟨fun j => if j = i + 1 then D else Xs j, fun j hj => ?_, fun i' hi' => ?_⟩
    · by_cases hji : j = i + 1
      · simp only [hji, if_true]; exact hD
      · simp only [hji, if_false]; exact hXs j (by omega)
    · by_cases hi'' : i' = i + 1
      · subst hi''
        refine ⟨y', hy'R, fun p => ?_⟩
        by_cases hp : p.val < n
        · have : p = Fin.castSucc ⟨p.val, hp⟩ := Fin.ext rfl
          have h2 := hy'C ⟨p.val, hp⟩
          rw [this]
          simp only [Cm, patSet, Fin.val_succ, Fin.val_castSucc, Fin.val_last] at h2 ⊢
          by_cases hq' : p.val < n - (i + 1)
          · rw [if_pos hq'] at h2 ⊢; exact h2
          · rw [if_neg hq'] at h2 ⊢
            have hne : p.val - (n - (i + 1)) ≠ i + 1 := by omega
            simp only [hne, if_false]; exact h2
        · have : p = Fin.last n := Fin.ext (by simp only [Fin.val_last]; have := p.2; omega)
          rw [this]
          simp only [patSet, Fin.val_last]
          have : ¬ (n < n - (i + 1)) := by omega
          rw [if_neg this]
          have e : n - (n - (i + 1)) = i + 1 := by omega
          rw [e]; simp only [if_true]; exact hy'l
      · obtain ⟨z, hzR, hzp⟩ := hy i' (by omega)
        refine ⟨z, hzR, fun p => ?_⟩
        have := hzp p
        simp only [patSet, Fin.val_succ, Fin.val_castSucc, Fin.val_last] at this ⊢
        by_cases hq' : p.val < n - i'
        · rw [if_pos hq'] at this ⊢; exact this
        · rw [if_neg hq'] at this ⊢
          have hne : p.val - (n - i') ≠ i + 1 := by
            have := p.2; omega
          simp only [hne, if_false]; exact this


/-- the `i`-th stage tuple, on natural-number indices -/
def Tf (n i : ℕ) (bN xN : ℕ → A) (p : ℕ) : A := if p < n - i then bN (i + p) else xN (p - (n - i))

theorem Tf_succ {n i : ℕ} (bN xN : ℕ → A) (hi : i + 1 ≤ n) (p : ℕ) (hp : p < n) :
    Tf n (i + 1) bN xN p = Tf n i bN xN (p + 1) := by
  simp only [Tf]
  by_cases h : p < n - (i + 1)
  · have h' : p + 1 < n - i := by omega
    rw [if_pos h, if_pos h']; congr 1; omega
  · have h' : ¬ p + 1 < n - i := by omega
    rw [if_neg h, if_neg h']; congr 1; omega

theorem walk413 (hR : IsSubuniverse L R) (hcyc : IsCyclicRel R) (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a)
    {I : Set A} (hI : MinAbsorbing L I) {n : ℕ} (h1 : 1 ≤ n) (hn : n + 1 ≤ q + 1)
    (hIpow : ∀ x : Fin n → A, (∀ i, x i ∈ I) → x ∈ Rn R n (Nat.le_of_succ_le hn))
    (hP2 : P2 L R hR (n + 1) hn) :
    ∃ v : subS (Rn R n (Nat.le_of_succ_le hn)) (Rn_sub R hR n (Nat.le_of_succ_le hn)),
      ∀ b : Fin n → A, (∀ i, b i ∈ I) →
        ∃ hb : b ∈ Rn R n (Nat.le_of_succ_le hn), Walk (Hrel R hR hn) ⟨b, hb⟩ v (n : ℤ) := by
  classical
  have hn' : n ≤ q + 1 := Nat.le_of_succ_le hn
  obtain ⟨a0, ha0⟩ := hI.1
  obtain ⟨Xs, hXs, hy⟩ := exists_Xs R hR hcyc h0 hI h1 hn hIpow (n - 1) (by omega)
  have hpatmin : ∀ i' ≤ n - 1, ∀ p : Fin (n + 1), MinAbsorbing L (patSet I Xs n i' p.val) := by
    intro i' hi' p
    simp only [patSet]
    by_cases hp : p.val < n - i'
    · rw [if_pos hp]; exact hI
    · rw [if_neg hp]; exact hXs _ (by have := p.2; omega)
  have hall : ∀ i' ≤ n - 1, ∀ t : Fin (n + 1) → A, (∀ p, t p ∈ patSet I Xs n i' p.val) → t ∈ Rn R (n + 1) hn := by
    intro i' hi' t ht
    obtain ⟨y, hyR, hyp⟩ := hy i' hi'
    exact (hP2 (fun p => patSet I Xs n i' p.val) (hpatmin i' hi') ⟨y, hyR, hyp⟩).1 t ht
  have hXne : ∀ j : Fin n, ∃ a, a ∈ Xs j.val := fun j => (hXs j.val (by have := j.2; omega)).1
  choose xs hxs using hXne
  let xN : ℕ → A := fun j => if h : j < n then xs ⟨j, h⟩ else a0
  have hxN : ∀ j, j < n → xN j ∈ Xs j := by
    intro j hj; simp only [xN, dif_pos hj]; exact hxs ⟨j, hj⟩
  -- the stage tuples
  have hTmem : ∀ (b : Fin n → A), (∀ i, b i ∈ I) → ∀ i ≤ n - 1,
      (fun p : Fin (n + 1) => Tf n i (fun k => if h : k < n then b ⟨k, h⟩ else a0) xN p.val) ∈ Rn R (n + 1) hn := by
    intro b hb i hi
    apply hall i hi
    intro p
    simp only [Tf, patSet]
    by_cases hp : p.val < n - i
    · rw [if_pos hp, if_pos hp]
      have : i + p.val < n := by omega
      simp only [dif_pos this]; exact hb _
    · rw [if_neg hp, if_neg hp]
      exact hxN _ (by have := p.2; omega)
  -- the target vertex
  have hvR : (fun p : Fin n => xN p.val) ∈ Rn R n hn' := by
    have := Rn_tail hcyc hn (hTmem (fun _ => a0) (fun _ => ha0) (n - 1) le_rfl)
    convert this using 1
    funext p
    simp only [Fin.tail, Tf, Fin.val_succ]
    have : ¬ (p.val + 1 < n - (n - 1)) := by omega
    rw [if_neg this]
    congr 1; omega
  refine ⟨⟨_, hvR⟩, fun b hb => ?_⟩
  have hbR : b ∈ Rn R n hn' := hIpow b hb
  refine ⟨hbR, ?_⟩
  set bN : ℕ → A := fun k => if h : k < n then b ⟨k, h⟩ else a0 with hbN
  have hbmem : ∀ i, b i ∈ I := hb
  have hT := hTmem b hb
  -- vertices
  have hVmem : ∀ k ≤ n, (fun p : Fin n => Tf n k bN xN p.val) ∈ Rn R n hn' := by
    intro k hk
    by_cases hkn : k ≤ n - 1
    · have := Rn_init hn (hT k hkn)
      convert this using 1
      funext p
      rfl
    · have hkn' : k = n := by omega
      subst hkn'
      convert hvR using 1
      funext p
      simp [Tf]
  have hedge : ∀ k (hk : k + 1 ≤ n), ((⟨_, hVmem k (by omega)⟩ : subS (Rn R n hn') (Rn_sub R hR n hn')),
      (⟨_, hVmem (k + 1) (by omega)⟩ : subS (Rn R n hn') (Rn_sub R hR n hn'))) ∈ Hrel R hR hn := by
    intro k hk
    refine ⟨_, hT k (by omega), rfl, ?_⟩
    show (fun p : Fin n => Tf n (k + 1) bN xN p.val) = Fin.tail (fun p : Fin (n + 1) => Tf n k bN xN p.val)
    funext p
    simp only [Fin.tail, Fin.val_succ]
    exact Tf_succ bN xN hk p.val p.2
  have hwalk : ∀ k (hk : k ≤ n), Walk (Hrel R hR hn) ⟨b, hbR⟩ ⟨_, hVmem k hk⟩ (k : ℤ) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have : (⟨_, hVmem 0 hk⟩ : subS (Rn R n hn') (Rn_sub R hR n hn')) = ⟨b, hbR⟩ := by
        apply Subtype.ext; funext p
        simp [Tf, hbN, p.2]
      rw [this]; simpa using Walk.refl _
    | succ k ih =>
      intro hk
      have := Walk.fwd (ih (by omega)) (hedge k hk)
      push_cast
      exact this
  have hlast := hwalk n le_rfl
  have : (⟨_, hVmem n le_rfl⟩ : subS (Rn R n hn') (Rn_sub R hR n hn')) = ⟨_, hvR⟩ := by
    apply Subtype.ext; funext p
    simp [Tf]
  rw [this] at hlast
  exact hlast


theorem I_sub_V (hR : IsSubuniverse L R) (hcyc : IsCyclicRel R) (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a)
    (hnc : ∀ a : A, (fun _ => a) ∉ R)
    (hsub : ∀ S : L.Substructure A, (S : Set A) ≠ Set.univ → HasCyclicTermOp L S (q + 1))
    {I : Set A} (hI : MinAbsorbing L I) {n : ℕ} (h1 : 1 ≤ n) (hn : n + 1 ≤ q + 1)
    (hIpow : ∀ x : Fin n → A, (∀ i, x i ∈ I) → x ∈ Rn R n (Nat.le_of_succ_le hn)) :
    I ⊆ Prod.fst '' Erel R I hn ∧ I ⊆ Prod.snd '' Erel R I hn := by
  have hV1abs := Erel_fst_abs R hR hcyc h0 hI.2.1 hn
  have hV2abs := Erel_snd_abs R hR hcyc h0 hI.2.1 hn
  by_cases hIu : I = Set.univ
  · subst hIu
    refine ⟨fun a _ => ?_, fun a _ => ?_⟩
    · obtain ⟨p, hp, hpa⟩ := (Frel_subdirect R hcyc h0 hn).1 ▸ (show a ∈ (Set.univ : Set A) from trivial)
      exact ⟨p, ⟨hp.choose, hp.choose_spec.1, hp.choose_spec.2.1, hp.choose_spec.2.2, fun _ _ => trivial⟩, hpa⟩
    · obtain ⟨p, hp, hpa⟩ := (Frel_subdirect R hcyc h0 hn).2 ▸ (show a ∈ (Set.univ : Set A) from trivial)
      exact ⟨p, ⟨hp.choose, hp.choose_spec.1, hp.choose_spec.2.1, hp.choose_spec.2.2, fun _ _ => trivial⟩, hpa⟩
  · obtain ⟨⟨J, hJ, hJI, wR, hwR, hwRI, hwRJ⟩, ⟨J', hJ', hJ'I, wL, hwL, hwL0, hwLI⟩⟩ :=
      claim49 R hR hcyc h0 hnc hsub hI hIu hn hIpow
    have hpR : (wR 0, wR (Fin.last n)) ∈ Erel R I hn := ⟨wR, hwR, rfl, rfl, fun i hi => hwRI i⟩
    have hpL : (wL 0, wL (Fin.last n)) ∈ Erel R I hn := by
      refine ⟨wL, hwL, rfl, rfl, fun i hi => ?_⟩
      have : Fin.castSucc i = Fin.succ ⟨i.val - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [this]; exact hwLI _
    have hw0 : wR 0 ∈ I := by
      have : (0 : Fin (n + 1)) = Fin.castSucc ⟨0, by omega⟩ := Fin.ext (by simp)
      rw [this]; exact hwRI _
    have hbI : wL (Fin.last n) ∈ I := by
      have : Fin.last n = Fin.succ ⟨n - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [this]; exact hwLI _
    refine ⟨?_, ?_⟩
    · have := hI.2.2 (I ∩ Prod.fst '' Erel R I hn) ⟨wR 0, hw0, _, hpR, rfl⟩ Set.inter_subset_left
        (absorbing_inter I _ hI.2.1 hV1abs)
      intro x hx; rw [← this] at hx; exact hx.2
    · have := hI.2.2 (I ∩ Prod.snd '' Erel R I hn) ⟨wL (Fin.last n), hbI, _, hpL, rfl⟩ Set.inter_subset_left
        (absorbing_inter I _ hI.2.1 hV2abs)
      intro x hx; rw [← this] at hx; exact hx.2

theorem edge_tuple (hR : IsSubuniverse L R) {W D I : Set A} (hW : MinAbsorbing L W) (hD : MinAbsorbing L D)
    (hI : MinAbsorbing L I) {n : ℕ} (h1 : 1 ≤ n) (hn : n + 1 ≤ q + 1)
    (hP2 : P2 L R hR (n + 1) hn) {w d : A} (hwd : (w, d) ∈ Erel R I hn) (hw : w ∈ W) (hd : d ∈ D) {b : A}
    (hb : b ∈ I) :
    (fun p : Fin (n + 1) => if p.val = 0 then w else if p = Fin.last n then d else b) ∈ Rn R (n + 1) hn := by
  classical
  obtain ⟨w1, hw1, hw10, hw1l, hw1I⟩ := hwd
  replace hw10 : w1 0 = w := hw10
  replace hw1l : w1 (Fin.last n) = d := hw1l
  let Q : Fin (n + 1) → Set A := fun p => if p.val = 0 then W else if p = Fin.last n then D else I
  have hQ : ∀ p, MinAbsorbing L (Q p) := by
    intro p; simp only [Q]
    by_cases h0 : p.val = 0
    · rw [if_pos h0]; exact hW
    · rw [if_neg h0]
      by_cases hl : p = Fin.last n
      · rw [if_pos hl]; exact hD
      · rw [if_neg hl]; exact hI
  have hmemQ : ∀ p, w1 p ∈ Q p := by
    intro p; simp only [Q]
    by_cases h0 : p.val = 0
    · rw [if_pos h0]
      have : p = 0 := Fin.ext h0
      rw [this, hw10]; exact hw
    · rw [if_neg h0]
      by_cases hl : p = Fin.last n
      · rw [if_pos hl, hl, hw1l]; exact hd
      · rw [if_neg hl]
        have hpn : p.val < n := by
          have := p.2; have : p.val ≠ n := fun h => hl (Fin.ext (by simp [h])); omega
        have : p = Fin.castSucc ⟨p.val, hpn⟩ := Fin.ext rfl
        rw [this]; exact hw1I ⟨p.val, hpn⟩ (by simpa using Nat.pos_of_ne_zero h0)
  refine (hP2 Q hQ ⟨w1, hw1, hmemQ⟩).1 _ (fun p => ?_)
  simp only [Q]
  by_cases h0 : p.val = 0
  · rw [if_pos h0, if_pos h0]; exact hw
  · rw [if_neg h0, if_neg h0]
    by_cases hl : p = Fin.last n
    · rw [if_pos hl, if_pos hl]; exact hd
    · rw [if_neg hl, if_neg hl]; exact hb


theorem walk414 (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hR : IsSubuniverse L R)
    (hsimple : ∀ r : A → A → Prop, Equivalence r →
      (∀ (n : ℕ) (f : L.Functions n) (x y : Fin n → A), (∀ i, r (x i) (y i)) →
        r (Structure.funMap f x) (Structure.funMap f y)) →
      (∀ a b, r a b → a = b) ∨ ∀ a b, r a b)
    (hsub : ∀ S : L.Substructure A, (S : Set A) ≠ Set.univ → HasCyclicTermOp L S (q + 1))
    (hcyc : IsCyclicRel R) (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a) (hRne : R.Nonempty)
    (hnc : ∀ a : A, (fun _ => a) ∉ R) (hprime : (q + 1).Prime) (hpA : Nat.card A < q + 1)
    {I : Set A} (hI : MinAbsorbing L I) {n : ℕ} (h1 : 1 ≤ n) (hn : n + 1 ≤ q + 1)
    (hIpow : ∀ x : Fin n → A, (∀ i, x i ∈ I) → x ∈ Rn R n (Nat.le_of_succ_le hn))
    (hP2 : P2 L R hR (n + 1) hn) {b : A} (hb : b ∈ I) :
    ∃ hβ : (fun _ : Fin n => b) ∈ Rn R n (Nat.le_of_succ_le hn),
      Walk (Hrel R hR hn) ⟨fun _ => b, hβ⟩ ⟨fun _ => b, hβ⟩ 1 := by
  classical
  have hn' : n ≤ q + 1 := Nat.le_of_succ_le hn
  have hEsub := Erel_sub R hR hI.2.1.1 (n := n) hn
  have hElin := Erel_linked R hR hA.1 hsimple hcyc h0 hRne hnc hprime hpA hI.2.1 h1 hn
  have hV1abs := Erel_fst_abs R hR hcyc h0 hI.2.1 hn
  have hV2abs := Erel_snd_abs R hR hcyc h0 hI.2.1 hn
  obtain ⟨hIV1, hIV2⟩ := I_sub_V R hR hcyc h0 hnc hsub hI h1 hn hIpow
  obtain ⟨hsubE, hsdE, hlinE⟩ := Esub_facts hEsub hElin hV1abs.1 hV2abs.1 rfl rfl
  have hT1 := subS_taylor _ hV1abs.1 T hA
  have hT2 := subS_taylor _ hV2abs.1 T hA
  have hIm1 := minAbs_restrict hV1abs.1 hV1abs hI hIV1
  have hIm2 := minAbs_restrict hV2abs.1 hV2abs hI hIV2
  let x0 : subS _ hV1abs.1 ⊕ subS _ hV2abs.1 := Sum.inl ⟨b, hIV1 hb⟩
  let y0 : subS _ hV1abs.1 ⊕ subS _ hV2abs.1 := Sum.inr ⟨b, hIV2 hb⟩
  have hrt := prop215_v T hT1 hT2 (Esub (Erel R I hn) _ _ hV1abs.1 hV2abs.1) hsubE hsdE hlinE x0 y0
    ⟨{z | z.1 ∈ I}, hIm1, hb⟩ ⟨{z | z.1 ∈ I}, hIm2, hb⟩
  have hβ : (fun _ : Fin n => b) ∈ Rn R n hn' := hIpow _ (fun _ => hb)
  let uV : A → (Fin n → A) := fun w p => if p.val = 0 then w else b
  let tV : A → (Fin n → A) := fun d p => if p.val = n - 1 then d else b
  -- the edge associated with an E-pair
  have hedge : ∀ (W D : Set A), MinAbsorbing L W → MinAbsorbing L D → ∀ w d, (w, d) ∈ Erel R I hn →
      w ∈ W → d ∈ D → ∃ (hu : uV w ∈ Rn R n hn') (ht : tV d ∈ Rn R n hn'),
        ((⟨uV w, hu⟩ : subS (Rn R n hn') (Rn_sub R hR n hn')), (⟨tV d, ht⟩ : subS (Rn R n hn') (Rn_sub R hR n hn')))
          ∈ Hrel R hR hn := by
    intro W D hW hD w d hwd hw hd
    have hT := edge_tuple R hR hW hD hI h1 hn hP2 hwd hw hd hb
    have hinit : Fin.init (fun p : Fin (n + 1) => if p.val = 0 then w else if p = Fin.last n then d else b) = uV w := by
      funext p
      simp only [Fin.init, uV, Fin.val_castSucc]
      by_cases h : p.val = 0
      · simp [h]
      · have : Fin.castSucc p ≠ Fin.last n := Fin.castSucc_ne_last p
        simp [h, this]
    have htail : Fin.tail (fun p : Fin (n + 1) => if p.val = 0 then w else if p = Fin.last n then d else b) = tV d := by
      funext p
      simp only [Fin.tail, tV, Fin.val_succ]
      by_cases h : p.val = n - 1
      · have : Fin.succ p = Fin.last n := Fin.ext (by simp; omega)
        simp [this, h]
      · have : Fin.succ p ≠ Fin.last n := fun h' => h (by have := congrArg Fin.val h'; simp at this; omega)
        simp [this, h]
    have hu : uV w ∈ Rn R n hn' := hinit ▸ Rn_init hn hT
    have ht : tV d ∈ Rn R n hn' := htail ▸ Rn_tail hcyc hn hT
    exact ⟨hu, ht, _, hT, hinit.symm, htail.symm⟩
  have huβ : uV b = fun _ => b := by funext p; simp [uV]
  have htβ : tV b = fun _ => b := by funext p; simp [tV]
  have key : ∀ z, Relation.ReflTransGen (MinStep L (Esub (Erel R I hn) _ _ hV1abs.1 hV2abs.1)) x0 z →
      (match z with
        | Sum.inl w => ∃ hu : uV w.1 ∈ Rn R n hn',
            Walk (Hrel R hR hn) ⟨fun _ => b, hβ⟩ ⟨uV w.1, hu⟩ 0
        | Sum.inr d => ∃ ht : tV d.1 ∈ Rn R n hn',
            Walk (Hrel R hR hn) ⟨fun _ => b, hβ⟩ ⟨tV d.1, ht⟩ 1) := by
    intro z hz
    induction hz with
    | refl =>
      refine ⟨by simp only [x0]; rw [huβ]; exact hβ, ?_⟩
      have : (⟨uV b, by rw [huβ]; exact hβ⟩ : subS (Rn R n hn') (Rn_sub R hR n hn')) = ⟨fun _ => b, hβ⟩ :=
        Subtype.ext huβ
      simp only [x0]
      rw [this]; exact Walk.refl _
    | @tail z₀ z₁ _ hstep ih =>
      obtain ⟨hadj, hm0, hm1⟩ := hstep
      rcases z₀ with w | d <;> rcases z₁ with w' | d'
      · exact absurd hadj (by simp [LinkAdj])
      · -- inl w → inr d'
        simp only [LinkAdj] at hadj
        obtain ⟨hu, hwalk⟩ := ih
        obtain ⟨W', hW', hwW'⟩ := hm0
        obtain ⟨D', hD', hdD'⟩ := hm1
        obtain ⟨hu', ht', hedge'⟩ := hedge _ _ (minAbs_lift hV1abs.1 hV1abs hW') (minAbs_lift hV2abs.1 hV2abs hD')
          w d' hadj ⟨w, hwW', rfl⟩ ⟨d', hdD', rfl⟩
        refine ⟨ht', ?_⟩
        have := Walk.fwd hwalk (show ((⟨uV w.1, hu⟩ : subS (Rn R n hn') (Rn_sub R hR n hn')), (⟨tV d'.1, ht'⟩ : subS (Rn R n hn') (Rn_sub R hR n hn'))) ∈ Hrel R hR hn from hedge')
        simpa using this
      · -- inr d → inl w'
        simp only [LinkAdj] at hadj
        obtain ⟨ht, hwalk⟩ := ih
        obtain ⟨D', hD', hdD'⟩ := hm0
        obtain ⟨W', hW', hwW'⟩ := hm1
        obtain ⟨hu', ht', hedge'⟩ := hedge _ _ (minAbs_lift hV1abs.1 hV1abs hW') (minAbs_lift hV2abs.1 hV2abs hD')
          w' d hadj ⟨w', hwW', rfl⟩ ⟨d, hdD', rfl⟩
        refine ⟨hu', ?_⟩
        have := Walk.bwd hwalk (show ((⟨uV w'.1, hu'⟩ : subS (Rn R n hn') (Rn_sub R hR n hn')), (⟨tV d.1, ht⟩ : subS (Rn R n hn') (Rn_sub R hR n hn'))) ∈ Hrel R hR hn from hedge')
        simpa using this
      · exact absurd hadj (by simp [LinkAdj])
  obtain ⟨ht, hwalk⟩ := key y0 hrt
  refine ⟨hβ, ?_⟩
  have : (⟨tV b, ht⟩ : subS (Rn R n hn') (Rn_sub R hR n hn')) = ⟨fun _ => b, hβ⟩ := Subtype.ext htβ
  simp only [y0] at hwalk
  rw [this] at hwalk
  exact hwalk


section homs
variable {X : Type w} {Y : Type w'} [L.Structure X] [L.Structure Y]

theorem hom_realize (h : X → Y) (hh : ∀ (m : ℕ) (f : L.Functions m) (x : Fin m → X), h (funMap f x) = funMap f (fun i => h (x i)))
    {α : Type*} (t : L.Term α) (a : α → X) : h (t.realize a) = t.realize (fun i => h (a i)) := by
  induction t with
  | var i => rfl
  | func f ts ih => simp only [Term.realize]; rw [hh]; simp only [ih]

theorem min_image_surj (h : X → Y) (hh : ∀ (m : ℕ) (f : L.Functions m) (x : Fin m → X), h (funMap f x) = funMap f (fun i => h (x i)))
    (hsurj : Function.Surjective h) {K : Set X} (hK : MinAbsorbing L K) : MinAbsorbing L (h '' K) := by
  have hpre : ∀ {F : Set Y}, IsAbsorbing L F → IsAbsorbing L (h ⁻¹' F) := by
    intro F hF
    obtain ⟨hFs, m, t, hm, ht⟩ := hF
    refine ⟨?_, m, t, hm, fun k a hak => ?_⟩
    · intro n f x hx
      show h (funMap f x) ∈ F
      rw [hh]; exact hFs n f _ hx
    · show h (t.realize a) ∈ F
      rw [hom_realize h hh]
      exact ht k _ (fun i hi => hak i hi)
  obtain ⟨hKne, ⟨hKs, m, t, hm, ht⟩, hKmin⟩ := hK
  have himg : IsAbsorbing L (h '' K) := by
    refine ⟨?_, m, t, hm, fun j a haj => ?_⟩
    · intro n f y hy
      choose x hxK hxy using hy
      refine ⟨funMap f x, hKs n f x hxK, ?_⟩
      rw [hh]; congr 1; ext i; exact hxy i
    · have hex : ∀ i, ∃ x : X, (i ≠ j → x ∈ K) ∧ h x = a i := by
        intro i
        by_cases hij : i = j
        · obtain ⟨x, hx⟩ := hsurj (a i); exact ⟨x, fun hh' => absurd hij hh', hx⟩
        · obtain ⟨x, hxK, hxa⟩ := haj i hij; exact ⟨x, fun _ => hxK, hxa⟩
      choose x hxK hxa using hex
      refine ⟨t.realize x, ht j x (fun i hi => hxK i hi), ?_⟩
      rw [hom_realize h hh]; congr 1; ext i; exact hxa i
  refine ⟨hKne.image _, himg, fun F hFne hFsub hFabs => ?_⟩
  have hPabs := absorbing_inter K _ ⟨hKs, m, t, hm, ht⟩ (hpre hFabs)
  obtain ⟨a, ha⟩ := hFne
  obtain ⟨x, hxK, hxa⟩ := hFsub ha
  have hPne : (K ∩ h ⁻¹' F).Nonempty := ⟨x, hxK, by simp only [Set.mem_preimage, hxa]; exact ha⟩
  have heq := hKmin _ hPne Set.inter_subset_left hPabs
  ext y
  constructor
  · intro hy; exact hFsub hy
  · rintro ⟨x, hxK, rfl⟩
    have : x ∈ K ∩ h ⁻¹' F := by rw [heq]; exact hxK
    exact this.2

end homs


theorem P1_step [L.IsAlgebraic] (T : TaylorDatum L) (hA : IsTaylorAlg T A) (hR : IsSubuniverse L R)
    (hsimple : ∀ r : A → A → Prop, Equivalence r →
      (∀ (n : ℕ) (f : L.Functions n) (x y : Fin n → A), (∀ i, r (x i) (y i)) →
        r (Structure.funMap f x) (Structure.funMap f y)) →
      (∀ a b, r a b → a = b) ∨ ∀ a b, r a b)
    (hsub : ∀ S : L.Substructure A, (S : Set A) ≠ Set.univ → HasCyclicTermOp L S (q + 1))
    (hcyc : IsCyclicRel R) (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a) (hRne : R.Nonempty)
    (hnc : ∀ a : A, (fun _ => a) ∉ R) (hprime : (q + 1).Prime) (hpA : Nat.card A < q + 1)
    {n : ℕ} (h1 : 1 ≤ n) (hn : n + 1 ≤ q + 1)
    (H1 : P1 L R hR n (Nat.le_of_succ_le hn)) (hP2 : P2 L R hR (n + 1) hn) : P1 L R hR (n + 1) hn := by
  classical
  have hn' : n ≤ q + 1 := Nat.le_of_succ_le hn
  obtain ⟨I, hI, hIpow, hIminX⟩ := H1
  have hTX : IsTaylorAlg T (subS (Rn R n hn') (Rn_sub R hR n hn')) := taylor_Rn T hA R hR n hn'
  let XT := subS (Rn R n hn') (Rn_sub R hR n hn')
  let Esub' : L.Substructure (XT × XT) := subS (Hrel R hR hn) (Hrel_sub R hR hn)
  have hsm : Smooth (Esub' : Set (XT × XT)) := Hrel_smooth R hR hcyc hn
  obtain ⟨b, hb⟩ := hI.1
  obtain ⟨hβ, hloop1⟩ := walk414 R T hA hR hsimple hsub hcyc h0 hRne hnc hprime hpA hI h1 hn hIpow hP2 hb
  obtain ⟨v, hv⟩ := walk413 R hR hcyc h0 hI h1 hn hIpow hP2
  obtain ⟨hβ2, hwβ⟩ := hv (fun _ => b) (fun _ => hb)
  have hlen : ∃ a, Walk (Esub' : Set (XT × XT)) a a 1 := ⟨_, hloop1⟩
  obtain ⟨-, hmore⟩ := BKAbsorption.loop_lemma T hTX Esub' hsm hlen
  have hI'ne : ({x : XT | ∀ i, x.1 i ∈ I}).Nonempty := hIminX.1
  obtain ⟨K, hK, x, hxK, hxloop⟩ := hmore _ hIminX.2.1 hI'ne ⟨⟨fun _ => b, hβ⟩, hloop1, fun x hx => by
    obtain ⟨hxR, hwx⟩ := hv x.1 hx
    exact ⟨_, hwβ.append hwx.symm⟩⟩
  obtain ⟨w, hwR, hw1, hw2⟩ := hxloop
  -- w is constant
  have hconst : ∀ j : Fin (n + 1), w j = w 0 := by
    have hstep : ∀ i : Fin n, w (Fin.castSucc i) = w (Fin.succ i) := by
      intro i
      have e1 := congrFun hw1 i
      have e2 := congrFun hw2 i
      simp only [Fin.init, Fin.tail] at e1 e2
      rw [← e1, ← e2]
    have hnat : ∀ m : ℕ, ∀ hm : m < n + 1, w ⟨m, hm⟩ = w 0 := by
      intro m
      induction m with
      | zero => intro _; rfl
      | succ m ih =>
        intro hm
        have := hstep ⟨m, by omega⟩
        have e : (Fin.succ ⟨m, by omega⟩ : Fin (n + 1)) = ⟨m + 1, hm⟩ := Fin.ext rfl
        rw [e] at this
        rw [← this]
        exact ih (by omega)
    intro j; exact hnat j.val j.2
  let π : XT → A := fun y => y.1 ⟨0, h1⟩
  have hπ : ∀ (m : ℕ) (f : L.Functions m) (y : Fin m → XT), π (funMap f y) = funMap f (fun i => π (y i)) :=
    fun m f y => rfl
  have hπsurj : Function.Surjective π := by
    intro a
    obtain ⟨r, hr, hra⟩ := h0 a
    refine ⟨⟨fun i => r (Fin.castLE hn' i), ⟨r, hr, fun _ => rfl⟩⟩, ?_⟩
    show r (Fin.castLE hn' ⟨0, h1⟩) = a
    have : Fin.castLE hn' (⟨0, h1⟩ : Fin n) = 0 := rfl
    rw [this]; exact hra
  have hJ := min_image_surj π hπ hπsurj hK
  have hcJ : w 0 ∈ π '' K := by
    refine ⟨x, hxK, ?_⟩
    show x.1 ⟨0, h1⟩ = w 0
    have := congrFun hw1 ⟨0, h1⟩
    simp only [Fin.init] at this
    rw [this]; exact hconst _
  obtain ⟨hsubJ, hminJ⟩ := hP2 (fun _ => π '' K) (fun _ => hJ) ⟨w, hwR, fun j => by rw [hconst j]; exact hcJ⟩
  exact ⟨π '' K, hJ, fun t ht => hsubJ t ht, hminJ⟩

end loop

theorem step_full [Finite A] [L.IsAlgebraic] (T : TaylorDatum L) (hA : IsTaylorAlg T A) (R : Set (Fin (q + 1) → A)) (hR : IsSubuniverse L R)
    (hsimple : ∀ r : A → A → Prop, Equivalence r →
      (∀ (n : ℕ) (f : L.Functions n) (x y : Fin n → A), (∀ i, r (x i) (y i)) →
        r (Structure.funMap f x) (Structure.funMap f y)) →
      (∀ a b, r a b → a = b) ∨ ∀ a b, r a b)
    (hsub : ∀ S : L.Substructure A, (S : Set A) ≠ Set.univ → HasCyclicTermOp L S (q + 1))
    (hcyc : IsCyclicRel R) (h0 : ∀ a : A, ∃ r ∈ R, r 0 = a) (hRne : R.Nonempty)
    (hnc : ∀ a : A, (fun _ => a) ∉ R) (hprime : (q + 1).Prime) (hpA : Nat.card A < q + 1)
    {n : ℕ} (h1 : 1 ≤ n) (hn : n + 1 ≤ q + 1)
    (H1 : P1 L R hR n (Nat.le_of_succ_le hn)) (H2 : P2 L R hR n (Nat.le_of_succ_le hn)) :
    P1 L R hR (n + 1) hn ∧ P2 L R hR (n + 1) hn := by
  obtain ⟨I, hI, hIpow, hIminX⟩ := H1
  have hS : Linked (Srel R hR hn) := by
    by_cases hIu : I = Set.univ
    · exact S_linked_univ R hR hsimple hcyc h0 hRne hnc hprime hpA hn
        (fun x => hIpow x (fun i => hIu ▸ trivial))
    · exact S_linked_proper R T hA hR hsimple hsub hcyc h0 hRne hnc hprime hpA hI hIu h1 hn hIpow H2
  have hP2 := P2_step T hA R hR hcyc h0 hn H2 hS
  exact ⟨P1_step R T hA hR hsimple hsub hcyc h0 hRne hnc hprime hpA h1 hn ⟨I, hI, hIpow, hIminX⟩ hP2, hP2⟩

theorem main_full [Finite A] [L.IsAlgebraic] (T : TaylorDatum L) (hA : IsTaylorAlg T A) (R : Set (Fin (q + 1) → A)) (hR : IsSubuniverse L R)
    (hsimple : ∀ r : A → A → Prop, Equivalence r →
      (∀ (n : ℕ) (f : L.Functions n) (x y : Fin n → A), (∀ i, r (x i) (y i)) →
        r (Structure.funMap f x) (Structure.funMap f y)) →
      (∀ a b, r a b → a = b) ∨ ∀ a b, r a b)
    (hsub : ∀ S : L.Substructure A, (S : Set A) ≠ Set.univ → HasCyclicTermOp L S (q + 1))
    (hcyc : IsCyclicRel R) (hRne : R.Nonempty)
    (hnc : ∀ a : A, (fun _ => a) ∉ R) (hprime : (q + 1).Prime) (hpA : Nat.card A < q + 1) : False := by
  have h0 := R1_univ hsub R hR hcyc hRne hnc
  have key : ∀ n : ℕ, 1 ≤ n → ∀ hn : n ≤ q + 1, P1 L R hR n hn ∧ P2 L R hR n hn := by
    intro n h1
    induction n, h1 using Nat.le_induction with
    | base => intro hn; exact base_case hsub R hR hcyc hRne hnc
    | succ n h1 ih =>
      intro hn
      have := ih (Nat.le_of_succ_le hn)
      exact step_full T hA R hR hsimple hsub hcyc h0 hRne hnc hprime hpA h1 hn this.1 this.2
  obtain ⟨I, hI, hIpow, -⟩ := (key (q + 1) (by omega) le_rfl).1
  obtain ⟨a, ha⟩ := hI.1
  obtain ⟨r, hr, hrx⟩ := hIpow (fun _ => a) (fun _ => ha)
  apply hnc a
  convert hr using 1
  ext i
  have := hrx i
  simpa using this.symm

theorem cyclic_simple_core_proof [Finite A] [L.IsAlgebraic] (T : TaylorDatum L) (hA : IsTaylorAlg T A) (p : ℕ) (hp : p.Prime)
    (hpA : Nat.card A < p)
    (hsimple : ∀ r : A → A → Prop, Equivalence r →
      (∀ (n : ℕ) (f : L.Functions n) (x y : Fin n → A), (∀ i, r (x i) (y i)) →
        r (Structure.funMap f x) (Structure.funMap f y)) →
      (∀ a b, r a b → a = b) ∨ ∀ a b, r a b)
    (hsub : ∀ S : L.Substructure A, (S : Set A) ≠ Set.univ → HasCyclicTermOp L S p) :
    HasCyclicTermOp L A p := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  rw [BKAbsorption.cyclic_iff_subpower hA.1 (q + 1) hp.two_le]
  intro R hRne hRsub hRcyc
  by_contra hnc
  push_neg at hnc
  exact main_full T hA R hRsub hsimple hsub hRcyc hRne hnc hp hpA

end glue
end BKGlue

universe u₁ v₁ w₁

open FirstOrder FirstOrder.Language in
theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] {A : Type w₁} [L.Structure A] [Finite A]
    (T : BKAbsorption.TaylorDatum L)
    (hA : BKAbsorption.IsTaylorAlg T A) (p : ℕ) (hp : p.Prime) (hpA : Nat.card A < p)
    (hsimple : ∀ r : A → A → Prop, Equivalence r →
      (∀ (n : ℕ) (f : L.Functions n) (x y : Fin n → A), (∀ i, r (x i) (y i)) →
        r (Structure.funMap f x) (Structure.funMap f y)) →
      (∀ a b, r a b → a = b) ∨ ∀ a b, r a b)
    (hsub : ∀ S : L.Substructure A, (S : Set A) ≠ Set.univ → BKAbsorption.HasCyclicTermOp L S p) :
    BKAbsorption.HasCyclicTermOp L A p :=
  BKGlue.cyclic_simple_core_proof T hA p hp hpA hsimple hsub
