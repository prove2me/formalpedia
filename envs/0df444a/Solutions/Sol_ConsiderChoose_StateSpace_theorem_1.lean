-- Prove2me | solution 1 for ConsiderChoose.StateSpace.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:59:21.006811+00:00
-- url     : https://prove2.me/submissions/a3929223-da01-4b72-8ac8-00ab8fcc9ca7

import Mathlib
import Definitions.Def_ConsiderChoose_StateSpace_Model

set_option autoImplicit false

namespace ConsiderChoose.StateSpace.InjectionProof

variable {N K : ℕ} {C : Fin K → Finset (Fin N)}

lemma reachable_nonempty {S : Finset (Fin N)} {T : Finset (Fin K)}
    (h : Reachable C S T) : S.Nonempty ∧ T.Nonempty := by
  cases h with
  | root _ hs ht => exact ⟨hs, ht⟩
  | stock _ _ _ hs ht => exact ⟨hs, ht⟩
  | skip _ _ _ hs ht => exact ⟨hs, ht⟩

lemma reachable_connected {S : Finset (Fin N)} {T : Finset (Fin K)}
    (h : Reachable C S T) : GConnected C S T := by
  cases h with
  | root hc _ _ => exact hc.2.2.1
  | stock _ _ hc _ _ => exact hc.2.2.1
  | skip _ _ hc _ _ => exact hc.2.2.1

def MissingBelow (C : Fin K → Finset (Fin N)) (S : Finset (Fin N)) (T : Finset (Fin K)) : Prop :=
  ∀ j ∈ T, ∀ i ∈ C j, i ∉ S → ∀ s ∈ S, i < s

def Blocked (C : Fin K → Finset (Fin N)) (S : Finset (Fin N)) (T : Finset (Fin K)) : Prop :=
  ∀ j, j ∉ T → (∃ s ∈ S, s ∈ C j) →
    ∃ i, (∀ s ∈ S, i < s) ∧ i ∈ C j ∧ ∀ t ∈ T, i ∉ C t

lemma component_step {S S' : Finset (Fin N)} {T U T' : Finset (Fin K)}
    (hs : S.Nonempty) (hU : U ⊆ T)
    (hcomp : IsComponent C (S.erase (S.min' hs)) U S' T')
    (hm : MissingBelow C S T) (hb : Blocked C S T)
    (hremoved : ∀ j ∈ T, j ∉ U → S.min' hs ∈ C j)
    (hremain : ∀ j ∈ U, j ∉ T ∨ S.min' hs ∉ C j ∨ U = T) :
    MissingBelow C S' T' ∧ Blocked C S' T' := by
  have hSS : S' ⊆ S := fun s hs' => Finset.mem_of_mem_erase (hcomp.1 hs')
  have hTT : T' ⊆ T := fun j hj => hU (hcomp.2.1 hj)
  have hlt : ∀ s ∈ S', S.min' hs < s := by
    intro s hs'
    have hmem := Finset.mem_erase.mp (hcomp.1 hs')
    exact lt_of_le_of_ne (Finset.min'_le S s hmem.2) (Ne.symm hmem.1)
  constructor
  · intro j hj i hi hin s hs'
    by_cases hiS : i ∈ S
    · by_cases hieq : i = S.min' hs
      · subst i
        exact hlt s hs'
      · exact False.elim (hcomp.2.2.2.2 j hj i
          (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hieq, hiS⟩, hin⟩) hi)
    · exact hm j (hTT hj) i hi hiS s (hSS hs')
  · intro j hj ⟨s, hs', hsj⟩
    by_cases hjT : j ∈ T
    · by_cases hjU : j ∈ U
      · exact False.elim (hcomp.2.2.2.1 s hs' j (Finset.mem_sdiff.mpr ⟨hjU, hj⟩) hsj)
      · refine ⟨S.min' hs, hlt, hremoved j hjT hjU, ?_⟩
        intro t ht hit
        rcases hremain t (hcomp.2.1 ht) with hnot | hnot | heq
        · exact hnot (hTT ht)
        · exact hnot hit
        · exact hjU (heq.symm ▸ hjT)
    · obtain ⟨i, hilow, hij, hit⟩ := hb j hjT ⟨s, hSS hs', hsj⟩
      exact ⟨i, fun s hs' => hilow s (hSS hs'), hij, fun t ht => hit t (hTT ht)⟩

lemma reachable_invariants {S : Finset (Fin N)} {T : Finset (Fin K)}
    (h : Reachable C S T) : MissingBelow C S T ∧ Blocked C S T := by
  induction h with
  | root hc hs ht =>
      constructor
      · intro j hj i hi hin s hs'
        exact False.elim (hc.2.2.2.2 j hj i (by simpa using hin) hi)
      · intro j hj ⟨s, hs', hsj⟩
        exact False.elim (hc.2.2.2.1 s hs' j (by simpa using hj) hsj)
  | stock hr hs hc hs' ht' ih =>
      apply component_step hs Finset.sdiff_subset hc ih.1 ih.2
      · intro j hj hjU
        by_contra hnot
        exact hjU (Finset.mem_sdiff.mpr ⟨hj, by simpa [typesOf, hj] using hnot⟩)
      · intro j hj
        exact Or.inr (Or.inl (fun hit => (Finset.mem_sdiff.mp hj).2
          (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hj).1, hit⟩)))
  | skip hr hs hc hs' ht' ih =>
      exact component_step hs (fun _ h => h) hc ih.1 ih.2
        (fun _ hj hn => False.elim (hn hj)) (fun _ _ => Or.inr (Or.inr rfl))

end ConsiderChoose.StateSpace.InjectionProof


set_option autoImplicit false

namespace ConsiderChoose.StateSpace.InjectionProof

variable {N K : ℕ} {C : Fin K → Finset (Fin N)}

@[simp] lemma bip_adj_lr (i : Fin N) (j : Fin K) :
    (bip C).Adj (Sum.inl i) (Sum.inr j) ↔ i ∈ C j := by
  simp [bip, SimpleGraph.fromRel_adj]

@[simp] lemma bip_adj_ll (i i' : Fin N) :
    ¬ (bip C).Adj (Sum.inl i) (Sum.inl i') := by
  simp [bip, SimpleGraph.fromRel_adj]

@[simp] lemma bip_adj_rr (j j' : Fin K) :
    ¬ (bip C).Adj (Sum.inr j) (Sum.inr j') := by
  simp [bip, SimpleGraph.fromRel_adj]

lemma product_incident {S : Finset (Fin N)} {T : Finset (Fin K)}
    (hc : GConnected C S T) (ht : T.Nonempty) (i : Fin N) (hi : i ∈ S) :
    ∃ j ∈ T, i ∈ C j := by
  obtain ⟨j, hj⟩ := ht
  let x : verts S T := ⟨Sum.inl i, hi⟩
  let y : verts S T := ⟨Sum.inr j, hj⟩
  have hxy : x ≠ y := by intro h; have := congrArg Subtype.val h; simp [x, y] at this
  obtain ⟨v, hv⟩ := (hc.preconnected x y).nonempty_neighborSet_left hxy
  rcases v with ⟨v, hvST⟩
  cases v with
  | inl i' => exact False.elim (bip_adj_ll i i' hv)
  | inr j' => exact ⟨j', hvST, (bip_adj_lr i j').mp hv⟩

lemma reachable_product_incident {S : Finset (Fin N)} {T : Finset (Fin K)}
    (h : Reachable C S T) (i : Fin N) (hi : i ∈ S) : ∃ j ∈ T, i ∈ C j :=
  product_incident (reachable_connected h) (reachable_nonempty h).2 i hi

lemma mem_Phi {S : Finset (Fin N)} {T : Finset (Fin K)} (hs : S.Nonempty) (i : Fin N) :
    i ∈ Phi C S T ↔ i ≤ S.min' hs ∧ ∃ j ∈ T, i ∈ C j := by
  simp [Phi, hs]

lemma min_mem_Phi {S : Finset (Fin N)} {T : Finset (Fin K)} (h : Reachable C S T) :
    S.min' (reachable_nonempty h).1 ∈ Phi C S T := by
  rw [mem_Phi (reachable_nonempty h).1]
  exact ⟨le_rfl, reachable_product_incident h _ (Finset.min'_mem _ _)⟩

lemma min_eq_of_Phi_eq {S₁ S₂ : Finset (Fin N)} {T₁ T₂ : Finset (Fin K)}
    (h₁ : Reachable C S₁ T₁) (h₂ : Reachable C S₂ T₂)
    (hPhi : Phi C S₁ T₁ = Phi C S₂ T₂) :
    S₁.min' (reachable_nonempty h₁).1 = S₂.min' (reachable_nonempty h₂).1 := by
  apply le_antisymm
  · exact ((mem_Phi (reachable_nonempty h₂).1 _).mp (hPhi ▸ min_mem_Phi h₁)).1
  · exact ((mem_Phi (reachable_nonempty h₁).1 _).mp (hPhi.symm ▸ min_mem_Phi h₂)).1

lemma reachable_suffix {S : Finset (Fin N)} {T : Finset (Fin K)}
    (h : Reachable C S T) (j : Fin K) (hj : j ∈ T) (i : Fin N) (hi : i ∈ C j)
    (hle : S.min' (reachable_nonempty h).1 ≤ i) : i ∈ S := by
  by_contra hn
  exact (not_lt_of_ge hle) ((reachable_invariants h).1 j hj i hi hn _ (Finset.min'_mem _ _))

lemma reachable_recovery {S : Finset (Fin N)} {T : Finset (Fin K)}
    (h : Reachable C S T) :
    S = (T.biUnion C).filter (S.min' (reachable_nonempty h).1 ≤ ·) := by
  ext i
  constructor
  · intro hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr (reachable_product_incident h i hi),
      Finset.min'_le S i hi⟩
  · intro hi
    obtain ⟨hiU, hle⟩ := Finset.mem_filter.mp hi
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hiU
    exact reachable_suffix h j hj i hij hle

lemma connected_propagate {V : Type*} {G : SimpleGraph V} (hc : G.Connected)
    (P : V → Prop) (hstep : ∀ x y, G.Adj x y → P x → P y)
    (a : V) (ha : P a) : ∀ b, P b := by
  intro b
  obtain ⟨w⟩ := hc.preconnected a b
  induction w with
  | nil => exact ha
  | @cons u v w huv path ih => exact ih (hstep u v huv ha)

end ConsiderChoose.StateSpace.InjectionProof


set_option autoImplicit false
open ConsiderChoose.StateSpace ConsiderChoose.StateSpace.InjectionProof

namespace ConsiderChoose.StateSpace.InjectionProof

lemma extra_type_disjoint {N K : ℕ} (C : Fin K → Finset (Fin N))
    {S₁ S₂ : Finset (Fin N)} {T₁ T₂ : Finset (Fin K)}
    (h₁ : Reachable C S₁ T₁) (h₂ : Reachable C S₂ T₂) (hΦ : Phi C S₁ T₁ = Phi C S₂ T₂)
    {u' : Fin K} (hu : u' ∈ T₂ \ T₁) : C u' ∩ S₁ = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨hsC, hsS⟩ := Finset.mem_inter.mp hs
  obtain ⟨i, hiS, hiC, hiT⟩ := (reachable_invariants h₁).2 u' (Finset.mem_sdiff.mp hu).2 ⟨s, hsS, hsC⟩
  have hmin := min_eq_of_Phi_eq h₁ h₂ hΦ
  have hilow : i ≤ S₂.min' (reachable_nonempty h₂).1 := by
    rw [← hmin]
    exact (hiS _ (Finset.min'_mem _ _)).le
  have hiPhi : i ∈ Phi C S₂ T₂ := (mem_Phi (reachable_nonempty h₂).1 i).mpr
    ⟨hilow, u', (Finset.mem_sdiff.mp hu).1, hiC⟩
  have hiPhi' : i ∈ Phi C S₁ T₁ := hΦ.symm ▸ hiPhi
  obtain ⟨j, hj, hij⟩ := ((mem_Phi (reachable_nonempty h₁).1 i).mp hiPhi').2
  exact hiT j hj hij

end ConsiderChoose.StateSpace.InjectionProof


set_option autoImplicit false

namespace ConsiderChoose.StateSpace.InjectionProof

variable {N K : ℕ} {C : Fin K → Finset (Fin N)}

lemma state_subset_of_Phi_eq {S₁ S₂ : Finset (Fin N)} {T₁ T₂ : Finset (Fin K)}
    (h₁ : Reachable C S₁ T₁) (h₂ : Reachable C S₂ T₂)
    (hPhi : Phi C S₁ T₁ = Phi C S₂ T₂) : S₂ ⊆ S₁ ∧ T₂ ⊆ T₁ := by
  have hmin := min_eq_of_Phi_eq h₁ h₂ hPhi
  let P : verts S₂ T₂ → Prop := fun v => Sum.elim (· ∈ S₁) (· ∈ T₁) v.val
  have hstep : ∀ x y : verts S₂ T₂, ((bip C).induce (verts S₂ T₂)).Adj x y → P x → P y := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hadj hp
    cases x with
    | inl i =>
        cases y with
        | inl i' => exact False.elim (bip_adj_ll i i' hadj)
        | inr j =>
            change j ∈ T₁
            by_contra hj
            have hdis := extra_type_disjoint C h₁ h₂ hPhi (Finset.mem_sdiff.mpr ⟨hy, hj⟩)
            have hmem : i ∈ C j ∩ S₁ := Finset.mem_inter.mpr ⟨(bip_adj_lr i j).mp hadj, hp⟩
            rw [hdis] at hmem
            exact Finset.notMem_empty i hmem
    | inr j =>
        cases y with
        | inr j' => exact False.elim (bip_adj_rr j j' hadj)
        | inl i =>
            change i ∈ S₁
            apply reachable_suffix h₁ j hp i ((bip_adj_lr i j).mp hadj.symm)
            rw [hmin]
            exact Finset.min'_le S₂ i hy
  let a : verts S₂ T₂ := ⟨Sum.inl (S₂.min' (reachable_nonempty h₂).1), Finset.min'_mem _ _⟩
  have ha : P a := by
    change S₂.min' (reachable_nonempty h₂).1 ∈ S₁
    rw [← hmin]
    exact Finset.min'_mem _ _
  have hall := connected_propagate (reachable_connected h₂) P hstep a ha
  exact ⟨fun i hi => hall ⟨Sum.inl i, hi⟩, fun j hj => hall ⟨Sum.inr j, hj⟩⟩

lemma reachable_eq_of_Phi_eq {S₁ S₂ : Finset (Fin N)} {T₁ T₂ : Finset (Fin K)}
    (h₁ : Reachable C S₁ T₁) (h₂ : Reachable C S₂ T₂)
    (hPhi : Phi C S₁ T₁ = Phi C S₂ T₂) : S₁ = S₂ ∧ T₁ = T₂ := by
  have h12 := state_subset_of_Phi_eq h₁ h₂ hPhi
  have h21 := state_subset_of_Phi_eq h₂ h₁ hPhi.symm
  exact ⟨Finset.Subset.antisymm h21.1 h12.1, Finset.Subset.antisymm h21.2 h12.2⟩

end ConsiderChoose.StateSpace.InjectionProof

open ConsiderChoose.StateSpace ConsiderChoose.StateSpace.InjectionProof

theorem ConsiderChoose.StateSpace.InjectionProof.central_lemma {N K : ℕ} (C : Fin K → Finset (Fin N)) :
    Set.InjOn (fun p : Finset (Fin N) × Finset (Fin K) => Phi C p.1 p.2) (stateSpace C) ∧
      ((fun p : Finset (Fin N) × Finset (Fin K) => Phi C p.1 p.2) '' stateSpace C).ncard =
        (stateSpace C).ncard := by
  have hinj : Set.InjOn (fun p : Finset (Fin N) × Finset (Fin K) => Phi C p.1 p.2) (stateSpace C) := by
    intro p hp q hq heq
    obtain ⟨hs, ht⟩ := reachable_eq_of_Phi_eq hp hq heq
    exact Prod.ext hs ht
  exact ⟨hinj, hinj.ncard_image⟩

namespace ConsiderChoose.StateSpace.CountingProof

lemma reachable_nonempty {N K : ℕ} {C : Fin K → Finset (Fin N)}
    {S : Finset (Fin N)} {T : Finset (Fin K)} (h : Reachable C S T) : S.Nonempty := by
  cases h with
  | root _ hs _ => exact hs
  | stock _ _ _ hs _ => exact hs
  | skip _ _ _ hs _ => exact hs

lemma card_bounds_of_injective {N K : ℕ} (C : Fin K → Finset (Fin N))
    (hinj : Set.InjOn (fun p : Finset (Fin N) × Finset (Fin K) => Phi C p.1 p.2)
      (stateSpace C)) :
    (stateSpace C).ncard ≤ min (2 ^ N) (N * 2 ^ K) := by
  classical
  have hcard := hinj.ncard_image
  have hpow : (stateSpace C).ncard ≤ 2 ^ N := by
    calc
      (stateSpace C).ncard =
          ((fun p : Finset (Fin N) × Finset (Fin K) => Phi C p.1 p.2) '' stateSpace C).ncard :=
        hcard.symm
      _ ≤ Nat.card (Finset (Fin N)) := Set.ncard_le_card _
      _ = 2 ^ N := by simp [Nat.card_eq_fintype_card]
  let f : Fin N × Finset (Fin K) → Finset (Fin N) :=
    fun q => (Finset.univ.filter (· ≤ q.1)) ∩ q.2.biUnion C
  have hcover :
      (fun p : Finset (Fin N) × Finset (Fin K) => Phi C p.1 p.2) '' stateSpace C ⊆
        f '' Set.univ := by
    rintro _ ⟨p, hp, rfl⟩
    have hs := reachable_nonempty hp
    refine ⟨(p.1.min' hs, p.2), Set.mem_univ _, ?_⟩
    simp only [f, Phi, dif_pos hs]
  have hprod : (stateSpace C).ncard ≤ N * 2 ^ K := by
    calc
      (stateSpace C).ncard =
          ((fun p : Finset (Fin N) × Finset (Fin K) => Phi C p.1 p.2) '' stateSpace C).ncard :=
        hcard.symm
      _ ≤ (f '' Set.univ).ncard := Set.ncard_le_ncard hcover
      _ ≤ (Set.univ : Set (Fin N × Finset (Fin K))).ncard := Set.ncard_image_le
      _ = N * 2 ^ K := by simp [Nat.card_eq_fintype_card]
  exact le_min hpow hprod

lemma polynomial_of_product_bound {N K n : ℕ} (hcount : n ≤ N * 2 ^ K)
    (c : ℕ) (hK : K ≤ c * Nat.log 2 N) : n ≤ N ^ (c + 1) := by
  by_cases hN : N = 0
  · simpa [hN] using hcount
  have hpow : 2 ^ K ≤ N ^ c := by
    calc
      2 ^ K ≤ 2 ^ (c * Nat.log 2 N) := Nat.pow_le_pow_right (by decide) hK
      _ = (2 ^ Nat.log 2 N) ^ c := by rw [Nat.mul_comm, pow_mul]
      _ ≤ N ^ c := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hN) c
  calc
    n ≤ N * 2 ^ K := hcount
    _ ≤ N * N ^ c := Nat.mul_le_mul_left N hpow
    _ = N ^ (c + 1) := by rw [pow_succ']

lemma theorem_of_injective {N K : ℕ} (C : Fin K → Finset (Fin N))
    (hinj : Set.InjOn (fun p : Finset (Fin N) × Finset (Fin K) => Phi C p.1 p.2)
      (stateSpace C)) :
    (stateSpace C).ncard ≤ min (2 ^ N) (N * 2 ^ K) ∧
      ∀ c : ℕ, K ≤ c * Nat.log 2 N → (stateSpace C).ncard ≤ N ^ (c + 1) := by
  have h := card_bounds_of_injective C hinj
  exact ⟨h, fun c hc => polynomial_of_product_bound (le_trans h (min_le_right _ _)) c hc⟩

end ConsiderChoose.StateSpace.CountingProof

open ConsiderChoose.StateSpace

theorem solution {N K : ℕ} (C : Fin K → Finset (Fin N)) :
    (stateSpace C).ncard ≤ min (2 ^ N) (N * 2 ^ K) ∧
      ∀ c : ℕ, K ≤ c * Nat.log 2 N → (stateSpace C).ncard ≤ N ^ (c + 1) := by
  exact CountingProof.theorem_of_injective C (InjectionProof.central_lemma C).1
