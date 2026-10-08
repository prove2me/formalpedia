-- Prove2me | solution 1 for FourColourRSST.Ring.claim_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:58:04.751825+00:00
-- url     : https://prove2.me/submissions/ea7fedf5-069d-48f8-abc8-3981b27979c6

import Mathlib
import Definitions.Def_FourColourRSST_Ring_Setting

open FourColourRSST.Ring
set_option synthInstance.maxSize 10000
set_option maxRecDepth 10000
set_option maxHeartbeats 0

local instance : Fintype ℤˣ := Fintype.ofList [1, -1] (by
  intro u
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp)

private def allowed (κ : EdgeColouring 5) (θ : SignType) : Finset (SignedMatch 5) :=
  Finset.univ.filter (fun p => ¬ p.1.IsDiag ∧
    (∀ e ∈ p.1, κ e ≠ θ) ∧
    ∀ e f : Fin 5, p.1 = s(e, f) → (κ e = κ f ↔ p.2 = 1))

local instance (q : Sym2 (Fin 5)) : DecidableRel (ringMinus q).Adj := by
  unfold ringMinus
  infer_instance

attribute [-instance] Finset.fintype


private theorem bounded (κ : EdgeColouring 5) (θ : SignType)
    (M : Set (SignedMatch 5)) (hm : IsSignedMatching M) (hf : Fits θ κ M) :
    M ⊆ (allowed κ θ : Set (SignedMatch 5)) := by
  intro p hp
  simp only [allowed, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hm.1 p hp, ?_, hf.2 p hp⟩
  intro e he
  have h : e ∈ edgesOf M := ⟨p, hp, he⟩
  rw [hf.1] at h
  exact h

private theorem finite_claim1 : ∀ N ∈ (allowed (base5 0 1) 1).powerset,
    IsSignedMatching (N : Set (SignedMatch 5)) → Fits 1 (base5 0 1) N →
    Fits 1 (base5 0 2) N ∨ Fits 1 (base5 0 4) N := by
  intro N hN
  fin_cases hN
  all_goals simp only [IsSignedMatching, Fits, edgesOf, Set.ext_iff, Set.mem_ofPred_eq, Finset.mem_coe]
  all_goals decide +kernel

private theorem finite_claim1b : ∀ N ∈ (allowed (base5 0 1) (-1)).powerset,
    IsSignedMatching (N : Set (SignedMatch 5)) → Fits (-1) (base5 0 1) N →
    Fits (-1) (base5 2 1) N ∨ Fits (-1) (base5 4 1) N := by
  intro N hN
  fin_cases hN
  all_goals simp only [IsSignedMatching, Fits, edgesOf, Set.ext_iff, Set.mem_ofPred_eq, Finset.mem_coe]
  all_goals decide +kernel

private theorem finite_claim2 : ∀ N ∈ (allowed (base5 0 2) (-1)).powerset,
    IsSignedMatching (N : Set (SignedMatch 5)) → Fits (-1) (base5 0 2) N →
    Fits (-1) (base5 1 2) N ∨ Fits (-1) (base5 4 2) N := by
  intro N hN
  fin_cases hN
  all_goals simp only [IsSignedMatching, Fits, edgesOf, Set.ext_iff, Set.mem_ofPred_eq, Finset.mem_coe]
  all_goals decide +kernel

private theorem matching_cases (κ κ₁ κ₂ : EdgeColouring 5) (θ : SignType)
    (hf : ∀ N ∈ (allowed κ θ).powerset, IsSignedMatching (N : Set (SignedMatch 5)) →
      Fits θ κ N → Fits θ κ₁ N ∨ Fits θ κ₂ N)
    (C : Set (EdgeColouring 5)) (hC : Consistent C) (hκ : κ ∈ C) : κ₁ ∈ C ∨ κ₂ ∈ C := by
  classical
  obtain ⟨M, hm, hfit, hall⟩ := hC κ hκ θ
  let N := M.toFinset
  have heq : (N : Set (SignedMatch 5)) = M := Set.coe_toFinset M
  have hN : N ∈ (allowed κ θ).powerset := by
    rw [Finset.mem_powerset]
    intro p hp
    exact bounded κ θ M hm hfit (by simpa [N] using hp)
  rcases hf N hN (heq.symm ▸ hm) (heq.symm ▸ hfit) with h | h
  · exact Or.inl (hall _ (heq ▸ h))
  · exact Or.inr (hall _ (heq ▸ h))
private theorem fits_perm {k : ℕ} (θ : SignType) (κ : EdgeColouring k)
    (M : Set (SignedMatch k)) (σ : Equiv.Perm SignType) (hσ : σ θ = θ)
    (h : Fits θ κ M) : Fits θ (fun e => σ (κ e)) M := by
  constructor
  · rw [h.1]
    ext e
    change (κ e ≠ θ) ↔ (σ (κ e) ≠ θ)
    have he : σ (κ e) = θ ↔ κ e = θ := by
      constructor
      · intro h; exact σ.injective (h.trans hσ.symm)
      · intro h; exact (congrArg σ h).trans hσ
    exact not_congr he.symm
  · intro p hp e f hef
    rw [σ.injective.eq_iff]
    exact h.2 p hp e f hef

private theorem colour_closed {k : ℕ} [NeZero k]
    (C : Set (EdgeColouring k)) (hC : Consistent C)
    (σ : Equiv.Perm SignType) : ∀ κ ∈ C, (fun e => σ (κ e)) ∈ C := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simpa using (fun κ (hκ : κ ∈ C) => hκ)
  | swap_mul σ a b hab ih =>
    intro κ hκ
    have hex : ∃ θ : SignType, Equiv.swap a b θ = θ := by
      cases a <;> cases b <;> decide
    obtain ⟨θ, hθ⟩ := hex
    obtain ⟨M, _, hfit, hall⟩ := hC _ (ih κ hκ) θ
    exact hall _ (fits_perm θ _ M (Equiv.swap a b) hθ hfit)


private theorem class_mem (C : Set (EdgeColouring 5)) (hC : Consistent C)
    (i j : Fin 5) (h : base5 i j ∈ C) : A i j ⊆ C := by
  intro κ hκ
  obtain ⟨σ, hσ⟩ := hκ
  rw [show κ = fun e => σ (base5 i j e) from funext hσ]
  exact colour_closed C hC σ _ h

private theorem base_mem (i j : Fin 5) : base5 i j ∈ A i j :=
  ⟨1, fun _ => rfl⟩

private theorem reverse_class (i j : Fin 5) (hij : i ≠ j) : A i j = A j i := by
  have he : base5 j i = fun e => Equiv.swap (1 : SignType) (-1) (base5 i j e) := by
    funext e
    by_cases h₁ : e = i <;> by_cases h₂ : e = j <;>
      simp_all [base5, Equiv.swap_apply_def]
  ext κ
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ * Equiv.swap (1 : SignType) (-1), ?_⟩
    intro e
    rw [hσ e, he]
    simp
  · rintro ⟨σ, hσ⟩
    refine ⟨σ * Equiv.swap (1 : SignType) (-1), ?_⟩
    intro e
    rw [hσ e, he]
    rfl

theorem solution (C : Set (EdgeColouring 5)) (hC : Consistent C) (h12 : A 0 1 ⊆ C) :
    (A 0 2 ⊆ C ∨ A 0 4 ⊆ C) ∧ (A 1 2 ⊆ C ∨ A 1 4 ⊆ C) := by
  have hκ := h12 (base_mem 0 1)
  constructor
  · rcases matching_cases _ _ _ 1 finite_claim1 C hC hκ with h | h
    · exact Or.inl (class_mem C hC 0 2 h)
    · exact Or.inr (class_mem C hC 0 4 h)
  · rcases matching_cases _ _ _ (-1) finite_claim1b C hC hκ with h | h
    · left
      rw [reverse_class 1 2 (by decide)]
      exact class_mem C hC 2 1 h
    · right
      rw [reverse_class 1 4 (by decide)]
      exact class_mem C hC 4 1 h

#print axioms solution
