-- Prove2me | solution 1 for ClusterSim.EdgeCut.eqs_31_32
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T23:06:08.39841+00:00
-- url     : https://prove2.me/submissions/ed7f838b-d092-4a4a-9485-43584b05019a

import Definitions.Def_ClusterSim_EdgeCut_Cut
import Theorems.Thm_ClusterSim_EdgeCut_eqs_23_30

open ClusterSim.EdgeCut

private lemma sum_pauli_state (a b : Idx) :
    (∑ i : Fin 8, (coef i : ℂ) * (obsTensor (pauli i) a * stateTensor (eigProj i) b)) =
      if a = b then 1 else 0 := by
  have ⟨h1, h2⟩ := eqs_23_30 a b
  rw [← h2, h1]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma cut_prod_split (G : TensorNetwork) (C : Finset G.E) (s : C → Fin 8)
    (α : G.E → Idx) (β : C → Idx) :
    (coefS s : ℂ) * (∏ v' : (cut G C s).V, (cut G C s).A v' (Sum.elim α β)) =
      (∏ v : G.V, G.A v (fun e => if h : e ∈ C ∧ G.tgt e = v then β ⟨e, h.1⟩ else α e)) *
        ∏ c : C, (coef (s c) : ℂ) *
          (obsTensor (pauli (s c)) (α c.1) * stateTensor (eigProj (s c)) (β c)) := by
  change (coefS s : ℂ) * (∏ v' : G.V ⊕ (C ⊕ C), (cut G C s).A v' (Sum.elim α β)) = _
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
  have hcoef : (coefS s : ℂ) = ∏ c : C, (coef (s c) : ℂ) := by
    unfold coefS
    exact map_prod Complex.ofRealHom _ _
  rw [hcoef]
  have h1 : (∏ x : G.V, (cut G C s).A (Sum.inl x) (Sum.elim α β)) =
      ∏ v : G.V, G.A v (fun e => if h : e ∈ C ∧ G.tgt e = v then β ⟨e, h.1⟩ else α e) := rfl
  have h2 : (∏ c : C, (coef (s c) : ℂ)) *
      (∏ x : C, (cut G C s).A (Sum.inr (Sum.inl x)) (Sum.elim α β) *
        (cut G C s).A (Sum.inr (Sum.inr x)) (Sum.elim α β)) =
      ∏ c : C, (coef (s c) : ℂ) *
        (obsTensor (pauli (s c)) (α c.1) * stateTensor (eigProj (s c)) (β c)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro c _
    rfl
  rw [h1, ← h2]
  ring

theorem solution (G : TensorNetwork) (C : Finset G.E) :
    value G = ∑ s : C → Fin 8, (coefS s : ℂ) * value (cut G C s) := by
  symm
  have h_expand : ∀ s : C → Fin 8,
      (coefS s : ℂ) * value (cut G C s) =
        ∑ α : G.E → Idx, ∑ β : C → Idx,
          (coefS s : ℂ) * (∏ v' : (cut G C s).V, (cut G C s).A v' (Sum.elim α β)) := by
    intro s
    unfold value
    rw [Finset.mul_sum]
    change (∑ α' : G.E ⊕ C → Idx,
        (coefS s : ℂ) * ∏ v' : (cut G C s).V, (cut G C s).A v' α') = _
    rw [← Equiv.sum_comp (Equiv.sumArrowEquivProdArrow G.E C Idx).symm]
    rw [Fintype.sum_prod_type]
    rfl
  simp_rw [h_expand, cut_prod_split]
  rw [Finset.sum_comm]
  unfold value
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.sum_comm]
  have h_inner : ∀ β : C → Idx,
      (∑ s : C → Fin 8,
        (∏ v : G.V, G.A v (fun e => if h : e ∈ C ∧ G.tgt e = v then β ⟨e, h.1⟩ else α e)) *
          ∏ c : C, (coef (s c) : ℂ) *
            (obsTensor (pauli (s c)) (α c.1) * stateTensor (eigProj (s c)) (β c))) =
      if β = (fun c : C => α c.1) then ∏ v : G.V, G.A v α else 0 := by
    intro β
    rw [← Finset.mul_sum]
    have h_prod_sum := (Fintype.prod_sum (fun (c : C) (i : Fin 8) =>
      (coef i : ℂ) * (obsTensor (pauli i) (α c.1) * stateTensor (eigProj i) (β c)))).symm
    rw [h_prod_sum]
    simp_rw [sum_pauli_state, Finset.prod_boole]
    by_cases hβ : β = (fun c : C => α c.1)
    · subst hβ
      simp only [Finset.mem_univ, implies_true, ↓reduceIte, mul_one]
      apply Finset.prod_congr rfl
      intro v _
      congr 1
      funext e
      split_ifs <;> rfl
    · have h_not_all : ¬ ∀ x ∈ (Finset.univ : Finset C), α x.1 = β x := by
        intro hall
        apply hβ
        funext c
        exact (hall c (Finset.mem_univ c)).symm
      simp only [h_not_all, hβ, ↓reduceIte, mul_zero]
  simp_rw [h_inner]
  simp
