-- Prove2me | solution 1 for DetANN.lemma_7_1_graph
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-14T20:14:25.6886+00:00
-- url     : https://prove2.me/submissions/6b8ebb80-9a32-4aaf-b43d-10cecc8b5214

import Mathlib
import Definitions.Def_DetANN_Multigraph
import Definitions.Def_DetANN_MGG
import Theorems.Thm_DetANN_mgg_spectral_bound

open DetANN

namespace L71Red

/-- `(W f)(u) = Δ⁻¹ ∑ₖ f(nbr u k)`. -/
lemma mulVec_adjMatrix {V : Type} [Fintype V] [DecidableEq V] {Δ : ℕ}
    (nbr : V → Fin Δ → V) (f : V → ℝ) (u : V) :
    Matrix.mulVec (adjMatrix nbr) f u = (Δ : ℝ)⁻¹ * ∑ k, f (nbr u k) := by
  simp only [Matrix.mulVec, dotProduct, adjMatrix, edgeCount]
  rw [Finset.mul_sum, ← Finset.sum_fiberwise Finset.univ (fun k => nbr u k)
    (fun k => (Δ : ℝ)⁻¹ * f (nbr u k))]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.sum_congr rfl (g := fun _ => (Δ : ℝ)⁻¹ * f v)
    (fun k hk => by rw [(Finset.mem_filter.1 hk).2])]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- Split an occurrence `o : Fin 16` as `o = j + 8 t` with `j : Fin 8`, `t : Fin 2`. -/
lemma sum_fin16 {M : Type} [AddCommMonoid M] (F : Fin 16 → M) :
    ∑ o, F o = ∑ t : Fin 2, ∑ j : Fin 8,
      F ⟨j.val + 8 * t.val, by have := j.isLt; have := t.isLt; omega⟩ := by
  rw [← Fintype.sum_prod_type']
  refine (Fintype.sum_equiv (finProdFinEquiv : Fin 2 × Fin 8 ≃ Fin 16) _ _ (fun p => ?_)).symm
  congr 1

lemma base_split {M : Type} [AddCommMonoid M] (k : ℕ) (v : Lemma71Vtx k)
    (F : Lemma71Vtx k → M) :
    ∑ o, F (lemma71Base k v o) = ∑ t : Fin 2, ∑ j : Fin 8,
      F ((mggNbr (2 ^ (k / 2)) (v.1, v.2.1) j).1, (mggNbr (2 ^ (k / 2)) (v.1, v.2.1) j).2,
        ⟨t.val % (k % 2 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩) := by
  rw [sum_fin16]
  refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun j _ => ?_))
  have e1 : (⟨(j.val + 8 * t.val) % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8) = j :=
    Fin.ext (by simp)
  have e2 : (j.val + 8 * t.val) / 8 = t.val := by omega
  simp only [lemma71Base, e1, e2]

lemma fold_sum (s : ℕ) (hs : s = 0 ∨ s = 1) (φ : Fin (s + 1) → ℝ) :
    ((s : ℝ) + 1) * ∑ t : Fin 2, φ ⟨t.val % (s + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ =
      2 * ∑ c, φ c := by
  rcases hs with rfl | rfl
  · have h : ∀ c : Fin (0 + 1), c = 0 := fun c => Fin.ext (by have := c.isLt; simp)
    rw [Fin.sum_univ_two, Fin.sum_univ_one, h ⟨_, _⟩, h ⟨_, _⟩]
    push_cast; ring
  · rw [Fin.sum_univ_two, Fin.sum_univ_two]
    have h0 : (⟨(0 : Fin 2).val % (1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (1 + 1)) = 0 := rfl
    have h1 : (⟨(1 : Fin 2).val % (1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (1 + 1)) = 1 := rfl
    rw [h0, h1]; push_cast; ring

lemma fold_sq (s : ℕ) (hs : s = 0 ∨ s = 1) (φ : Fin (s + 1) → ℝ) :
    ((s : ℝ) + 1) * (1 / 2 * ∑ t : Fin 2, φ ⟨t.val % (s + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩) ^ 2
      ≤ ∑ c, φ c ^ 2 := by
  rcases hs with rfl | rfl
  · have h : ∀ c : Fin (0 + 1), c = 0 := fun c => Fin.ext (by have := c.isLt; simp)
    rw [Fin.sum_univ_two, Fin.sum_univ_one, h ⟨_, _⟩, h ⟨_, _⟩]
    push_cast; nlinarith
  · rw [Fin.sum_univ_two, Fin.sum_univ_two]
    have h0 : (⟨(0 : Fin 2).val % (1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (1 + 1)) = 0 := rfl
    have h1 : (⟨(1 : Fin 2).val % (1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (1 + 1)) = 1 := rfl
    rw [h0, h1]; push_cast; nlinarith [sq_nonneg (φ 0 - φ 1)]

/-- How many `t ∈ {0, 1}` reduce to `a` modulo `s + 1` (for `s ∈ {0, 1}`) does not depend on `a`. -/
lemma cnt_const (s : ℕ) (hs : s = 0 ∨ s = 1) (a b : ℕ) (ha : a < s + 1) (hb : b < s + 1) :
    (∑ t : Fin 2, if t.val % (s + 1) = a then 1 else 0 : ℕ) =
      ∑ t : Fin 2, if t.val % (s + 1) = b then 1 else 0 := by
  rcases hs with rfl | rfl
  · have : a = 0 := by omega
    have : b = 0 := by omega
    subst a; subst b; rfl
  · interval_cases a <;> interval_cases b <;> simp only [Fin.sum_univ_two] <;> decide

/-- Sum over `ℤ_m × ℤ_m × Fin n` as an iterated sum. -/
lemma sum_vtx {m n : ℕ} [NeZero m] (h : ZMod m × ZMod m × Fin n → ℝ) :
    ∑ x, h x = ∑ p : ZMod m × ZMod m, ∑ c : Fin n, h (p.1, p.2, c) := by
  rw [← (Equiv.prodAssoc (ZMod m) (ZMod m) (Fin n)).sum_comp, Fintype.sum_prod_type]
  rfl

end L71Red

open L71Red in
theorem solution (k : ℕ) :
    0 < theta0 ∧ theta0 < 1 ∧ IsUndirected (lemma71Nbr k) ∧
      ContractsMeanZero (adjMatrix (lemma71Nbr k)) theta0 := by
  set m := 2 ^ (k / 2) with hm
  have : NeZero m := ⟨by positivity⟩
  obtain ⟨hU, hC⟩ := mgg_spectral_bound m
  have hs : k % 2 = 0 ∨ k % 2 = 1 := Nat.mod_two_eq_zero_or_one k
  set e := lemma71Equiv k with he
  -- edge counts of the lifted graph
  have hn : ∀ u v, edgeCount (lemma71Nbr k) u v = edgeCount (lemma71Base k) (e u) (e v) := by
    intro u v
    unfold edgeCount lemma71Nbr
    congr 1
    ext o
    simp [he, Equiv.symm_apply_eq]
  have hb : ∀ x y : Lemma71Vtx k, edgeCount (lemma71Base k) x y =
      edgeCount (mggNbr m) (x.1, x.2.1) (y.1, y.2.1) *
        ∑ t : Fin 2, if t.val % (k % 2 + 1) = y.2.2.val then 1 else 0 := by
    intro x y
    unfold edgeCount
    rw [Finset.card_filter, Finset.card_filter,
      base_split k x (fun w => if w = y then 1 else 0), Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    obtain ⟨y1, y2, y3⟩ := y
    rw [ite_zero_mul_ite_zero, mul_one]
    simp only [Prod.ext_iff, Fin.ext_iff, and_assoc]
    rfl
  refine ⟨by unfold theta0; positivity, ?_, ?_, ?_⟩
  · unfold theta0
    rw [div_lt_one (by norm_num)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  · intro u v
    rw [hn, hn, hb, hb, hU]
    congr 1
    exact cnt_const (k % 2) hs _ _ (e v).2.2.isLt (e u).2.2.isLt
  · intro f hf
    set F : Lemma71Vtx k → ℝ := fun x => f (e.symm x) with hF
    set g : ZMod m × ZMod m → ℝ := fun p =>
      1 / 2 * ∑ t : Fin 2, F (p.1, p.2, ⟨t.val % (k % 2 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩)
      with hg
    have hWf : ∀ u, Matrix.mulVec (adjMatrix (lemma71Nbr k)) f u =
        Matrix.mulVec (adjMatrix (mggNbr m)) g ((e u).1, (e u).2.1) := by
      intro u
      rw [mulVec_adjMatrix, mulVec_adjMatrix]
      have : ∑ o, f (lemma71Nbr k u o) = ∑ o, F (lemma71Base k (e u) o) := rfl
      rw [this, base_split]
      simp only [hg, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun t _ => ?_))
      norm_num
      ring
    have hFsum : ∑ x, F x = 0 := by
      rw [hF, e.symm.sum_comp f, hf]
    have hg0 : ∑ p, g p = 0 := by
      have key : ((k % 2 : ℕ) + 1 : ℝ) * ∑ p, g p = ∑ x, F x := by
        rw [sum_vtx, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        have := fold_sum (k % 2) hs (fun c => F (p.1, p.2, c))
        simp only [hg]
        linarith
      rw [hFsum] at key
      have hpos : (0 : ℝ) < (k % 2 : ℕ) + 1 := by positivity
      exact (mul_eq_zero.1 key).resolve_left hpos.ne'
    have hgsq : ((k % 2 : ℕ) + 1 : ℝ) * ∑ p, g p ^ 2 ≤ ∑ x, F x ^ 2 := by
      rw [sum_vtx (fun x => F x ^ 2), Finset.mul_sum]
      exact Finset.sum_le_sum (fun p _ => fold_sq (k % 2) hs (fun c => F (p.1, p.2, c)))
    have hFsq : ∑ x, F x ^ 2 = ∑ v, f v ^ 2 := e.symm.sum_comp (fun v => f v ^ 2)
    have hmain := hC g hg0
    calc ∑ u, Matrix.mulVec (adjMatrix (lemma71Nbr k)) f u ^ 2
        = ∑ x : Lemma71Vtx k, Matrix.mulVec (adjMatrix (mggNbr m)) g (x.1, x.2.1) ^ 2 := by
          simp only [hWf]
          exact e.sum_comp (fun x => Matrix.mulVec (adjMatrix (mggNbr m)) g (x.1, x.2.1) ^ 2)
      _ = ((k % 2 : ℕ) + 1 : ℝ) * ∑ p, Matrix.mulVec (adjMatrix (mggNbr m)) g p ^ 2 := by
          rw [sum_vtx, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          simp [Finset.sum_const, Finset.card_univ]
      _ ≤ ((k % 2 : ℕ) + 1 : ℝ) * (theta0 ^ 2 * ∑ p, g p ^ 2) := by gcongr
      _ = theta0 ^ 2 * (((k % 2 : ℕ) + 1 : ℝ) * ∑ p, g p ^ 2) := by ring
      _ ≤ theta0 ^ 2 * ∑ x, F x ^ 2 := by gcongr
      _ = theta0 ^ 2 * ∑ v, f v ^ 2 := by rw [hFsq]
