-- Prove2me | solution 1 for Conway99.RootedVerified.rooted_block_identities_20261003
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-03T08:16:29.187097+00:00
-- url     : https://prove2.me/submissions/7692aab4-44be-4639-a131-52f75c0117da

import Definitions.Def_Conway99_Rooted_Blocks_20261003

set_option autoImplicit false

namespace Conway99

open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem compl_adj_eq (G : SimpleGraph V) [DecidableRel G.Adj] (α : Type*) [Ring α]
    [DecidableEq α] :
    Gᶜ.adjMatrix α = (of 1 : Matrix V V α) - 1 - G.adjMatrix α := by
  have h := G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one (α := α)
  rw [G.compl_adjMatrix_eq_adjMatrix_compl α] at h
  linear_combination (norm := module) h

theorem srg_A_sq {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSRGWith 99 14 1 2)
    (α : Type*) [Ring α] [DecidableEq α] :
    (G.adjMatrix α) ^ 2
      = 12 • (1 : Matrix V V α) - G.adjMatrix α + 2 • (of 1 : Matrix V V α) := by
  have hm := h.matrix_eq (α := α)
  rw [compl_adj_eq G α] at hm
  rw [hm]; module

end Conway99

namespace Conway99.RootedVerified

open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

private lemma split_sum (f : V → ℤ) :
    (∑ v : V, f v) = f r + (∑ u : Rooted.LocT G r, f u.1) +
      (∑ w : Rooted.FarT G r, f w.1) := by
  have hr : r ∉ Rooted.LocF G r := by simp [Rooted.LocF]
  have hroot : (∑ v ∈ insert r (Rooted.LocF G r), f v) =
      f r + ∑ v ∈ Rooted.LocF G r, f v := by
    rw [Finset.sum_insert hr]
  have hloc : (∑ v ∈ Rooted.LocF G r, f v) =
      ∑ u : Rooted.LocT G r, f u.1 :=
    Finset.sum_subtype (Rooted.LocF G r) (fun _ => Iff.rfl) f
  have hfar : (∑ v ∈ Rooted.FarF G r, f v) =
      ∑ w : Rooted.FarT G r, f w.1 :=
    Finset.sum_subtype (Rooted.FarF G r) (fun _ => Iff.rfl) f
  calc
    (∑ v : V, f v) = (∑ v ∈ insert r (Rooted.LocF G r), f v) +
        (∑ v ∈ Rooted.FarF G r, f v) := by
      simpa [Rooted.FarF] using
        (Finset.sum_add_sum_compl (insert r (Rooted.LocF G r)) f).symm
    _ = _ := by rw [hroot, hloc, hfar]

private lemma far_not_root (x : Rooted.FarT G r) : x.1 ≠ r ∧ ¬ G.Adj r x.1 := by
  have hx : x.1 ∉ insert r (Rooted.LocF G r) :=
    (Finset.mem_sdiff.mp x.2).2
  simp only [Finset.mem_insert, not_or] at hx
  exact ⟨hx.1, by simpa [Rooted.LocF] using hx.2⟩

private lemma far_root_entry (x : Rooted.FarT G r) :
    G.adjMatrix ℤ x.1 r = 0 := by
  have hx := (far_not_root G r x).2
  simp [SimpleGraph.adjMatrix_apply, G.adj_comm, hx]

private lemma square_split (x : Rooted.FarT G r) (y : V) :
    (∑ v : V, G.adjMatrix ℤ x.1 v * G.adjMatrix ℤ v y) =
      (∑ u : Rooted.LocT G r,
        G.adjMatrix ℤ x.1 u.1 * G.adjMatrix ℤ u.1 y) +
      (∑ w : Rooted.FarT G r,
        G.adjMatrix ℤ x.1 w.1 * G.adjMatrix ℤ w.1 y) := by
  have hs := split_sum G r (fun v => G.adjMatrix ℤ x.1 v * G.adjMatrix ℤ v y)
  rw [far_root_entry G r x, zero_mul, zero_add] at hs
  exact hs

private lemma square_entry (h : G.IsSRGWith 99 14 1 2) (x y : V) :
    (∑ v : V, G.adjMatrix ℤ x v * G.adjMatrix ℤ v y) +
      G.adjMatrix ℤ x y = (if x = y then 12 else 0) + 2 := by
  have hh := congrArg (fun M : Matrix V V ℤ => M x y) (srg_A_sq h ℤ)
  simp only [sq, Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply] at hh
  simp [Matrix.one_apply, Matrix.of_apply] at hh ⊢
  omega

theorem transport (h : G.IsSRGWith 99 14 1 2) :
    Rooted.AFar G r * Rooted.NReg G r +
      Rooted.NReg G r * Rooted.MMate G r + Rooted.NReg G r =
      2 • allOnes (Rooted.FarT G r) (Rooted.LocT G r) ℤ := by
  ext x y
  have hxy : x.1 ≠ y.1 := by
    intro e
    have hy : G.Adj r y.1 := (G.mem_neighborFinset r y.1).mp y.2
    exact (far_not_root G r x).2 (e.symm ▸ hy)
  have hs := square_split G r x y.1
  have he := square_entry G h x.1 y.1
  simp only [if_neg hxy, zero_add] at he
  change ((∑ w : Rooted.FarT G r,
      G.adjMatrix ℤ x.1 w.1 * G.adjMatrix ℤ w.1 y.1) +
      (∑ u : Rooted.LocT G r,
        G.adjMatrix ℤ x.1 u.1 * G.adjMatrix ℤ u.1 y.1)) +
      G.adjMatrix ℤ x.1 y.1 = 2
  omega

theorem far_quadratic (h : G.IsSRGWith 99 14 1 2) :
    Rooted.AFar G r ^ 2 + Rooted.AFar G r +
      Rooted.NReg G r * (Rooted.NReg G r)ᵀ =
      12 • (1 : Matrix (Rooted.FarT G r) (Rooted.FarT G r) ℤ) +
        2 • allOnes (Rooted.FarT G r) (Rooted.FarT G r) ℤ := by
  ext x y
  have hs := square_split G r x y.1
  have he := square_entry G h x.1 y.1
  simp only [Subtype.coe_inj] at he
  simp only [sq, Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply,
    Matrix.one_apply, allOnes_apply, Rooted.AFar, Rooted.NReg,
    Matrix.submatrix_apply, Matrix.transpose_apply] at ⊢
  simp only [nsmul_eq_mul, mul_ite, mul_one, mul_zero] at ⊢
  have hsym (u : Rooted.LocT G r) :
      G.adjMatrix ℤ y.1 u.1 = G.adjMatrix ℤ u.1 y.1 := by
    simp [SimpleGraph.adjMatrix_apply, G.adj_comm]
  simp_rw [hsym]
  change (∑ w : Rooted.FarT G r,
      G.adjMatrix ℤ x.1 w.1 * G.adjMatrix ℤ w.1 y.1) +
    G.adjMatrix ℤ x.1 y.1 +
    (∑ u : Rooted.LocT G r,
      G.adjMatrix ℤ x.1 u.1 * G.adjMatrix ℤ u.1 y.1) =
      (if x = y then 12 else 0) + 2
  omega

theorem far_degree (h : G.IsSRGWith 99 14 1 2) (x : Rooted.FarT G r) :
    (∑ w : Rooted.FarT G r, Rooted.AFar G r x w) = 12 := by
  have hrow := G.adjMatrix_mulVec_const_apply_of_regular
    (α := ℤ) (a := 1) h.regular (v := x.1)
  have hrow' : (∑ v : V, G.adjMatrix ℤ x.1 v) = 14 := by
    simpa [Matrix.mulVec, dotProduct, Function.const] using hrow
  have hlocal : (∑ u : Rooted.LocT G r, G.adjMatrix ℤ x.1 u.1) = 2 := by
    have hs := square_split G r x r
    have he := square_entry G h x.1 r
    have hfar : (∑ w : Rooted.FarT G r,
        G.adjMatrix ℤ x.1 w.1 * G.adjMatrix ℤ w.1 r) = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      rw [far_root_entry G r w, mul_zero]
    have hloc : ∀ u : Rooted.LocT G r, G.adjMatrix ℤ u.1 r = 1 := by
      intro u
      have hu : G.Adj r u.1 := (G.mem_neighborFinset r u.1).mp u.2
      simp [SimpleGraph.adjMatrix_apply, G.adj_comm, hu]
    rw [hfar, add_zero] at hs
    simp_rw [hloc, mul_one] at hs
    rw [far_root_entry G r x] at he
    simp only [if_neg (far_not_root G r x).1, zero_add] at he
    omega
  have hs := split_sum G r (fun v => G.adjMatrix ℤ x.1 v)
  rw [far_root_entry G r x, zero_add] at hs
  change (∑ w : Rooted.FarT G r, G.adjMatrix ℤ x.1 w.1) = 12
  omega

end Conway99.RootedVerified

#print axioms Conway99.RootedVerified.transport
#print axioms Conway99.RootedVerified.far_quadratic
#print axioms Conway99.RootedVerified.far_degree


open Matrix Finset

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)
    (h : G.IsSRGWith 99 14 1 2) :
    (Conway99.Rooted.AFar G r * Conway99.Rooted.NReg G r +
      Conway99.Rooted.NReg G r * Conway99.Rooted.MMate G r +
      Conway99.Rooted.NReg G r =
      2 • Conway99.allOnes (Conway99.Rooted.FarT G r) (Conway99.Rooted.LocT G r) ℤ) ∧
    (Conway99.Rooted.AFar G r ^ 2 + Conway99.Rooted.AFar G r +
      Conway99.Rooted.NReg G r * (Conway99.Rooted.NReg G r)ᵀ =
      12 • (1 : Matrix (Conway99.Rooted.FarT G r) (Conway99.Rooted.FarT G r) ℤ) +
      2 • Conway99.allOnes (Conway99.Rooted.FarT G r) (Conway99.Rooted.FarT G r) ℤ) ∧
    (∀ x : Conway99.Rooted.FarT G r,
      (∑ w : Conway99.Rooted.FarT G r, Conway99.Rooted.AFar G r x w) = 12) := by
  exact ⟨Conway99.RootedVerified.transport G r h,
    Conway99.RootedVerified.far_quadratic G r h,
    Conway99.RootedVerified.far_degree G r h⟩

#print axioms solution
