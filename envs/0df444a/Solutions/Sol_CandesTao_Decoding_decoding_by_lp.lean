-- Prove2me | solution 1 for CandesTao.Decoding.decoding_by_lp
-- status  : ACCEPTED   (prove)
-- author  : @radokirov
-- created : 2026-10-01T05:06:47.031007+00:00
-- url     : https://prove2.me/submissions/1596869b-0e68-4beb-8a3e-15daf46ab64d

import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_CandesTao_Decoding_L1Minimization
import Theorems.Thm_CandesTao_Decoding_l1_recovers_sparse_vector

open CandesTao.Decoding

theorem solution {p m n : ℕ} (hmn : n < m)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : Function.Injective A.mulVec)
    (F : Matrix (Fin p) (Fin m) ℝ) (hFA : F * A = 0) (S : ℕ)
    (hS : 1 ≤ S) (hSm : 3 * S ≤ m)
    (h : restrictedIsometryConst F S + restrictedOrthogonalityConst F S S +
      restrictedOrthogonalityConst F S (2 * S) < 1)
    (f : Fin n → ℝ) (e : Fin m → ℝ) (T : Finset (Fin m)) (hT : T.card ≤ S)
    (he : SupportedOn e T) :
    IsUniqueResidualL1Minimizer A (A.mulVec f + e) f := by
  -- Theorem 1.4 applied to the error vector `e`
  obtain ⟨-, hmin⟩ := l1_recovers_sparse_vector F S hS hSm h T e hT he
  intro g hg
  have hres : A.mulVec f + e - A.mulVec f = e := by abel
  rw [hres]
  -- the residual of `g` is `e + A (f - g)`, which has the same image under `F`
  apply hmin (A.mulVec f + e - A.mulVec g)
  · rw [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hFA, Matrix.zero_mulVec, Matrix.zero_mulVec]
    abel
  · intro heq
    apply hg
    apply hA
    have : A.mulVec f - A.mulVec g = 0 := by
      have h2 : A.mulVec f + e - A.mulVec g - e = 0 := by rw [heq, sub_self]
      rw [← h2]; abel
    exact (sub_eq_zero.mp this).symm
