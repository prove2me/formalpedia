-- Prove2me | solution 1 for DiscreteConvex.MixedMatrices.matrixSubRank_eq_card_of_nonzero_transversal
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:37:03.152997+00:00
-- url     : https://prove2.me/submissions/928793ba-a576-4ce4-9df3-623c80c34e29

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank

set_option autoImplicit false

namespace DiscreteConvex.MixedMatrices

/-- Generic block with a nonzero "transversal": if the nonzero entries of `T` are algebraically
independent over `K`, `ψ` is injective on the column set `J` and `T (ψ c) c ≠ 0` for every
`c ∈ J`, then the square block `T[ψ(J), J]` has full rank `|J|`. -/
theorem pk_matrixSubRank_eq_card_of_nonzero_transversal {R C K F : Type*} [Fintype R] [Fintype C]
    [Field K] [Field F] [Algebra K F] [DecidableEq R] [DecidableEq C] (T : Matrix R C F)
    (hT : AlgebraicIndependent K (fun e : {p : R × C // T p.1 p.2 ≠ 0} => T e.1.1 e.1.2))
    (J : Finset C) (ψ : C → R) (hψ : Set.InjOn ψ (J : Set C)) (hne : ∀ c ∈ J, T (ψ c) c ≠ 0) :
    MatrixSubRank T (J.image ψ) J = J.card := by
  classical
  -- the square block with rows reindexed by `ψ`
  let N : Matrix J J F := Matrix.of fun c c' => T (ψ c) c'
  have hdiag : ∀ c : J, N c c ≠ 0 := fun c => hne c c.2
  -- the nonzero entries of `N` are algebraically independent over `K`
  let P : Type _ := {p : J × J // N p.1 p.2 ≠ 0}
  let y : P → F := fun p => N p.1.1 p.1.2
  have hy : AlgebraicIndependent K y := by
    let g : P → {p : R × C // T p.1 p.2 ≠ 0} := fun p => ⟨(ψ p.1.1, p.1.2), p.2⟩
    have hg : Function.Injective g := by
      intro p q hpq
      have h1 : ψ p.1.1 = ψ q.1.1 := congrArg (fun e => e.1.1) hpq
      have h2 : (p.1.2 : C) = q.1.2 := congrArg (fun e => e.1.2) hpq
      apply Subtype.ext
      apply Prod.ext
      · exact Subtype.ext (hψ p.1.1.2 q.1.1.2 h1)
      · exact Subtype.ext h2
    exact hT.comp g hg
  have hinj : Function.Injective (MvPolynomial.aeval (R := K) y) :=
    algebraicIndependent_iff_injective_aeval.mp hy
  -- the generic matrix with the zero pattern of `N`
  let Y : Matrix J J (MvPolynomial P K) :=
    Matrix.of fun c c' => if h : N c c' ≠ 0 then MvPolynomial.X ⟨(c, c'), h⟩ else 0
  have hY : (MvPolynomial.aeval (R := K) y).toRingHom.mapMatrix Y = N := by
    ext c c'
    by_cases h : N c c' ≠ 0
    · simp [Y, h, y]
    · have : N c c' = 0 := not_not.mp h
      simp [Y, this]
  -- `det Y ≠ 0`: specialise the variables to the identity pattern
  have hdetY : Y.det ≠ 0 := by
    let φ : MvPolynomial P K →+* K :=
      (MvPolynomial.eval (fun p : P => if p.1.1 = p.1.2 then (1 : K) else 0))
    have hφ : φ.mapMatrix Y = 1 := by
      ext c c'
      by_cases h : N c c' ≠ 0
      · by_cases hcc : c = c'
        · subst hcc; simp [Y, h, φ]
        · simp [Y, h, φ, hcc, Matrix.one_apply_ne hcc]
      · have h0 : N c c' = 0 := not_not.mp h
        have hcc : c ≠ c' := by
          rintro rfl
          exact h (hdiag c)
        have hY0 : Y c c' = 0 := by simp [Y, h0]
        simp [hY0, Matrix.one_apply_ne hcc]
    intro h0
    have := congrArg φ h0
    rw [RingHom.map_det, hφ] at this
    simp at this
  have hdetN : N.det ≠ 0 := by
    have : (MvPolynomial.aeval (R := K) y) Y.det ≠ 0 := by
      intro h
      exact hdetY (hinj (by simpa using h))
    rw [show ((MvPolynomial.aeval (R := K) y) Y.det) = N.det from by
      have := (MvPolynomial.aeval (R := K) y).toRingHom.map_det Y
      rw [hY] at this
      simpa using this] at this
    exact this
  -- reindex the block
  let e : J ≃ (J.image ψ) := Equiv.ofBijective
    (fun c : J => (⟨ψ c, Finset.mem_image_of_mem ψ c.2⟩ : J.image ψ))
    ⟨fun a b hab => Subtype.ext (hψ a.2 b.2 (congrArg Subtype.val hab)), by
      rintro ⟨r, hr⟩
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hr
      exact ⟨⟨c, hc⟩, rfl⟩⟩
  have hsub : (T.submatrix ((↑) : J.image ψ → R) ((↑) : J → C)).submatrix e (Equiv.refl J) = N := by
    ext c c'
    rfl
  unfold MatrixSubRank
  rw [← Matrix.rank_submatrix _ e (Equiv.refl J), hsub, Matrix.rank_of_det_ne_zero hdetN]
  simp

end DiscreteConvex.MixedMatrices

open DiscreteConvex.MixedMatrices

theorem solution {R C K F : Type*} [Fintype R] [Fintype C]
    [Field K] [Field F] [Algebra K F] [DecidableEq R] [DecidableEq C] (T : Matrix R C F)
    (hT : AlgebraicIndependent K (fun e : {p : R × C // T p.1 p.2 ≠ 0} => T e.1.1 e.1.2))
    (J : Finset C) (ψ : C → R) (hψ : Set.InjOn ψ (J : Set C)) (hne : ∀ c ∈ J, T (ψ c) c ≠ 0) :
    MatrixSubRank T (J.image ψ) J = J.card :=
  pk_matrixSubRank_eq_card_of_nonzero_transversal T hT J ψ hψ hne

#print axioms solution
