-- Prove2me | solution 1 for Formalism.NG.BlockDetAlt.schur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:53:01.849534+00:00
-- url     : https://prove2.me/submissions/ba9a5c09-ab20-4311-8e56-ee0b8b511146

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst
import Theorems.Thm_Formalism_NG_BlockDetAlt_detGood
import Theorems.Thm_Formalism_NG_BlockDetAlt_isUnit_det_of_const
import Theorems.Thm_Formalism_NG_BlockDetAlt_invGood

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.BlockDetAlt
variable {O : Type*} [CommRing O] {X' : Type*}
variable {d : Type} [Fintype d] [DecidableEq d]
variable {d : Type} [Fintype d] [DecidableEq d]
namespace Formalism.NG.BlockDetAlt
theorem _root_.solution (T' : Subalgebra O (X' → O)) (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    (hyp : HypDet T' R') (g : Type) [Fintype g] : SchurP T' R' g := by
  classical
  have hFin : ∀ n : ℕ, SchurP T' R' (Fin n) := by
    intro n
    induction n with
    | zero =>
      intro _ Φ _ _
      rw [Matrix.det_isEmpty]
      exact (goodS T').one_mem
    | succ n ih =>
      intro _ Φ hΦ hc
      let E : Fin (n + 1) × d ≃ d ⊕ (Fin n × d) :=
        ((finSuccEquiv n).prodCongr (Equiv.refl d)).trans (optEquiv (Fin n) d)
      have hE : ∀ i, E.symm (Sum.inl i) = (0, i) := fun i => by simp [E, optEquiv]
      have hE' : ∀ (p : Fin n) i, E.symm (Sum.inr (p, i)) = (p.succ, i) := fun p i => by simp [E, optEquiv]
      let A : Matrix d d (PowerSeries (X' → FractionRing O)) := Matrix.of fun i j => Φ (0, i) (0, j)
      let B : Matrix d (Fin n × d) (PowerSeries (X' → FractionRing O)) :=
        Matrix.of fun i Q => Φ (0, i) (Q.1.succ, Q.2)
      let C : Matrix (Fin n × d) d (PowerSeries (X' → FractionRing O)) :=
        Matrix.of fun P j => Φ (P.1.succ, P.2) (0, j)
      let D : Matrix (Fin n × d) (Fin n × d) (PowerSeries (X' → FractionRing O)) :=
        Matrix.of fun P Q => Φ (P.1.succ, P.2) (Q.1.succ, Q.2)
      have hblk : Matrix.reindex E E Φ = Matrix.fromBlocks A B C D := by
        ext (i | ⟨p, i⟩) (j | ⟨q, j⟩) <;> simp [A, B, C, D, Matrix.reindex_apply, hE, hE']
      have hc' : ∀ P Q, PowerSeries.constantCoeff (Φ P Q) = if P = Q then 1 else 0 := fun P Q => by
        have h1 := congrFun (congrFun hc P) Q
        simpa [Matrix.one_apply] using h1
      have hAc : (PowerSeries.constantCoeff).mapMatrix A = 1 := by
        ext i j
        simp [A, hc', Matrix.one_apply]
      have hAg : A ∈ goodM R' := hΦ 0 0
      haveI : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_det_of_const A hAc)
      rw [← Matrix.det_reindex_self E Φ, hblk, Matrix.det_fromBlocks₁₁]
      apply (goodS T').mul_mem (detGood T' R' hyp hAg)
      apply ih
      · intro p q
        have hb : (Matrix.of fun i j => (D - C * ⅟A * B) (p, i) (q, j)) =
            (Matrix.of fun i j => Φ (p.succ, i) (q.succ, j)) -
              (Matrix.of fun i j => Φ (p.succ, i) (0, j)) * A⁻¹ * (Matrix.of fun i j => Φ (0, i) (q.succ, j)) := by
          ext i j
          simp [A, B, C, D, Matrix.mul_apply, Matrix.invOf_eq_nonsing_inv]
        rw [hb]
        exact (goodM R').sub_mem (hΦ p.succ q.succ)
          ((goodM R').mul_mem ((goodM R').mul_mem (hΦ p.succ 0) (invGood R' hAg hAc)) (hΦ 0 q.succ))
      · ext P Q
        simp [A, B, C, D, Matrix.mul_apply, hc', Matrix.one_apply, Matrix.invOf_eq_nonsing_inv, Fin.succ_ne_zero]
        all_goals simp only [← Prod.ext_iff]
  intro _ Φ hΦ hc
  let e := Fintype.equivFin g
  let E : g × d ≃ Fin (Fintype.card g) × d := e.prodCongr (Equiv.refl d)
  have h := hFin (Fintype.card g) (Matrix.reindex E E Φ) ?_ ?_
  · rwa [Matrix.det_reindex_self] at h
  · intro p q
    have hb : (Matrix.of fun i j => Matrix.reindex E E Φ (p, i) (q, j)) =
        Matrix.of fun i j => Φ (e.symm p, i) (e.symm q, j) := by
      ext i j
      simp [E]
    rw [hb]
    exact hΦ _ _
  · rw [show (PowerSeries.constantCoeff).mapMatrix (Matrix.reindex E E Φ) =
        Matrix.reindex E E ((PowerSeries.constantCoeff).mapMatrix Φ) from rfl, hc, Matrix.reindex_apply,
      Matrix.submatrix_one_equiv]
end Formalism.NG.BlockDetAlt
