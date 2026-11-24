-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.st_Pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:48.186344+00:00
-- url     : https://prove2.me/submissions/1d679f85-2c2c-4453-b78f-096767108e9f

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepTie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M
section steptie
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)
variable {D}
private theorem st_vec_lemma {N : ℕ} (LL : Letters N) (T : TieData) (hA : T.Admissible LL)
    (b kk : Fin T.t) (h : T.pos b = T.pos kk + 1) : False := by
  have hA' : _ ∧ _ ∧ _ := hA
  obtain ⟨-, hv, -⟩ := hA'
  obtain ⟨h1, hb1, -⟩ := hv b
  obtain ⟨h2, -, hk2⟩ := hv kk
  have he : (⟨T.pos b, by omega⟩ : Fin N) = ⟨T.pos kk + 1, h2⟩ := Fin.ext h
  rw [he, hk2] at hb1
  exact Bool.false_ne_true hb1
end steptie
end Formalism.InvariantFactorPaths.KP.LL
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)
variable {D}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (kk : Fin D.T.t)
    (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    Pt p D j jp kk y = tieP (wv D kk) (ev D kk) (zi D r kk) (si D r kk)
      (D.LL.deg (D.letterAt (D.T.pos kk)) - j kk) (D.LL.deg (D.letterAt (D.T.pos kk + 1)) - j kk) (D.T.z kk) y := by
  have hB' : _ ∧ _ ∧ _ ∧ _ := hB
  obtain ⟨hA, hlt, -, hN⟩ := hB'
  have hA' : _ ∧ _ ∧ _ := hA
  have hinj : Function.Injective D.T.pos := hA'.1.injective
  have hk1 := hlt kk
  have hu := D.uPos.2
  have e1 : ((D.letterAt (D.T.pos kk) : Fin N) : ℕ) = D.T.pos kk := by
    show min (D.T.pos kk) (N - 1) = D.T.pos kk
    omega
  have e2 : ((D.letterAt (D.T.pos kk + 1) : Fin N) : ℕ) = D.T.pos kk + 1 := by
    show min (D.T.pos kk + 1) (N - 1) = D.T.pos kk + 1
    omega
  have hs1 : (∑ i, if D.T.pos kk = D.T.pos i ∨ D.T.pos kk = D.T.pos i + 1 then j i else 0) = j kk := by
    rw [Finset.sum_eq_single kk (fun b _ hb => if_neg (by
      rintro (h | h)
      · exact hb (hinj h.symm)
      · exact st_vec_lemma D.LL D.T hA kk b h)) (fun h => absurd (Finset.mem_univ kk) h)]
    exact if_pos (Or.inl rfl)
  have hs2 : (∑ i, if D.T.pos kk + 1 = D.T.pos i ∨ D.T.pos kk + 1 = D.T.pos i + 1 then j i else 0) = j kk := by
    rw [Finset.sum_eq_single kk (fun b _ hb => if_neg (by
      rintro (h | h)
      · exact st_vec_lemma D.LL D.T hA b kk h.symm
      · exact hb (hinj (by omega)))) (fun h => absurd (Finset.mem_univ kk) h)]
    exact if_pos (Or.inr rfl)
  have hne1 : ¬ (D.letterAt (D.T.pos kk) = D.uPos) := by
    intro h
    have h' := congrArg Fin.val h
    rw [e1] at h'
    omega
  have hne2 : ¬ (D.letterAt (D.T.pos kk + 1) = D.uPos) := by
    intro h
    have h' := congrArg Fin.val h
    rw [e2] at h'
    omega
  have h1 : (D.lettersAt j jp).deg (D.letterAt (D.T.pos kk)) = D.LL.deg (D.letterAt (D.T.pos kk)) - j kk := by
    show D.LL.deg (D.letterAt (D.T.pos kk)) - (∑ i, if ((D.letterAt (D.T.pos kk) : Fin N) : ℕ) = D.T.pos i ∨
      ((D.letterAt (D.T.pos kk) : Fin N) : ℕ) = D.T.pos i + 1 then j i else 0) -
      (if D.letterAt (D.T.pos kk) = D.uPos then jp else 0) = _
    rw [e1, hs1, if_neg hne1, Nat.sub_zero]
  have h2 : (D.lettersAt j jp).deg (D.letterAt (D.T.pos kk + 1)) = D.LL.deg (D.letterAt (D.T.pos kk + 1)) - j kk := by
    show D.LL.deg (D.letterAt (D.T.pos kk + 1)) - (∑ i, if ((D.letterAt (D.T.pos kk + 1) : Fin N) : ℕ) = D.T.pos i ∨
      ((D.letterAt (D.T.pos kk + 1) : Fin N) : ℕ) = D.T.pos i + 1 then j i else 0) -
      (if D.letterAt (D.T.pos kk + 1) = D.uPos then jp else 0) = _
    rw [e2, hs2, if_neg hne2, Nat.sub_zero]
  show tieP (wv D kk) (ev D kk) (zi D r kk) (si D r kk) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos kk)))
    ((D.lettersAt j jp).deg (D.letterAt (D.T.pos kk + 1))) (D.T.z kk) y = _
  rw [h1, h2]
end Formalism.InvariantFactorPaths.KP.LL
