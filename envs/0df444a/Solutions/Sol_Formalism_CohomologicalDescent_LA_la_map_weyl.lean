-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_map_weyl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:03:37.171999+00:00
-- url     : https://prove2.me/submissions/11d3bfd3-668a-4d99-a451-ffc0c049b997

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_word_mem
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_rowGen_X
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
open MvPolynomial
noncomputable section
namespace Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
private theorem la_rowGen_map_lemma (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r)
    (g : MvPolynomial (Fin r × Fin n) ℤ) :
    rowGen R a b (map (Int.castRingHom R) g) =
      Polynomial.map (map (Int.castRingHom R)) (rowGen ℤ a b g) := by
  induction g using MvPolynomial.induction_on
  next z => simp [rowGen]
  next p q hp hq => rw [map_add, map_add, hp, hq, map_add, Polynomial.map_add]
  next p v hp =>
    simp only [map_mul, MvPolynomial.map_X, hp, Polynomial.map_mul, la_rowGen_X]
    congr 1
    split_ifs <;> simp
private theorem la_rowDiv_map_lemma_2 (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (g : MvPolynomial (Fin r × Fin n) ℤ) :
    rowDiv R a b k (map (Int.castRingHom R) g) = map (Int.castRingHom R) (rowDiv ℤ a b k g) := by
  simp only [rowDiv, la_rowGen_map_lemma, Polynomial.coeff_map]
private theorem la_applyWord_map_lemma_3 (R : Type) [CommRing R] {r n : ℕ}
    (w : List (Fin r × Fin r × ℕ)) (g : MvPolynomial (Fin r × Fin n) ℤ) :
    applyWord R w (map (Int.castRingHom R) g) = map (Int.castRingHom R) (applyWord ℤ w g) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show rowDiv R x.1 x.2.1 x.2.2 (applyWord R w (map (Int.castRingHom R) g)) =
      map (Int.castRingHom R) (rowDiv ℤ x.1 x.2.1 x.2.2 (applyWord ℤ w g))
    rw [ih, la_rowDiv_map_lemma_2]
private theorem la_hw_map_lemma_4 (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    map (Int.castRingHom R) (hw ℤ hn ν) = hw R hn ν := by
  simp only [hw, lpMinor, map_prod, map_pow, RingHom.map_det, RingHom.mapMatrix_apply]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  congr 2
  ext p q
  simp
end Formalism.CohomologicalDescent.LA
end
end

set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℤ) (hf : f ∈ weyl ℤ r n hn ν) :
    map (Int.castRingHom R) f ∈ weyl R r n hn ν := by
  have hf' : f ∈ Submodule.span ℤ
      (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord ℤ w (hw ℤ hn ν)) := hf
  clear hf
  induction hf' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    rw [← la_applyWord_map_lemma_3, la_hw_map_lemma_4]
    exact la_word_mem R hn ν w
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul z x _ hx =>
    rw [map_zsmul]
    exact zsmul_mem hx z
end Formalism.CohomologicalDescent.LA
