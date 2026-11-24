-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_clear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:03:41.732797+00:00
-- url     : https://prove2.me/submissions/35e1ec3d-d540-404b-af71-47c41b8e3cb5

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
theorem _root_.solution (R : Type) [CommRing R] (l : ℕ) (hl : l.Prime)
    (hd : ∀ a : R, ∃ m : ℕ, ¬ l ∣ m ∧ ∃ z : ℤ, (m : R) * a = z)
    {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) R)
    (hf : f ∈ weyl R r n hn ν) :
    ∃ m : ℕ, ¬ l ∣ m ∧ ∃ f0 ∈ weyl ℤ r n hn ν, (m : R) • f = map (Int.castRingHom R) f0 := by
  have hf' : f ∈ Submodule.span R
      (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord R w (hw R hn ν)) := hf
  clear hf
  induction hf' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine ⟨1, hl.not_dvd_one, applyWord ℤ w (hw ℤ hn ν), la_word_mem ℤ hn ν w, ?_⟩
    rw [← la_applyWord_map_lemma_3, la_hw_map_lemma_4, Nat.cast_one, one_smul]
  | zero =>
    exact ⟨1, hl.not_dvd_one, 0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m1, hm1, f1, hf1, e1⟩ := hx
    obtain ⟨m2, hm2, f2, hf2, e2⟩ := hy
    refine ⟨m1 * m2, fun h => ((Nat.Prime.dvd_mul hl).mp h).elim hm1 hm2,
      (m2 : ℤ) • f1 + (m1 : ℤ) • f2,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hf1) (Submodule.smul_mem _ _ hf2), ?_⟩
    rw [map_add, map_zsmul, map_zsmul, ← e1, ← e2, ← Int.cast_smul_eq_zsmul R,
      ← Int.cast_smul_eq_zsmul R, smul_smul, smul_smul, smul_add, Nat.cast_mul, Int.cast_natCast,
      Int.cast_natCast, mul_comm (m2 : R) (m1 : R)]
  | smul a x _ hx =>
    obtain ⟨m1, hm1, f1, hf1, e1⟩ := hx
    obtain ⟨m, hm, z, hz⟩ := hd a
    refine ⟨m * m1, fun h => ((Nat.Prime.dvd_mul hl).mp h).elim hm hm1, z • f1,
      Submodule.smul_mem _ _ hf1, ?_⟩
    rw [map_zsmul, ← e1, ← Int.cast_smul_eq_zsmul R, smul_smul, smul_smul, ← hz, Nat.cast_mul]
    congr 1
    ring
end Formalism.CohomologicalDescent.LA
