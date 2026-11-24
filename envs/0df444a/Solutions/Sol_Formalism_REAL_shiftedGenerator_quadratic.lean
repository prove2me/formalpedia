-- Prove2me | solution 1 for Formalism.REAL.shiftedGenerator_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:35:56.580328+00:00
-- url     : https://prove2.me/submissions/ceca0a34-b49e-4e90-8ab9-9884bf84017a

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Theorems.Thm_Formalism_REAL_shiftedGenerator_eq_ite_smul_add
import Theorems.Thm_Formalism_REAL_ite_zero_eq_mul_ite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.REAL
private theorem Tm_eq_smul_one_add {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (x : ℂ) (a b : Fin n) :
    Tm E x a b = (x * (if a = b then (1 : ℂ) else 0)) • (1 : A) + E a b := by
  rw [shiftedGenerator_eq_ite_smul_add, ite_zero_eq_mul_ite]
end Formalism.REAL
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (x y : ℂ) (hxy : x - y = 1) (p q c d : Fin n) :
    Tm E x p c * Tm E y q d - Tm E x q c * Tm E y p d + Tm E x p d * Tm E y q c
      - Tm E x q d * Tm E y p c = 0 := by
  have hx : x = y + 1 := eq_add_of_sub_eq' hxy
  subst hx
  have h1 : E p c * E q d = E q d * E p c + ((if q = c then (1 : ℂ) else 0) • E p d
      - (if p = d then (1 : ℂ) else 0) • E q c) := by
    rw [eq_add_of_sub_eq' (hE p c q d)]
    congr 1
    rcases eq_or_ne c q with h | h
    · subst h
      rcases eq_or_ne d p with h' | h'
      · subst h'; simp
      · simp [h', h'.symm]
    · rcases eq_or_ne d p with h' | h'
      · subst h'; simp [h, h.symm]
      · simp [h, h.symm, h', h'.symm]
  have h2 : E p d * E q c = E q c * E p d + ((if q = d then (1 : ℂ) else 0) • E p c
      - (if p = c then (1 : ℂ) else 0) • E q d) := by
    rw [eq_add_of_sub_eq' (hE p d q c)]
    congr 1
    rcases eq_or_ne d q with h | h
    · subst h
      rcases eq_or_ne c p with h' | h'
      · subst h'; simp
      · simp [h', h'.symm]
    · rcases eq_or_ne c p with h' | h'
      · subst h'; simp [h, h.symm]
      · simp [h, h.symm, h', h'.symm]
  simp only [Tm_eq_smul_one_add]
  generalize (if p = c then (1 : ℂ) else 0) = δpc at h2 ⊢
  generalize (if q = d then (1 : ℂ) else 0) = δqd at h2 ⊢
  generalize (if q = c then (1 : ℂ) else 0) = δqc at h1 ⊢
  generalize (if p = d then (1 : ℂ) else 0) = δpd at h1 ⊢
  generalize E p c = Epc at h1 h2 ⊢
  generalize E q d = Eqd at h1 h2 ⊢
  generalize E q c = Eqc at h1 h2 ⊢
  generalize E p d = Epd at h1 h2 ⊢
  simp only [add_mul, mul_add]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  rw [h1, h2]
  module
end Formalism.REAL
