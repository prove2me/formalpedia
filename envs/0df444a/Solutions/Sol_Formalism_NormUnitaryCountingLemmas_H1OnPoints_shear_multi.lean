-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.H1OnPoints.shear_multi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:42:11.930864+00:00
-- url     : https://prove2.me/submissions/de1e7d54-532b-4d83-b2c0-b8af3283ab5e

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NatDegreeAevalLe
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_H1OnPoints_shear_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.H1OnPoints
variable {R : Type*} [CommRing R]
namespace Formalism.NormUnitaryCountingLemmas.H1OnPoints
theorem _root_.solution {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} {ν : Fin (N + 1) → ℕ}
    {F : MvPolynomial (Fin (N + 1) × Fin n) R} (hF : F ∈ H R ν)
    (y : Fin (N + 1) × Fin n → S) (s : Fin (N + 1) → S) (T : Finset (Fin (N + 1)))
    (hT : (0 : Fin (N + 1)) ∉ T) :
    aeval (fun p => y p + if p.1 ∈ T then s p.1 * y (0, p.2) else 0) F = aeval y F := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    have ha0 : a ≠ 0 := fun h => hT (h ▸ Finset.mem_insert_self _ _)
    have h0T : (0 : Fin (N + 1)) ∉ T := fun h => hT (Finset.mem_insert_of_mem h)
    have key : (fun p : Fin (N + 1) × Fin n =>
        y p + if p.1 ∈ insert a T then s p.1 * y (0, p.2) else 0) =
        fun p => (fun q : Fin (N + 1) × Fin n => y q + if q.1 ∈ T then s q.1 * y (0, q.2) else 0) p
          + if p.1 = a then s a * (fun q : Fin (N + 1) × Fin n =>
              y q + if q.1 ∈ T then s q.1 * y (0, q.2) else 0) (0, p.2) else 0 := by
      funext p
      by_cases hpa : p.1 = a
      · have : p.1 ∉ T := hpa ▸ haT
        simp [hpa, h0T, haT]
      · simp [hpa, Finset.mem_insert]
    rw [key, shear_inv hF 0 a (Fin.pos_iff_ne_zero.mpr ha0), ih h0T]
end Formalism.NormUnitaryCountingLemmas.H1OnPoints
